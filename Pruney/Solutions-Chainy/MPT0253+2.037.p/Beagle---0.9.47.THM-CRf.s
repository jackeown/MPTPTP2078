%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:18 EST 2020

% Result     : Theorem 2.94s
% Output     : CNFRefutation 2.94s
% Verified   : 
% Statistics : Number of formulae       :   55 (  61 expanded)
%              Number of leaves         :   28 (  32 expanded)
%              Depth                    :   10
%              Number of atoms          :   52 (  62 expanded)
%              Number of equality atoms :   33 (  39 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r2_hidden(A,B)
          & r2_hidden(C,B) )
       => k2_xboole_0(k2_tarski(A,C),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(C,B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_enumset1)).

tff(f_43,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_41,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_49,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(c_34,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_32,plain,(
    r2_hidden('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_306,plain,(
    ! [A_68,B_69,C_70] :
      ( r1_tarski(k2_tarski(A_68,B_69),C_70)
      | ~ r2_hidden(B_69,C_70)
      | ~ r2_hidden(A_68,C_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = A_5
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_939,plain,(
    ! [A_109,B_110,C_111] :
      ( k3_xboole_0(k2_tarski(A_109,B_110),C_111) = k2_tarski(A_109,B_110)
      | ~ r2_hidden(B_110,C_111)
      | ~ r2_hidden(A_109,C_111) ) ),
    inference(resolution,[status(thm)],[c_306,c_6])).

tff(c_53,plain,(
    ! [B_35,A_36] : k3_xboole_0(B_35,A_36) = k3_xboole_0(A_36,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_71,plain,(
    ! [B_35,A_36] : k2_xboole_0(B_35,k3_xboole_0(A_36,B_35)) = B_35 ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_4])).

tff(c_990,plain,(
    ! [C_114,A_115,B_116] :
      ( k2_xboole_0(C_114,k2_tarski(A_115,B_116)) = C_114
      | ~ r2_hidden(B_116,C_114)
      | ~ r2_hidden(A_115,C_114) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_939,c_71])).

tff(c_168,plain,(
    ! [C_54,B_55,A_56] : k1_enumset1(C_54,B_55,A_56) = k1_enumset1(A_56,B_55,C_54) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,(
    ! [A_18,B_19] : k1_enumset1(A_18,A_18,B_19) = k2_tarski(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_184,plain,(
    ! [C_54,B_55] : k1_enumset1(C_54,B_55,B_55) = k2_tarski(B_55,C_54) ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_16])).

tff(c_12,plain,(
    ! [A_14,B_15,C_16] : k2_xboole_0(k2_tarski(A_14,B_15),k1_tarski(C_16)) = k1_enumset1(A_14,B_15,C_16) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_14,plain,(
    ! [A_17] : k2_tarski(A_17,A_17) = k1_tarski(A_17) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_442,plain,(
    ! [A_85,B_86,C_87,D_88] : k2_xboole_0(k2_tarski(A_85,B_86),k2_tarski(C_87,D_88)) = k2_enumset1(A_85,B_86,C_87,D_88) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_462,plain,(
    ! [A_85,B_86,A_17] : k2_xboole_0(k2_tarski(A_85,B_86),k1_tarski(A_17)) = k2_enumset1(A_85,B_86,A_17,A_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_442])).

tff(c_467,plain,(
    ! [A_89,B_90,A_91] : k2_enumset1(A_89,B_90,A_91,A_91) = k1_enumset1(A_89,B_90,A_91) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_462])).

tff(c_18,plain,(
    ! [A_20,B_21,C_22] : k2_enumset1(A_20,A_20,B_21,C_22) = k1_enumset1(A_20,B_21,C_22) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_474,plain,(
    ! [B_90,A_91] : k1_enumset1(B_90,B_90,A_91) = k1_enumset1(B_90,A_91,A_91) ),
    inference(superposition,[status(thm),theory(equality)],[c_467,c_18])).

tff(c_486,plain,(
    ! [B_92,A_93] : k2_tarski(B_92,A_93) = k2_tarski(A_93,B_92) ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_16,c_474])).

tff(c_22,plain,(
    ! [A_27,B_28] : k3_tarski(k2_tarski(A_27,B_28)) = k2_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_561,plain,(
    ! [B_94,A_95] : k3_tarski(k2_tarski(B_94,A_95)) = k2_xboole_0(A_95,B_94) ),
    inference(superposition,[status(thm),theory(equality)],[c_486,c_22])).

tff(c_567,plain,(
    ! [B_94,A_95] : k2_xboole_0(B_94,A_95) = k2_xboole_0(A_95,B_94) ),
    inference(superposition,[status(thm),theory(equality)],[c_561,c_22])).

tff(c_30,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_3'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_587,plain,(
    k2_xboole_0('#skF_2',k2_tarski('#skF_1','#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_567,c_30])).

tff(c_1004,plain,
    ( ~ r2_hidden('#skF_3','#skF_2')
    | ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_990,c_587])).

tff(c_1057,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_1004])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.15/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.36  % Computer   : n007.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 16:33:36 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.21/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.94/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.94/1.49  
% 2.94/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.94/1.49  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 2.94/1.49  
% 2.94/1.49  %Foreground sorts:
% 2.94/1.49  
% 2.94/1.49  
% 2.94/1.49  %Background operators:
% 2.94/1.49  
% 2.94/1.49  
% 2.94/1.49  %Foreground operators:
% 2.94/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.94/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.94/1.49  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.94/1.49  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.94/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.94/1.49  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.94/1.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.94/1.49  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.94/1.49  tff('#skF_2', type, '#skF_2': $i).
% 2.94/1.49  tff('#skF_3', type, '#skF_3': $i).
% 2.94/1.49  tff('#skF_1', type, '#skF_1': $i).
% 2.94/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.94/1.49  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.94/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.94/1.49  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.94/1.49  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.94/1.49  
% 2.94/1.50  tff(f_62, negated_conjecture, ~(![A, B, C]: ((r2_hidden(A, B) & r2_hidden(C, B)) => (k2_xboole_0(k2_tarski(A, C), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_zfmisc_1)).
% 2.94/1.50  tff(f_55, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.94/1.50  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.94/1.50  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.94/1.50  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 2.94/1.50  tff(f_37, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(C, B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t102_enumset1)).
% 2.94/1.50  tff(f_43, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.94/1.50  tff(f_39, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_enumset1)).
% 2.94/1.50  tff(f_41, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.94/1.50  tff(f_35, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l53_enumset1)).
% 2.94/1.50  tff(f_45, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.94/1.50  tff(f_49, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.94/1.50  tff(c_34, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.94/1.50  tff(c_32, plain, (r2_hidden('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.94/1.50  tff(c_306, plain, (![A_68, B_69, C_70]: (r1_tarski(k2_tarski(A_68, B_69), C_70) | ~r2_hidden(B_69, C_70) | ~r2_hidden(A_68, C_70))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.94/1.50  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=A_5 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.94/1.50  tff(c_939, plain, (![A_109, B_110, C_111]: (k3_xboole_0(k2_tarski(A_109, B_110), C_111)=k2_tarski(A_109, B_110) | ~r2_hidden(B_110, C_111) | ~r2_hidden(A_109, C_111))), inference(resolution, [status(thm)], [c_306, c_6])).
% 2.94/1.50  tff(c_53, plain, (![B_35, A_36]: (k3_xboole_0(B_35, A_36)=k3_xboole_0(A_36, B_35))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.94/1.50  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k3_xboole_0(A_3, B_4))=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.94/1.50  tff(c_71, plain, (![B_35, A_36]: (k2_xboole_0(B_35, k3_xboole_0(A_36, B_35))=B_35)), inference(superposition, [status(thm), theory('equality')], [c_53, c_4])).
% 2.94/1.50  tff(c_990, plain, (![C_114, A_115, B_116]: (k2_xboole_0(C_114, k2_tarski(A_115, B_116))=C_114 | ~r2_hidden(B_116, C_114) | ~r2_hidden(A_115, C_114))), inference(superposition, [status(thm), theory('equality')], [c_939, c_71])).
% 2.94/1.50  tff(c_168, plain, (![C_54, B_55, A_56]: (k1_enumset1(C_54, B_55, A_56)=k1_enumset1(A_56, B_55, C_54))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.94/1.50  tff(c_16, plain, (![A_18, B_19]: (k1_enumset1(A_18, A_18, B_19)=k2_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.94/1.50  tff(c_184, plain, (![C_54, B_55]: (k1_enumset1(C_54, B_55, B_55)=k2_tarski(B_55, C_54))), inference(superposition, [status(thm), theory('equality')], [c_168, c_16])).
% 2.94/1.50  tff(c_12, plain, (![A_14, B_15, C_16]: (k2_xboole_0(k2_tarski(A_14, B_15), k1_tarski(C_16))=k1_enumset1(A_14, B_15, C_16))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.94/1.50  tff(c_14, plain, (![A_17]: (k2_tarski(A_17, A_17)=k1_tarski(A_17))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.94/1.50  tff(c_442, plain, (![A_85, B_86, C_87, D_88]: (k2_xboole_0(k2_tarski(A_85, B_86), k2_tarski(C_87, D_88))=k2_enumset1(A_85, B_86, C_87, D_88))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.94/1.50  tff(c_462, plain, (![A_85, B_86, A_17]: (k2_xboole_0(k2_tarski(A_85, B_86), k1_tarski(A_17))=k2_enumset1(A_85, B_86, A_17, A_17))), inference(superposition, [status(thm), theory('equality')], [c_14, c_442])).
% 2.94/1.50  tff(c_467, plain, (![A_89, B_90, A_91]: (k2_enumset1(A_89, B_90, A_91, A_91)=k1_enumset1(A_89, B_90, A_91))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_462])).
% 2.94/1.50  tff(c_18, plain, (![A_20, B_21, C_22]: (k2_enumset1(A_20, A_20, B_21, C_22)=k1_enumset1(A_20, B_21, C_22))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.94/1.50  tff(c_474, plain, (![B_90, A_91]: (k1_enumset1(B_90, B_90, A_91)=k1_enumset1(B_90, A_91, A_91))), inference(superposition, [status(thm), theory('equality')], [c_467, c_18])).
% 2.94/1.50  tff(c_486, plain, (![B_92, A_93]: (k2_tarski(B_92, A_93)=k2_tarski(A_93, B_92))), inference(demodulation, [status(thm), theory('equality')], [c_184, c_16, c_474])).
% 2.94/1.50  tff(c_22, plain, (![A_27, B_28]: (k3_tarski(k2_tarski(A_27, B_28))=k2_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.94/1.50  tff(c_561, plain, (![B_94, A_95]: (k3_tarski(k2_tarski(B_94, A_95))=k2_xboole_0(A_95, B_94))), inference(superposition, [status(thm), theory('equality')], [c_486, c_22])).
% 2.94/1.50  tff(c_567, plain, (![B_94, A_95]: (k2_xboole_0(B_94, A_95)=k2_xboole_0(A_95, B_94))), inference(superposition, [status(thm), theory('equality')], [c_561, c_22])).
% 2.94/1.50  tff(c_30, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_3'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.94/1.50  tff(c_587, plain, (k2_xboole_0('#skF_2', k2_tarski('#skF_1', '#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_567, c_30])).
% 2.94/1.50  tff(c_1004, plain, (~r2_hidden('#skF_3', '#skF_2') | ~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_990, c_587])).
% 2.94/1.50  tff(c_1057, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_1004])).
% 2.94/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.94/1.50  
% 2.94/1.50  Inference rules
% 2.94/1.50  ----------------------
% 2.94/1.50  #Ref     : 0
% 2.94/1.50  #Sup     : 256
% 2.94/1.50  #Fact    : 0
% 2.94/1.50  #Define  : 0
% 2.94/1.50  #Split   : 0
% 2.94/1.50  #Chain   : 0
% 2.94/1.50  #Close   : 0
% 2.94/1.50  
% 2.94/1.50  Ordering : KBO
% 2.94/1.50  
% 2.94/1.50  Simplification rules
% 2.94/1.50  ----------------------
% 2.94/1.50  #Subsume      : 35
% 2.94/1.50  #Demod        : 81
% 2.94/1.50  #Tautology    : 136
% 2.94/1.50  #SimpNegUnit  : 0
% 2.94/1.50  #BackRed      : 1
% 2.94/1.50  
% 2.94/1.50  #Partial instantiations: 0
% 2.94/1.50  #Strategies tried      : 1
% 2.94/1.50  
% 2.94/1.50  Timing (in seconds)
% 2.94/1.50  ----------------------
% 2.94/1.51  Preprocessing        : 0.31
% 2.94/1.51  Parsing              : 0.17
% 2.94/1.51  CNF conversion       : 0.02
% 2.94/1.51  Main loop            : 0.36
% 2.94/1.51  Inferencing          : 0.14
% 2.94/1.51  Reduction            : 0.13
% 2.94/1.51  Demodulation         : 0.10
% 2.94/1.51  BG Simplification    : 0.02
% 2.94/1.51  Subsumption          : 0.05
% 2.94/1.51  Abstraction          : 0.02
% 2.94/1.51  MUC search           : 0.00
% 2.94/1.51  Cooper               : 0.00
% 2.94/1.51  Total                : 0.70
% 2.94/1.51  Index Insertion      : 0.00
% 2.94/1.51  Index Deletion       : 0.00
% 2.94/1.51  Index Matching       : 0.00
% 2.94/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
