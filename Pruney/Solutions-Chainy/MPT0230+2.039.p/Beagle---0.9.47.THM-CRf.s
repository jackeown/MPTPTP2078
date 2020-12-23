%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:02 EST 2020

% Result     : Theorem 4.81s
% Output     : CNFRefutation 4.81s
% Verified   : 
% Statistics : Number of formulae       :   53 (  62 expanded)
%              Number of leaves         :   27 (  33 expanded)
%              Depth                    :    9
%              Number of atoms          :   51 (  72 expanded)
%              Number of equality atoms :   39 (  54 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(f_72,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r1_tarski(k1_tarski(A),k2_tarski(B,C))
          & A != B
          & A != C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_58,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_54,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k2_xboole_0(B,C)) = k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).

tff(f_52,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_48,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_46,plain,(
    '#skF_5' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_42,plain,(
    ! [A_26,B_27,C_28] : k2_enumset1(A_26,A_26,B_27,C_28) = k1_enumset1(A_26,B_27,C_28) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_40,plain,(
    ! [A_24,B_25] : k1_enumset1(A_24,A_24,B_25) = k2_tarski(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_630,plain,(
    ! [A_92,B_93,C_94,D_95] : k2_xboole_0(k1_enumset1(A_92,B_93,C_94),k1_tarski(D_95)) = k2_enumset1(A_92,B_93,C_94,D_95) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_657,plain,(
    ! [A_24,B_25,D_95] : k2_xboole_0(k2_tarski(A_24,B_25),k1_tarski(D_95)) = k2_enumset1(A_24,A_24,B_25,D_95) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_630])).

tff(c_1537,plain,(
    ! [A_137,B_138,D_139] : k2_xboole_0(k2_tarski(A_137,B_138),k1_tarski(D_139)) = k1_enumset1(A_137,B_138,D_139) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_657])).

tff(c_50,plain,(
    r1_tarski(k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_106,plain,(
    ! [A_48,B_49] :
      ( k3_xboole_0(A_48,B_49) = A_48
      | ~ r1_tarski(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_113,plain,(
    k3_xboole_0(k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) = k1_tarski('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_106])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_10,B_11] : r1_tarski(A_10,k2_xboole_0(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_114,plain,(
    ! [A_10,B_11] : k3_xboole_0(A_10,k2_xboole_0(A_10,B_11)) = A_10 ),
    inference(resolution,[status(thm)],[c_10,c_106])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_175,plain,(
    ! [A_66,B_67,C_68] : k2_xboole_0(k3_xboole_0(A_66,B_67),k3_xboole_0(A_66,C_68)) = k3_xboole_0(A_66,k2_xboole_0(B_67,C_68)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_214,plain,(
    ! [A_3,C_68] : k3_xboole_0(A_3,k2_xboole_0(A_3,C_68)) = k2_xboole_0(A_3,k3_xboole_0(A_3,C_68)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_175])).

tff(c_221,plain,(
    ! [A_69,C_70] : k2_xboole_0(A_69,k3_xboole_0(A_69,C_70)) = A_69 ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_214])).

tff(c_305,plain,(
    ! [B_77,A_78] : k2_xboole_0(B_77,k3_xboole_0(A_78,B_77)) = B_77 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_221])).

tff(c_336,plain,(
    k2_xboole_0(k2_tarski('#skF_4','#skF_5'),k1_tarski('#skF_3')) = k2_tarski('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_305])).

tff(c_1578,plain,(
    k1_enumset1('#skF_4','#skF_5','#skF_3') = k2_tarski('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1537,c_336])).

tff(c_14,plain,(
    ! [E_18,A_12,B_13] : r2_hidden(E_18,k1_enumset1(A_12,B_13,E_18)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1621,plain,(
    r2_hidden('#skF_3',k2_tarski('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1578,c_14])).

tff(c_286,plain,(
    ! [E_73,C_74,B_75,A_76] :
      ( E_73 = C_74
      | E_73 = B_75
      | E_73 = A_76
      | ~ r2_hidden(E_73,k1_enumset1(A_76,B_75,C_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_4443,plain,(
    ! [E_220,B_221,A_222] :
      ( E_220 = B_221
      | E_220 = A_222
      | E_220 = A_222
      | ~ r2_hidden(E_220,k2_tarski(A_222,B_221)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_286])).

tff(c_4454,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1621,c_4443])).

tff(c_4469,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_48,c_46,c_4454])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:27:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.81/1.98  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.81/1.99  
% 4.81/1.99  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.81/1.99  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 4.81/1.99  
% 4.81/1.99  %Foreground sorts:
% 4.81/1.99  
% 4.81/1.99  
% 4.81/1.99  %Background operators:
% 4.81/1.99  
% 4.81/1.99  
% 4.81/1.99  %Foreground operators:
% 4.81/1.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.81/1.99  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.81/1.99  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.81/1.99  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.81/1.99  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.81/1.99  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.81/1.99  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.81/1.99  tff('#skF_5', type, '#skF_5': $i).
% 4.81/1.99  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 4.81/1.99  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.81/1.99  tff('#skF_3', type, '#skF_3': $i).
% 4.81/1.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.81/1.99  tff('#skF_4', type, '#skF_4': $i).
% 4.81/1.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.81/1.99  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.81/1.99  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.81/1.99  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 4.81/1.99  
% 4.81/2.00  tff(f_72, negated_conjecture, ~(![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 4.81/2.00  tff(f_60, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 4.81/2.00  tff(f_58, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 4.81/2.00  tff(f_54, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 4.81/2.00  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.81/2.00  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.81/2.00  tff(f_37, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.81/2.00  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 4.81/2.00  tff(f_31, axiom, (![A, B, C]: (k3_xboole_0(A, k2_xboole_0(B, C)) = k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_xboole_1)).
% 4.81/2.00  tff(f_52, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 4.81/2.00  tff(c_48, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.81/2.00  tff(c_46, plain, ('#skF_5'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.81/2.00  tff(c_42, plain, (![A_26, B_27, C_28]: (k2_enumset1(A_26, A_26, B_27, C_28)=k1_enumset1(A_26, B_27, C_28))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.81/2.00  tff(c_40, plain, (![A_24, B_25]: (k1_enumset1(A_24, A_24, B_25)=k2_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.81/2.00  tff(c_630, plain, (![A_92, B_93, C_94, D_95]: (k2_xboole_0(k1_enumset1(A_92, B_93, C_94), k1_tarski(D_95))=k2_enumset1(A_92, B_93, C_94, D_95))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.81/2.00  tff(c_657, plain, (![A_24, B_25, D_95]: (k2_xboole_0(k2_tarski(A_24, B_25), k1_tarski(D_95))=k2_enumset1(A_24, A_24, B_25, D_95))), inference(superposition, [status(thm), theory('equality')], [c_40, c_630])).
% 4.81/2.00  tff(c_1537, plain, (![A_137, B_138, D_139]: (k2_xboole_0(k2_tarski(A_137, B_138), k1_tarski(D_139))=k1_enumset1(A_137, B_138, D_139))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_657])).
% 4.81/2.00  tff(c_50, plain, (r1_tarski(k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.81/2.00  tff(c_106, plain, (![A_48, B_49]: (k3_xboole_0(A_48, B_49)=A_48 | ~r1_tarski(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.81/2.00  tff(c_113, plain, (k3_xboole_0(k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))=k1_tarski('#skF_3')), inference(resolution, [status(thm)], [c_50, c_106])).
% 4.81/2.00  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.81/2.00  tff(c_10, plain, (![A_10, B_11]: (r1_tarski(A_10, k2_xboole_0(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.81/2.00  tff(c_114, plain, (![A_10, B_11]: (k3_xboole_0(A_10, k2_xboole_0(A_10, B_11))=A_10)), inference(resolution, [status(thm)], [c_10, c_106])).
% 4.81/2.00  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.81/2.00  tff(c_175, plain, (![A_66, B_67, C_68]: (k2_xboole_0(k3_xboole_0(A_66, B_67), k3_xboole_0(A_66, C_68))=k3_xboole_0(A_66, k2_xboole_0(B_67, C_68)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.81/2.00  tff(c_214, plain, (![A_3, C_68]: (k3_xboole_0(A_3, k2_xboole_0(A_3, C_68))=k2_xboole_0(A_3, k3_xboole_0(A_3, C_68)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_175])).
% 4.81/2.00  tff(c_221, plain, (![A_69, C_70]: (k2_xboole_0(A_69, k3_xboole_0(A_69, C_70))=A_69)), inference(demodulation, [status(thm), theory('equality')], [c_114, c_214])).
% 4.81/2.00  tff(c_305, plain, (![B_77, A_78]: (k2_xboole_0(B_77, k3_xboole_0(A_78, B_77))=B_77)), inference(superposition, [status(thm), theory('equality')], [c_2, c_221])).
% 4.81/2.00  tff(c_336, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), k1_tarski('#skF_3'))=k2_tarski('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_113, c_305])).
% 4.81/2.00  tff(c_1578, plain, (k1_enumset1('#skF_4', '#skF_5', '#skF_3')=k2_tarski('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1537, c_336])).
% 4.81/2.00  tff(c_14, plain, (![E_18, A_12, B_13]: (r2_hidden(E_18, k1_enumset1(A_12, B_13, E_18)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.81/2.00  tff(c_1621, plain, (r2_hidden('#skF_3', k2_tarski('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1578, c_14])).
% 4.81/2.00  tff(c_286, plain, (![E_73, C_74, B_75, A_76]: (E_73=C_74 | E_73=B_75 | E_73=A_76 | ~r2_hidden(E_73, k1_enumset1(A_76, B_75, C_74)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.81/2.00  tff(c_4443, plain, (![E_220, B_221, A_222]: (E_220=B_221 | E_220=A_222 | E_220=A_222 | ~r2_hidden(E_220, k2_tarski(A_222, B_221)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_286])).
% 4.81/2.00  tff(c_4454, plain, ('#skF_5'='#skF_3' | '#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_1621, c_4443])).
% 4.81/2.00  tff(c_4469, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_48, c_46, c_4454])).
% 4.81/2.00  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.81/2.00  
% 4.81/2.00  Inference rules
% 4.81/2.00  ----------------------
% 4.81/2.00  #Ref     : 0
% 4.81/2.00  #Sup     : 1104
% 4.81/2.00  #Fact    : 0
% 4.81/2.00  #Define  : 0
% 4.81/2.00  #Split   : 0
% 4.81/2.00  #Chain   : 0
% 4.81/2.00  #Close   : 0
% 4.81/2.00  
% 4.81/2.00  Ordering : KBO
% 4.81/2.00  
% 4.81/2.00  Simplification rules
% 4.81/2.00  ----------------------
% 4.81/2.00  #Subsume      : 27
% 4.81/2.00  #Demod        : 1672
% 4.81/2.00  #Tautology    : 770
% 4.81/2.00  #SimpNegUnit  : 1
% 4.81/2.00  #BackRed      : 3
% 4.81/2.00  
% 4.81/2.00  #Partial instantiations: 0
% 4.81/2.00  #Strategies tried      : 1
% 4.81/2.00  
% 4.81/2.00  Timing (in seconds)
% 4.81/2.00  ----------------------
% 4.81/2.00  Preprocessing        : 0.36
% 4.81/2.00  Parsing              : 0.18
% 4.81/2.00  CNF conversion       : 0.03
% 4.81/2.00  Main loop            : 0.83
% 4.81/2.00  Inferencing          : 0.24
% 4.81/2.00  Reduction            : 0.40
% 4.81/2.00  Demodulation         : 0.34
% 4.81/2.00  BG Simplification    : 0.03
% 4.81/2.00  Subsumption          : 0.11
% 4.81/2.00  Abstraction          : 0.04
% 4.81/2.00  MUC search           : 0.00
% 4.81/2.00  Cooper               : 0.00
% 4.81/2.00  Total                : 1.21
% 4.81/2.00  Index Insertion      : 0.00
% 4.81/2.00  Index Deletion       : 0.00
% 4.81/2.00  Index Matching       : 0.00
% 4.81/2.00  BG Taut test         : 0.00
%------------------------------------------------------------------------------
