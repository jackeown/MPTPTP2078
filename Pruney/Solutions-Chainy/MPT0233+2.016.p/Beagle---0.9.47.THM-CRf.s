%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:26 EST 2020

% Result     : Theorem 4.37s
% Output     : CNFRefutation 4.37s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 101 expanded)
%              Number of leaves         :   24 (  46 expanded)
%              Depth                    :   11
%              Number of atoms          :   66 ( 129 expanded)
%              Number of equality atoms :   40 (  77 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r1_tarski(k2_tarski(A,B),k2_tarski(C,D))
          & A != C
          & A != D ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_54,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_58,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_52,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_44,plain,(
    '#skF_5' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_42,plain,(
    '#skF_6' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_46,plain,(
    r1_tarski(k2_tarski('#skF_3','#skF_4'),k2_tarski('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_133,plain,(
    ! [A_47,B_48] :
      ( k2_xboole_0(A_47,B_48) = B_48
      | ~ r1_tarski(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_143,plain,(
    k2_xboole_0(k2_tarski('#skF_3','#skF_4'),k2_tarski('#skF_5','#skF_6')) = k2_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_46,c_133])).

tff(c_59,plain,(
    ! [B_35,A_36] : k2_xboole_0(B_35,A_36) = k2_xboole_0(A_36,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_8,B_9] : r1_tarski(A_8,k2_xboole_0(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_74,plain,(
    ! [A_36,B_35] : r1_tarski(A_36,k2_xboole_0(B_35,A_36)) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_8])).

tff(c_204,plain,(
    r1_tarski(k2_tarski('#skF_5','#skF_6'),k2_tarski('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_74])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( k2_xboole_0(A_6,B_7) = B_7
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_249,plain,(
    k2_xboole_0(k2_tarski('#skF_5','#skF_6'),k2_tarski('#skF_5','#skF_6')) = k2_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_204,c_6])).

tff(c_34,plain,(
    ! [A_17,B_18,C_19] : k2_xboole_0(k1_tarski(A_17),k2_tarski(B_18,C_19)) = k1_enumset1(A_17,B_18,C_19) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_38,plain,(
    ! [A_21,B_22] : k1_enumset1(A_21,A_21,B_22) = k2_tarski(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_590,plain,(
    ! [A_73,B_74,C_75] : k2_xboole_0(k1_tarski(A_73),k2_tarski(B_74,C_75)) = k1_enumset1(A_73,B_74,C_75) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_654,plain,(
    ! [A_76,B_77,C_78] : r1_tarski(k1_tarski(A_76),k1_enumset1(A_76,B_77,C_78)) ),
    inference(superposition,[status(thm),theory(equality)],[c_590,c_8])).

tff(c_660,plain,(
    ! [A_21,B_22] : r1_tarski(k1_tarski(A_21),k2_tarski(A_21,B_22)) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_654])).

tff(c_151,plain,(
    ! [A_51,C_52,B_53] :
      ( r1_tarski(A_51,k2_xboole_0(C_52,B_53))
      | ~ r1_tarski(A_51,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_300,plain,(
    ! [A_63,A_64,B_65] :
      ( r1_tarski(A_63,k2_xboole_0(A_64,B_65))
      | ~ r1_tarski(A_63,A_64) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_151])).

tff(c_317,plain,(
    ! [A_66] :
      ( r1_tarski(A_66,k2_tarski('#skF_5','#skF_6'))
      | ~ r1_tarski(A_66,k2_tarski('#skF_3','#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_300])).

tff(c_1887,plain,(
    ! [A_121] :
      ( k2_xboole_0(A_121,k2_tarski('#skF_5','#skF_6')) = k2_tarski('#skF_5','#skF_6')
      | ~ r1_tarski(A_121,k2_tarski('#skF_3','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_317,c_6])).

tff(c_1898,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),k2_tarski('#skF_5','#skF_6')) = k2_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_660,c_1887])).

tff(c_145,plain,(
    ! [A_8,B_9] : k2_xboole_0(A_8,k2_xboole_0(A_8,B_9)) = k2_xboole_0(A_8,B_9) ),
    inference(resolution,[status(thm)],[c_8,c_133])).

tff(c_162,plain,(
    ! [A_54,B_55] : k2_xboole_0(A_54,k2_xboole_0(A_54,B_55)) = k2_xboole_0(A_54,B_55) ),
    inference(resolution,[status(thm)],[c_8,c_133])).

tff(c_186,plain,(
    ! [A_1,B_2] : k2_xboole_0(A_1,k2_xboole_0(B_2,A_1)) = k2_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_162])).

tff(c_322,plain,(
    ! [A_67,B_68] : k2_xboole_0(A_67,k2_xboole_0(B_68,A_67)) = k2_xboole_0(B_68,A_67) ),
    inference(resolution,[status(thm)],[c_74,c_133])).

tff(c_485,plain,(
    ! [B_71,A_72] : k2_xboole_0(B_71,k2_xboole_0(B_71,A_72)) = k2_xboole_0(A_72,B_71) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_322])).

tff(c_544,plain,(
    ! [B_2,A_1] : k2_xboole_0(k2_xboole_0(B_2,A_1),A_1) = k2_xboole_0(A_1,k2_xboole_0(A_1,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_485])).

tff(c_584,plain,(
    ! [B_2,A_1] : k2_xboole_0(k2_xboole_0(B_2,A_1),A_1) = k2_xboole_0(A_1,B_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_544])).

tff(c_2039,plain,(
    k2_xboole_0(k2_tarski('#skF_5','#skF_6'),k2_tarski('#skF_5','#skF_6')) = k2_xboole_0(k2_tarski('#skF_5','#skF_6'),k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1898,c_584])).

tff(c_2089,plain,(
    k1_enumset1('#skF_3','#skF_5','#skF_6') = k2_tarski('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_249,c_34,c_2,c_2039])).

tff(c_16,plain,(
    ! [E_16,B_11,C_12] : r2_hidden(E_16,k1_enumset1(E_16,B_11,C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2124,plain,(
    r2_hidden('#skF_3',k2_tarski('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2089,c_16])).

tff(c_816,plain,(
    ! [E_90,C_91,B_92,A_93] :
      ( E_90 = C_91
      | E_90 = B_92
      | E_90 = A_93
      | ~ r2_hidden(E_90,k1_enumset1(A_93,B_92,C_91)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_3620,plain,(
    ! [E_191,B_192,A_193] :
      ( E_191 = B_192
      | E_191 = A_193
      | E_191 = A_193
      | ~ r2_hidden(E_191,k2_tarski(A_193,B_192)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_816])).

tff(c_3631,plain,
    ( '#skF_6' = '#skF_3'
    | '#skF_5' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2124,c_3620])).

tff(c_3646,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_44,c_42,c_3631])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.30  % Computer   : n010.cluster.edu
% 0.11/0.30  % Model      : x86_64 x86_64
% 0.11/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.30  % Memory     : 8042.1875MB
% 0.11/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.30  % CPULimit   : 60
% 0.11/0.30  % DateTime   : Tue Dec  1 15:16:14 EST 2020
% 0.11/0.31  % CPUTime    : 
% 0.11/0.31  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.37/1.79  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.37/1.79  
% 4.37/1.79  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.37/1.79  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 4.37/1.79  
% 4.37/1.79  %Foreground sorts:
% 4.37/1.79  
% 4.37/1.79  
% 4.37/1.79  %Background operators:
% 4.37/1.79  
% 4.37/1.79  
% 4.37/1.79  %Foreground operators:
% 4.37/1.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.37/1.79  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.37/1.79  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.37/1.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.37/1.79  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.37/1.79  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.37/1.79  tff('#skF_5', type, '#skF_5': $i).
% 4.37/1.79  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 4.37/1.79  tff('#skF_6', type, '#skF_6': $i).
% 4.37/1.79  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.37/1.79  tff('#skF_3', type, '#skF_3': $i).
% 4.37/1.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.37/1.79  tff('#skF_4', type, '#skF_4': $i).
% 4.37/1.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.37/1.79  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.37/1.79  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 4.37/1.79  
% 4.37/1.81  tff(f_70, negated_conjecture, ~(![A, B, C, D]: ~((r1_tarski(k2_tarski(A, B), k2_tarski(C, D)) & ~(A = C)) & ~(A = D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_zfmisc_1)).
% 4.37/1.81  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.37/1.81  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.37/1.81  tff(f_37, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.37/1.81  tff(f_54, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 4.37/1.81  tff(f_58, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 4.37/1.81  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 4.37/1.81  tff(f_52, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 4.37/1.81  tff(c_44, plain, ('#skF_5'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.37/1.81  tff(c_42, plain, ('#skF_6'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.37/1.81  tff(c_46, plain, (r1_tarski(k2_tarski('#skF_3', '#skF_4'), k2_tarski('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.37/1.81  tff(c_133, plain, (![A_47, B_48]: (k2_xboole_0(A_47, B_48)=B_48 | ~r1_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.37/1.81  tff(c_143, plain, (k2_xboole_0(k2_tarski('#skF_3', '#skF_4'), k2_tarski('#skF_5', '#skF_6'))=k2_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_46, c_133])).
% 4.37/1.81  tff(c_59, plain, (![B_35, A_36]: (k2_xboole_0(B_35, A_36)=k2_xboole_0(A_36, B_35))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.37/1.81  tff(c_8, plain, (![A_8, B_9]: (r1_tarski(A_8, k2_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.37/1.81  tff(c_74, plain, (![A_36, B_35]: (r1_tarski(A_36, k2_xboole_0(B_35, A_36)))), inference(superposition, [status(thm), theory('equality')], [c_59, c_8])).
% 4.37/1.81  tff(c_204, plain, (r1_tarski(k2_tarski('#skF_5', '#skF_6'), k2_tarski('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_143, c_74])).
% 4.37/1.81  tff(c_6, plain, (![A_6, B_7]: (k2_xboole_0(A_6, B_7)=B_7 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.37/1.81  tff(c_249, plain, (k2_xboole_0(k2_tarski('#skF_5', '#skF_6'), k2_tarski('#skF_5', '#skF_6'))=k2_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_204, c_6])).
% 4.37/1.81  tff(c_34, plain, (![A_17, B_18, C_19]: (k2_xboole_0(k1_tarski(A_17), k2_tarski(B_18, C_19))=k1_enumset1(A_17, B_18, C_19))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.37/1.81  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.37/1.81  tff(c_38, plain, (![A_21, B_22]: (k1_enumset1(A_21, A_21, B_22)=k2_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.37/1.81  tff(c_590, plain, (![A_73, B_74, C_75]: (k2_xboole_0(k1_tarski(A_73), k2_tarski(B_74, C_75))=k1_enumset1(A_73, B_74, C_75))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.37/1.81  tff(c_654, plain, (![A_76, B_77, C_78]: (r1_tarski(k1_tarski(A_76), k1_enumset1(A_76, B_77, C_78)))), inference(superposition, [status(thm), theory('equality')], [c_590, c_8])).
% 4.37/1.81  tff(c_660, plain, (![A_21, B_22]: (r1_tarski(k1_tarski(A_21), k2_tarski(A_21, B_22)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_654])).
% 4.37/1.81  tff(c_151, plain, (![A_51, C_52, B_53]: (r1_tarski(A_51, k2_xboole_0(C_52, B_53)) | ~r1_tarski(A_51, B_53))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.37/1.81  tff(c_300, plain, (![A_63, A_64, B_65]: (r1_tarski(A_63, k2_xboole_0(A_64, B_65)) | ~r1_tarski(A_63, A_64))), inference(superposition, [status(thm), theory('equality')], [c_2, c_151])).
% 4.37/1.81  tff(c_317, plain, (![A_66]: (r1_tarski(A_66, k2_tarski('#skF_5', '#skF_6')) | ~r1_tarski(A_66, k2_tarski('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_143, c_300])).
% 4.37/1.81  tff(c_1887, plain, (![A_121]: (k2_xboole_0(A_121, k2_tarski('#skF_5', '#skF_6'))=k2_tarski('#skF_5', '#skF_6') | ~r1_tarski(A_121, k2_tarski('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_317, c_6])).
% 4.37/1.81  tff(c_1898, plain, (k2_xboole_0(k1_tarski('#skF_3'), k2_tarski('#skF_5', '#skF_6'))=k2_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_660, c_1887])).
% 4.37/1.81  tff(c_145, plain, (![A_8, B_9]: (k2_xboole_0(A_8, k2_xboole_0(A_8, B_9))=k2_xboole_0(A_8, B_9))), inference(resolution, [status(thm)], [c_8, c_133])).
% 4.37/1.81  tff(c_162, plain, (![A_54, B_55]: (k2_xboole_0(A_54, k2_xboole_0(A_54, B_55))=k2_xboole_0(A_54, B_55))), inference(resolution, [status(thm)], [c_8, c_133])).
% 4.37/1.81  tff(c_186, plain, (![A_1, B_2]: (k2_xboole_0(A_1, k2_xboole_0(B_2, A_1))=k2_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_162])).
% 4.37/1.81  tff(c_322, plain, (![A_67, B_68]: (k2_xboole_0(A_67, k2_xboole_0(B_68, A_67))=k2_xboole_0(B_68, A_67))), inference(resolution, [status(thm)], [c_74, c_133])).
% 4.37/1.81  tff(c_485, plain, (![B_71, A_72]: (k2_xboole_0(B_71, k2_xboole_0(B_71, A_72))=k2_xboole_0(A_72, B_71))), inference(superposition, [status(thm), theory('equality')], [c_2, c_322])).
% 4.37/1.81  tff(c_544, plain, (![B_2, A_1]: (k2_xboole_0(k2_xboole_0(B_2, A_1), A_1)=k2_xboole_0(A_1, k2_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_186, c_485])).
% 4.37/1.81  tff(c_584, plain, (![B_2, A_1]: (k2_xboole_0(k2_xboole_0(B_2, A_1), A_1)=k2_xboole_0(A_1, B_2))), inference(demodulation, [status(thm), theory('equality')], [c_145, c_544])).
% 4.37/1.81  tff(c_2039, plain, (k2_xboole_0(k2_tarski('#skF_5', '#skF_6'), k2_tarski('#skF_5', '#skF_6'))=k2_xboole_0(k2_tarski('#skF_5', '#skF_6'), k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1898, c_584])).
% 4.37/1.81  tff(c_2089, plain, (k1_enumset1('#skF_3', '#skF_5', '#skF_6')=k2_tarski('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_249, c_34, c_2, c_2039])).
% 4.37/1.81  tff(c_16, plain, (![E_16, B_11, C_12]: (r2_hidden(E_16, k1_enumset1(E_16, B_11, C_12)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.37/1.81  tff(c_2124, plain, (r2_hidden('#skF_3', k2_tarski('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_2089, c_16])).
% 4.37/1.81  tff(c_816, plain, (![E_90, C_91, B_92, A_93]: (E_90=C_91 | E_90=B_92 | E_90=A_93 | ~r2_hidden(E_90, k1_enumset1(A_93, B_92, C_91)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.37/1.81  tff(c_3620, plain, (![E_191, B_192, A_193]: (E_191=B_192 | E_191=A_193 | E_191=A_193 | ~r2_hidden(E_191, k2_tarski(A_193, B_192)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_816])).
% 4.37/1.81  tff(c_3631, plain, ('#skF_6'='#skF_3' | '#skF_5'='#skF_3'), inference(resolution, [status(thm)], [c_2124, c_3620])).
% 4.37/1.81  tff(c_3646, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_44, c_42, c_3631])).
% 4.37/1.81  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.37/1.81  
% 4.37/1.81  Inference rules
% 4.37/1.81  ----------------------
% 4.37/1.81  #Ref     : 0
% 4.37/1.81  #Sup     : 922
% 4.37/1.81  #Fact    : 0
% 4.37/1.81  #Define  : 0
% 4.37/1.81  #Split   : 0
% 4.37/1.81  #Chain   : 0
% 4.37/1.81  #Close   : 0
% 4.37/1.81  
% 4.37/1.81  Ordering : KBO
% 4.37/1.81  
% 4.37/1.81  Simplification rules
% 4.37/1.81  ----------------------
% 4.37/1.81  #Subsume      : 109
% 4.37/1.81  #Demod        : 1063
% 4.37/1.81  #Tautology    : 594
% 4.37/1.81  #SimpNegUnit  : 4
% 4.37/1.81  #BackRed      : 0
% 4.37/1.81  
% 4.37/1.81  #Partial instantiations: 0
% 4.37/1.81  #Strategies tried      : 1
% 4.37/1.81  
% 4.37/1.81  Timing (in seconds)
% 4.37/1.81  ----------------------
% 4.37/1.81  Preprocessing        : 0.30
% 4.37/1.81  Parsing              : 0.15
% 4.37/1.81  CNF conversion       : 0.02
% 4.37/1.81  Main loop            : 0.78
% 4.37/1.81  Inferencing          : 0.22
% 4.37/1.81  Reduction            : 0.38
% 4.37/1.81  Demodulation         : 0.33
% 4.37/1.81  BG Simplification    : 0.03
% 4.37/1.81  Subsumption          : 0.11
% 4.37/1.81  Abstraction          : 0.04
% 4.37/1.81  MUC search           : 0.00
% 4.37/1.81  Cooper               : 0.00
% 4.37/1.81  Total                : 1.11
% 4.37/1.81  Index Insertion      : 0.00
% 4.37/1.81  Index Deletion       : 0.00
% 4.37/1.81  Index Matching       : 0.00
% 4.37/1.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
