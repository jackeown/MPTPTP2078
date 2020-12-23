%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:05 EST 2020

% Result     : Theorem 4.63s
% Output     : CNFRefutation 4.63s
% Verified   : 
% Statistics : Number of formulae       :   66 (  93 expanded)
%              Number of leaves         :   34 (  47 expanded)
%              Depth                    :   10
%              Number of atoms          :   60 (  96 expanded)
%              Number of equality atoms :   26 (  43 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_98,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_xboole_0(k2_tarski(A,B),C),C)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_89,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(A,C,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_enumset1)).

tff(f_77,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_91,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(B,A,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_enumset1)).

tff(f_73,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_93,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_69,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_78,plain,(
    ~ r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_22,plain,(
    ! [A_16,B_17] : r1_tarski(A_16,k2_xboole_0(A_16,B_17)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_295,plain,(
    ! [A_113,C_114,B_115] : k1_enumset1(A_113,C_114,B_115) = k1_enumset1(A_113,B_115,C_114) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_60,plain,(
    ! [A_39,B_40] : k1_enumset1(A_39,A_39,B_40) = k2_tarski(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_399,plain,(
    ! [B_119,C_120] : k1_enumset1(B_119,C_120,B_119) = k2_tarski(B_119,C_120) ),
    inference(superposition,[status(thm),theory(equality)],[c_295,c_60])).

tff(c_74,plain,(
    ! [B_70,A_69,C_71] : k1_enumset1(B_70,A_69,C_71) = k1_enumset1(A_69,B_70,C_71) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_414,plain,(
    ! [C_120,B_119] : k1_enumset1(C_120,B_119,B_119) = k2_tarski(B_119,C_120) ),
    inference(superposition,[status(thm),theory(equality)],[c_399,c_74])).

tff(c_932,plain,(
    ! [A_141,B_142,C_143] : k2_xboole_0(k2_tarski(A_141,B_142),k1_tarski(C_143)) = k1_enumset1(A_141,B_142,C_143) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1384,plain,(
    ! [A_159,B_160,C_161] : r1_tarski(k2_tarski(A_159,B_160),k1_enumset1(A_159,B_160,C_161)) ),
    inference(superposition,[status(thm),theory(equality)],[c_932,c_22])).

tff(c_1395,plain,(
    ! [C_120,B_119] : r1_tarski(k2_tarski(C_120,B_119),k2_tarski(B_119,C_120)) ),
    inference(superposition,[status(thm),theory(equality)],[c_414,c_1384])).

tff(c_1466,plain,(
    ! [C_168,B_169] : r1_tarski(k2_tarski(C_168,B_169),k2_tarski(B_169,C_168)) ),
    inference(superposition,[status(thm),theory(equality)],[c_414,c_1384])).

tff(c_14,plain,(
    ! [B_13,A_12] :
      ( B_13 = A_12
      | ~ r1_tarski(B_13,A_12)
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1468,plain,(
    ! [C_168,B_169] :
      ( k2_tarski(C_168,B_169) = k2_tarski(B_169,C_168)
      | ~ r1_tarski(k2_tarski(B_169,C_168),k2_tarski(C_168,B_169)) ) ),
    inference(resolution,[status(thm)],[c_1466,c_14])).

tff(c_1480,plain,(
    ! [C_170,B_171] : k2_tarski(C_170,B_171) = k2_tarski(B_171,C_170) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1395,c_1468])).

tff(c_76,plain,(
    ! [A_72,B_73] : k3_tarski(k2_tarski(A_72,B_73)) = k2_xboole_0(A_72,B_73) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1612,plain,(
    ! [C_179,B_180] : k3_tarski(k2_tarski(C_179,B_180)) = k2_xboole_0(B_180,C_179) ),
    inference(superposition,[status(thm),theory(equality)],[c_1480,c_76])).

tff(c_1618,plain,(
    ! [C_179,B_180] : k2_xboole_0(C_179,B_180) = k2_xboole_0(B_180,C_179) ),
    inference(superposition,[status(thm),theory(equality)],[c_1612,c_76])).

tff(c_80,plain,(
    r1_tarski(k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_215,plain,(
    ! [B_106,A_107] :
      ( B_106 = A_107
      | ~ r1_tarski(B_106,A_107)
      | ~ r1_tarski(A_107,B_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_224,plain,
    ( k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = '#skF_6'
    | ~ r1_tarski('#skF_6',k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6')) ),
    inference(resolution,[status(thm)],[c_80,c_215])).

tff(c_464,plain,(
    ~ r1_tarski('#skF_6',k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_224])).

tff(c_1639,plain,(
    ~ r1_tarski('#skF_6',k2_xboole_0('#skF_6',k2_tarski('#skF_4','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1618,c_464])).

tff(c_1643,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1639])).

tff(c_1644,plain,(
    k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_224])).

tff(c_1651,plain,(
    r1_tarski(k2_tarski('#skF_4','#skF_5'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1644,c_22])).

tff(c_163,plain,(
    ! [A_94,B_95] : k1_enumset1(A_94,A_94,B_95) = k2_tarski(A_94,B_95) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_36,plain,(
    ! [E_30,B_25,C_26] : r2_hidden(E_30,k1_enumset1(E_30,B_25,C_26)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_169,plain,(
    ! [A_94,B_95] : r2_hidden(A_94,k2_tarski(A_94,B_95)) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_36])).

tff(c_1655,plain,(
    ! [C_181,B_182,A_183] :
      ( r2_hidden(C_181,B_182)
      | ~ r2_hidden(C_181,A_183)
      | ~ r1_tarski(A_183,B_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_3676,plain,(
    ! [A_289,B_290,B_291] :
      ( r2_hidden(A_289,B_290)
      | ~ r1_tarski(k2_tarski(A_289,B_291),B_290) ) ),
    inference(resolution,[status(thm)],[c_169,c_1655])).

tff(c_3704,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_1651,c_3676])).

tff(c_3730,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_3704])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:14:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.63/1.84  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.63/1.84  
% 4.63/1.84  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.63/1.84  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 4.63/1.84  
% 4.63/1.84  %Foreground sorts:
% 4.63/1.84  
% 4.63/1.84  
% 4.63/1.84  %Background operators:
% 4.63/1.84  
% 4.63/1.84  
% 4.63/1.84  %Foreground operators:
% 4.63/1.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.63/1.84  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.63/1.84  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.63/1.84  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.63/1.84  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.63/1.84  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.63/1.84  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.63/1.84  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.63/1.84  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.63/1.84  tff('#skF_5', type, '#skF_5': $i).
% 4.63/1.84  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 4.63/1.84  tff('#skF_6', type, '#skF_6': $i).
% 4.63/1.84  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.63/1.84  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.63/1.84  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.63/1.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.63/1.84  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.63/1.84  tff('#skF_4', type, '#skF_4': $i).
% 4.63/1.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.63/1.84  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.63/1.84  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 4.63/1.84  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.63/1.84  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.63/1.84  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.63/1.84  
% 4.63/1.86  tff(f_98, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_xboole_0(k2_tarski(A, B), C), C) => r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_zfmisc_1)).
% 4.63/1.86  tff(f_48, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.63/1.86  tff(f_89, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(A, C, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_enumset1)).
% 4.63/1.86  tff(f_77, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 4.63/1.86  tff(f_91, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(B, A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_enumset1)).
% 4.63/1.86  tff(f_73, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_enumset1)).
% 4.63/1.86  tff(f_44, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.63/1.86  tff(f_93, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 4.63/1.86  tff(f_69, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 4.63/1.86  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.63/1.86  tff(c_78, plain, (~r2_hidden('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.63/1.86  tff(c_22, plain, (![A_16, B_17]: (r1_tarski(A_16, k2_xboole_0(A_16, B_17)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.63/1.86  tff(c_295, plain, (![A_113, C_114, B_115]: (k1_enumset1(A_113, C_114, B_115)=k1_enumset1(A_113, B_115, C_114))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.63/1.86  tff(c_60, plain, (![A_39, B_40]: (k1_enumset1(A_39, A_39, B_40)=k2_tarski(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.63/1.86  tff(c_399, plain, (![B_119, C_120]: (k1_enumset1(B_119, C_120, B_119)=k2_tarski(B_119, C_120))), inference(superposition, [status(thm), theory('equality')], [c_295, c_60])).
% 4.63/1.86  tff(c_74, plain, (![B_70, A_69, C_71]: (k1_enumset1(B_70, A_69, C_71)=k1_enumset1(A_69, B_70, C_71))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.63/1.86  tff(c_414, plain, (![C_120, B_119]: (k1_enumset1(C_120, B_119, B_119)=k2_tarski(B_119, C_120))), inference(superposition, [status(thm), theory('equality')], [c_399, c_74])).
% 4.63/1.86  tff(c_932, plain, (![A_141, B_142, C_143]: (k2_xboole_0(k2_tarski(A_141, B_142), k1_tarski(C_143))=k1_enumset1(A_141, B_142, C_143))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.63/1.86  tff(c_1384, plain, (![A_159, B_160, C_161]: (r1_tarski(k2_tarski(A_159, B_160), k1_enumset1(A_159, B_160, C_161)))), inference(superposition, [status(thm), theory('equality')], [c_932, c_22])).
% 4.63/1.86  tff(c_1395, plain, (![C_120, B_119]: (r1_tarski(k2_tarski(C_120, B_119), k2_tarski(B_119, C_120)))), inference(superposition, [status(thm), theory('equality')], [c_414, c_1384])).
% 4.63/1.86  tff(c_1466, plain, (![C_168, B_169]: (r1_tarski(k2_tarski(C_168, B_169), k2_tarski(B_169, C_168)))), inference(superposition, [status(thm), theory('equality')], [c_414, c_1384])).
% 4.63/1.86  tff(c_14, plain, (![B_13, A_12]: (B_13=A_12 | ~r1_tarski(B_13, A_12) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.63/1.86  tff(c_1468, plain, (![C_168, B_169]: (k2_tarski(C_168, B_169)=k2_tarski(B_169, C_168) | ~r1_tarski(k2_tarski(B_169, C_168), k2_tarski(C_168, B_169)))), inference(resolution, [status(thm)], [c_1466, c_14])).
% 4.63/1.86  tff(c_1480, plain, (![C_170, B_171]: (k2_tarski(C_170, B_171)=k2_tarski(B_171, C_170))), inference(demodulation, [status(thm), theory('equality')], [c_1395, c_1468])).
% 4.63/1.86  tff(c_76, plain, (![A_72, B_73]: (k3_tarski(k2_tarski(A_72, B_73))=k2_xboole_0(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.63/1.86  tff(c_1612, plain, (![C_179, B_180]: (k3_tarski(k2_tarski(C_179, B_180))=k2_xboole_0(B_180, C_179))), inference(superposition, [status(thm), theory('equality')], [c_1480, c_76])).
% 4.63/1.86  tff(c_1618, plain, (![C_179, B_180]: (k2_xboole_0(C_179, B_180)=k2_xboole_0(B_180, C_179))), inference(superposition, [status(thm), theory('equality')], [c_1612, c_76])).
% 4.63/1.86  tff(c_80, plain, (r1_tarski(k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.63/1.86  tff(c_215, plain, (![B_106, A_107]: (B_106=A_107 | ~r1_tarski(B_106, A_107) | ~r1_tarski(A_107, B_106))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.63/1.86  tff(c_224, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')='#skF_6' | ~r1_tarski('#skF_6', k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6'))), inference(resolution, [status(thm)], [c_80, c_215])).
% 4.63/1.86  tff(c_464, plain, (~r1_tarski('#skF_6', k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6'))), inference(splitLeft, [status(thm)], [c_224])).
% 4.63/1.86  tff(c_1639, plain, (~r1_tarski('#skF_6', k2_xboole_0('#skF_6', k2_tarski('#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_1618, c_464])).
% 4.63/1.86  tff(c_1643, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_1639])).
% 4.63/1.86  tff(c_1644, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')='#skF_6'), inference(splitRight, [status(thm)], [c_224])).
% 4.63/1.86  tff(c_1651, plain, (r1_tarski(k2_tarski('#skF_4', '#skF_5'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1644, c_22])).
% 4.63/1.86  tff(c_163, plain, (![A_94, B_95]: (k1_enumset1(A_94, A_94, B_95)=k2_tarski(A_94, B_95))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.63/1.86  tff(c_36, plain, (![E_30, B_25, C_26]: (r2_hidden(E_30, k1_enumset1(E_30, B_25, C_26)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.63/1.86  tff(c_169, plain, (![A_94, B_95]: (r2_hidden(A_94, k2_tarski(A_94, B_95)))), inference(superposition, [status(thm), theory('equality')], [c_163, c_36])).
% 4.63/1.86  tff(c_1655, plain, (![C_181, B_182, A_183]: (r2_hidden(C_181, B_182) | ~r2_hidden(C_181, A_183) | ~r1_tarski(A_183, B_182))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.63/1.86  tff(c_3676, plain, (![A_289, B_290, B_291]: (r2_hidden(A_289, B_290) | ~r1_tarski(k2_tarski(A_289, B_291), B_290))), inference(resolution, [status(thm)], [c_169, c_1655])).
% 4.63/1.86  tff(c_3704, plain, (r2_hidden('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_1651, c_3676])).
% 4.63/1.86  tff(c_3730, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_3704])).
% 4.63/1.86  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.63/1.86  
% 4.63/1.86  Inference rules
% 4.63/1.86  ----------------------
% 4.63/1.86  #Ref     : 0
% 4.63/1.86  #Sup     : 931
% 4.63/1.86  #Fact    : 0
% 4.63/1.86  #Define  : 0
% 4.63/1.86  #Split   : 2
% 4.63/1.86  #Chain   : 0
% 4.63/1.86  #Close   : 0
% 4.63/1.86  
% 4.63/1.86  Ordering : KBO
% 4.63/1.86  
% 4.63/1.86  Simplification rules
% 4.63/1.86  ----------------------
% 4.63/1.86  #Subsume      : 70
% 4.63/1.86  #Demod        : 467
% 4.63/1.86  #Tautology    : 579
% 4.63/1.86  #SimpNegUnit  : 1
% 4.63/1.86  #BackRed      : 6
% 4.63/1.86  
% 4.63/1.86  #Partial instantiations: 0
% 4.63/1.86  #Strategies tried      : 1
% 4.63/1.86  
% 4.63/1.86  Timing (in seconds)
% 4.63/1.86  ----------------------
% 4.63/1.86  Preprocessing        : 0.34
% 4.63/1.86  Parsing              : 0.18
% 4.63/1.86  CNF conversion       : 0.02
% 4.63/1.86  Main loop            : 0.75
% 4.63/1.86  Inferencing          : 0.24
% 4.63/1.86  Reduction            : 0.32
% 4.63/1.86  Demodulation         : 0.26
% 4.63/1.86  BG Simplification    : 0.03
% 4.63/1.86  Subsumption          : 0.12
% 4.63/1.86  Abstraction          : 0.04
% 4.63/1.86  MUC search           : 0.00
% 4.63/1.86  Cooper               : 0.00
% 4.63/1.86  Total                : 1.12
% 4.63/1.86  Index Insertion      : 0.00
% 4.63/1.86  Index Deletion       : 0.00
% 4.63/1.86  Index Matching       : 0.00
% 4.63/1.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
