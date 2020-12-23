%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:34 EST 2020

% Result     : Theorem 2.58s
% Output     : CNFRefutation 2.58s
% Verified   : 
% Statistics : Number of formulae       :   58 (  64 expanded)
%              Number of leaves         :   30 (  35 expanded)
%              Depth                    :   11
%              Number of atoms          :   59 (  73 expanded)
%              Number of equality atoms :   22 (  30 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_74,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_70,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_90,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
       => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_zfmisc_1)).

tff(f_72,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_85,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_47,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(c_126,plain,(
    ! [A_58,B_59] : k1_enumset1(A_58,A_58,B_59) = k2_tarski(A_58,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_40,plain,(
    ! [E_26,A_20,B_21] : r2_hidden(E_26,k1_enumset1(A_20,B_21,E_26)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_135,plain,(
    ! [B_59,A_58] : r2_hidden(B_59,k2_tarski(A_58,B_59)) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_40])).

tff(c_74,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_62,plain,(
    ! [A_27] : k2_tarski(A_27,A_27) = k1_tarski(A_27) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_42,plain,(
    ! [E_26,A_20,C_22] : r2_hidden(E_26,k1_enumset1(A_20,E_26,C_22)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_144,plain,(
    ! [A_60,B_61] : r2_hidden(A_60,k2_tarski(A_60,B_61)) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_42])).

tff(c_153,plain,(
    ! [A_27] : r2_hidden(A_27,k1_tarski(A_27)) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_144])).

tff(c_2,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,k4_xboole_0(A_1,B_2))
      | r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_30,plain,(
    ! [A_14,B_15] : r1_tarski(A_14,k2_xboole_0(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_36,plain,(
    ! [B_19,A_18] : k2_tarski(B_19,A_18) = k2_tarski(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_169,plain,(
    ! [A_65,B_66] : k3_tarski(k2_tarski(A_65,B_66)) = k2_xboole_0(A_65,B_66) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_229,plain,(
    ! [A_75,B_76] : k3_tarski(k2_tarski(A_75,B_76)) = k2_xboole_0(B_76,A_75) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_169])).

tff(c_72,plain,(
    ! [A_39,B_40] : k3_tarski(k2_tarski(A_39,B_40)) = k2_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_235,plain,(
    ! [B_76,A_75] : k2_xboole_0(B_76,A_75) = k2_xboole_0(A_75,B_76) ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_72])).

tff(c_76,plain,(
    r1_tarski(k2_xboole_0(k1_tarski('#skF_5'),'#skF_6'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_255,plain,(
    r1_tarski(k2_xboole_0('#skF_6',k1_tarski('#skF_5')),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_235,c_76])).

tff(c_310,plain,(
    ! [B_84,A_85] :
      ( B_84 = A_85
      | ~ r1_tarski(B_84,A_85)
      | ~ r1_tarski(A_85,B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_312,plain,
    ( k2_xboole_0('#skF_6',k1_tarski('#skF_5')) = '#skF_6'
    | ~ r1_tarski('#skF_6',k2_xboole_0('#skF_6',k1_tarski('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_255,c_310])).

tff(c_323,plain,(
    k2_xboole_0('#skF_6',k1_tarski('#skF_5')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_312])).

tff(c_398,plain,(
    ! [A_104,B_105,C_106] : k4_xboole_0(k4_xboole_0(A_104,B_105),C_106) = k4_xboole_0(A_104,k2_xboole_0(B_105,C_106)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_486,plain,(
    ! [D_117,C_118,A_119,B_120] :
      ( ~ r2_hidden(D_117,C_118)
      | ~ r2_hidden(D_117,k4_xboole_0(A_119,k2_xboole_0(B_120,C_118))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_398,c_4])).

tff(c_508,plain,(
    ! [D_121,A_122] :
      ( ~ r2_hidden(D_121,k1_tarski('#skF_5'))
      | ~ r2_hidden(D_121,k4_xboole_0(A_122,'#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_323,c_486])).

tff(c_562,plain,(
    ! [D_134,A_135] :
      ( ~ r2_hidden(D_134,k1_tarski('#skF_5'))
      | r2_hidden(D_134,'#skF_6')
      | ~ r2_hidden(D_134,A_135) ) ),
    inference(resolution,[status(thm)],[c_2,c_508])).

tff(c_565,plain,(
    ! [A_135] :
      ( r2_hidden('#skF_5','#skF_6')
      | ~ r2_hidden('#skF_5',A_135) ) ),
    inference(resolution,[status(thm)],[c_153,c_562])).

tff(c_569,plain,(
    ! [A_136] : ~ r2_hidden('#skF_5',A_136) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_565])).

tff(c_595,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_135,c_569])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:37:32 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.58/1.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.58/1.41  
% 2.58/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.58/1.41  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 2.58/1.41  
% 2.58/1.41  %Foreground sorts:
% 2.58/1.41  
% 2.58/1.41  
% 2.58/1.41  %Background operators:
% 2.58/1.41  
% 2.58/1.41  
% 2.58/1.41  %Foreground operators:
% 2.58/1.41  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.58/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.58/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.58/1.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.58/1.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.58/1.41  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.58/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.58/1.41  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.58/1.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.58/1.41  tff('#skF_5', type, '#skF_5': $i).
% 2.58/1.41  tff('#skF_6', type, '#skF_6': $i).
% 2.58/1.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.58/1.41  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.58/1.41  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.58/1.41  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.58/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.58/1.41  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.58/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.58/1.41  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.58/1.41  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.58/1.41  
% 2.58/1.43  tff(f_74, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.58/1.43  tff(f_70, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.58/1.43  tff(f_90, negated_conjecture, ~(![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 2.58/1.43  tff(f_72, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.58/1.43  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.58/1.43  tff(f_49, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.58/1.43  tff(f_55, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.58/1.43  tff(f_85, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.58/1.43  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.58/1.43  tff(f_47, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 2.58/1.43  tff(c_126, plain, (![A_58, B_59]: (k1_enumset1(A_58, A_58, B_59)=k2_tarski(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.58/1.43  tff(c_40, plain, (![E_26, A_20, B_21]: (r2_hidden(E_26, k1_enumset1(A_20, B_21, E_26)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.58/1.43  tff(c_135, plain, (![B_59, A_58]: (r2_hidden(B_59, k2_tarski(A_58, B_59)))), inference(superposition, [status(thm), theory('equality')], [c_126, c_40])).
% 2.58/1.43  tff(c_74, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.58/1.43  tff(c_62, plain, (![A_27]: (k2_tarski(A_27, A_27)=k1_tarski(A_27))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.58/1.43  tff(c_42, plain, (![E_26, A_20, C_22]: (r2_hidden(E_26, k1_enumset1(A_20, E_26, C_22)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.58/1.43  tff(c_144, plain, (![A_60, B_61]: (r2_hidden(A_60, k2_tarski(A_60, B_61)))), inference(superposition, [status(thm), theory('equality')], [c_126, c_42])).
% 2.58/1.43  tff(c_153, plain, (![A_27]: (r2_hidden(A_27, k1_tarski(A_27)))), inference(superposition, [status(thm), theory('equality')], [c_62, c_144])).
% 2.58/1.43  tff(c_2, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, k4_xboole_0(A_1, B_2)) | r2_hidden(D_6, B_2) | ~r2_hidden(D_6, A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.58/1.43  tff(c_30, plain, (![A_14, B_15]: (r1_tarski(A_14, k2_xboole_0(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.58/1.43  tff(c_36, plain, (![B_19, A_18]: (k2_tarski(B_19, A_18)=k2_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.58/1.43  tff(c_169, plain, (![A_65, B_66]: (k3_tarski(k2_tarski(A_65, B_66))=k2_xboole_0(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.58/1.43  tff(c_229, plain, (![A_75, B_76]: (k3_tarski(k2_tarski(A_75, B_76))=k2_xboole_0(B_76, A_75))), inference(superposition, [status(thm), theory('equality')], [c_36, c_169])).
% 2.58/1.43  tff(c_72, plain, (![A_39, B_40]: (k3_tarski(k2_tarski(A_39, B_40))=k2_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.58/1.43  tff(c_235, plain, (![B_76, A_75]: (k2_xboole_0(B_76, A_75)=k2_xboole_0(A_75, B_76))), inference(superposition, [status(thm), theory('equality')], [c_229, c_72])).
% 2.58/1.43  tff(c_76, plain, (r1_tarski(k2_xboole_0(k1_tarski('#skF_5'), '#skF_6'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.58/1.43  tff(c_255, plain, (r1_tarski(k2_xboole_0('#skF_6', k1_tarski('#skF_5')), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_235, c_76])).
% 2.58/1.43  tff(c_310, plain, (![B_84, A_85]: (B_84=A_85 | ~r1_tarski(B_84, A_85) | ~r1_tarski(A_85, B_84))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.58/1.43  tff(c_312, plain, (k2_xboole_0('#skF_6', k1_tarski('#skF_5'))='#skF_6' | ~r1_tarski('#skF_6', k2_xboole_0('#skF_6', k1_tarski('#skF_5')))), inference(resolution, [status(thm)], [c_255, c_310])).
% 2.58/1.43  tff(c_323, plain, (k2_xboole_0('#skF_6', k1_tarski('#skF_5'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_312])).
% 2.58/1.43  tff(c_398, plain, (![A_104, B_105, C_106]: (k4_xboole_0(k4_xboole_0(A_104, B_105), C_106)=k4_xboole_0(A_104, k2_xboole_0(B_105, C_106)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.58/1.43  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.58/1.43  tff(c_486, plain, (![D_117, C_118, A_119, B_120]: (~r2_hidden(D_117, C_118) | ~r2_hidden(D_117, k4_xboole_0(A_119, k2_xboole_0(B_120, C_118))))), inference(superposition, [status(thm), theory('equality')], [c_398, c_4])).
% 2.58/1.43  tff(c_508, plain, (![D_121, A_122]: (~r2_hidden(D_121, k1_tarski('#skF_5')) | ~r2_hidden(D_121, k4_xboole_0(A_122, '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_323, c_486])).
% 2.58/1.43  tff(c_562, plain, (![D_134, A_135]: (~r2_hidden(D_134, k1_tarski('#skF_5')) | r2_hidden(D_134, '#skF_6') | ~r2_hidden(D_134, A_135))), inference(resolution, [status(thm)], [c_2, c_508])).
% 2.58/1.43  tff(c_565, plain, (![A_135]: (r2_hidden('#skF_5', '#skF_6') | ~r2_hidden('#skF_5', A_135))), inference(resolution, [status(thm)], [c_153, c_562])).
% 2.58/1.43  tff(c_569, plain, (![A_136]: (~r2_hidden('#skF_5', A_136))), inference(negUnitSimplification, [status(thm)], [c_74, c_565])).
% 2.58/1.43  tff(c_595, plain, $false, inference(resolution, [status(thm)], [c_135, c_569])).
% 2.58/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.58/1.43  
% 2.58/1.43  Inference rules
% 2.58/1.43  ----------------------
% 2.58/1.43  #Ref     : 0
% 2.58/1.43  #Sup     : 127
% 2.58/1.43  #Fact    : 0
% 2.58/1.43  #Define  : 0
% 2.58/1.43  #Split   : 1
% 2.58/1.43  #Chain   : 0
% 2.58/1.43  #Close   : 0
% 2.58/1.43  
% 2.58/1.43  Ordering : KBO
% 2.58/1.43  
% 2.58/1.43  Simplification rules
% 2.58/1.43  ----------------------
% 2.58/1.43  #Subsume      : 24
% 2.58/1.43  #Demod        : 33
% 2.58/1.43  #Tautology    : 59
% 2.58/1.43  #SimpNegUnit  : 2
% 2.58/1.43  #BackRed      : 2
% 2.58/1.43  
% 2.58/1.43  #Partial instantiations: 0
% 2.58/1.43  #Strategies tried      : 1
% 2.58/1.43  
% 2.58/1.43  Timing (in seconds)
% 2.58/1.43  ----------------------
% 2.58/1.43  Preprocessing        : 0.34
% 2.58/1.43  Parsing              : 0.18
% 2.58/1.43  CNF conversion       : 0.03
% 2.58/1.43  Main loop            : 0.28
% 2.58/1.43  Inferencing          : 0.09
% 2.58/1.43  Reduction            : 0.10
% 2.58/1.43  Demodulation         : 0.07
% 2.58/1.43  BG Simplification    : 0.02
% 2.58/1.43  Subsumption          : 0.05
% 2.58/1.43  Abstraction          : 0.02
% 2.58/1.43  MUC search           : 0.00
% 2.58/1.43  Cooper               : 0.00
% 2.58/1.43  Total                : 0.65
% 2.58/1.43  Index Insertion      : 0.00
% 2.58/1.43  Index Deletion       : 0.00
% 2.58/1.43  Index Matching       : 0.00
% 2.58/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
