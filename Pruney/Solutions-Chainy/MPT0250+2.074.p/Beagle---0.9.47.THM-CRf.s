%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:41 EST 2020

% Result     : Theorem 5.70s
% Output     : CNFRefutation 5.94s
% Verified   : 
% Statistics : Number of formulae       :   55 (  71 expanded)
%              Number of leaves         :   28 (  37 expanded)
%              Depth                    :    9
%              Number of atoms          :   55 (  87 expanded)
%              Number of equality atoms :   14 (  31 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_82,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
       => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_77,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_55,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_60,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_113,plain,(
    ! [A_69,B_70] : k1_enumset1(A_69,A_69,B_70) = k2_tarski(A_69,B_70) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_16,plain,(
    ! [E_14,A_8,B_9] : r2_hidden(E_14,k1_enumset1(A_8,B_9,E_14)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_119,plain,(
    ! [B_70,A_69] : r2_hidden(B_70,k2_tarski(A_69,B_70)) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_16])).

tff(c_58,plain,(
    ! [A_51,B_52] : k3_tarski(k2_tarski(A_51,B_52)) = k2_xboole_0(A_51,B_52) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_106,plain,(
    ! [A_67,B_68] :
      ( r1_tarski(A_67,k3_tarski(B_68))
      | ~ r2_hidden(A_67,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_5878,plain,(
    ! [A_9690,A_9691,B_9692] :
      ( r1_tarski(A_9690,k2_xboole_0(A_9691,B_9692))
      | ~ r2_hidden(A_9690,k2_tarski(A_9691,B_9692)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_106])).

tff(c_5902,plain,(
    ! [B_70,A_69] : r1_tarski(B_70,k2_xboole_0(A_69,B_70)) ),
    inference(resolution,[status(thm)],[c_119,c_5878])).

tff(c_62,plain,(
    r1_tarski(k2_xboole_0(k1_tarski('#skF_4'),'#skF_5'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_142,plain,(
    ! [B_76,A_77] :
      ( B_76 = A_77
      | ~ r1_tarski(B_76,A_77)
      | ~ r1_tarski(A_77,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_150,plain,
    ( k2_xboole_0(k1_tarski('#skF_4'),'#skF_5') = '#skF_5'
    | ~ r1_tarski('#skF_5',k2_xboole_0(k1_tarski('#skF_4'),'#skF_5')) ),
    inference(resolution,[status(thm)],[c_62,c_142])).

tff(c_220,plain,(
    ~ r1_tarski('#skF_5',k2_xboole_0(k1_tarski('#skF_4'),'#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_150])).

tff(c_5948,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5902,c_220])).

tff(c_5949,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),'#skF_5') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_150])).

tff(c_18,plain,(
    ! [E_14,A_8,C_10] : r2_hidden(E_14,k1_enumset1(A_8,E_14,C_10)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_122,plain,(
    ! [A_69,B_70] : r2_hidden(A_69,k2_tarski(A_69,B_70)) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_18])).

tff(c_56,plain,(
    ! [A_49,B_50] :
      ( r1_tarski(A_49,k3_tarski(B_50))
      | ~ r2_hidden(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_38,plain,(
    ! [A_15] : k2_tarski(A_15,A_15) = k1_tarski(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_131,plain,(
    ! [B_71,A_72] : r2_hidden(B_71,k2_tarski(A_72,B_71)) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_16])).

tff(c_134,plain,(
    ! [A_15] : r2_hidden(A_15,k1_tarski(A_15)) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_131])).

tff(c_6119,plain,(
    ! [C_9994,B_9995,A_9996] :
      ( r2_hidden(C_9994,B_9995)
      | ~ r2_hidden(C_9994,A_9996)
      | ~ r1_tarski(A_9996,B_9995) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_6212,plain,(
    ! [A_10002,B_10003] :
      ( r2_hidden(A_10002,B_10003)
      | ~ r1_tarski(k1_tarski(A_10002),B_10003) ) ),
    inference(resolution,[status(thm)],[c_134,c_6119])).

tff(c_6655,plain,(
    ! [A_10035,B_10036] :
      ( r2_hidden(A_10035,k3_tarski(B_10036))
      | ~ r2_hidden(k1_tarski(A_10035),B_10036) ) ),
    inference(resolution,[status(thm)],[c_56,c_6212])).

tff(c_6659,plain,(
    ! [A_10035,B_70] : r2_hidden(A_10035,k3_tarski(k2_tarski(k1_tarski(A_10035),B_70))) ),
    inference(resolution,[status(thm)],[c_122,c_6655])).

tff(c_6697,plain,(
    ! [A_10044,B_10045] : r2_hidden(A_10044,k2_xboole_0(k1_tarski(A_10044),B_10045)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_6659])).

tff(c_6706,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_5949,c_6697])).

tff(c_6714,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_6706])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:35:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.70/2.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.70/2.18  
% 5.70/2.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.70/2.18  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 5.70/2.18  
% 5.70/2.18  %Foreground sorts:
% 5.70/2.18  
% 5.70/2.18  
% 5.70/2.18  %Background operators:
% 5.70/2.18  
% 5.70/2.18  
% 5.70/2.18  %Foreground operators:
% 5.70/2.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.70/2.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.70/2.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.70/2.18  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.70/2.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.70/2.18  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.70/2.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.70/2.18  tff('#skF_5', type, '#skF_5': $i).
% 5.70/2.18  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 5.70/2.18  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.70/2.18  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.70/2.18  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.70/2.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.70/2.18  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.70/2.18  tff('#skF_4', type, '#skF_4': $i).
% 5.70/2.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.70/2.18  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 5.70/2.18  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.70/2.18  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.70/2.18  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.70/2.18  
% 5.94/2.19  tff(f_82, negated_conjecture, ~(![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 5.94/2.19  tff(f_57, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 5.94/2.19  tff(f_53, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 5.94/2.19  tff(f_77, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 5.94/2.19  tff(f_75, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 5.94/2.19  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.94/2.19  tff(f_55, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 5.94/2.19  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.94/2.19  tff(c_60, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.94/2.19  tff(c_113, plain, (![A_69, B_70]: (k1_enumset1(A_69, A_69, B_70)=k2_tarski(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.94/2.19  tff(c_16, plain, (![E_14, A_8, B_9]: (r2_hidden(E_14, k1_enumset1(A_8, B_9, E_14)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.94/2.19  tff(c_119, plain, (![B_70, A_69]: (r2_hidden(B_70, k2_tarski(A_69, B_70)))), inference(superposition, [status(thm), theory('equality')], [c_113, c_16])).
% 5.94/2.19  tff(c_58, plain, (![A_51, B_52]: (k3_tarski(k2_tarski(A_51, B_52))=k2_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.94/2.19  tff(c_106, plain, (![A_67, B_68]: (r1_tarski(A_67, k3_tarski(B_68)) | ~r2_hidden(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.94/2.19  tff(c_5878, plain, (![A_9690, A_9691, B_9692]: (r1_tarski(A_9690, k2_xboole_0(A_9691, B_9692)) | ~r2_hidden(A_9690, k2_tarski(A_9691, B_9692)))), inference(superposition, [status(thm), theory('equality')], [c_58, c_106])).
% 5.94/2.19  tff(c_5902, plain, (![B_70, A_69]: (r1_tarski(B_70, k2_xboole_0(A_69, B_70)))), inference(resolution, [status(thm)], [c_119, c_5878])).
% 5.94/2.19  tff(c_62, plain, (r1_tarski(k2_xboole_0(k1_tarski('#skF_4'), '#skF_5'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.94/2.19  tff(c_142, plain, (![B_76, A_77]: (B_76=A_77 | ~r1_tarski(B_76, A_77) | ~r1_tarski(A_77, B_76))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.94/2.19  tff(c_150, plain, (k2_xboole_0(k1_tarski('#skF_4'), '#skF_5')='#skF_5' | ~r1_tarski('#skF_5', k2_xboole_0(k1_tarski('#skF_4'), '#skF_5'))), inference(resolution, [status(thm)], [c_62, c_142])).
% 5.94/2.19  tff(c_220, plain, (~r1_tarski('#skF_5', k2_xboole_0(k1_tarski('#skF_4'), '#skF_5'))), inference(splitLeft, [status(thm)], [c_150])).
% 5.94/2.19  tff(c_5948, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5902, c_220])).
% 5.94/2.19  tff(c_5949, plain, (k2_xboole_0(k1_tarski('#skF_4'), '#skF_5')='#skF_5'), inference(splitRight, [status(thm)], [c_150])).
% 5.94/2.19  tff(c_18, plain, (![E_14, A_8, C_10]: (r2_hidden(E_14, k1_enumset1(A_8, E_14, C_10)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.94/2.19  tff(c_122, plain, (![A_69, B_70]: (r2_hidden(A_69, k2_tarski(A_69, B_70)))), inference(superposition, [status(thm), theory('equality')], [c_113, c_18])).
% 5.94/2.19  tff(c_56, plain, (![A_49, B_50]: (r1_tarski(A_49, k3_tarski(B_50)) | ~r2_hidden(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.94/2.19  tff(c_38, plain, (![A_15]: (k2_tarski(A_15, A_15)=k1_tarski(A_15))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.94/2.19  tff(c_131, plain, (![B_71, A_72]: (r2_hidden(B_71, k2_tarski(A_72, B_71)))), inference(superposition, [status(thm), theory('equality')], [c_113, c_16])).
% 5.94/2.19  tff(c_134, plain, (![A_15]: (r2_hidden(A_15, k1_tarski(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_131])).
% 5.94/2.19  tff(c_6119, plain, (![C_9994, B_9995, A_9996]: (r2_hidden(C_9994, B_9995) | ~r2_hidden(C_9994, A_9996) | ~r1_tarski(A_9996, B_9995))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.94/2.19  tff(c_6212, plain, (![A_10002, B_10003]: (r2_hidden(A_10002, B_10003) | ~r1_tarski(k1_tarski(A_10002), B_10003))), inference(resolution, [status(thm)], [c_134, c_6119])).
% 5.94/2.19  tff(c_6655, plain, (![A_10035, B_10036]: (r2_hidden(A_10035, k3_tarski(B_10036)) | ~r2_hidden(k1_tarski(A_10035), B_10036))), inference(resolution, [status(thm)], [c_56, c_6212])).
% 5.94/2.19  tff(c_6659, plain, (![A_10035, B_70]: (r2_hidden(A_10035, k3_tarski(k2_tarski(k1_tarski(A_10035), B_70))))), inference(resolution, [status(thm)], [c_122, c_6655])).
% 5.94/2.19  tff(c_6697, plain, (![A_10044, B_10045]: (r2_hidden(A_10044, k2_xboole_0(k1_tarski(A_10044), B_10045)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_6659])).
% 5.94/2.19  tff(c_6706, plain, (r2_hidden('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_5949, c_6697])).
% 5.94/2.19  tff(c_6714, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_6706])).
% 5.94/2.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.94/2.19  
% 5.94/2.19  Inference rules
% 5.94/2.19  ----------------------
% 5.94/2.19  #Ref     : 0
% 5.94/2.19  #Sup     : 924
% 5.94/2.19  #Fact    : 18
% 5.94/2.19  #Define  : 0
% 5.94/2.19  #Split   : 1
% 5.94/2.19  #Chain   : 0
% 5.94/2.19  #Close   : 0
% 5.94/2.19  
% 5.94/2.19  Ordering : KBO
% 5.94/2.19  
% 5.94/2.19  Simplification rules
% 5.94/2.19  ----------------------
% 5.94/2.19  #Subsume      : 204
% 5.94/2.19  #Demod        : 293
% 5.94/2.19  #Tautology    : 353
% 5.94/2.19  #SimpNegUnit  : 1
% 5.94/2.19  #BackRed      : 2
% 5.94/2.19  
% 5.94/2.19  #Partial instantiations: 2970
% 5.94/2.19  #Strategies tried      : 1
% 5.94/2.19  
% 5.94/2.19  Timing (in seconds)
% 5.94/2.19  ----------------------
% 5.94/2.19  Preprocessing        : 0.32
% 5.94/2.19  Parsing              : 0.16
% 5.94/2.19  CNF conversion       : 0.02
% 5.94/2.19  Main loop            : 1.04
% 5.94/2.19  Inferencing          : 0.53
% 5.94/2.19  Reduction            : 0.30
% 5.94/2.19  Demodulation         : 0.25
% 5.94/2.19  BG Simplification    : 0.04
% 5.94/2.19  Subsumption          : 0.12
% 5.94/2.19  Abstraction          : 0.05
% 5.94/2.19  MUC search           : 0.00
% 5.94/2.19  Cooper               : 0.00
% 5.94/2.19  Total                : 1.39
% 5.94/2.19  Index Insertion      : 0.00
% 5.94/2.19  Index Deletion       : 0.00
% 5.94/2.20  Index Matching       : 0.00
% 5.94/2.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
