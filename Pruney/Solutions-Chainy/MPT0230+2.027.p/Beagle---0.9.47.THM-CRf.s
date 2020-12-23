%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:00 EST 2020

% Result     : Theorem 2.99s
% Output     : CNFRefutation 3.10s
% Verified   : 
% Statistics : Number of formulae       :   53 (  59 expanded)
%              Number of leaves         :   30 (  35 expanded)
%              Depth                    :    7
%              Number of atoms          :   54 (  70 expanded)
%              Number of equality atoms :   26 (  36 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_1

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_107,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r1_tarski(k1_tarski(A),k2_tarski(B,C))
          & A != B
          & A != C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_zfmisc_1)).

tff(f_83,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_37,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_92,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_97,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(c_86,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_84,plain,(
    '#skF_7' != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_112,plain,(
    ! [A_51] : k2_tarski(A_51,A_51) = k1_tarski(A_51) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_58,plain,(
    ! [D_32,A_27] : r2_hidden(D_32,k2_tarski(A_27,D_32)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_118,plain,(
    ! [A_51] : r2_hidden(A_51,k1_tarski(A_51)) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_58])).

tff(c_12,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_215,plain,(
    ! [A_76,B_77] :
      ( k3_xboole_0(A_76,B_77) = A_76
      | ~ r1_tarski(A_76,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_226,plain,(
    ! [B_6] : k3_xboole_0(B_6,B_6) = B_6 ),
    inference(resolution,[status(thm)],[c_12,c_215])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_xboole_0(A_3,B_4)
      | k3_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_268,plain,(
    ! [A_80,B_81] :
      ( ~ r2_hidden(A_80,B_81)
      | ~ r1_xboole_0(k1_tarski(A_80),B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_732,plain,(
    ! [A_105,B_106] :
      ( ~ r2_hidden(A_105,B_106)
      | k3_xboole_0(k1_tarski(A_105),B_106) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_268])).

tff(c_746,plain,(
    ! [A_105] :
      ( ~ r2_hidden(A_105,k1_tarski(A_105))
      | k1_tarski(A_105) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_732])).

tff(c_758,plain,(
    ! [A_105] : k1_tarski(A_105) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_746])).

tff(c_197,plain,(
    ! [A_72,B_73] :
      ( r1_xboole_0(k1_tarski(A_72),B_73)
      | r2_hidden(A_72,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_679,plain,(
    ! [A_103,B_104] :
      ( k3_xboole_0(k1_tarski(A_103),B_104) = k1_xboole_0
      | r2_hidden(A_103,B_104) ) ),
    inference(resolution,[status(thm)],[c_197,c_4])).

tff(c_88,plain,(
    r1_tarski(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_225,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) = k1_tarski('#skF_5') ),
    inference(resolution,[status(thm)],[c_88,c_215])).

tff(c_688,plain,
    ( k1_tarski('#skF_5') = k1_xboole_0
    | r2_hidden('#skF_5',k2_tarski('#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_679,c_225])).

tff(c_979,plain,(
    r2_hidden('#skF_5',k2_tarski('#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_758,c_688])).

tff(c_56,plain,(
    ! [D_32,B_28,A_27] :
      ( D_32 = B_28
      | D_32 = A_27
      | ~ r2_hidden(D_32,k2_tarski(A_27,B_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_982,plain,
    ( '#skF_7' = '#skF_5'
    | '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_979,c_56])).

tff(c_986,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_84,c_982])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:31:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.99/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.10/1.46  
% 3.10/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.10/1.46  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_1
% 3.10/1.46  
% 3.10/1.46  %Foreground sorts:
% 3.10/1.46  
% 3.10/1.46  
% 3.10/1.46  %Background operators:
% 3.10/1.46  
% 3.10/1.46  
% 3.10/1.46  %Foreground operators:
% 3.10/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.10/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.10/1.46  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.10/1.46  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.10/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.10/1.46  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.10/1.46  tff('#skF_7', type, '#skF_7': $i).
% 3.10/1.46  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.10/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.10/1.46  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.10/1.46  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.10/1.46  tff('#skF_5', type, '#skF_5': $i).
% 3.10/1.46  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.10/1.46  tff('#skF_6', type, '#skF_6': $i).
% 3.10/1.46  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.10/1.46  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.10/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.10/1.46  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.10/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.10/1.46  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.10/1.46  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.10/1.46  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 3.10/1.46  
% 3.10/1.47  tff(f_107, negated_conjecture, ~(![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 3.10/1.47  tff(f_83, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.10/1.47  tff(f_81, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 3.10/1.47  tff(f_37, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.10/1.47  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.10/1.47  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.10/1.47  tff(f_92, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 3.10/1.47  tff(f_97, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.10/1.47  tff(c_86, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.10/1.47  tff(c_84, plain, ('#skF_7'!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.10/1.47  tff(c_112, plain, (![A_51]: (k2_tarski(A_51, A_51)=k1_tarski(A_51))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.10/1.47  tff(c_58, plain, (![D_32, A_27]: (r2_hidden(D_32, k2_tarski(A_27, D_32)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.10/1.47  tff(c_118, plain, (![A_51]: (r2_hidden(A_51, k1_tarski(A_51)))), inference(superposition, [status(thm), theory('equality')], [c_112, c_58])).
% 3.10/1.47  tff(c_12, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.10/1.47  tff(c_215, plain, (![A_76, B_77]: (k3_xboole_0(A_76, B_77)=A_76 | ~r1_tarski(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.10/1.47  tff(c_226, plain, (![B_6]: (k3_xboole_0(B_6, B_6)=B_6)), inference(resolution, [status(thm)], [c_12, c_215])).
% 3.10/1.47  tff(c_6, plain, (![A_3, B_4]: (r1_xboole_0(A_3, B_4) | k3_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.10/1.47  tff(c_268, plain, (![A_80, B_81]: (~r2_hidden(A_80, B_81) | ~r1_xboole_0(k1_tarski(A_80), B_81))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.10/1.47  tff(c_732, plain, (![A_105, B_106]: (~r2_hidden(A_105, B_106) | k3_xboole_0(k1_tarski(A_105), B_106)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_268])).
% 3.10/1.47  tff(c_746, plain, (![A_105]: (~r2_hidden(A_105, k1_tarski(A_105)) | k1_tarski(A_105)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_226, c_732])).
% 3.10/1.47  tff(c_758, plain, (![A_105]: (k1_tarski(A_105)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_118, c_746])).
% 3.10/1.47  tff(c_197, plain, (![A_72, B_73]: (r1_xboole_0(k1_tarski(A_72), B_73) | r2_hidden(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.10/1.47  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.10/1.47  tff(c_679, plain, (![A_103, B_104]: (k3_xboole_0(k1_tarski(A_103), B_104)=k1_xboole_0 | r2_hidden(A_103, B_104))), inference(resolution, [status(thm)], [c_197, c_4])).
% 3.10/1.47  tff(c_88, plain, (r1_tarski(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.10/1.47  tff(c_225, plain, (k3_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))=k1_tarski('#skF_5')), inference(resolution, [status(thm)], [c_88, c_215])).
% 3.10/1.47  tff(c_688, plain, (k1_tarski('#skF_5')=k1_xboole_0 | r2_hidden('#skF_5', k2_tarski('#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_679, c_225])).
% 3.10/1.47  tff(c_979, plain, (r2_hidden('#skF_5', k2_tarski('#skF_6', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_758, c_688])).
% 3.10/1.47  tff(c_56, plain, (![D_32, B_28, A_27]: (D_32=B_28 | D_32=A_27 | ~r2_hidden(D_32, k2_tarski(A_27, B_28)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.10/1.47  tff(c_982, plain, ('#skF_7'='#skF_5' | '#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_979, c_56])).
% 3.10/1.47  tff(c_986, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_84, c_982])).
% 3.10/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.10/1.47  
% 3.10/1.47  Inference rules
% 3.10/1.47  ----------------------
% 3.10/1.47  #Ref     : 0
% 3.10/1.47  #Sup     : 201
% 3.10/1.47  #Fact    : 0
% 3.10/1.47  #Define  : 0
% 3.10/1.47  #Split   : 1
% 3.10/1.47  #Chain   : 0
% 3.10/1.47  #Close   : 0
% 3.10/1.47  
% 3.10/1.47  Ordering : KBO
% 3.10/1.47  
% 3.10/1.47  Simplification rules
% 3.10/1.47  ----------------------
% 3.10/1.47  #Subsume      : 15
% 3.10/1.47  #Demod        : 84
% 3.10/1.47  #Tautology    : 143
% 3.10/1.47  #SimpNegUnit  : 7
% 3.10/1.47  #BackRed      : 0
% 3.10/1.47  
% 3.10/1.47  #Partial instantiations: 0
% 3.10/1.47  #Strategies tried      : 1
% 3.10/1.47  
% 3.10/1.47  Timing (in seconds)
% 3.10/1.47  ----------------------
% 3.10/1.48  Preprocessing        : 0.35
% 3.10/1.48  Parsing              : 0.17
% 3.10/1.48  CNF conversion       : 0.03
% 3.10/1.48  Main loop            : 0.36
% 3.10/1.48  Inferencing          : 0.12
% 3.10/1.48  Reduction            : 0.13
% 3.10/1.48  Demodulation         : 0.09
% 3.10/1.48  BG Simplification    : 0.02
% 3.10/1.48  Subsumption          : 0.07
% 3.10/1.48  Abstraction          : 0.02
% 3.10/1.48  MUC search           : 0.00
% 3.10/1.48  Cooper               : 0.00
% 3.10/1.48  Total                : 0.74
% 3.10/1.48  Index Insertion      : 0.00
% 3.10/1.48  Index Deletion       : 0.00
% 3.10/1.48  Index Matching       : 0.00
% 3.10/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
