%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:00 EST 2020

% Result     : Theorem 2.07s
% Output     : CNFRefutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   54 (  74 expanded)
%              Number of leaves         :   25 (  36 expanded)
%              Depth                    :    6
%              Number of atoms          :   54 (  94 expanded)
%              Number of equality atoms :   19 (  37 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_3

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_65,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
      <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_52,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_52,plain,
    ( ~ r2_hidden('#skF_5','#skF_6')
    | r2_hidden('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_76,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_48,plain,(
    ! [A_20,B_21] :
      ( r1_xboole_0(k1_tarski(A_20),B_21)
      | r2_hidden(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_78,plain,(
    ! [A_30,B_31] :
      ( k4_xboole_0(A_30,B_31) = A_30
      | ~ r1_xboole_0(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_129,plain,(
    ! [A_49,B_50] :
      ( k4_xboole_0(k1_tarski(A_49),B_50) = k1_tarski(A_49)
      | r2_hidden(A_49,B_50) ) ),
    inference(resolution,[status(thm)],[c_48,c_78])).

tff(c_50,plain,
    ( k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') != k1_tarski('#skF_5')
    | r2_hidden('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_122,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') != k1_tarski('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_135,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_122])).

tff(c_149,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_135])).

tff(c_150,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_44,plain,(
    ! [A_17] : k2_tarski(A_17,A_17) = k1_tarski(A_17) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_66,plain,(
    ! [D_23,B_24] : r2_hidden(D_23,k2_tarski(D_23,B_24)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_69,plain,(
    ! [A_17] : r2_hidden(A_17,k1_tarski(A_17)) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_66])).

tff(c_151,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') = k1_tarski('#skF_5') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_54,plain,
    ( k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') != k1_tarski('#skF_5')
    | k4_xboole_0(k1_tarski('#skF_7'),'#skF_8') = k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_152,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') != k1_tarski('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_164,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_152])).

tff(c_165,plain,(
    k4_xboole_0(k1_tarski('#skF_7'),'#skF_8') = k1_tarski('#skF_7') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_194,plain,(
    ! [D_52] :
      ( ~ r2_hidden(D_52,'#skF_8')
      | ~ r2_hidden(D_52,k1_tarski('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_4])).

tff(c_198,plain,(
    ~ r2_hidden('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_69,c_194])).

tff(c_202,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_198])).

tff(c_203,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_204,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_56,plain,
    ( ~ r2_hidden('#skF_5','#skF_6')
    | k4_xboole_0(k1_tarski('#skF_7'),'#skF_8') = k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_237,plain,(
    k4_xboole_0(k1_tarski('#skF_7'),'#skF_8') = k1_tarski('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_56])).

tff(c_245,plain,(
    ! [D_66] :
      ( ~ r2_hidden(D_66,'#skF_8')
      | ~ r2_hidden(D_66,k1_tarski('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_4])).

tff(c_249,plain,(
    ~ r2_hidden('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_69,c_245])).

tff(c_253,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_249])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:23:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.07/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.24  
% 2.07/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.25  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_3
% 2.07/1.25  
% 2.07/1.25  %Foreground sorts:
% 2.07/1.25  
% 2.07/1.25  
% 2.07/1.25  %Background operators:
% 2.07/1.25  
% 2.07/1.25  
% 2.07/1.25  %Foreground operators:
% 2.07/1.25  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.07/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.07/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.07/1.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.07/1.25  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.07/1.25  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.07/1.25  tff('#skF_7', type, '#skF_7': $i).
% 2.07/1.25  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.07/1.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.07/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.07/1.25  tff('#skF_5', type, '#skF_5': $i).
% 2.07/1.25  tff('#skF_6', type, '#skF_6': $i).
% 2.07/1.25  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.07/1.25  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.07/1.25  tff('#skF_8', type, '#skF_8': $i).
% 2.07/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.07/1.25  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.07/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.07/1.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.07/1.25  
% 2.07/1.26  tff(f_65, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_zfmisc_1)).
% 2.07/1.26  tff(f_59, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.07/1.26  tff(f_41, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.07/1.26  tff(f_52, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.07/1.26  tff(f_50, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 2.07/1.26  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.07/1.26  tff(c_52, plain, (~r2_hidden('#skF_5', '#skF_6') | r2_hidden('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.07/1.26  tff(c_76, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_52])).
% 2.07/1.26  tff(c_48, plain, (![A_20, B_21]: (r1_xboole_0(k1_tarski(A_20), B_21) | r2_hidden(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.07/1.26  tff(c_78, plain, (![A_30, B_31]: (k4_xboole_0(A_30, B_31)=A_30 | ~r1_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.07/1.26  tff(c_129, plain, (![A_49, B_50]: (k4_xboole_0(k1_tarski(A_49), B_50)=k1_tarski(A_49) | r2_hidden(A_49, B_50))), inference(resolution, [status(thm)], [c_48, c_78])).
% 2.07/1.26  tff(c_50, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')!=k1_tarski('#skF_5') | r2_hidden('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.07/1.26  tff(c_122, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')!=k1_tarski('#skF_5')), inference(splitLeft, [status(thm)], [c_50])).
% 2.07/1.26  tff(c_135, plain, (r2_hidden('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_129, c_122])).
% 2.07/1.26  tff(c_149, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_135])).
% 2.07/1.26  tff(c_150, plain, (r2_hidden('#skF_7', '#skF_8')), inference(splitRight, [status(thm)], [c_50])).
% 2.07/1.26  tff(c_44, plain, (![A_17]: (k2_tarski(A_17, A_17)=k1_tarski(A_17))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.07/1.26  tff(c_66, plain, (![D_23, B_24]: (r2_hidden(D_23, k2_tarski(D_23, B_24)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.07/1.26  tff(c_69, plain, (![A_17]: (r2_hidden(A_17, k1_tarski(A_17)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_66])).
% 2.07/1.26  tff(c_151, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')=k1_tarski('#skF_5')), inference(splitRight, [status(thm)], [c_50])).
% 2.07/1.26  tff(c_54, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')!=k1_tarski('#skF_5') | k4_xboole_0(k1_tarski('#skF_7'), '#skF_8')=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.07/1.26  tff(c_152, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')!=k1_tarski('#skF_5')), inference(splitLeft, [status(thm)], [c_54])).
% 2.07/1.26  tff(c_164, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_151, c_152])).
% 2.07/1.26  tff(c_165, plain, (k4_xboole_0(k1_tarski('#skF_7'), '#skF_8')=k1_tarski('#skF_7')), inference(splitRight, [status(thm)], [c_54])).
% 2.07/1.26  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.07/1.26  tff(c_194, plain, (![D_52]: (~r2_hidden(D_52, '#skF_8') | ~r2_hidden(D_52, k1_tarski('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_165, c_4])).
% 2.07/1.26  tff(c_198, plain, (~r2_hidden('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_69, c_194])).
% 2.07/1.26  tff(c_202, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_150, c_198])).
% 2.07/1.26  tff(c_203, plain, (r2_hidden('#skF_7', '#skF_8')), inference(splitRight, [status(thm)], [c_52])).
% 2.07/1.26  tff(c_204, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_52])).
% 2.07/1.26  tff(c_56, plain, (~r2_hidden('#skF_5', '#skF_6') | k4_xboole_0(k1_tarski('#skF_7'), '#skF_8')=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.07/1.26  tff(c_237, plain, (k4_xboole_0(k1_tarski('#skF_7'), '#skF_8')=k1_tarski('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_204, c_56])).
% 2.07/1.26  tff(c_245, plain, (![D_66]: (~r2_hidden(D_66, '#skF_8') | ~r2_hidden(D_66, k1_tarski('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_237, c_4])).
% 2.07/1.26  tff(c_249, plain, (~r2_hidden('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_69, c_245])).
% 2.07/1.26  tff(c_253, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_203, c_249])).
% 2.07/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.26  
% 2.07/1.26  Inference rules
% 2.07/1.26  ----------------------
% 2.07/1.26  #Ref     : 0
% 2.07/1.26  #Sup     : 43
% 2.07/1.26  #Fact    : 0
% 2.07/1.26  #Define  : 0
% 2.07/1.26  #Split   : 4
% 2.07/1.26  #Chain   : 0
% 2.07/1.26  #Close   : 0
% 2.07/1.26  
% 2.07/1.26  Ordering : KBO
% 2.07/1.26  
% 2.07/1.26  Simplification rules
% 2.07/1.26  ----------------------
% 2.07/1.26  #Subsume      : 2
% 2.07/1.26  #Demod        : 6
% 2.07/1.26  #Tautology    : 29
% 2.07/1.26  #SimpNegUnit  : 1
% 2.07/1.26  #BackRed      : 0
% 2.07/1.26  
% 2.07/1.26  #Partial instantiations: 0
% 2.07/1.26  #Strategies tried      : 1
% 2.07/1.26  
% 2.07/1.26  Timing (in seconds)
% 2.07/1.26  ----------------------
% 2.07/1.26  Preprocessing        : 0.32
% 2.07/1.26  Parsing              : 0.16
% 2.07/1.26  CNF conversion       : 0.03
% 2.07/1.26  Main loop            : 0.18
% 2.07/1.26  Inferencing          : 0.06
% 2.07/1.26  Reduction            : 0.06
% 2.07/1.26  Demodulation         : 0.04
% 2.07/1.26  BG Simplification    : 0.02
% 2.07/1.26  Subsumption          : 0.03
% 2.07/1.26  Abstraction          : 0.01
% 2.07/1.26  MUC search           : 0.00
% 2.07/1.26  Cooper               : 0.00
% 2.07/1.26  Total                : 0.53
% 2.07/1.26  Index Insertion      : 0.00
% 2.07/1.26  Index Deletion       : 0.00
% 2.07/1.26  Index Matching       : 0.00
% 2.07/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
