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
% DateTime   : Thu Dec  3 10:08:59 EST 2020

% Result     : Theorem 2.97s
% Output     : CNFRefutation 2.97s
% Verified   : 
% Statistics : Number of formulae       :   50 (  76 expanded)
%              Number of leaves         :   25 (  38 expanded)
%              Depth                    :    7
%              Number of atoms          :   56 ( 128 expanded)
%              Number of equality atoms :   14 (  38 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_4

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_71,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(A,k2_zfmisc_1(k2_tarski(B,C),D))
       => ( ( k1_mcart_1(A) = B
            | k1_mcart_1(A) = C )
          & r2_hidden(k2_mcart_1(A),D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_mcart_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ~ ( ~ r2_hidden(A,C)
        & ~ r2_hidden(B,C)
        & C != k4_xboole_0(C,k2_tarski(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_44,plain,
    ( k1_mcart_1('#skF_5') != '#skF_7'
    | ~ r2_hidden(k2_mcart_1('#skF_5'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_54,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_5'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_42,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k2_tarski('#skF_6','#skF_7'),'#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_79,plain,(
    ! [A_40,C_41,B_42] :
      ( r2_hidden(k2_mcart_1(A_40),C_41)
      | ~ r2_hidden(A_40,k2_zfmisc_1(B_42,C_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_81,plain,(
    r2_hidden(k2_mcart_1('#skF_5'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_42,c_79])).

tff(c_85,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_81])).

tff(c_86,plain,(
    k1_mcart_1('#skF_5') != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_87,plain,(
    r2_hidden(k2_mcart_1('#skF_5'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_46,plain,
    ( k1_mcart_1('#skF_5') != '#skF_6'
    | ~ r2_hidden(k2_mcart_1('#skF_5'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_98,plain,(
    k1_mcart_1('#skF_5') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_46])).

tff(c_22,plain,(
    ! [C_11] : r2_hidden(C_11,k1_tarski(C_11)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_101,plain,(
    ! [A_51,B_52,C_53] :
      ( r2_hidden(k1_mcart_1(A_51),B_52)
      | ~ r2_hidden(A_51,k2_zfmisc_1(B_52,C_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_104,plain,(
    r2_hidden(k1_mcart_1('#skF_5'),k2_tarski('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_42,c_101])).

tff(c_336,plain,(
    ! [C_654,A_655,B_656] :
      ( k4_xboole_0(C_654,k2_tarski(A_655,B_656)) = C_654
      | r2_hidden(B_656,C_654)
      | r2_hidden(A_655,C_654) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_720,plain,(
    ! [D_1580,A_1581,B_1582,C_1583] :
      ( ~ r2_hidden(D_1580,k2_tarski(A_1581,B_1582))
      | ~ r2_hidden(D_1580,C_1583)
      | r2_hidden(B_1582,C_1583)
      | r2_hidden(A_1581,C_1583) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_336,c_4])).

tff(c_769,plain,(
    ! [C_1689] :
      ( ~ r2_hidden(k1_mcart_1('#skF_5'),C_1689)
      | r2_hidden('#skF_7',C_1689)
      | r2_hidden('#skF_6',C_1689) ) ),
    inference(resolution,[status(thm)],[c_104,c_720])).

tff(c_803,plain,
    ( r2_hidden('#skF_7',k1_tarski(k1_mcart_1('#skF_5')))
    | r2_hidden('#skF_6',k1_tarski(k1_mcart_1('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_22,c_769])).

tff(c_813,plain,(
    r2_hidden('#skF_6',k1_tarski(k1_mcart_1('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_803])).

tff(c_20,plain,(
    ! [C_11,A_7] :
      ( C_11 = A_7
      | ~ r2_hidden(C_11,k1_tarski(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_818,plain,(
    k1_mcart_1('#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_813,c_20])).

tff(c_869,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_818])).

tff(c_870,plain,(
    r2_hidden('#skF_7',k1_tarski(k1_mcart_1('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_803])).

tff(c_903,plain,(
    k1_mcart_1('#skF_5') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_870,c_20])).

tff(c_954,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_903])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:40:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.97/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.97/1.46  
% 2.97/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.97/1.47  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_4
% 2.97/1.47  
% 2.97/1.47  %Foreground sorts:
% 2.97/1.47  
% 2.97/1.47  
% 2.97/1.47  %Background operators:
% 2.97/1.47  
% 2.97/1.47  
% 2.97/1.47  %Foreground operators:
% 2.97/1.47  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.97/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.97/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.97/1.47  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.97/1.47  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.97/1.47  tff('#skF_7', type, '#skF_7': $i).
% 2.97/1.47  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.97/1.47  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.97/1.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.97/1.47  tff('#skF_5', type, '#skF_5': $i).
% 2.97/1.47  tff('#skF_6', type, '#skF_6': $i).
% 2.97/1.47  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.97/1.47  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.97/1.47  tff('#skF_8', type, '#skF_8': $i).
% 2.97/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.97/1.47  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.97/1.47  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.97/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.97/1.47  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.97/1.47  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.97/1.47  
% 2.97/1.48  tff(f_71, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(k2_tarski(B, C), D)) => (((k1_mcart_1(A) = B) | (k1_mcart_1(A) = C)) & r2_hidden(k2_mcart_1(A), D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_mcart_1)).
% 2.97/1.48  tff(f_62, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 2.97/1.48  tff(f_42, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.97/1.48  tff(f_56, axiom, (![A, B, C]: ~((~r2_hidden(A, C) & ~r2_hidden(B, C)) & ~(C = k4_xboole_0(C, k2_tarski(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_zfmisc_1)).
% 2.97/1.48  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.97/1.48  tff(c_44, plain, (k1_mcart_1('#skF_5')!='#skF_7' | ~r2_hidden(k2_mcart_1('#skF_5'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.97/1.48  tff(c_54, plain, (~r2_hidden(k2_mcart_1('#skF_5'), '#skF_8')), inference(splitLeft, [status(thm)], [c_44])).
% 2.97/1.48  tff(c_42, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k2_tarski('#skF_6', '#skF_7'), '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.97/1.48  tff(c_79, plain, (![A_40, C_41, B_42]: (r2_hidden(k2_mcart_1(A_40), C_41) | ~r2_hidden(A_40, k2_zfmisc_1(B_42, C_41)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.97/1.48  tff(c_81, plain, (r2_hidden(k2_mcart_1('#skF_5'), '#skF_8')), inference(resolution, [status(thm)], [c_42, c_79])).
% 2.97/1.48  tff(c_85, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_81])).
% 2.97/1.48  tff(c_86, plain, (k1_mcart_1('#skF_5')!='#skF_7'), inference(splitRight, [status(thm)], [c_44])).
% 2.97/1.48  tff(c_87, plain, (r2_hidden(k2_mcart_1('#skF_5'), '#skF_8')), inference(splitRight, [status(thm)], [c_44])).
% 2.97/1.48  tff(c_46, plain, (k1_mcart_1('#skF_5')!='#skF_6' | ~r2_hidden(k2_mcart_1('#skF_5'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.97/1.48  tff(c_98, plain, (k1_mcart_1('#skF_5')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_87, c_46])).
% 2.97/1.48  tff(c_22, plain, (![C_11]: (r2_hidden(C_11, k1_tarski(C_11)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.97/1.48  tff(c_101, plain, (![A_51, B_52, C_53]: (r2_hidden(k1_mcart_1(A_51), B_52) | ~r2_hidden(A_51, k2_zfmisc_1(B_52, C_53)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.97/1.48  tff(c_104, plain, (r2_hidden(k1_mcart_1('#skF_5'), k2_tarski('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_42, c_101])).
% 2.97/1.48  tff(c_336, plain, (![C_654, A_655, B_656]: (k4_xboole_0(C_654, k2_tarski(A_655, B_656))=C_654 | r2_hidden(B_656, C_654) | r2_hidden(A_655, C_654))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.97/1.48  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.97/1.48  tff(c_720, plain, (![D_1580, A_1581, B_1582, C_1583]: (~r2_hidden(D_1580, k2_tarski(A_1581, B_1582)) | ~r2_hidden(D_1580, C_1583) | r2_hidden(B_1582, C_1583) | r2_hidden(A_1581, C_1583))), inference(superposition, [status(thm), theory('equality')], [c_336, c_4])).
% 2.97/1.48  tff(c_769, plain, (![C_1689]: (~r2_hidden(k1_mcart_1('#skF_5'), C_1689) | r2_hidden('#skF_7', C_1689) | r2_hidden('#skF_6', C_1689))), inference(resolution, [status(thm)], [c_104, c_720])).
% 2.97/1.48  tff(c_803, plain, (r2_hidden('#skF_7', k1_tarski(k1_mcart_1('#skF_5'))) | r2_hidden('#skF_6', k1_tarski(k1_mcart_1('#skF_5')))), inference(resolution, [status(thm)], [c_22, c_769])).
% 2.97/1.48  tff(c_813, plain, (r2_hidden('#skF_6', k1_tarski(k1_mcart_1('#skF_5')))), inference(splitLeft, [status(thm)], [c_803])).
% 2.97/1.48  tff(c_20, plain, (![C_11, A_7]: (C_11=A_7 | ~r2_hidden(C_11, k1_tarski(A_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.97/1.48  tff(c_818, plain, (k1_mcart_1('#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_813, c_20])).
% 2.97/1.48  tff(c_869, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_818])).
% 2.97/1.48  tff(c_870, plain, (r2_hidden('#skF_7', k1_tarski(k1_mcart_1('#skF_5')))), inference(splitRight, [status(thm)], [c_803])).
% 2.97/1.48  tff(c_903, plain, (k1_mcart_1('#skF_5')='#skF_7'), inference(resolution, [status(thm)], [c_870, c_20])).
% 2.97/1.48  tff(c_954, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_903])).
% 2.97/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.97/1.48  
% 2.97/1.48  Inference rules
% 2.97/1.48  ----------------------
% 2.97/1.48  #Ref     : 0
% 2.97/1.48  #Sup     : 137
% 2.97/1.48  #Fact    : 0
% 2.97/1.48  #Define  : 0
% 2.97/1.48  #Split   : 3
% 2.97/1.48  #Chain   : 0
% 2.97/1.48  #Close   : 0
% 2.97/1.48  
% 2.97/1.48  Ordering : KBO
% 2.97/1.48  
% 2.97/1.48  Simplification rules
% 2.97/1.48  ----------------------
% 2.97/1.48  #Subsume      : 7
% 2.97/1.48  #Demod        : 2
% 2.97/1.48  #Tautology    : 29
% 2.97/1.48  #SimpNegUnit  : 3
% 2.97/1.48  #BackRed      : 0
% 2.97/1.48  
% 2.97/1.48  #Partial instantiations: 945
% 2.97/1.48  #Strategies tried      : 1
% 2.97/1.48  
% 2.97/1.48  Timing (in seconds)
% 2.97/1.48  ----------------------
% 3.10/1.48  Preprocessing        : 0.32
% 3.10/1.48  Parsing              : 0.16
% 3.10/1.48  CNF conversion       : 0.02
% 3.10/1.48  Main loop            : 0.38
% 3.10/1.48  Inferencing          : 0.19
% 3.10/1.48  Reduction            : 0.08
% 3.10/1.48  Demodulation         : 0.05
% 3.10/1.48  BG Simplification    : 0.02
% 3.10/1.48  Subsumption          : 0.06
% 3.10/1.48  Abstraction          : 0.02
% 3.10/1.48  MUC search           : 0.00
% 3.10/1.48  Cooper               : 0.00
% 3.10/1.48  Total                : 0.72
% 3.10/1.48  Index Insertion      : 0.00
% 3.10/1.48  Index Deletion       : 0.00
% 3.10/1.48  Index Matching       : 0.00
% 3.10/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
