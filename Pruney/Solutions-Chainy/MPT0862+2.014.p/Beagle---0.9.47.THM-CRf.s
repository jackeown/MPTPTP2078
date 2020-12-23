%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:06 EST 2020

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.46s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 100 expanded)
%              Number of leaves         :   24 (  44 expanded)
%              Depth                    :    7
%              Number of atoms          :   63 ( 186 expanded)
%              Number of equality atoms :   22 (  64 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(f_77,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),k2_tarski(C,D)))
       => ( k1_mcart_1(A) = B
          & ( k2_mcart_1(A) = C
            | k2_mcart_1(A) = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_mcart_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),C))
     => ( k1_mcart_1(A) = B
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_mcart_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k2_tarski(A,B)
    <=> ( ~ r2_hidden(A,C)
        & ~ r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_48,plain,
    ( k2_mcart_1('#skF_3') != '#skF_6'
    | k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_60,plain,(
    k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_46,plain,(
    r2_hidden('#skF_3',k2_zfmisc_1(k1_tarski('#skF_4'),k2_tarski('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_90,plain,(
    ! [A_45,B_46,C_47] :
      ( k1_mcart_1(A_45) = B_46
      | ~ r2_hidden(A_45,k2_zfmisc_1(k1_tarski(B_46),C_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_93,plain,(
    k1_mcart_1('#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_46,c_90])).

tff(c_97,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_93])).

tff(c_98,plain,(
    k2_mcart_1('#skF_3') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_99,plain,(
    k1_mcart_1('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_50,plain,
    ( k2_mcart_1('#skF_3') != '#skF_5'
    | k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_105,plain,(
    k2_mcart_1('#skF_3') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_50])).

tff(c_129,plain,(
    ! [A_64,C_65,B_66] :
      ( r2_hidden(k2_mcart_1(A_64),C_65)
      | ~ r2_hidden(A_64,k2_zfmisc_1(B_66,C_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_132,plain,(
    r2_hidden(k2_mcart_1('#skF_3'),k2_tarski('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_46,c_129])).

tff(c_220,plain,(
    ! [A_89,B_90,C_91] :
      ( k4_xboole_0(k2_tarski(A_89,B_90),C_91) = k2_tarski(A_89,B_90)
      | r2_hidden(B_90,C_91)
      | r2_hidden(A_89,C_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_28,plain,(
    ! [C_15,B_14] : ~ r2_hidden(C_15,k4_xboole_0(B_14,k1_tarski(C_15))) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_370,plain,(
    ! [C_99,A_100,B_101] :
      ( ~ r2_hidden(C_99,k2_tarski(A_100,B_101))
      | r2_hidden(B_101,k1_tarski(C_99))
      | r2_hidden(A_100,k1_tarski(C_99)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_220,c_28])).

tff(c_383,plain,
    ( r2_hidden('#skF_6',k1_tarski(k2_mcart_1('#skF_3')))
    | r2_hidden('#skF_5',k1_tarski(k2_mcart_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_132,c_370])).

tff(c_384,plain,(
    r2_hidden('#skF_5',k1_tarski(k2_mcart_1('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_383])).

tff(c_148,plain,(
    ! [A_75,B_76,C_77] :
      ( r2_hidden(A_75,k4_xboole_0(B_76,k1_tarski(C_77)))
      | C_77 = A_75
      | ~ r2_hidden(A_75,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_160,plain,(
    ! [A_75,C_77,B_76] :
      ( ~ r2_hidden(A_75,k1_tarski(C_77))
      | C_77 = A_75
      | ~ r2_hidden(A_75,B_76) ) ),
    inference(resolution,[status(thm)],[c_148,c_4])).

tff(c_390,plain,(
    ! [B_76] :
      ( k2_mcart_1('#skF_3') = '#skF_5'
      | ~ r2_hidden('#skF_5',B_76) ) ),
    inference(resolution,[status(thm)],[c_384,c_160])).

tff(c_395,plain,(
    ! [B_76] : ~ r2_hidden('#skF_5',B_76) ),
    inference(negUnitSimplification,[status(thm)],[c_105,c_390])).

tff(c_413,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_395,c_384])).

tff(c_414,plain,(
    r2_hidden('#skF_6',k1_tarski(k2_mcart_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_383])).

tff(c_421,plain,(
    ! [B_76] :
      ( k2_mcart_1('#skF_3') = '#skF_6'
      | ~ r2_hidden('#skF_6',B_76) ) ),
    inference(resolution,[status(thm)],[c_414,c_160])).

tff(c_426,plain,(
    ! [B_76] : ~ r2_hidden('#skF_6',B_76) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_421])).

tff(c_428,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_426,c_414])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:14:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.15/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.29  
% 2.15/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.29  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 2.15/1.29  
% 2.15/1.29  %Foreground sorts:
% 2.15/1.29  
% 2.15/1.29  
% 2.15/1.29  %Background operators:
% 2.15/1.29  
% 2.15/1.29  
% 2.15/1.29  %Foreground operators:
% 2.15/1.29  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.15/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.15/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.15/1.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.15/1.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.15/1.29  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.15/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.15/1.29  tff('#skF_5', type, '#skF_5': $i).
% 2.15/1.29  tff('#skF_6', type, '#skF_6': $i).
% 2.15/1.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.15/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.15/1.29  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.15/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.15/1.29  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.15/1.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.15/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.15/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.15/1.29  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.15/1.29  
% 2.46/1.30  tff(f_77, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), k2_tarski(C, D))) => ((k1_mcart_1(A) = B) & ((k2_mcart_1(A) = C) | (k2_mcart_1(A) = D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_mcart_1)).
% 2.46/1.30  tff(f_68, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), C)) => ((k1_mcart_1(A) = B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_mcart_1)).
% 2.46/1.30  tff(f_62, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 2.46/1.30  tff(f_56, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k2_tarski(A, B)) <=> (~r2_hidden(A, C) & ~r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_zfmisc_1)).
% 2.46/1.30  tff(f_48, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 2.46/1.30  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.46/1.30  tff(c_48, plain, (k2_mcart_1('#skF_3')!='#skF_6' | k1_mcart_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.46/1.30  tff(c_60, plain, (k1_mcart_1('#skF_3')!='#skF_4'), inference(splitLeft, [status(thm)], [c_48])).
% 2.46/1.30  tff(c_46, plain, (r2_hidden('#skF_3', k2_zfmisc_1(k1_tarski('#skF_4'), k2_tarski('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.46/1.30  tff(c_90, plain, (![A_45, B_46, C_47]: (k1_mcart_1(A_45)=B_46 | ~r2_hidden(A_45, k2_zfmisc_1(k1_tarski(B_46), C_47)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.46/1.30  tff(c_93, plain, (k1_mcart_1('#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_46, c_90])).
% 2.46/1.30  tff(c_97, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_93])).
% 2.46/1.30  tff(c_98, plain, (k2_mcart_1('#skF_3')!='#skF_6'), inference(splitRight, [status(thm)], [c_48])).
% 2.46/1.30  tff(c_99, plain, (k1_mcart_1('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_48])).
% 2.46/1.30  tff(c_50, plain, (k2_mcart_1('#skF_3')!='#skF_5' | k1_mcart_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.46/1.30  tff(c_105, plain, (k2_mcart_1('#skF_3')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_99, c_50])).
% 2.46/1.30  tff(c_129, plain, (![A_64, C_65, B_66]: (r2_hidden(k2_mcart_1(A_64), C_65) | ~r2_hidden(A_64, k2_zfmisc_1(B_66, C_65)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.46/1.30  tff(c_132, plain, (r2_hidden(k2_mcart_1('#skF_3'), k2_tarski('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_46, c_129])).
% 2.46/1.30  tff(c_220, plain, (![A_89, B_90, C_91]: (k4_xboole_0(k2_tarski(A_89, B_90), C_91)=k2_tarski(A_89, B_90) | r2_hidden(B_90, C_91) | r2_hidden(A_89, C_91))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.46/1.30  tff(c_28, plain, (![C_15, B_14]: (~r2_hidden(C_15, k4_xboole_0(B_14, k1_tarski(C_15))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.46/1.30  tff(c_370, plain, (![C_99, A_100, B_101]: (~r2_hidden(C_99, k2_tarski(A_100, B_101)) | r2_hidden(B_101, k1_tarski(C_99)) | r2_hidden(A_100, k1_tarski(C_99)))), inference(superposition, [status(thm), theory('equality')], [c_220, c_28])).
% 2.46/1.30  tff(c_383, plain, (r2_hidden('#skF_6', k1_tarski(k2_mcart_1('#skF_3'))) | r2_hidden('#skF_5', k1_tarski(k2_mcart_1('#skF_3')))), inference(resolution, [status(thm)], [c_132, c_370])).
% 2.46/1.30  tff(c_384, plain, (r2_hidden('#skF_5', k1_tarski(k2_mcart_1('#skF_3')))), inference(splitLeft, [status(thm)], [c_383])).
% 2.46/1.30  tff(c_148, plain, (![A_75, B_76, C_77]: (r2_hidden(A_75, k4_xboole_0(B_76, k1_tarski(C_77))) | C_77=A_75 | ~r2_hidden(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.46/1.30  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.46/1.30  tff(c_160, plain, (![A_75, C_77, B_76]: (~r2_hidden(A_75, k1_tarski(C_77)) | C_77=A_75 | ~r2_hidden(A_75, B_76))), inference(resolution, [status(thm)], [c_148, c_4])).
% 2.46/1.30  tff(c_390, plain, (![B_76]: (k2_mcart_1('#skF_3')='#skF_5' | ~r2_hidden('#skF_5', B_76))), inference(resolution, [status(thm)], [c_384, c_160])).
% 2.46/1.30  tff(c_395, plain, (![B_76]: (~r2_hidden('#skF_5', B_76))), inference(negUnitSimplification, [status(thm)], [c_105, c_390])).
% 2.46/1.30  tff(c_413, plain, $false, inference(negUnitSimplification, [status(thm)], [c_395, c_384])).
% 2.46/1.30  tff(c_414, plain, (r2_hidden('#skF_6', k1_tarski(k2_mcart_1('#skF_3')))), inference(splitRight, [status(thm)], [c_383])).
% 2.46/1.30  tff(c_421, plain, (![B_76]: (k2_mcart_1('#skF_3')='#skF_6' | ~r2_hidden('#skF_6', B_76))), inference(resolution, [status(thm)], [c_414, c_160])).
% 2.46/1.30  tff(c_426, plain, (![B_76]: (~r2_hidden('#skF_6', B_76))), inference(negUnitSimplification, [status(thm)], [c_98, c_421])).
% 2.46/1.30  tff(c_428, plain, $false, inference(negUnitSimplification, [status(thm)], [c_426, c_414])).
% 2.46/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.46/1.30  
% 2.46/1.30  Inference rules
% 2.46/1.30  ----------------------
% 2.46/1.30  #Ref     : 0
% 2.46/1.30  #Sup     : 86
% 2.46/1.30  #Fact    : 0
% 2.46/1.30  #Define  : 0
% 2.46/1.30  #Split   : 2
% 2.46/1.30  #Chain   : 0
% 2.46/1.30  #Close   : 0
% 2.46/1.30  
% 2.46/1.30  Ordering : KBO
% 2.46/1.30  
% 2.46/1.30  Simplification rules
% 2.46/1.30  ----------------------
% 2.46/1.30  #Subsume      : 7
% 2.46/1.30  #Demod        : 12
% 2.46/1.30  #Tautology    : 39
% 2.46/1.30  #SimpNegUnit  : 5
% 2.46/1.30  #BackRed      : 2
% 2.46/1.30  
% 2.46/1.30  #Partial instantiations: 0
% 2.46/1.30  #Strategies tried      : 1
% 2.46/1.30  
% 2.46/1.30  Timing (in seconds)
% 2.46/1.30  ----------------------
% 2.46/1.31  Preprocessing        : 0.30
% 2.46/1.31  Parsing              : 0.16
% 2.46/1.31  CNF conversion       : 0.02
% 2.46/1.31  Main loop            : 0.26
% 2.46/1.31  Inferencing          : 0.10
% 2.46/1.31  Reduction            : 0.07
% 2.46/1.31  Demodulation         : 0.04
% 2.46/1.31  BG Simplification    : 0.02
% 2.46/1.31  Subsumption          : 0.05
% 2.46/1.31  Abstraction          : 0.02
% 2.46/1.31  MUC search           : 0.00
% 2.46/1.31  Cooper               : 0.00
% 2.46/1.31  Total                : 0.59
% 2.46/1.31  Index Insertion      : 0.00
% 2.46/1.31  Index Deletion       : 0.00
% 2.46/1.31  Index Matching       : 0.00
% 2.46/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
