%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:00 EST 2020

% Result     : Theorem 2.79s
% Output     : CNFRefutation 2.79s
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
        ( r2_hidden(A,k2_zfmisc_1(B,k2_tarski(C,D)))
       => ( r2_hidden(k1_mcart_1(A),B)
          & ( k2_mcart_1(A) = C
            | k2_mcart_1(A) = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_mcart_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ~ ( ~ r2_hidden(A,C)
        & ~ r2_hidden(B,C)
        & C != k4_xboole_0(C,k2_tarski(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_44,plain,
    ( k2_mcart_1('#skF_5') != '#skF_8'
    | ~ r2_hidden(k1_mcart_1('#skF_5'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_54,plain,(
    ~ r2_hidden(k1_mcart_1('#skF_5'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_42,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1('#skF_6',k2_tarski('#skF_7','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_75,plain,(
    ! [A_37,B_38,C_39] :
      ( r2_hidden(k1_mcart_1(A_37),B_38)
      | ~ r2_hidden(A_37,k2_zfmisc_1(B_38,C_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_77,plain,(
    r2_hidden(k1_mcart_1('#skF_5'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_75])).

tff(c_81,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_77])).

tff(c_82,plain,(
    k2_mcart_1('#skF_5') != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_83,plain,(
    r2_hidden(k1_mcart_1('#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_46,plain,
    ( k2_mcart_1('#skF_5') != '#skF_7'
    | ~ r2_hidden(k1_mcart_1('#skF_5'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_94,plain,(
    k2_mcart_1('#skF_5') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_46])).

tff(c_22,plain,(
    ! [C_11] : r2_hidden(C_11,k1_tarski(C_11)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_106,plain,(
    ! [A_51,C_52,B_53] :
      ( r2_hidden(k2_mcart_1(A_51),C_52)
      | ~ r2_hidden(A_51,k2_zfmisc_1(B_53,C_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_109,plain,(
    r2_hidden(k2_mcart_1('#skF_5'),k2_tarski('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_42,c_106])).

tff(c_380,plain,(
    ! [C_679,A_680,B_681] :
      ( k4_xboole_0(C_679,k2_tarski(A_680,B_681)) = C_679
      | r2_hidden(B_681,C_679)
      | r2_hidden(A_680,C_679) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_842,plain,(
    ! [D_1631,A_1632,B_1633,C_1634] :
      ( ~ r2_hidden(D_1631,k2_tarski(A_1632,B_1633))
      | ~ r2_hidden(D_1631,C_1634)
      | r2_hidden(B_1633,C_1634)
      | r2_hidden(A_1632,C_1634) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_380,c_4])).

tff(c_860,plain,(
    ! [C_1687] :
      ( ~ r2_hidden(k2_mcart_1('#skF_5'),C_1687)
      | r2_hidden('#skF_8',C_1687)
      | r2_hidden('#skF_7',C_1687) ) ),
    inference(resolution,[status(thm)],[c_109,c_842])).

tff(c_896,plain,
    ( r2_hidden('#skF_8',k1_tarski(k2_mcart_1('#skF_5')))
    | r2_hidden('#skF_7',k1_tarski(k2_mcart_1('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_22,c_860])).

tff(c_937,plain,(
    r2_hidden('#skF_7',k1_tarski(k2_mcart_1('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_896])).

tff(c_20,plain,(
    ! [C_11,A_7] :
      ( C_11 = A_7
      | ~ r2_hidden(C_11,k1_tarski(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_942,plain,(
    k2_mcart_1('#skF_5') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_937,c_20])).

tff(c_995,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_942])).

tff(c_996,plain,(
    r2_hidden('#skF_8',k1_tarski(k2_mcart_1('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_896])).

tff(c_1002,plain,(
    k2_mcart_1('#skF_5') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_996,c_20])).

tff(c_1055,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_1002])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:15:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.79/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/1.39  
% 2.79/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/1.39  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_4
% 2.79/1.39  
% 2.79/1.39  %Foreground sorts:
% 2.79/1.39  
% 2.79/1.39  
% 2.79/1.39  %Background operators:
% 2.79/1.39  
% 2.79/1.39  
% 2.79/1.39  %Foreground operators:
% 2.79/1.39  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.79/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.79/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.79/1.39  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.79/1.39  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.79/1.39  tff('#skF_7', type, '#skF_7': $i).
% 2.79/1.39  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.79/1.39  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.79/1.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.79/1.39  tff('#skF_5', type, '#skF_5': $i).
% 2.79/1.39  tff('#skF_6', type, '#skF_6': $i).
% 2.79/1.39  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.79/1.39  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.79/1.39  tff('#skF_8', type, '#skF_8': $i).
% 2.79/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.79/1.39  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.79/1.39  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.79/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.79/1.39  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.79/1.39  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.79/1.39  
% 2.79/1.40  tff(f_71, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(B, k2_tarski(C, D))) => (r2_hidden(k1_mcart_1(A), B) & ((k2_mcart_1(A) = C) | (k2_mcart_1(A) = D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_mcart_1)).
% 2.79/1.40  tff(f_62, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 2.79/1.40  tff(f_42, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.79/1.40  tff(f_56, axiom, (![A, B, C]: ~((~r2_hidden(A, C) & ~r2_hidden(B, C)) & ~(C = k4_xboole_0(C, k2_tarski(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_zfmisc_1)).
% 2.79/1.40  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.79/1.40  tff(c_44, plain, (k2_mcart_1('#skF_5')!='#skF_8' | ~r2_hidden(k1_mcart_1('#skF_5'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.79/1.40  tff(c_54, plain, (~r2_hidden(k1_mcart_1('#skF_5'), '#skF_6')), inference(splitLeft, [status(thm)], [c_44])).
% 2.79/1.40  tff(c_42, plain, (r2_hidden('#skF_5', k2_zfmisc_1('#skF_6', k2_tarski('#skF_7', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.79/1.40  tff(c_75, plain, (![A_37, B_38, C_39]: (r2_hidden(k1_mcart_1(A_37), B_38) | ~r2_hidden(A_37, k2_zfmisc_1(B_38, C_39)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.79/1.40  tff(c_77, plain, (r2_hidden(k1_mcart_1('#skF_5'), '#skF_6')), inference(resolution, [status(thm)], [c_42, c_75])).
% 2.79/1.40  tff(c_81, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_77])).
% 2.79/1.40  tff(c_82, plain, (k2_mcart_1('#skF_5')!='#skF_8'), inference(splitRight, [status(thm)], [c_44])).
% 2.79/1.40  tff(c_83, plain, (r2_hidden(k1_mcart_1('#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_44])).
% 2.79/1.40  tff(c_46, plain, (k2_mcart_1('#skF_5')!='#skF_7' | ~r2_hidden(k1_mcart_1('#skF_5'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.79/1.40  tff(c_94, plain, (k2_mcart_1('#skF_5')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_83, c_46])).
% 2.79/1.40  tff(c_22, plain, (![C_11]: (r2_hidden(C_11, k1_tarski(C_11)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.79/1.40  tff(c_106, plain, (![A_51, C_52, B_53]: (r2_hidden(k2_mcart_1(A_51), C_52) | ~r2_hidden(A_51, k2_zfmisc_1(B_53, C_52)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.79/1.40  tff(c_109, plain, (r2_hidden(k2_mcart_1('#skF_5'), k2_tarski('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_42, c_106])).
% 2.79/1.40  tff(c_380, plain, (![C_679, A_680, B_681]: (k4_xboole_0(C_679, k2_tarski(A_680, B_681))=C_679 | r2_hidden(B_681, C_679) | r2_hidden(A_680, C_679))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.79/1.40  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.79/1.40  tff(c_842, plain, (![D_1631, A_1632, B_1633, C_1634]: (~r2_hidden(D_1631, k2_tarski(A_1632, B_1633)) | ~r2_hidden(D_1631, C_1634) | r2_hidden(B_1633, C_1634) | r2_hidden(A_1632, C_1634))), inference(superposition, [status(thm), theory('equality')], [c_380, c_4])).
% 2.79/1.40  tff(c_860, plain, (![C_1687]: (~r2_hidden(k2_mcart_1('#skF_5'), C_1687) | r2_hidden('#skF_8', C_1687) | r2_hidden('#skF_7', C_1687))), inference(resolution, [status(thm)], [c_109, c_842])).
% 2.79/1.40  tff(c_896, plain, (r2_hidden('#skF_8', k1_tarski(k2_mcart_1('#skF_5'))) | r2_hidden('#skF_7', k1_tarski(k2_mcart_1('#skF_5')))), inference(resolution, [status(thm)], [c_22, c_860])).
% 2.79/1.40  tff(c_937, plain, (r2_hidden('#skF_7', k1_tarski(k2_mcart_1('#skF_5')))), inference(splitLeft, [status(thm)], [c_896])).
% 2.79/1.40  tff(c_20, plain, (![C_11, A_7]: (C_11=A_7 | ~r2_hidden(C_11, k1_tarski(A_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.79/1.40  tff(c_942, plain, (k2_mcart_1('#skF_5')='#skF_7'), inference(resolution, [status(thm)], [c_937, c_20])).
% 2.79/1.40  tff(c_995, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_942])).
% 2.79/1.40  tff(c_996, plain, (r2_hidden('#skF_8', k1_tarski(k2_mcart_1('#skF_5')))), inference(splitRight, [status(thm)], [c_896])).
% 2.79/1.40  tff(c_1002, plain, (k2_mcart_1('#skF_5')='#skF_8'), inference(resolution, [status(thm)], [c_996, c_20])).
% 2.79/1.40  tff(c_1055, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_1002])).
% 2.79/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/1.40  
% 2.79/1.40  Inference rules
% 2.79/1.40  ----------------------
% 2.79/1.40  #Ref     : 0
% 2.79/1.40  #Sup     : 142
% 2.79/1.40  #Fact    : 0
% 2.79/1.40  #Define  : 0
% 2.79/1.40  #Split   : 3
% 2.79/1.40  #Chain   : 0
% 2.79/1.40  #Close   : 0
% 2.79/1.40  
% 2.79/1.40  Ordering : KBO
% 2.79/1.40  
% 2.79/1.40  Simplification rules
% 2.79/1.40  ----------------------
% 2.79/1.40  #Subsume      : 7
% 2.79/1.40  #Demod        : 2
% 2.79/1.40  #Tautology    : 35
% 2.79/1.40  #SimpNegUnit  : 3
% 2.79/1.40  #BackRed      : 0
% 2.79/1.40  
% 2.79/1.40  #Partial instantiations: 875
% 2.79/1.40  #Strategies tried      : 1
% 2.79/1.40  
% 2.79/1.40  Timing (in seconds)
% 2.79/1.40  ----------------------
% 2.79/1.40  Preprocessing        : 0.29
% 2.79/1.40  Parsing              : 0.15
% 2.79/1.40  CNF conversion       : 0.02
% 2.79/1.40  Main loop            : 0.36
% 2.79/1.40  Inferencing          : 0.18
% 2.79/1.40  Reduction            : 0.08
% 2.79/1.40  Demodulation         : 0.05
% 2.79/1.40  BG Simplification    : 0.02
% 2.79/1.40  Subsumption          : 0.05
% 2.79/1.40  Abstraction          : 0.02
% 2.79/1.40  MUC search           : 0.00
% 2.79/1.40  Cooper               : 0.00
% 2.79/1.40  Total                : 0.68
% 2.79/1.40  Index Insertion      : 0.00
% 2.79/1.41  Index Deletion       : 0.00
% 2.79/1.41  Index Matching       : 0.00
% 2.79/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
