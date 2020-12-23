%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:01 EST 2020

% Result     : Theorem 1.78s
% Output     : CNFRefutation 1.78s
% Verified   : 
% Statistics : Number of formulae       :   43 (  77 expanded)
%              Number of leaves         :   19 (  36 expanded)
%              Depth                    :    7
%              Number of atoms          :   60 ( 144 expanded)
%              Number of equality atoms :   23 (  66 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(A,k2_zfmisc_1(B,k2_tarski(C,D)))
       => ( r2_hidden(k1_mcart_1(A),B)
          & ( k2_mcart_1(A) = C
            | k2_mcart_1(A) = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_mcart_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) )
     => ( ! [D,E] : A != k4_tarski(D,E)
        | r2_hidden(A,k2_zfmisc_1(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_mcart_1)).

tff(f_51,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(A,k2_zfmisc_1(k2_tarski(B,C),D))
     => ( ( k1_mcart_1(A) = B
          | k1_mcart_1(A) = C )
        & r2_hidden(k2_mcart_1(A),D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_mcart_1)).

tff(c_20,plain,
    ( k2_mcart_1('#skF_1') != '#skF_4'
    | ~ r2_hidden(k1_mcart_1('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_51,plain,(
    ~ r2_hidden(k1_mcart_1('#skF_1'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_18,plain,(
    r2_hidden('#skF_1',k2_zfmisc_1('#skF_2',k2_tarski('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_52,plain,(
    ! [A_25,B_26,C_27] :
      ( r2_hidden(k1_mcart_1(A_25),B_26)
      | ~ r2_hidden(A_25,k2_zfmisc_1(B_26,C_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_54,plain,(
    r2_hidden(k1_mcart_1('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_52])).

tff(c_58,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_54])).

tff(c_60,plain,(
    r2_hidden(k1_mcart_1('#skF_1'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_22,plain,
    ( k2_mcart_1('#skF_1') != '#skF_3'
    | ~ r2_hidden(k1_mcart_1('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_62,plain,(
    k2_mcart_1('#skF_1') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_22])).

tff(c_59,plain,(
    k2_mcart_1('#skF_1') != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_68,plain,(
    ! [A_31,C_32,B_33] :
      ( r2_hidden(k2_mcart_1(A_31),C_32)
      | ~ r2_hidden(A_31,k2_zfmisc_1(B_33,C_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_71,plain,(
    r2_hidden(k2_mcart_1('#skF_1'),k2_tarski('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_18,c_68])).

tff(c_14,plain,(
    ! [A_17,B_18] : k1_mcart_1(k4_tarski(A_17,B_18)) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_16,plain,(
    ! [A_17,B_18] : k2_mcart_1(k4_tarski(A_17,B_18)) = B_18 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_8,plain,(
    ! [D_11,E_12,B_7,C_8] :
      ( r2_hidden(k4_tarski(D_11,E_12),k2_zfmisc_1(B_7,C_8))
      | ~ r2_hidden(k2_mcart_1(k4_tarski(D_11,E_12)),C_8)
      | ~ r2_hidden(k1_mcart_1(k4_tarski(D_11,E_12)),B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_23,plain,(
    ! [D_11,E_12,B_7,C_8] :
      ( r2_hidden(k4_tarski(D_11,E_12),k2_zfmisc_1(B_7,C_8))
      | ~ r2_hidden(E_12,C_8)
      | ~ r2_hidden(D_11,B_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_16,c_8])).

tff(c_81,plain,(
    ! [A_38,C_39,B_40,D_41] :
      ( k1_mcart_1(A_38) = C_39
      | k1_mcart_1(A_38) = B_40
      | ~ r2_hidden(A_38,k2_zfmisc_1(k2_tarski(B_40,C_39),D_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_85,plain,(
    ! [E_12,C_39,D_11,C_8,B_40] :
      ( k1_mcart_1(k4_tarski(D_11,E_12)) = C_39
      | k1_mcart_1(k4_tarski(D_11,E_12)) = B_40
      | ~ r2_hidden(E_12,C_8)
      | ~ r2_hidden(D_11,k2_tarski(B_40,C_39)) ) ),
    inference(resolution,[status(thm)],[c_23,c_81])).

tff(c_87,plain,(
    ! [E_12,C_39,D_11,C_8,B_40] :
      ( D_11 = C_39
      | D_11 = B_40
      | ~ r2_hidden(E_12,C_8)
      | ~ r2_hidden(D_11,k2_tarski(B_40,C_39)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14,c_85])).

tff(c_88,plain,(
    ! [E_12,C_8] : ~ r2_hidden(E_12,C_8) ),
    inference(splitLeft,[status(thm)],[c_87])).

tff(c_95,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_71])).

tff(c_97,plain,(
    ! [D_42,C_43,B_44] :
      ( D_42 = C_43
      | D_42 = B_44
      | ~ r2_hidden(D_42,k2_tarski(B_44,C_43)) ) ),
    inference(splitRight,[status(thm)],[c_87])).

tff(c_100,plain,
    ( k2_mcart_1('#skF_1') = '#skF_4'
    | k2_mcart_1('#skF_1') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_71,c_97])).

tff(c_104,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_59,c_100])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:39:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.78/1.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.15  
% 1.78/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.15  %$ r2_hidden > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.78/1.15  
% 1.78/1.15  %Foreground sorts:
% 1.78/1.15  
% 1.78/1.15  
% 1.78/1.15  %Background operators:
% 1.78/1.15  
% 1.78/1.15  
% 1.78/1.15  %Foreground operators:
% 1.78/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.78/1.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.78/1.15  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.78/1.15  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.78/1.15  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.78/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.78/1.15  tff('#skF_3', type, '#skF_3': $i).
% 1.78/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.78/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.78/1.15  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.78/1.15  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.78/1.15  tff('#skF_4', type, '#skF_4': $i).
% 1.78/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.78/1.15  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.78/1.15  
% 1.78/1.16  tff(f_64, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(B, k2_tarski(C, D))) => (r2_hidden(k1_mcart_1(A), B) & ((k2_mcart_1(A) = C) | (k2_mcart_1(A) = D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_mcart_1)).
% 1.78/1.16  tff(f_33, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 1.78/1.16  tff(f_55, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 1.78/1.16  tff(f_43, axiom, (![A, B, C]: ((r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)) => ((![D, E]: ~(A = k4_tarski(D, E))) | r2_hidden(A, k2_zfmisc_1(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_mcart_1)).
% 1.78/1.16  tff(f_51, axiom, (![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(k2_tarski(B, C), D)) => (((k1_mcart_1(A) = B) | (k1_mcart_1(A) = C)) & r2_hidden(k2_mcart_1(A), D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_mcart_1)).
% 1.78/1.16  tff(c_20, plain, (k2_mcart_1('#skF_1')!='#skF_4' | ~r2_hidden(k1_mcart_1('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.78/1.16  tff(c_51, plain, (~r2_hidden(k1_mcart_1('#skF_1'), '#skF_2')), inference(splitLeft, [status(thm)], [c_20])).
% 1.78/1.16  tff(c_18, plain, (r2_hidden('#skF_1', k2_zfmisc_1('#skF_2', k2_tarski('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.78/1.16  tff(c_52, plain, (![A_25, B_26, C_27]: (r2_hidden(k1_mcart_1(A_25), B_26) | ~r2_hidden(A_25, k2_zfmisc_1(B_26, C_27)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.78/1.16  tff(c_54, plain, (r2_hidden(k1_mcart_1('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_18, c_52])).
% 1.78/1.16  tff(c_58, plain, $false, inference(negUnitSimplification, [status(thm)], [c_51, c_54])).
% 1.78/1.16  tff(c_60, plain, (r2_hidden(k1_mcart_1('#skF_1'), '#skF_2')), inference(splitRight, [status(thm)], [c_20])).
% 1.78/1.16  tff(c_22, plain, (k2_mcart_1('#skF_1')!='#skF_3' | ~r2_hidden(k1_mcart_1('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.78/1.16  tff(c_62, plain, (k2_mcart_1('#skF_1')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_22])).
% 1.78/1.16  tff(c_59, plain, (k2_mcart_1('#skF_1')!='#skF_4'), inference(splitRight, [status(thm)], [c_20])).
% 1.78/1.16  tff(c_68, plain, (![A_31, C_32, B_33]: (r2_hidden(k2_mcart_1(A_31), C_32) | ~r2_hidden(A_31, k2_zfmisc_1(B_33, C_32)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.78/1.16  tff(c_71, plain, (r2_hidden(k2_mcart_1('#skF_1'), k2_tarski('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_18, c_68])).
% 1.78/1.16  tff(c_14, plain, (![A_17, B_18]: (k1_mcart_1(k4_tarski(A_17, B_18))=A_17)), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.78/1.16  tff(c_16, plain, (![A_17, B_18]: (k2_mcart_1(k4_tarski(A_17, B_18))=B_18)), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.78/1.16  tff(c_8, plain, (![D_11, E_12, B_7, C_8]: (r2_hidden(k4_tarski(D_11, E_12), k2_zfmisc_1(B_7, C_8)) | ~r2_hidden(k2_mcart_1(k4_tarski(D_11, E_12)), C_8) | ~r2_hidden(k1_mcart_1(k4_tarski(D_11, E_12)), B_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.78/1.16  tff(c_23, plain, (![D_11, E_12, B_7, C_8]: (r2_hidden(k4_tarski(D_11, E_12), k2_zfmisc_1(B_7, C_8)) | ~r2_hidden(E_12, C_8) | ~r2_hidden(D_11, B_7))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_16, c_8])).
% 1.78/1.16  tff(c_81, plain, (![A_38, C_39, B_40, D_41]: (k1_mcart_1(A_38)=C_39 | k1_mcart_1(A_38)=B_40 | ~r2_hidden(A_38, k2_zfmisc_1(k2_tarski(B_40, C_39), D_41)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.78/1.16  tff(c_85, plain, (![E_12, C_39, D_11, C_8, B_40]: (k1_mcart_1(k4_tarski(D_11, E_12))=C_39 | k1_mcart_1(k4_tarski(D_11, E_12))=B_40 | ~r2_hidden(E_12, C_8) | ~r2_hidden(D_11, k2_tarski(B_40, C_39)))), inference(resolution, [status(thm)], [c_23, c_81])).
% 1.78/1.16  tff(c_87, plain, (![E_12, C_39, D_11, C_8, B_40]: (D_11=C_39 | D_11=B_40 | ~r2_hidden(E_12, C_8) | ~r2_hidden(D_11, k2_tarski(B_40, C_39)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_14, c_85])).
% 1.78/1.16  tff(c_88, plain, (![E_12, C_8]: (~r2_hidden(E_12, C_8))), inference(splitLeft, [status(thm)], [c_87])).
% 1.78/1.16  tff(c_95, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_71])).
% 1.78/1.16  tff(c_97, plain, (![D_42, C_43, B_44]: (D_42=C_43 | D_42=B_44 | ~r2_hidden(D_42, k2_tarski(B_44, C_43)))), inference(splitRight, [status(thm)], [c_87])).
% 1.78/1.16  tff(c_100, plain, (k2_mcart_1('#skF_1')='#skF_4' | k2_mcart_1('#skF_1')='#skF_3'), inference(resolution, [status(thm)], [c_71, c_97])).
% 1.78/1.16  tff(c_104, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_59, c_100])).
% 1.78/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.16  
% 1.78/1.16  Inference rules
% 1.78/1.16  ----------------------
% 1.78/1.16  #Ref     : 0
% 1.78/1.16  #Sup     : 13
% 1.78/1.16  #Fact    : 0
% 1.78/1.16  #Define  : 0
% 1.78/1.16  #Split   : 2
% 1.78/1.16  #Chain   : 0
% 1.78/1.16  #Close   : 0
% 1.78/1.16  
% 1.78/1.16  Ordering : KBO
% 1.78/1.16  
% 1.78/1.16  Simplification rules
% 1.78/1.16  ----------------------
% 1.78/1.16  #Subsume      : 6
% 1.78/1.16  #Demod        : 8
% 1.78/1.16  #Tautology    : 9
% 1.78/1.16  #SimpNegUnit  : 8
% 1.78/1.16  #BackRed      : 3
% 1.78/1.16  
% 1.78/1.16  #Partial instantiations: 0
% 1.78/1.16  #Strategies tried      : 1
% 1.78/1.16  
% 1.78/1.16  Timing (in seconds)
% 1.78/1.16  ----------------------
% 1.78/1.16  Preprocessing        : 0.29
% 1.78/1.16  Parsing              : 0.15
% 1.78/1.16  CNF conversion       : 0.02
% 1.78/1.16  Main loop            : 0.10
% 1.78/1.16  Inferencing          : 0.03
% 1.78/1.16  Reduction            : 0.03
% 1.78/1.17  Demodulation         : 0.03
% 1.78/1.17  BG Simplification    : 0.01
% 1.78/1.17  Subsumption          : 0.01
% 1.78/1.17  Abstraction          : 0.01
% 1.78/1.17  MUC search           : 0.00
% 1.78/1.17  Cooper               : 0.00
% 1.78/1.17  Total                : 0.41
% 1.78/1.17  Index Insertion      : 0.00
% 1.78/1.17  Index Deletion       : 0.00
% 1.78/1.17  Index Matching       : 0.00
% 1.78/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
