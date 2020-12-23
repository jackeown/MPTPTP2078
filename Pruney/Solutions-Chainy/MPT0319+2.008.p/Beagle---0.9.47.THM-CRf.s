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
% DateTime   : Thu Dec  3 09:54:11 EST 2020

% Result     : Theorem 1.84s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   45 (  74 expanded)
%              Number of leaves         :   23 (  36 expanded)
%              Depth                    :    7
%              Number of atoms          :   52 ( 114 expanded)
%              Number of equality atoms :   10 (  18 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_69,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( A != B
       => ( r1_xboole_0(k2_zfmisc_1(k1_tarski(A),C),k2_zfmisc_1(k1_tarski(B),D))
          & r1_xboole_0(k2_zfmisc_1(C,k1_tarski(A)),k2_zfmisc_1(D,k1_tarski(B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t131_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_54,axiom,(
    ! [A,B,C,D] :
      ( ( r1_xboole_0(A,B)
        | r1_xboole_0(C,D) )
     => r1_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).

tff(f_61,axiom,(
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

tff(c_42,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_28,plain,(
    ! [A_17,B_18] :
      ( r1_xboole_0(k1_tarski(A_17),B_18)
      | r2_hidden(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_118,plain,(
    ! [C_56,D_57,A_58,B_59] :
      ( ~ r1_xboole_0(C_56,D_57)
      | r1_xboole_0(k2_zfmisc_1(A_58,C_56),k2_zfmisc_1(B_59,D_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_32,plain,(
    ! [A_19,B_20,C_21,D_22] :
      ( ~ r1_xboole_0(A_19,B_20)
      | r1_xboole_0(k2_zfmisc_1(A_19,C_21),k2_zfmisc_1(B_20,D_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_40,plain,
    ( ~ r1_xboole_0(k2_zfmisc_1('#skF_5',k1_tarski('#skF_3')),k2_zfmisc_1('#skF_6',k1_tarski('#skF_4')))
    | ~ r1_xboole_0(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_5'),k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_75,plain,(
    ~ r1_xboole_0(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_5'),k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_79,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_32,c_75])).

tff(c_83,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_28,c_79])).

tff(c_89,plain,(
    ! [A_50,B_51,C_52] :
      ( r2_hidden(A_50,k4_xboole_0(B_51,k1_tarski(C_52)))
      | C_52 = A_50
      | ~ r2_hidden(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_104,plain,(
    ! [A_53,C_54,B_55] :
      ( ~ r2_hidden(A_53,k1_tarski(C_54))
      | C_54 = A_53
      | ~ r2_hidden(A_53,B_55) ) ),
    inference(resolution,[status(thm)],[c_89,c_4])).

tff(c_106,plain,(
    ! [B_55] :
      ( '#skF_3' = '#skF_4'
      | ~ r2_hidden('#skF_3',B_55) ) ),
    inference(resolution,[status(thm)],[c_83,c_104])).

tff(c_109,plain,(
    ! [B_55] : ~ r2_hidden('#skF_3',B_55) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_106])).

tff(c_111,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_109,c_83])).

tff(c_112,plain,(
    ~ r1_xboole_0(k2_zfmisc_1('#skF_5',k1_tarski('#skF_3')),k2_zfmisc_1('#skF_6',k1_tarski('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_122,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_118,c_112])).

tff(c_126,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_28,c_122])).

tff(c_136,plain,(
    ! [A_64,B_65,C_66] :
      ( r2_hidden(A_64,k4_xboole_0(B_65,k1_tarski(C_66)))
      | C_66 = A_64
      | ~ r2_hidden(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_151,plain,(
    ! [A_67,C_68,B_69] :
      ( ~ r2_hidden(A_67,k1_tarski(C_68))
      | C_68 = A_67
      | ~ r2_hidden(A_67,B_69) ) ),
    inference(resolution,[status(thm)],[c_136,c_4])).

tff(c_153,plain,(
    ! [B_69] :
      ( '#skF_3' = '#skF_4'
      | ~ r2_hidden('#skF_3',B_69) ) ),
    inference(resolution,[status(thm)],[c_126,c_151])).

tff(c_156,plain,(
    ! [B_69] : ~ r2_hidden('#skF_3',B_69) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_153])).

tff(c_158,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_156,c_126])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:25:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.84/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.18  
% 1.93/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.18  %$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 1.93/1.18  
% 1.93/1.18  %Foreground sorts:
% 1.93/1.18  
% 1.93/1.18  
% 1.93/1.18  %Background operators:
% 1.93/1.18  
% 1.93/1.18  
% 1.93/1.18  %Foreground operators:
% 1.93/1.18  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.93/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.93/1.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.93/1.18  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.93/1.18  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.93/1.18  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.93/1.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.93/1.18  tff('#skF_5', type, '#skF_5': $i).
% 1.93/1.18  tff('#skF_6', type, '#skF_6': $i).
% 1.93/1.18  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.93/1.18  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.93/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.93/1.18  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.93/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.18  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.93/1.18  tff('#skF_4', type, '#skF_4': $i).
% 1.93/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.18  
% 1.93/1.19  tff(f_69, negated_conjecture, ~(![A, B, C, D]: (~(A = B) => (r1_xboole_0(k2_zfmisc_1(k1_tarski(A), C), k2_zfmisc_1(k1_tarski(B), D)) & r1_xboole_0(k2_zfmisc_1(C, k1_tarski(A)), k2_zfmisc_1(D, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t131_zfmisc_1)).
% 1.93/1.19  tff(f_48, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 1.93/1.19  tff(f_54, axiom, (![A, B, C, D]: ((r1_xboole_0(A, B) | r1_xboole_0(C, D)) => r1_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t127_zfmisc_1)).
% 1.93/1.19  tff(f_61, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 1.93/1.19  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 1.93/1.19  tff(c_42, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.93/1.19  tff(c_28, plain, (![A_17, B_18]: (r1_xboole_0(k1_tarski(A_17), B_18) | r2_hidden(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.93/1.19  tff(c_118, plain, (![C_56, D_57, A_58, B_59]: (~r1_xboole_0(C_56, D_57) | r1_xboole_0(k2_zfmisc_1(A_58, C_56), k2_zfmisc_1(B_59, D_57)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.93/1.19  tff(c_32, plain, (![A_19, B_20, C_21, D_22]: (~r1_xboole_0(A_19, B_20) | r1_xboole_0(k2_zfmisc_1(A_19, C_21), k2_zfmisc_1(B_20, D_22)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.93/1.19  tff(c_40, plain, (~r1_xboole_0(k2_zfmisc_1('#skF_5', k1_tarski('#skF_3')), k2_zfmisc_1('#skF_6', k1_tarski('#skF_4'))) | ~r1_xboole_0(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_5'), k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.93/1.19  tff(c_75, plain, (~r1_xboole_0(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_5'), k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_6'))), inference(splitLeft, [status(thm)], [c_40])).
% 1.93/1.19  tff(c_79, plain, (~r1_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_32, c_75])).
% 1.93/1.19  tff(c_83, plain, (r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_28, c_79])).
% 1.93/1.19  tff(c_89, plain, (![A_50, B_51, C_52]: (r2_hidden(A_50, k4_xboole_0(B_51, k1_tarski(C_52))) | C_52=A_50 | ~r2_hidden(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.93/1.19  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.93/1.19  tff(c_104, plain, (![A_53, C_54, B_55]: (~r2_hidden(A_53, k1_tarski(C_54)) | C_54=A_53 | ~r2_hidden(A_53, B_55))), inference(resolution, [status(thm)], [c_89, c_4])).
% 1.93/1.19  tff(c_106, plain, (![B_55]: ('#skF_3'='#skF_4' | ~r2_hidden('#skF_3', B_55))), inference(resolution, [status(thm)], [c_83, c_104])).
% 1.93/1.19  tff(c_109, plain, (![B_55]: (~r2_hidden('#skF_3', B_55))), inference(negUnitSimplification, [status(thm)], [c_42, c_106])).
% 1.93/1.19  tff(c_111, plain, $false, inference(negUnitSimplification, [status(thm)], [c_109, c_83])).
% 1.93/1.19  tff(c_112, plain, (~r1_xboole_0(k2_zfmisc_1('#skF_5', k1_tarski('#skF_3')), k2_zfmisc_1('#skF_6', k1_tarski('#skF_4')))), inference(splitRight, [status(thm)], [c_40])).
% 1.93/1.19  tff(c_122, plain, (~r1_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_118, c_112])).
% 1.93/1.19  tff(c_126, plain, (r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_28, c_122])).
% 1.93/1.19  tff(c_136, plain, (![A_64, B_65, C_66]: (r2_hidden(A_64, k4_xboole_0(B_65, k1_tarski(C_66))) | C_66=A_64 | ~r2_hidden(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.93/1.19  tff(c_151, plain, (![A_67, C_68, B_69]: (~r2_hidden(A_67, k1_tarski(C_68)) | C_68=A_67 | ~r2_hidden(A_67, B_69))), inference(resolution, [status(thm)], [c_136, c_4])).
% 1.93/1.19  tff(c_153, plain, (![B_69]: ('#skF_3'='#skF_4' | ~r2_hidden('#skF_3', B_69))), inference(resolution, [status(thm)], [c_126, c_151])).
% 1.93/1.19  tff(c_156, plain, (![B_69]: (~r2_hidden('#skF_3', B_69))), inference(negUnitSimplification, [status(thm)], [c_42, c_153])).
% 1.93/1.19  tff(c_158, plain, $false, inference(negUnitSimplification, [status(thm)], [c_156, c_126])).
% 1.93/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.19  
% 1.93/1.19  Inference rules
% 1.93/1.19  ----------------------
% 1.93/1.19  #Ref     : 0
% 1.93/1.19  #Sup     : 22
% 1.93/1.19  #Fact    : 0
% 1.93/1.19  #Define  : 0
% 1.93/1.19  #Split   : 1
% 1.93/1.19  #Chain   : 0
% 1.93/1.19  #Close   : 0
% 1.93/1.19  
% 1.93/1.19  Ordering : KBO
% 1.93/1.19  
% 1.93/1.19  Simplification rules
% 1.93/1.19  ----------------------
% 1.93/1.19  #Subsume      : 1
% 1.93/1.19  #Demod        : 0
% 1.93/1.19  #Tautology    : 12
% 1.93/1.19  #SimpNegUnit  : 4
% 1.93/1.19  #BackRed      : 2
% 1.93/1.19  
% 1.93/1.19  #Partial instantiations: 0
% 1.93/1.19  #Strategies tried      : 1
% 1.93/1.19  
% 1.93/1.19  Timing (in seconds)
% 1.93/1.19  ----------------------
% 1.93/1.19  Preprocessing        : 0.30
% 1.93/1.19  Parsing              : 0.16
% 1.93/1.19  CNF conversion       : 0.02
% 1.93/1.20  Main loop            : 0.14
% 1.93/1.20  Inferencing          : 0.05
% 1.93/1.20  Reduction            : 0.04
% 1.93/1.20  Demodulation         : 0.02
% 1.93/1.20  BG Simplification    : 0.01
% 1.93/1.20  Subsumption          : 0.03
% 1.93/1.20  Abstraction          : 0.01
% 1.93/1.20  MUC search           : 0.00
% 1.93/1.20  Cooper               : 0.00
% 1.93/1.20  Total                : 0.46
% 1.93/1.20  Index Insertion      : 0.00
% 1.93/1.20  Index Deletion       : 0.00
% 1.93/1.20  Index Matching       : 0.00
% 1.93/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
