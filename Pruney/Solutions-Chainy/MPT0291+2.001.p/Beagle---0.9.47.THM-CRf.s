%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:34 EST 2020

% Result     : Theorem 6.66s
% Output     : CNFRefutation 6.66s
% Verified   : 
% Statistics : Number of formulae       :   38 (  47 expanded)
%              Number of leaves         :   20 (  27 expanded)
%              Depth                    :    7
%              Number of atoms          :   51 (  80 expanded)
%              Number of equality atoms :    2 (   5 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k3_xboole_0 > #nlpp > k3_tarski > #skF_6 > #skF_1 > #skF_3 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_66,negated_conjecture,(
    ~ ! [A,B] :
        ( ! [C] :
            ( r2_hidden(C,A)
           => r1_xboole_0(C,B) )
       => r1_xboole_0(k3_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

tff(c_42,plain,(
    ~ r1_xboole_0(k3_tarski('#skF_8'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_50,plain,(
    ! [A_46,B_47] :
      ( r2_hidden('#skF_3'(A_46,B_47),k3_xboole_0(A_46,B_47))
      | r1_xboole_0(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_64,plain,(
    ! [A_46,B_47] :
      ( r2_hidden('#skF_3'(A_46,B_47),B_47)
      | r1_xboole_0(A_46,B_47) ) ),
    inference(resolution,[status(thm)],[c_50,c_4])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,A_1)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_65,plain,(
    ! [A_46,B_47] :
      ( r2_hidden('#skF_3'(A_46,B_47),A_46)
      | r1_xboole_0(A_46,B_47) ) ),
    inference(resolution,[status(thm)],[c_50,c_6])).

tff(c_28,plain,(
    ! [C_27,A_12] :
      ( r2_hidden(C_27,'#skF_7'(A_12,k3_tarski(A_12),C_27))
      | ~ r2_hidden(C_27,k3_tarski(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_138,plain,(
    ! [A_65,C_66] :
      ( r2_hidden('#skF_7'(A_65,k3_tarski(A_65),C_66),A_65)
      | ~ r2_hidden(C_66,k3_tarski(A_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_44,plain,(
    ! [C_32] :
      ( r1_xboole_0(C_32,'#skF_9')
      | ~ r2_hidden(C_32,'#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_195,plain,(
    ! [C_76] :
      ( r1_xboole_0('#skF_7'('#skF_8',k3_tarski('#skF_8'),C_76),'#skF_9')
      | ~ r2_hidden(C_76,k3_tarski('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_138,c_44])).

tff(c_122,plain,(
    ! [D_62,A_63,B_64] :
      ( r2_hidden(D_62,k3_xboole_0(A_63,B_64))
      | ~ r2_hidden(D_62,B_64)
      | ~ r2_hidden(D_62,A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_22,plain,(
    ! [A_7,B_8,C_11] :
      ( ~ r1_xboole_0(A_7,B_8)
      | ~ r2_hidden(C_11,k3_xboole_0(A_7,B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_135,plain,(
    ! [A_63,B_64,D_62] :
      ( ~ r1_xboole_0(A_63,B_64)
      | ~ r2_hidden(D_62,B_64)
      | ~ r2_hidden(D_62,A_63) ) ),
    inference(resolution,[status(thm)],[c_122,c_22])).

tff(c_4997,plain,(
    ! [D_330,C_331] :
      ( ~ r2_hidden(D_330,'#skF_9')
      | ~ r2_hidden(D_330,'#skF_7'('#skF_8',k3_tarski('#skF_8'),C_331))
      | ~ r2_hidden(C_331,k3_tarski('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_195,c_135])).

tff(c_5103,plain,(
    ! [C_332] :
      ( ~ r2_hidden(C_332,'#skF_9')
      | ~ r2_hidden(C_332,k3_tarski('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_28,c_4997])).

tff(c_5204,plain,(
    ! [B_333] :
      ( ~ r2_hidden('#skF_3'(k3_tarski('#skF_8'),B_333),'#skF_9')
      | r1_xboole_0(k3_tarski('#skF_8'),B_333) ) ),
    inference(resolution,[status(thm)],[c_65,c_5103])).

tff(c_5216,plain,(
    r1_xboole_0(k3_tarski('#skF_8'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_64,c_5204])).

tff(c_5222,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_42,c_5216])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:51:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.66/2.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.66/2.41  
% 6.66/2.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.66/2.41  %$ r2_hidden > r1_xboole_0 > k3_xboole_0 > #nlpp > k3_tarski > #skF_6 > #skF_1 > #skF_3 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_5 > #skF_4
% 6.66/2.41  
% 6.66/2.41  %Foreground sorts:
% 6.66/2.41  
% 6.66/2.41  
% 6.66/2.41  %Background operators:
% 6.66/2.41  
% 6.66/2.41  
% 6.66/2.41  %Foreground operators:
% 6.66/2.41  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 6.66/2.41  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 6.66/2.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.66/2.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.66/2.41  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 6.66/2.41  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.66/2.41  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.66/2.41  tff('#skF_9', type, '#skF_9': $i).
% 6.66/2.41  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 6.66/2.41  tff('#skF_8', type, '#skF_8': $i).
% 6.66/2.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.66/2.41  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.66/2.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.66/2.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.66/2.41  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 6.66/2.41  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 6.66/2.41  
% 6.66/2.42  tff(f_66, negated_conjecture, ~(![A, B]: ((![C]: (r2_hidden(C, A) => r1_xboole_0(C, B))) => r1_xboole_0(k3_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_zfmisc_1)).
% 6.66/2.42  tff(f_48, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 6.66/2.42  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 6.66/2.42  tff(f_58, axiom, (![A, B]: ((B = k3_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(C, D) & r2_hidden(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tarski)).
% 6.66/2.42  tff(c_42, plain, (~r1_xboole_0(k3_tarski('#skF_8'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.66/2.42  tff(c_50, plain, (![A_46, B_47]: (r2_hidden('#skF_3'(A_46, B_47), k3_xboole_0(A_46, B_47)) | r1_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.66/2.42  tff(c_4, plain, (![D_6, B_2, A_1]: (r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.66/2.42  tff(c_64, plain, (![A_46, B_47]: (r2_hidden('#skF_3'(A_46, B_47), B_47) | r1_xboole_0(A_46, B_47))), inference(resolution, [status(thm)], [c_50, c_4])).
% 6.66/2.42  tff(c_6, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, A_1) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.66/2.42  tff(c_65, plain, (![A_46, B_47]: (r2_hidden('#skF_3'(A_46, B_47), A_46) | r1_xboole_0(A_46, B_47))), inference(resolution, [status(thm)], [c_50, c_6])).
% 6.66/2.42  tff(c_28, plain, (![C_27, A_12]: (r2_hidden(C_27, '#skF_7'(A_12, k3_tarski(A_12), C_27)) | ~r2_hidden(C_27, k3_tarski(A_12)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.66/2.42  tff(c_138, plain, (![A_65, C_66]: (r2_hidden('#skF_7'(A_65, k3_tarski(A_65), C_66), A_65) | ~r2_hidden(C_66, k3_tarski(A_65)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.66/2.42  tff(c_44, plain, (![C_32]: (r1_xboole_0(C_32, '#skF_9') | ~r2_hidden(C_32, '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.66/2.42  tff(c_195, plain, (![C_76]: (r1_xboole_0('#skF_7'('#skF_8', k3_tarski('#skF_8'), C_76), '#skF_9') | ~r2_hidden(C_76, k3_tarski('#skF_8')))), inference(resolution, [status(thm)], [c_138, c_44])).
% 6.66/2.42  tff(c_122, plain, (![D_62, A_63, B_64]: (r2_hidden(D_62, k3_xboole_0(A_63, B_64)) | ~r2_hidden(D_62, B_64) | ~r2_hidden(D_62, A_63))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.66/2.42  tff(c_22, plain, (![A_7, B_8, C_11]: (~r1_xboole_0(A_7, B_8) | ~r2_hidden(C_11, k3_xboole_0(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.66/2.42  tff(c_135, plain, (![A_63, B_64, D_62]: (~r1_xboole_0(A_63, B_64) | ~r2_hidden(D_62, B_64) | ~r2_hidden(D_62, A_63))), inference(resolution, [status(thm)], [c_122, c_22])).
% 6.66/2.42  tff(c_4997, plain, (![D_330, C_331]: (~r2_hidden(D_330, '#skF_9') | ~r2_hidden(D_330, '#skF_7'('#skF_8', k3_tarski('#skF_8'), C_331)) | ~r2_hidden(C_331, k3_tarski('#skF_8')))), inference(resolution, [status(thm)], [c_195, c_135])).
% 6.66/2.42  tff(c_5103, plain, (![C_332]: (~r2_hidden(C_332, '#skF_9') | ~r2_hidden(C_332, k3_tarski('#skF_8')))), inference(resolution, [status(thm)], [c_28, c_4997])).
% 6.66/2.42  tff(c_5204, plain, (![B_333]: (~r2_hidden('#skF_3'(k3_tarski('#skF_8'), B_333), '#skF_9') | r1_xboole_0(k3_tarski('#skF_8'), B_333))), inference(resolution, [status(thm)], [c_65, c_5103])).
% 6.66/2.42  tff(c_5216, plain, (r1_xboole_0(k3_tarski('#skF_8'), '#skF_9')), inference(resolution, [status(thm)], [c_64, c_5204])).
% 6.66/2.42  tff(c_5222, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_42, c_5216])).
% 6.66/2.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.66/2.42  
% 6.66/2.42  Inference rules
% 6.66/2.42  ----------------------
% 6.66/2.42  #Ref     : 0
% 6.66/2.42  #Sup     : 1198
% 6.66/2.42  #Fact    : 0
% 6.66/2.42  #Define  : 0
% 6.66/2.42  #Split   : 3
% 6.66/2.42  #Chain   : 0
% 6.66/2.42  #Close   : 0
% 6.66/2.42  
% 6.66/2.42  Ordering : KBO
% 6.66/2.42  
% 6.66/2.42  Simplification rules
% 6.66/2.42  ----------------------
% 6.66/2.42  #Subsume      : 198
% 6.66/2.42  #Demod        : 112
% 6.66/2.42  #Tautology    : 85
% 6.66/2.42  #SimpNegUnit  : 10
% 6.66/2.42  #BackRed      : 3
% 6.66/2.42  
% 6.66/2.42  #Partial instantiations: 0
% 6.66/2.42  #Strategies tried      : 1
% 6.66/2.42  
% 6.66/2.42  Timing (in seconds)
% 6.66/2.42  ----------------------
% 6.66/2.42  Preprocessing        : 0.31
% 6.66/2.43  Parsing              : 0.15
% 6.66/2.43  CNF conversion       : 0.03
% 6.66/2.43  Main loop            : 1.35
% 6.66/2.43  Inferencing          : 0.51
% 6.66/2.43  Reduction            : 0.28
% 6.66/2.43  Demodulation         : 0.17
% 6.66/2.43  BG Simplification    : 0.06
% 6.66/2.43  Subsumption          : 0.39
% 6.66/2.43  Abstraction          : 0.07
% 6.66/2.43  MUC search           : 0.00
% 6.66/2.43  Cooper               : 0.00
% 6.66/2.43  Total                : 1.69
% 6.66/2.43  Index Insertion      : 0.00
% 6.66/2.43  Index Deletion       : 0.00
% 6.66/2.43  Index Matching       : 0.00
% 6.66/2.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
