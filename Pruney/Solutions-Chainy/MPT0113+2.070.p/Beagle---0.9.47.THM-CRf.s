%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:20 EST 2020

% Result     : Theorem 7.46s
% Output     : CNFRefutation 7.46s
% Verified   : 
% Statistics : Number of formulae       :   47 (  58 expanded)
%              Number of leaves         :   23 (  30 expanded)
%              Depth                    :    6
%              Number of atoms          :   61 (  87 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_77,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_70,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(c_40,plain,
    ( ~ r1_xboole_0('#skF_4','#skF_6')
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_44,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_42,plain,(
    r1_tarski('#skF_4',k4_xboole_0('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_200,plain,(
    ! [C_64,B_65,A_66] :
      ( r2_hidden(C_64,B_65)
      | ~ r2_hidden(C_64,A_66)
      | ~ r1_tarski(A_66,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_519,plain,(
    ! [A_115,B_116,B_117] :
      ( r2_hidden('#skF_1'(A_115,B_116),B_117)
      | ~ r1_tarski(A_115,B_117)
      | r1_tarski(A_115,B_116) ) ),
    inference(resolution,[status(thm)],[c_6,c_200])).

tff(c_12,plain,(
    ! [D_11,A_6,B_7] :
      ( r2_hidden(D_11,A_6)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_6378,plain,(
    ! [A_770,B_771,A_772,B_773] :
      ( r2_hidden('#skF_1'(A_770,B_771),A_772)
      | ~ r1_tarski(A_770,k4_xboole_0(A_772,B_773))
      | r1_tarski(A_770,B_771) ) ),
    inference(resolution,[status(thm)],[c_519,c_12])).

tff(c_6398,plain,(
    ! [B_774] :
      ( r2_hidden('#skF_1'('#skF_4',B_774),'#skF_5')
      | r1_tarski('#skF_4',B_774) ) ),
    inference(resolution,[status(thm)],[c_42,c_6378])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_6407,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_6398,c_4])).

tff(c_6413,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_44,c_6407])).

tff(c_6414,plain,(
    ~ r1_xboole_0('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_38,plain,(
    ! [A_21,B_22] : r1_xboole_0(k4_xboole_0(A_21,B_22),B_22) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_6416,plain,(
    ! [B_775,A_776] :
      ( r1_xboole_0(B_775,A_776)
      | ~ r1_xboole_0(A_776,B_775) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_6419,plain,(
    ! [B_22,A_21] : r1_xboole_0(B_22,k4_xboole_0(A_21,B_22)) ),
    inference(resolution,[status(thm)],[c_38,c_6416])).

tff(c_6425,plain,(
    ! [A_779,B_780] :
      ( k2_xboole_0(A_779,B_780) = B_780
      | ~ r1_tarski(A_779,B_780) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_6433,plain,(
    k2_xboole_0('#skF_4',k4_xboole_0('#skF_5','#skF_6')) = k4_xboole_0('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_6425])).

tff(c_6531,plain,(
    ! [A_801,B_802,C_803] :
      ( r1_xboole_0(A_801,B_802)
      | ~ r1_xboole_0(A_801,k2_xboole_0(B_802,C_803)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_6681,plain,(
    ! [A_829] :
      ( r1_xboole_0(A_829,'#skF_4')
      | ~ r1_xboole_0(A_829,k4_xboole_0('#skF_5','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6433,c_6531])).

tff(c_6700,plain,(
    r1_xboole_0('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_6419,c_6681])).

tff(c_26,plain,(
    ! [B_13,A_12] :
      ( r1_xboole_0(B_13,A_12)
      | ~ r1_xboole_0(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_6704,plain,(
    r1_xboole_0('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_6700,c_26])).

tff(c_6708,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6414,c_6704])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:54:35 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.46/2.60  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.46/2.61  
% 7.46/2.61  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.46/2.61  %$ r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 7.46/2.61  
% 7.46/2.61  %Foreground sorts:
% 7.46/2.61  
% 7.46/2.61  
% 7.46/2.61  %Background operators:
% 7.46/2.61  
% 7.46/2.61  
% 7.46/2.61  %Foreground operators:
% 7.46/2.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.46/2.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.46/2.61  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.46/2.61  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.46/2.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.46/2.61  tff('#skF_5', type, '#skF_5': $i).
% 7.46/2.61  tff('#skF_6', type, '#skF_6': $i).
% 7.46/2.61  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.46/2.61  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.46/2.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.46/2.61  tff('#skF_4', type, '#skF_4': $i).
% 7.46/2.61  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 7.46/2.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.46/2.61  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.46/2.61  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.46/2.61  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.46/2.61  
% 7.46/2.62  tff(f_77, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 7.46/2.62  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 7.46/2.62  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 7.46/2.62  tff(f_70, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 7.46/2.62  tff(f_46, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 7.46/2.62  tff(f_52, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 7.46/2.62  tff(f_68, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 7.46/2.62  tff(c_40, plain, (~r1_xboole_0('#skF_4', '#skF_6') | ~r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_77])).
% 7.46/2.62  tff(c_44, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_40])).
% 7.46/2.62  tff(c_42, plain, (r1_tarski('#skF_4', k4_xboole_0('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 7.46/2.62  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.46/2.62  tff(c_200, plain, (![C_64, B_65, A_66]: (r2_hidden(C_64, B_65) | ~r2_hidden(C_64, A_66) | ~r1_tarski(A_66, B_65))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.46/2.62  tff(c_519, plain, (![A_115, B_116, B_117]: (r2_hidden('#skF_1'(A_115, B_116), B_117) | ~r1_tarski(A_115, B_117) | r1_tarski(A_115, B_116))), inference(resolution, [status(thm)], [c_6, c_200])).
% 7.46/2.62  tff(c_12, plain, (![D_11, A_6, B_7]: (r2_hidden(D_11, A_6) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.46/2.62  tff(c_6378, plain, (![A_770, B_771, A_772, B_773]: (r2_hidden('#skF_1'(A_770, B_771), A_772) | ~r1_tarski(A_770, k4_xboole_0(A_772, B_773)) | r1_tarski(A_770, B_771))), inference(resolution, [status(thm)], [c_519, c_12])).
% 7.46/2.62  tff(c_6398, plain, (![B_774]: (r2_hidden('#skF_1'('#skF_4', B_774), '#skF_5') | r1_tarski('#skF_4', B_774))), inference(resolution, [status(thm)], [c_42, c_6378])).
% 7.46/2.62  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.46/2.62  tff(c_6407, plain, (r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_6398, c_4])).
% 7.46/2.62  tff(c_6413, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_44, c_6407])).
% 7.46/2.62  tff(c_6414, plain, (~r1_xboole_0('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_40])).
% 7.46/2.62  tff(c_38, plain, (![A_21, B_22]: (r1_xboole_0(k4_xboole_0(A_21, B_22), B_22))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.46/2.62  tff(c_6416, plain, (![B_775, A_776]: (r1_xboole_0(B_775, A_776) | ~r1_xboole_0(A_776, B_775))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.46/2.62  tff(c_6419, plain, (![B_22, A_21]: (r1_xboole_0(B_22, k4_xboole_0(A_21, B_22)))), inference(resolution, [status(thm)], [c_38, c_6416])).
% 7.46/2.62  tff(c_6425, plain, (![A_779, B_780]: (k2_xboole_0(A_779, B_780)=B_780 | ~r1_tarski(A_779, B_780))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.46/2.62  tff(c_6433, plain, (k2_xboole_0('#skF_4', k4_xboole_0('#skF_5', '#skF_6'))=k4_xboole_0('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_42, c_6425])).
% 7.46/2.62  tff(c_6531, plain, (![A_801, B_802, C_803]: (r1_xboole_0(A_801, B_802) | ~r1_xboole_0(A_801, k2_xboole_0(B_802, C_803)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.46/2.62  tff(c_6681, plain, (![A_829]: (r1_xboole_0(A_829, '#skF_4') | ~r1_xboole_0(A_829, k4_xboole_0('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_6433, c_6531])).
% 7.46/2.62  tff(c_6700, plain, (r1_xboole_0('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_6419, c_6681])).
% 7.46/2.62  tff(c_26, plain, (![B_13, A_12]: (r1_xboole_0(B_13, A_12) | ~r1_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.46/2.62  tff(c_6704, plain, (r1_xboole_0('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_6700, c_26])).
% 7.46/2.62  tff(c_6708, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6414, c_6704])).
% 7.46/2.62  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.46/2.62  
% 7.46/2.62  Inference rules
% 7.46/2.62  ----------------------
% 7.46/2.62  #Ref     : 0
% 7.46/2.62  #Sup     : 1541
% 7.46/2.62  #Fact    : 0
% 7.46/2.62  #Define  : 0
% 7.46/2.62  #Split   : 4
% 7.46/2.62  #Chain   : 0
% 7.46/2.62  #Close   : 0
% 7.46/2.62  
% 7.46/2.62  Ordering : KBO
% 7.46/2.62  
% 7.46/2.62  Simplification rules
% 7.46/2.62  ----------------------
% 7.46/2.62  #Subsume      : 117
% 7.46/2.62  #Demod        : 740
% 7.46/2.62  #Tautology    : 781
% 7.46/2.62  #SimpNegUnit  : 2
% 7.46/2.62  #BackRed      : 0
% 7.46/2.62  
% 7.46/2.62  #Partial instantiations: 0
% 7.46/2.62  #Strategies tried      : 1
% 7.46/2.62  
% 7.46/2.62  Timing (in seconds)
% 7.46/2.62  ----------------------
% 7.46/2.62  Preprocessing        : 0.29
% 7.46/2.62  Parsing              : 0.16
% 7.46/2.62  CNF conversion       : 0.02
% 7.46/2.62  Main loop            : 1.57
% 7.46/2.62  Inferencing          : 0.46
% 7.46/2.62  Reduction            : 0.66
% 7.46/2.62  Demodulation         : 0.54
% 7.46/2.62  BG Simplification    : 0.03
% 7.46/2.62  Subsumption          : 0.32
% 7.46/2.62  Abstraction          : 0.05
% 7.46/2.62  MUC search           : 0.00
% 7.46/2.62  Cooper               : 0.00
% 7.46/2.62  Total                : 1.89
% 7.46/2.62  Index Insertion      : 0.00
% 7.46/2.62  Index Deletion       : 0.00
% 7.46/2.62  Index Matching       : 0.00
% 7.46/2.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
