%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:32 EST 2020

% Result     : Theorem 2.69s
% Output     : CNFRefutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :   45 (  57 expanded)
%              Number of leaves         :   19 (  28 expanded)
%              Depth                    :   10
%              Number of atoms          :   64 ( 102 expanded)
%              Number of equality atoms :   12 (  20 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_xboole_0 > #nlpp > k3_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_57,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,B)
       => r1_tarski(k3_tarski(A),k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_tarski(C,B) )
     => r1_tarski(k3_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_41,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(c_32,plain,(
    ~ r1_tarski(k3_tarski('#skF_4'),k3_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_30,plain,(
    ! [A_12,B_13] :
      ( r2_hidden('#skF_3'(A_12,B_13),A_12)
      | r1_tarski(k3_tarski(A_12),B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_34,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_54,plain,(
    ! [A_20,B_21] :
      ( k4_xboole_0(A_20,B_21) = k1_xboole_0
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_66,plain,(
    k4_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_54])).

tff(c_204,plain,(
    ! [D_45,A_46,B_47] :
      ( r2_hidden(D_45,k4_xboole_0(A_46,B_47))
      | r2_hidden(D_45,B_47)
      | ~ r2_hidden(D_45,A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_216,plain,(
    ! [D_45] :
      ( r2_hidden(D_45,k1_xboole_0)
      | r2_hidden(D_45,'#skF_5')
      | ~ r2_hidden(D_45,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_204])).

tff(c_18,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),A_1)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_479,plain,(
    ! [A_67,B_68,C_69] :
      ( ~ r2_hidden('#skF_1'(A_67,B_68,C_69),B_68)
      | r2_hidden('#skF_2'(A_67,B_68,C_69),C_69)
      | k4_xboole_0(A_67,B_68) = C_69 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_496,plain,(
    ! [A_1,C_3] :
      ( r2_hidden('#skF_2'(A_1,A_1,C_3),C_3)
      | k4_xboole_0(A_1,A_1) = C_3 ) ),
    inference(resolution,[status(thm)],[c_18,c_479])).

tff(c_531,plain,(
    ! [A_72,C_73] :
      ( r2_hidden('#skF_2'(A_72,A_72,C_73),C_73)
      | k4_xboole_0(A_72,A_72) = C_73 ) ),
    inference(resolution,[status(thm)],[c_18,c_479])).

tff(c_24,plain,(
    ! [A_9] : k4_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_71,plain,(
    ! [D_22,B_23,A_24] :
      ( ~ r2_hidden(D_22,B_23)
      | ~ r2_hidden(D_22,k4_xboole_0(A_24,B_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_77,plain,(
    ! [D_22,A_9] :
      ( ~ r2_hidden(D_22,k1_xboole_0)
      | ~ r2_hidden(D_22,A_9) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_71])).

tff(c_623,plain,(
    ! [A_75,A_76] :
      ( ~ r2_hidden('#skF_2'(A_75,A_75,k1_xboole_0),A_76)
      | k4_xboole_0(A_75,A_75) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_531,c_77])).

tff(c_680,plain,(
    ! [A_80] : k4_xboole_0(A_80,A_80) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_496,c_623])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,A_1)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_724,plain,(
    ! [D_81,A_82] :
      ( r2_hidden(D_81,A_82)
      | ~ r2_hidden(D_81,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_680,c_6])).

tff(c_736,plain,(
    ! [D_45,A_82] :
      ( r2_hidden(D_45,A_82)
      | r2_hidden(D_45,'#skF_5')
      | ~ r2_hidden(D_45,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_216,c_724])).

tff(c_793,plain,(
    ! [D_45] :
      ( ~ r2_hidden(D_45,'#skF_4')
      | r2_hidden(D_45,'#skF_5') ) ),
    inference(factorization,[status(thm),theory(equality)],[c_736])).

tff(c_26,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,k3_tarski(B_11))
      | ~ r2_hidden(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_106,plain,(
    ! [A_33,B_34] :
      ( ~ r1_tarski('#skF_3'(A_33,B_34),B_34)
      | r1_tarski(k3_tarski(A_33),B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1023,plain,(
    ! [A_95,B_96] :
      ( r1_tarski(k3_tarski(A_95),k3_tarski(B_96))
      | ~ r2_hidden('#skF_3'(A_95,k3_tarski(B_96)),B_96) ) ),
    inference(resolution,[status(thm)],[c_26,c_106])).

tff(c_1075,plain,(
    ! [A_101] :
      ( r1_tarski(k3_tarski(A_101),k3_tarski('#skF_5'))
      | ~ r2_hidden('#skF_3'(A_101,k3_tarski('#skF_5')),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_793,c_1023])).

tff(c_1082,plain,(
    r1_tarski(k3_tarski('#skF_4'),k3_tarski('#skF_5')) ),
    inference(resolution,[status(thm)],[c_30,c_1075])).

tff(c_1086,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_32,c_1082])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:19:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.69/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.39  
% 2.69/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.40  %$ r2_hidden > r1_tarski > k4_xboole_0 > #nlpp > k3_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 2.69/1.40  
% 2.69/1.40  %Foreground sorts:
% 2.69/1.40  
% 2.69/1.40  
% 2.69/1.40  %Background operators:
% 2.69/1.40  
% 2.69/1.40  
% 2.69/1.40  %Foreground operators:
% 2.69/1.40  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.69/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.69/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.69/1.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.69/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.69/1.40  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.69/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.69/1.40  tff('#skF_5', type, '#skF_5': $i).
% 2.69/1.40  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.69/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.69/1.40  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.69/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.69/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.69/1.40  
% 2.69/1.41  tff(f_57, negated_conjecture, ~(![A, B]: (r1_tarski(A, B) => r1_tarski(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_zfmisc_1)).
% 2.69/1.41  tff(f_52, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_tarski(C, B))) => r1_tarski(k3_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_zfmisc_1)).
% 2.69/1.41  tff(f_39, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.69/1.41  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.69/1.41  tff(f_41, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.69/1.41  tff(f_45, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 2.69/1.41  tff(c_32, plain, (~r1_tarski(k3_tarski('#skF_4'), k3_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.69/1.41  tff(c_30, plain, (![A_12, B_13]: (r2_hidden('#skF_3'(A_12, B_13), A_12) | r1_tarski(k3_tarski(A_12), B_13))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.69/1.41  tff(c_34, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.69/1.41  tff(c_54, plain, (![A_20, B_21]: (k4_xboole_0(A_20, B_21)=k1_xboole_0 | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.69/1.41  tff(c_66, plain, (k4_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_34, c_54])).
% 2.69/1.41  tff(c_204, plain, (![D_45, A_46, B_47]: (r2_hidden(D_45, k4_xboole_0(A_46, B_47)) | r2_hidden(D_45, B_47) | ~r2_hidden(D_45, A_46))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.69/1.41  tff(c_216, plain, (![D_45]: (r2_hidden(D_45, k1_xboole_0) | r2_hidden(D_45, '#skF_5') | ~r2_hidden(D_45, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_66, c_204])).
% 2.69/1.41  tff(c_18, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), A_1) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.69/1.41  tff(c_479, plain, (![A_67, B_68, C_69]: (~r2_hidden('#skF_1'(A_67, B_68, C_69), B_68) | r2_hidden('#skF_2'(A_67, B_68, C_69), C_69) | k4_xboole_0(A_67, B_68)=C_69)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.69/1.41  tff(c_496, plain, (![A_1, C_3]: (r2_hidden('#skF_2'(A_1, A_1, C_3), C_3) | k4_xboole_0(A_1, A_1)=C_3)), inference(resolution, [status(thm)], [c_18, c_479])).
% 2.69/1.41  tff(c_531, plain, (![A_72, C_73]: (r2_hidden('#skF_2'(A_72, A_72, C_73), C_73) | k4_xboole_0(A_72, A_72)=C_73)), inference(resolution, [status(thm)], [c_18, c_479])).
% 2.69/1.41  tff(c_24, plain, (![A_9]: (k4_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.69/1.41  tff(c_71, plain, (![D_22, B_23, A_24]: (~r2_hidden(D_22, B_23) | ~r2_hidden(D_22, k4_xboole_0(A_24, B_23)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.69/1.41  tff(c_77, plain, (![D_22, A_9]: (~r2_hidden(D_22, k1_xboole_0) | ~r2_hidden(D_22, A_9))), inference(superposition, [status(thm), theory('equality')], [c_24, c_71])).
% 2.69/1.41  tff(c_623, plain, (![A_75, A_76]: (~r2_hidden('#skF_2'(A_75, A_75, k1_xboole_0), A_76) | k4_xboole_0(A_75, A_75)=k1_xboole_0)), inference(resolution, [status(thm)], [c_531, c_77])).
% 2.69/1.41  tff(c_680, plain, (![A_80]: (k4_xboole_0(A_80, A_80)=k1_xboole_0)), inference(resolution, [status(thm)], [c_496, c_623])).
% 2.69/1.41  tff(c_6, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, A_1) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.69/1.41  tff(c_724, plain, (![D_81, A_82]: (r2_hidden(D_81, A_82) | ~r2_hidden(D_81, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_680, c_6])).
% 2.69/1.41  tff(c_736, plain, (![D_45, A_82]: (r2_hidden(D_45, A_82) | r2_hidden(D_45, '#skF_5') | ~r2_hidden(D_45, '#skF_4'))), inference(resolution, [status(thm)], [c_216, c_724])).
% 2.69/1.41  tff(c_793, plain, (![D_45]: (~r2_hidden(D_45, '#skF_4') | r2_hidden(D_45, '#skF_5'))), inference(factorization, [status(thm), theory('equality')], [c_736])).
% 2.69/1.41  tff(c_26, plain, (![A_10, B_11]: (r1_tarski(A_10, k3_tarski(B_11)) | ~r2_hidden(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.69/1.41  tff(c_106, plain, (![A_33, B_34]: (~r1_tarski('#skF_3'(A_33, B_34), B_34) | r1_tarski(k3_tarski(A_33), B_34))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.69/1.41  tff(c_1023, plain, (![A_95, B_96]: (r1_tarski(k3_tarski(A_95), k3_tarski(B_96)) | ~r2_hidden('#skF_3'(A_95, k3_tarski(B_96)), B_96))), inference(resolution, [status(thm)], [c_26, c_106])).
% 2.69/1.41  tff(c_1075, plain, (![A_101]: (r1_tarski(k3_tarski(A_101), k3_tarski('#skF_5')) | ~r2_hidden('#skF_3'(A_101, k3_tarski('#skF_5')), '#skF_4'))), inference(resolution, [status(thm)], [c_793, c_1023])).
% 2.69/1.41  tff(c_1082, plain, (r1_tarski(k3_tarski('#skF_4'), k3_tarski('#skF_5'))), inference(resolution, [status(thm)], [c_30, c_1075])).
% 2.69/1.41  tff(c_1086, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_32, c_1082])).
% 2.69/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.41  
% 2.69/1.41  Inference rules
% 2.69/1.41  ----------------------
% 2.69/1.41  #Ref     : 0
% 2.69/1.41  #Sup     : 230
% 2.69/1.41  #Fact    : 2
% 2.69/1.41  #Define  : 0
% 2.69/1.41  #Split   : 2
% 2.69/1.41  #Chain   : 0
% 2.69/1.41  #Close   : 0
% 2.69/1.41  
% 2.69/1.41  Ordering : KBO
% 2.69/1.41  
% 2.69/1.41  Simplification rules
% 2.69/1.41  ----------------------
% 2.69/1.41  #Subsume      : 59
% 2.69/1.41  #Demod        : 52
% 2.69/1.41  #Tautology    : 76
% 2.69/1.41  #SimpNegUnit  : 1
% 2.69/1.41  #BackRed      : 3
% 2.69/1.41  
% 2.69/1.41  #Partial instantiations: 0
% 2.69/1.41  #Strategies tried      : 1
% 2.69/1.41  
% 2.69/1.41  Timing (in seconds)
% 2.69/1.41  ----------------------
% 2.69/1.41  Preprocessing        : 0.26
% 2.69/1.41  Parsing              : 0.14
% 2.69/1.41  CNF conversion       : 0.02
% 2.69/1.41  Main loop            : 0.38
% 2.69/1.41  Inferencing          : 0.15
% 2.69/1.41  Reduction            : 0.09
% 2.69/1.41  Demodulation         : 0.06
% 2.69/1.41  BG Simplification    : 0.02
% 2.69/1.41  Subsumption          : 0.09
% 2.69/1.41  Abstraction          : 0.02
% 2.69/1.41  MUC search           : 0.00
% 2.69/1.41  Cooper               : 0.00
% 2.69/1.41  Total                : 0.67
% 2.69/1.41  Index Insertion      : 0.00
% 2.69/1.41  Index Deletion       : 0.00
% 2.69/1.41  Index Matching       : 0.00
% 2.69/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
