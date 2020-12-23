%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:22 EST 2020

% Result     : Theorem 3.29s
% Output     : CNFRefutation 3.29s
% Verified   : 
% Statistics : Number of formulae       :   47 (  61 expanded)
%              Number of leaves         :   19 (  30 expanded)
%              Depth                    :   11
%              Number of atoms          :   70 ( 122 expanded)
%              Number of equality atoms :   12 (  20 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_xboole_0(B,C) )
       => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_61,axiom,(
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

tff(f_63,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(c_34,plain,(
    ~ r1_xboole_0('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_26,plain,(
    ! [A_9,B_10] :
      ( r2_hidden('#skF_3'(A_9,B_10),A_9)
      | r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_24,plain,(
    ! [A_9,B_10] :
      ( r2_hidden('#skF_3'(A_9,B_10),B_10)
      | r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_38,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_52,plain,(
    ! [A_20,B_21] :
      ( k4_xboole_0(A_20,B_21) = k1_xboole_0
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_56,plain,(
    k4_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_52])).

tff(c_176,plain,(
    ! [D_46,A_47,B_48] :
      ( r2_hidden(D_46,k4_xboole_0(A_47,B_48))
      | r2_hidden(D_46,B_48)
      | ~ r2_hidden(D_46,A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_185,plain,(
    ! [D_46] :
      ( r2_hidden(D_46,k1_xboole_0)
      | r2_hidden(D_46,'#skF_5')
      | ~ r2_hidden(D_46,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_176])).

tff(c_18,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),A_1)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_513,plain,(
    ! [A_82,B_83,C_84] :
      ( ~ r2_hidden('#skF_1'(A_82,B_83,C_84),B_83)
      | r2_hidden('#skF_2'(A_82,B_83,C_84),C_84)
      | k4_xboole_0(A_82,B_83) = C_84 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_523,plain,(
    ! [A_1,C_3] :
      ( r2_hidden('#skF_2'(A_1,A_1,C_3),C_3)
      | k4_xboole_0(A_1,A_1) = C_3 ) ),
    inference(resolution,[status(thm)],[c_18,c_513])).

tff(c_691,plain,(
    ! [A_103,C_104] :
      ( r2_hidden('#skF_2'(A_103,A_103,C_104),C_104)
      | k4_xboole_0(A_103,A_103) = C_104 ) ),
    inference(resolution,[status(thm)],[c_18,c_513])).

tff(c_32,plain,(
    ! [A_16] : k4_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_70,plain,(
    ! [D_24,B_25,A_26] :
      ( ~ r2_hidden(D_24,B_25)
      | ~ r2_hidden(D_24,k4_xboole_0(A_26,B_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_76,plain,(
    ! [D_24,A_16] :
      ( ~ r2_hidden(D_24,k1_xboole_0)
      | ~ r2_hidden(D_24,A_16) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_70])).

tff(c_865,plain,(
    ! [A_112,A_113] :
      ( ~ r2_hidden('#skF_2'(A_112,A_112,k1_xboole_0),A_113)
      | k4_xboole_0(A_112,A_112) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_691,c_76])).

tff(c_892,plain,(
    ! [A_114] : k4_xboole_0(A_114,A_114) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_523,c_865])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,A_1)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_985,plain,(
    ! [D_115,A_116] :
      ( r2_hidden(D_115,A_116)
      | ~ r2_hidden(D_115,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_892,c_6])).

tff(c_1010,plain,(
    ! [D_46,A_116] :
      ( r2_hidden(D_46,A_116)
      | r2_hidden(D_46,'#skF_5')
      | ~ r2_hidden(D_46,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_185,c_985])).

tff(c_1230,plain,(
    ! [D_127] :
      ( ~ r2_hidden(D_127,'#skF_4')
      | r2_hidden(D_127,'#skF_5') ) ),
    inference(factorization,[status(thm),theory(equality)],[c_1010])).

tff(c_36,plain,(
    r1_xboole_0('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_152,plain,(
    ! [A_42,B_43,C_44] :
      ( ~ r1_xboole_0(A_42,B_43)
      | ~ r2_hidden(C_44,B_43)
      | ~ r2_hidden(C_44,A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_164,plain,(
    ! [C_44] :
      ( ~ r2_hidden(C_44,'#skF_6')
      | ~ r2_hidden(C_44,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_36,c_152])).

tff(c_1249,plain,(
    ! [D_128] :
      ( ~ r2_hidden(D_128,'#skF_6')
      | ~ r2_hidden(D_128,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1230,c_164])).

tff(c_1310,plain,(
    ! [A_133] :
      ( ~ r2_hidden('#skF_3'(A_133,'#skF_6'),'#skF_4')
      | r1_xboole_0(A_133,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_24,c_1249])).

tff(c_1314,plain,(
    r1_xboole_0('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_26,c_1310])).

tff(c_1318,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_34,c_1314])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:50:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.29/1.53  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.29/1.53  
% 3.29/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.29/1.53  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 3.29/1.53  
% 3.29/1.53  %Foreground sorts:
% 3.29/1.53  
% 3.29/1.53  
% 3.29/1.53  %Background operators:
% 3.29/1.53  
% 3.29/1.53  
% 3.29/1.53  %Foreground operators:
% 3.29/1.53  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.29/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.29/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.29/1.53  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.29/1.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.29/1.53  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.29/1.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.29/1.53  tff('#skF_5', type, '#skF_5': $i).
% 3.29/1.53  tff('#skF_6', type, '#skF_6': $i).
% 3.29/1.53  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.29/1.53  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.29/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.29/1.53  tff('#skF_4', type, '#skF_4': $i).
% 3.29/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.29/1.53  
% 3.29/1.55  tff(f_70, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 3.29/1.55  tff(f_57, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.29/1.55  tff(f_61, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.29/1.55  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.29/1.55  tff(f_63, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.29/1.55  tff(c_34, plain, (~r1_xboole_0('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.29/1.55  tff(c_26, plain, (![A_9, B_10]: (r2_hidden('#skF_3'(A_9, B_10), A_9) | r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.29/1.55  tff(c_24, plain, (![A_9, B_10]: (r2_hidden('#skF_3'(A_9, B_10), B_10) | r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.29/1.55  tff(c_38, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.29/1.55  tff(c_52, plain, (![A_20, B_21]: (k4_xboole_0(A_20, B_21)=k1_xboole_0 | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.29/1.55  tff(c_56, plain, (k4_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_38, c_52])).
% 3.29/1.55  tff(c_176, plain, (![D_46, A_47, B_48]: (r2_hidden(D_46, k4_xboole_0(A_47, B_48)) | r2_hidden(D_46, B_48) | ~r2_hidden(D_46, A_47))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.29/1.55  tff(c_185, plain, (![D_46]: (r2_hidden(D_46, k1_xboole_0) | r2_hidden(D_46, '#skF_5') | ~r2_hidden(D_46, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_56, c_176])).
% 3.29/1.55  tff(c_18, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), A_1) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.29/1.55  tff(c_513, plain, (![A_82, B_83, C_84]: (~r2_hidden('#skF_1'(A_82, B_83, C_84), B_83) | r2_hidden('#skF_2'(A_82, B_83, C_84), C_84) | k4_xboole_0(A_82, B_83)=C_84)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.29/1.55  tff(c_523, plain, (![A_1, C_3]: (r2_hidden('#skF_2'(A_1, A_1, C_3), C_3) | k4_xboole_0(A_1, A_1)=C_3)), inference(resolution, [status(thm)], [c_18, c_513])).
% 3.29/1.55  tff(c_691, plain, (![A_103, C_104]: (r2_hidden('#skF_2'(A_103, A_103, C_104), C_104) | k4_xboole_0(A_103, A_103)=C_104)), inference(resolution, [status(thm)], [c_18, c_513])).
% 3.29/1.55  tff(c_32, plain, (![A_16]: (k4_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.29/1.55  tff(c_70, plain, (![D_24, B_25, A_26]: (~r2_hidden(D_24, B_25) | ~r2_hidden(D_24, k4_xboole_0(A_26, B_25)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.29/1.55  tff(c_76, plain, (![D_24, A_16]: (~r2_hidden(D_24, k1_xboole_0) | ~r2_hidden(D_24, A_16))), inference(superposition, [status(thm), theory('equality')], [c_32, c_70])).
% 3.29/1.55  tff(c_865, plain, (![A_112, A_113]: (~r2_hidden('#skF_2'(A_112, A_112, k1_xboole_0), A_113) | k4_xboole_0(A_112, A_112)=k1_xboole_0)), inference(resolution, [status(thm)], [c_691, c_76])).
% 3.29/1.55  tff(c_892, plain, (![A_114]: (k4_xboole_0(A_114, A_114)=k1_xboole_0)), inference(resolution, [status(thm)], [c_523, c_865])).
% 3.29/1.55  tff(c_6, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, A_1) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.29/1.55  tff(c_985, plain, (![D_115, A_116]: (r2_hidden(D_115, A_116) | ~r2_hidden(D_115, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_892, c_6])).
% 3.29/1.55  tff(c_1010, plain, (![D_46, A_116]: (r2_hidden(D_46, A_116) | r2_hidden(D_46, '#skF_5') | ~r2_hidden(D_46, '#skF_4'))), inference(resolution, [status(thm)], [c_185, c_985])).
% 3.29/1.55  tff(c_1230, plain, (![D_127]: (~r2_hidden(D_127, '#skF_4') | r2_hidden(D_127, '#skF_5'))), inference(factorization, [status(thm), theory('equality')], [c_1010])).
% 3.29/1.55  tff(c_36, plain, (r1_xboole_0('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.29/1.55  tff(c_152, plain, (![A_42, B_43, C_44]: (~r1_xboole_0(A_42, B_43) | ~r2_hidden(C_44, B_43) | ~r2_hidden(C_44, A_42))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.29/1.55  tff(c_164, plain, (![C_44]: (~r2_hidden(C_44, '#skF_6') | ~r2_hidden(C_44, '#skF_5'))), inference(resolution, [status(thm)], [c_36, c_152])).
% 3.29/1.55  tff(c_1249, plain, (![D_128]: (~r2_hidden(D_128, '#skF_6') | ~r2_hidden(D_128, '#skF_4'))), inference(resolution, [status(thm)], [c_1230, c_164])).
% 3.29/1.55  tff(c_1310, plain, (![A_133]: (~r2_hidden('#skF_3'(A_133, '#skF_6'), '#skF_4') | r1_xboole_0(A_133, '#skF_6'))), inference(resolution, [status(thm)], [c_24, c_1249])).
% 3.29/1.55  tff(c_1314, plain, (r1_xboole_0('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_26, c_1310])).
% 3.29/1.55  tff(c_1318, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_34, c_1314])).
% 3.29/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.29/1.55  
% 3.29/1.55  Inference rules
% 3.29/1.55  ----------------------
% 3.29/1.55  #Ref     : 0
% 3.29/1.55  #Sup     : 270
% 3.29/1.55  #Fact    : 2
% 3.29/1.55  #Define  : 0
% 3.29/1.55  #Split   : 2
% 3.29/1.55  #Chain   : 0
% 3.29/1.55  #Close   : 0
% 3.29/1.55  
% 3.29/1.55  Ordering : KBO
% 3.29/1.55  
% 3.29/1.55  Simplification rules
% 3.29/1.55  ----------------------
% 3.29/1.55  #Subsume      : 49
% 3.29/1.55  #Demod        : 96
% 3.29/1.55  #Tautology    : 96
% 3.29/1.55  #SimpNegUnit  : 1
% 3.29/1.55  #BackRed      : 5
% 3.29/1.55  
% 3.29/1.55  #Partial instantiations: 0
% 3.29/1.55  #Strategies tried      : 1
% 3.29/1.55  
% 3.29/1.55  Timing (in seconds)
% 3.29/1.55  ----------------------
% 3.29/1.55  Preprocessing        : 0.30
% 3.29/1.55  Parsing              : 0.17
% 3.29/1.55  CNF conversion       : 0.02
% 3.29/1.55  Main loop            : 0.45
% 3.29/1.55  Inferencing          : 0.18
% 3.29/1.55  Reduction            : 0.12
% 3.29/1.55  Demodulation         : 0.08
% 3.29/1.55  BG Simplification    : 0.02
% 3.29/1.55  Subsumption          : 0.10
% 3.29/1.55  Abstraction          : 0.02
% 3.29/1.55  MUC search           : 0.00
% 3.29/1.55  Cooper               : 0.00
% 3.29/1.55  Total                : 0.78
% 3.29/1.55  Index Insertion      : 0.00
% 3.29/1.55  Index Deletion       : 0.00
% 3.29/1.55  Index Matching       : 0.00
% 3.29/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
