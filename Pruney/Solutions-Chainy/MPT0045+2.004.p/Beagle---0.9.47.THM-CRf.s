%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:45 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 136 expanded)
%              Number of leaves         :   19 (  55 expanded)
%              Depth                    :   12
%              Number of atoms          :   63 ( 270 expanded)
%              Number of equality atoms :   13 (  58 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_xboole_0 > #nlpp > k1_xboole_0 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_58,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,k4_xboole_0(B,A))
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

tff(f_53,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_373,plain,(
    ! [A_63,B_64] :
      ( r2_hidden('#skF_4'(A_63,B_64),B_64)
      | r2_hidden('#skF_5'(A_63,B_64),A_63)
      | B_64 = A_63 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_40,plain,(
    r1_tarski('#skF_6',k4_xboole_0('#skF_7','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_42,plain,(
    ! [A_19,B_20] :
      ( k4_xboole_0(A_19,B_20) = k1_xboole_0
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_50,plain,(
    k4_xboole_0('#skF_6',k4_xboole_0('#skF_7','#skF_6')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_42])).

tff(c_184,plain,(
    ! [D_47,A_48,B_49] :
      ( r2_hidden(D_47,k4_xboole_0(A_48,B_49))
      | r2_hidden(D_47,B_49)
      | ~ r2_hidden(D_47,A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_268,plain,(
    ! [D_57] :
      ( r2_hidden(D_57,k1_xboole_0)
      | r2_hidden(D_57,k4_xboole_0('#skF_7','#skF_6'))
      | ~ r2_hidden(D_57,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_184])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( ~ r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_285,plain,(
    ! [D_57] :
      ( r2_hidden(D_57,k1_xboole_0)
      | ~ r2_hidden(D_57,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_268,c_10])).

tff(c_288,plain,(
    ! [D_58] :
      ( r2_hidden(D_58,k1_xboole_0)
      | ~ r2_hidden(D_58,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_268,c_10])).

tff(c_61,plain,(
    ! [A_27,B_28] :
      ( r2_hidden('#skF_1'(A_27,B_28),A_27)
      | r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_83,plain,(
    ! [A_30] : r1_tarski(A_30,A_30) ),
    inference(resolution,[status(thm)],[c_61,c_4])).

tff(c_36,plain,(
    ! [A_15,B_16] :
      ( k4_xboole_0(A_15,B_16) = k1_xboole_0
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_87,plain,(
    ! [A_30] : k4_xboole_0(A_30,A_30) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_83,c_36])).

tff(c_114,plain,(
    ! [D_34,B_35,A_36] :
      ( ~ r2_hidden(D_34,B_35)
      | ~ r2_hidden(D_34,k4_xboole_0(A_36,B_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_120,plain,(
    ! [D_34,A_30] :
      ( ~ r2_hidden(D_34,A_30)
      | ~ r2_hidden(D_34,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_114])).

tff(c_309,plain,(
    ! [D_59] :
      ( ~ r2_hidden(D_59,k1_xboole_0)
      | ~ r2_hidden(D_59,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_288,c_120])).

tff(c_321,plain,(
    ! [D_57] : ~ r2_hidden(D_57,'#skF_6') ),
    inference(resolution,[status(thm)],[c_285,c_309])).

tff(c_462,plain,(
    ! [B_68] :
      ( r2_hidden('#skF_4'('#skF_6',B_68),B_68)
      | B_68 = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_373,c_321])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_325,plain,(
    ! [D_60] : ~ r2_hidden(D_60,'#skF_6') ),
    inference(resolution,[status(thm)],[c_285,c_309])).

tff(c_337,plain,(
    ! [B_61] : r1_tarski('#skF_6',B_61) ),
    inference(resolution,[status(thm)],[c_6,c_325])).

tff(c_348,plain,(
    ! [B_62] : k4_xboole_0('#skF_6',B_62) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_337,c_36])).

tff(c_12,plain,(
    ! [D_11,A_6,B_7] :
      ( r2_hidden(D_11,A_6)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_362,plain,(
    ! [D_11] :
      ( r2_hidden(D_11,'#skF_6')
      | ~ r2_hidden(D_11,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_348,c_12])).

tff(c_370,plain,(
    ! [D_11] : ~ r2_hidden(D_11,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_321,c_362])).

tff(c_466,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_462,c_370])).

tff(c_484,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_466])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:22:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.28  
% 2.23/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.28  %$ r2_hidden > r1_tarski > k4_xboole_0 > #nlpp > k1_xboole_0 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 2.23/1.28  
% 2.23/1.28  %Foreground sorts:
% 2.23/1.28  
% 2.23/1.28  
% 2.23/1.28  %Background operators:
% 2.23/1.28  
% 2.23/1.28  
% 2.23/1.28  %Foreground operators:
% 2.23/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.23/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.23/1.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.23/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.23/1.28  tff('#skF_7', type, '#skF_7': $i).
% 2.23/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.23/1.28  tff('#skF_6', type, '#skF_6': $i).
% 2.23/1.28  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.23/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.23/1.28  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.23/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.23/1.28  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.23/1.28  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.23/1.28  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.23/1.28  
% 2.23/1.30  tff(f_58, negated_conjecture, ~(![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_xboole_1)).
% 2.23/1.30  tff(f_49, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 2.23/1.30  tff(f_53, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.23/1.30  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.23/1.30  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.23/1.30  tff(c_38, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.23/1.30  tff(c_373, plain, (![A_63, B_64]: (r2_hidden('#skF_4'(A_63, B_64), B_64) | r2_hidden('#skF_5'(A_63, B_64), A_63) | B_64=A_63)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.23/1.30  tff(c_40, plain, (r1_tarski('#skF_6', k4_xboole_0('#skF_7', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.23/1.30  tff(c_42, plain, (![A_19, B_20]: (k4_xboole_0(A_19, B_20)=k1_xboole_0 | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.23/1.30  tff(c_50, plain, (k4_xboole_0('#skF_6', k4_xboole_0('#skF_7', '#skF_6'))=k1_xboole_0), inference(resolution, [status(thm)], [c_40, c_42])).
% 2.23/1.30  tff(c_184, plain, (![D_47, A_48, B_49]: (r2_hidden(D_47, k4_xboole_0(A_48, B_49)) | r2_hidden(D_47, B_49) | ~r2_hidden(D_47, A_48))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.23/1.30  tff(c_268, plain, (![D_57]: (r2_hidden(D_57, k1_xboole_0) | r2_hidden(D_57, k4_xboole_0('#skF_7', '#skF_6')) | ~r2_hidden(D_57, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_50, c_184])).
% 2.23/1.30  tff(c_10, plain, (![D_11, B_7, A_6]: (~r2_hidden(D_11, B_7) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.23/1.30  tff(c_285, plain, (![D_57]: (r2_hidden(D_57, k1_xboole_0) | ~r2_hidden(D_57, '#skF_6'))), inference(resolution, [status(thm)], [c_268, c_10])).
% 2.23/1.30  tff(c_288, plain, (![D_58]: (r2_hidden(D_58, k1_xboole_0) | ~r2_hidden(D_58, '#skF_6'))), inference(resolution, [status(thm)], [c_268, c_10])).
% 2.23/1.30  tff(c_61, plain, (![A_27, B_28]: (r2_hidden('#skF_1'(A_27, B_28), A_27) | r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.23/1.30  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.23/1.30  tff(c_83, plain, (![A_30]: (r1_tarski(A_30, A_30))), inference(resolution, [status(thm)], [c_61, c_4])).
% 2.23/1.30  tff(c_36, plain, (![A_15, B_16]: (k4_xboole_0(A_15, B_16)=k1_xboole_0 | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.23/1.30  tff(c_87, plain, (![A_30]: (k4_xboole_0(A_30, A_30)=k1_xboole_0)), inference(resolution, [status(thm)], [c_83, c_36])).
% 2.23/1.30  tff(c_114, plain, (![D_34, B_35, A_36]: (~r2_hidden(D_34, B_35) | ~r2_hidden(D_34, k4_xboole_0(A_36, B_35)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.23/1.30  tff(c_120, plain, (![D_34, A_30]: (~r2_hidden(D_34, A_30) | ~r2_hidden(D_34, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_87, c_114])).
% 2.23/1.30  tff(c_309, plain, (![D_59]: (~r2_hidden(D_59, k1_xboole_0) | ~r2_hidden(D_59, '#skF_6'))), inference(resolution, [status(thm)], [c_288, c_120])).
% 2.23/1.30  tff(c_321, plain, (![D_57]: (~r2_hidden(D_57, '#skF_6'))), inference(resolution, [status(thm)], [c_285, c_309])).
% 2.23/1.30  tff(c_462, plain, (![B_68]: (r2_hidden('#skF_4'('#skF_6', B_68), B_68) | B_68='#skF_6')), inference(resolution, [status(thm)], [c_373, c_321])).
% 2.23/1.30  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.23/1.30  tff(c_325, plain, (![D_60]: (~r2_hidden(D_60, '#skF_6'))), inference(resolution, [status(thm)], [c_285, c_309])).
% 2.23/1.30  tff(c_337, plain, (![B_61]: (r1_tarski('#skF_6', B_61))), inference(resolution, [status(thm)], [c_6, c_325])).
% 2.23/1.30  tff(c_348, plain, (![B_62]: (k4_xboole_0('#skF_6', B_62)=k1_xboole_0)), inference(resolution, [status(thm)], [c_337, c_36])).
% 2.23/1.30  tff(c_12, plain, (![D_11, A_6, B_7]: (r2_hidden(D_11, A_6) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.23/1.30  tff(c_362, plain, (![D_11]: (r2_hidden(D_11, '#skF_6') | ~r2_hidden(D_11, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_348, c_12])).
% 2.23/1.30  tff(c_370, plain, (![D_11]: (~r2_hidden(D_11, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_321, c_362])).
% 2.23/1.30  tff(c_466, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_462, c_370])).
% 2.23/1.30  tff(c_484, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_466])).
% 2.23/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.30  
% 2.23/1.30  Inference rules
% 2.23/1.30  ----------------------
% 2.23/1.30  #Ref     : 0
% 2.23/1.30  #Sup     : 101
% 2.23/1.30  #Fact    : 0
% 2.23/1.30  #Define  : 0
% 2.23/1.30  #Split   : 0
% 2.23/1.30  #Chain   : 0
% 2.23/1.30  #Close   : 0
% 2.23/1.30  
% 2.23/1.30  Ordering : KBO
% 2.23/1.30  
% 2.23/1.30  Simplification rules
% 2.23/1.30  ----------------------
% 2.23/1.30  #Subsume      : 24
% 2.23/1.30  #Demod        : 17
% 2.23/1.30  #Tautology    : 36
% 2.23/1.30  #SimpNegUnit  : 3
% 2.23/1.30  #BackRed      : 0
% 2.23/1.30  
% 2.23/1.30  #Partial instantiations: 0
% 2.23/1.30  #Strategies tried      : 1
% 2.23/1.30  
% 2.23/1.30  Timing (in seconds)
% 2.23/1.30  ----------------------
% 2.23/1.30  Preprocessing        : 0.29
% 2.23/1.30  Parsing              : 0.15
% 2.23/1.30  CNF conversion       : 0.02
% 2.23/1.30  Main loop            : 0.24
% 2.23/1.30  Inferencing          : 0.09
% 2.23/1.30  Reduction            : 0.06
% 2.23/1.30  Demodulation         : 0.04
% 2.23/1.30  BG Simplification    : 0.02
% 2.23/1.30  Subsumption          : 0.06
% 2.23/1.30  Abstraction          : 0.01
% 2.23/1.30  MUC search           : 0.00
% 2.23/1.30  Cooper               : 0.00
% 2.23/1.30  Total                : 0.56
% 2.23/1.30  Index Insertion      : 0.00
% 2.23/1.30  Index Deletion       : 0.00
% 2.23/1.30  Index Matching       : 0.00
% 2.23/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
