%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:28 EST 2020

% Result     : Theorem 56.09s
% Output     : CNFRefutation 56.09s
% Verified   : 
% Statistics : Number of formulae       :   61 (  90 expanded)
%              Number of leaves         :   22 (  40 expanded)
%              Depth                    :   11
%              Number of atoms          :   89 ( 165 expanded)
%              Number of equality atoms :   13 (  23 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_setfam_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_1 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_setfam_1,type,(
    r1_setfam_1: ( $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_78,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,B)
       => r1_setfam_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_setfam_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
    <=> ! [C] :
          ~ ( r2_hidden(C,A)
            & ! [D] :
                ~ ( r2_hidden(D,B)
                  & r1_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(c_46,plain,(
    ~ r1_setfam_1('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_44,plain,(
    ! [A_24,B_25] :
      ( r2_hidden('#skF_3'(A_24,B_25),A_24)
      | r1_setfam_1(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_757,plain,(
    ! [A_87,B_88] :
      ( r2_hidden('#skF_3'(A_87,B_88),A_87)
      | r1_setfam_1(A_87,B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_8,plain,(
    ! [D_8,A_3,B_4] :
      ( r2_hidden(D_8,A_3)
      | ~ r2_hidden(D_8,k4_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10761,plain,(
    ! [A_287,B_288,B_289] :
      ( r2_hidden('#skF_3'(k4_xboole_0(A_287,B_288),B_289),A_287)
      | r1_setfam_1(k4_xboole_0(A_287,B_288),B_289) ) ),
    inference(resolution,[status(thm)],[c_757,c_8])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( ~ r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,k4_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_767,plain,(
    ! [A_3,B_4,B_88] :
      ( ~ r2_hidden('#skF_3'(k4_xboole_0(A_3,B_4),B_88),B_4)
      | r1_setfam_1(k4_xboole_0(A_3,B_4),B_88) ) ),
    inference(resolution,[status(thm)],[c_757,c_6])).

tff(c_10790,plain,(
    ! [A_287,B_289] : r1_setfam_1(k4_xboole_0(A_287,A_287),B_289) ),
    inference(resolution,[status(thm)],[c_10761,c_767])).

tff(c_26,plain,(
    ! [B_10] : r1_tarski(B_10,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_163,plain,(
    ! [A_48,C_49,B_50] :
      ( r1_tarski(A_48,C_49)
      | ~ r1_tarski(k2_xboole_0(A_48,B_50),C_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_189,plain,(
    ! [A_48,B_50] : r1_tarski(A_48,k2_xboole_0(A_48,B_50)) ),
    inference(resolution,[status(thm)],[c_26,c_163])).

tff(c_1155,plain,(
    ! [A_107,B_108,C_109] :
      ( r1_tarski(k4_xboole_0(A_107,B_108),C_109)
      | ~ r1_tarski(A_107,k2_xboole_0(B_108,C_109)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_30,plain,(
    ! [A_14,B_15] :
      ( k2_xboole_0(A_14,B_15) = B_15
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_8127,plain,(
    ! [A_268,B_269,C_270] :
      ( k2_xboole_0(k4_xboole_0(A_268,B_269),C_270) = C_270
      | ~ r1_tarski(A_268,k2_xboole_0(B_269,C_270)) ) ),
    inference(resolution,[status(thm)],[c_1155,c_30])).

tff(c_8403,plain,(
    ! [A_271,B_272] : k2_xboole_0(k4_xboole_0(A_271,A_271),B_272) = B_272 ),
    inference(resolution,[status(thm)],[c_189,c_8127])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8653,plain,(
    ! [B_272,A_271] : k2_xboole_0(B_272,k4_xboole_0(A_271,A_271)) = B_272 ),
    inference(superposition,[status(thm),theory(equality)],[c_8403,c_2])).

tff(c_48,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_85,plain,(
    ! [A_41,B_42] :
      ( k2_xboole_0(A_41,B_42) = B_42
      | ~ r1_tarski(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_97,plain,(
    k2_xboole_0('#skF_5','#skF_6') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_48,c_85])).

tff(c_190,plain,(
    ! [A_51,B_52] : r1_tarski(A_51,k2_xboole_0(A_51,B_52)) ),
    inference(resolution,[status(thm)],[c_26,c_163])).

tff(c_28,plain,(
    ! [A_11,C_13,B_12] :
      ( r1_tarski(A_11,C_13)
      | ~ r1_tarski(k2_xboole_0(A_11,B_12),C_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_272,plain,(
    ! [A_56,B_57,B_58] : r1_tarski(A_56,k2_xboole_0(k2_xboole_0(A_56,B_57),B_58)) ),
    inference(resolution,[status(thm)],[c_190,c_28])).

tff(c_295,plain,(
    ! [B_58] : r1_tarski('#skF_5',k2_xboole_0('#skF_6',B_58)) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_272])).

tff(c_9205,plain,(
    ! [B_277] : k2_xboole_0(k4_xboole_0('#skF_5','#skF_6'),B_277) = B_277 ),
    inference(resolution,[status(thm)],[c_295,c_8127])).

tff(c_9461,plain,(
    ! [A_271] : k4_xboole_0(A_271,A_271) = k4_xboole_0('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_8653,c_9205])).

tff(c_4,plain,(
    ! [D_8,A_3,B_4] :
      ( r2_hidden(D_8,k4_xboole_0(A_3,B_4))
      | r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_3257,plain,(
    ! [A_159,B_160,C_161] :
      ( r2_hidden('#skF_4'(A_159,B_160,C_161),B_160)
      | ~ r2_hidden(C_161,A_159)
      | ~ r1_setfam_1(A_159,B_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_12636,plain,(
    ! [A_322,A_323,B_324,C_325] :
      ( r2_hidden('#skF_4'(A_322,k4_xboole_0(A_323,B_324),C_325),A_323)
      | ~ r2_hidden(C_325,A_322)
      | ~ r1_setfam_1(A_322,k4_xboole_0(A_323,B_324)) ) ),
    inference(resolution,[status(thm)],[c_3257,c_8])).

tff(c_3267,plain,(
    ! [A_159,A_3,B_4,C_161] :
      ( ~ r2_hidden('#skF_4'(A_159,k4_xboole_0(A_3,B_4),C_161),B_4)
      | ~ r2_hidden(C_161,A_159)
      | ~ r1_setfam_1(A_159,k4_xboole_0(A_3,B_4)) ) ),
    inference(resolution,[status(thm)],[c_3257,c_6])).

tff(c_16056,plain,(
    ! [C_372,A_373,A_374] :
      ( ~ r2_hidden(C_372,A_373)
      | ~ r1_setfam_1(A_373,k4_xboole_0(A_374,A_374)) ) ),
    inference(resolution,[status(thm)],[c_12636,c_3267])).

tff(c_228710,plain,(
    ! [A_1660,B_1661,A_1662,D_1663] :
      ( ~ r1_setfam_1(k4_xboole_0(A_1660,B_1661),k4_xboole_0(A_1662,A_1662))
      | r2_hidden(D_1663,B_1661)
      | ~ r2_hidden(D_1663,A_1660) ) ),
    inference(resolution,[status(thm)],[c_4,c_16056])).

tff(c_228844,plain,(
    ! [A_271,A_1662,D_1663] :
      ( ~ r1_setfam_1(k4_xboole_0(A_271,A_271),k4_xboole_0(A_1662,A_1662))
      | r2_hidden(D_1663,'#skF_6')
      | ~ r2_hidden(D_1663,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9461,c_228710])).

tff(c_228943,plain,(
    ! [D_1664] :
      ( r2_hidden(D_1664,'#skF_6')
      | ~ r2_hidden(D_1664,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10790,c_228844])).

tff(c_236237,plain,(
    ! [B_1696] :
      ( r2_hidden('#skF_3'('#skF_5',B_1696),'#skF_6')
      | r1_setfam_1('#skF_5',B_1696) ) ),
    inference(resolution,[status(thm)],[c_44,c_228943])).

tff(c_1628,plain,(
    ! [A_127,B_128,D_129] :
      ( ~ r1_tarski('#skF_3'(A_127,B_128),D_129)
      | ~ r2_hidden(D_129,B_128)
      | r1_setfam_1(A_127,B_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1668,plain,(
    ! [A_127,B_128] :
      ( ~ r2_hidden('#skF_3'(A_127,B_128),B_128)
      | r1_setfam_1(A_127,B_128) ) ),
    inference(resolution,[status(thm)],[c_26,c_1628])).

tff(c_236253,plain,(
    r1_setfam_1('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_236237,c_1668])).

tff(c_236262,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_46,c_236253])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:39:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 56.09/44.71  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 56.09/44.71  
% 56.09/44.71  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 56.09/44.71  %$ r2_hidden > r1_tarski > r1_setfam_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_1 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2
% 56.09/44.71  
% 56.09/44.71  %Foreground sorts:
% 56.09/44.71  
% 56.09/44.71  
% 56.09/44.71  %Background operators:
% 56.09/44.71  
% 56.09/44.71  
% 56.09/44.71  %Foreground operators:
% 56.09/44.71  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 56.09/44.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 56.09/44.71  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 56.09/44.71  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 56.09/44.71  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 56.09/44.71  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 56.09/44.71  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 56.09/44.71  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 56.09/44.71  tff('#skF_5', type, '#skF_5': $i).
% 56.09/44.71  tff('#skF_6', type, '#skF_6': $i).
% 56.09/44.71  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 56.09/44.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 56.09/44.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 56.09/44.71  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 56.09/44.71  
% 56.09/44.73  tff(f_78, negated_conjecture, ~(![A, B]: (r1_tarski(A, B) => r1_setfam_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_setfam_1)).
% 56.09/44.73  tff(f_73, axiom, (![A, B]: (r1_setfam_1(A, B) <=> (![C]: ~(r2_hidden(C, A) & (![D]: ~(r2_hidden(D, B) & r1_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_setfam_1)).
% 56.09/44.73  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 56.09/44.73  tff(f_43, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 56.09/44.73  tff(f_47, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 56.09/44.73  tff(f_57, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 56.09/44.73  tff(f_51, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 56.09/44.73  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 56.09/44.73  tff(c_46, plain, (~r1_setfam_1('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_78])).
% 56.09/44.73  tff(c_44, plain, (![A_24, B_25]: (r2_hidden('#skF_3'(A_24, B_25), A_24) | r1_setfam_1(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_73])).
% 56.09/44.73  tff(c_757, plain, (![A_87, B_88]: (r2_hidden('#skF_3'(A_87, B_88), A_87) | r1_setfam_1(A_87, B_88))), inference(cnfTransformation, [status(thm)], [f_73])).
% 56.09/44.73  tff(c_8, plain, (![D_8, A_3, B_4]: (r2_hidden(D_8, A_3) | ~r2_hidden(D_8, k4_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 56.09/44.73  tff(c_10761, plain, (![A_287, B_288, B_289]: (r2_hidden('#skF_3'(k4_xboole_0(A_287, B_288), B_289), A_287) | r1_setfam_1(k4_xboole_0(A_287, B_288), B_289))), inference(resolution, [status(thm)], [c_757, c_8])).
% 56.09/44.73  tff(c_6, plain, (![D_8, B_4, A_3]: (~r2_hidden(D_8, B_4) | ~r2_hidden(D_8, k4_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 56.09/44.73  tff(c_767, plain, (![A_3, B_4, B_88]: (~r2_hidden('#skF_3'(k4_xboole_0(A_3, B_4), B_88), B_4) | r1_setfam_1(k4_xboole_0(A_3, B_4), B_88))), inference(resolution, [status(thm)], [c_757, c_6])).
% 56.09/44.73  tff(c_10790, plain, (![A_287, B_289]: (r1_setfam_1(k4_xboole_0(A_287, A_287), B_289))), inference(resolution, [status(thm)], [c_10761, c_767])).
% 56.09/44.73  tff(c_26, plain, (![B_10]: (r1_tarski(B_10, B_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 56.09/44.73  tff(c_163, plain, (![A_48, C_49, B_50]: (r1_tarski(A_48, C_49) | ~r1_tarski(k2_xboole_0(A_48, B_50), C_49))), inference(cnfTransformation, [status(thm)], [f_47])).
% 56.09/44.73  tff(c_189, plain, (![A_48, B_50]: (r1_tarski(A_48, k2_xboole_0(A_48, B_50)))), inference(resolution, [status(thm)], [c_26, c_163])).
% 56.09/44.73  tff(c_1155, plain, (![A_107, B_108, C_109]: (r1_tarski(k4_xboole_0(A_107, B_108), C_109) | ~r1_tarski(A_107, k2_xboole_0(B_108, C_109)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 56.09/44.73  tff(c_30, plain, (![A_14, B_15]: (k2_xboole_0(A_14, B_15)=B_15 | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 56.09/44.73  tff(c_8127, plain, (![A_268, B_269, C_270]: (k2_xboole_0(k4_xboole_0(A_268, B_269), C_270)=C_270 | ~r1_tarski(A_268, k2_xboole_0(B_269, C_270)))), inference(resolution, [status(thm)], [c_1155, c_30])).
% 56.09/44.73  tff(c_8403, plain, (![A_271, B_272]: (k2_xboole_0(k4_xboole_0(A_271, A_271), B_272)=B_272)), inference(resolution, [status(thm)], [c_189, c_8127])).
% 56.09/44.73  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 56.09/44.73  tff(c_8653, plain, (![B_272, A_271]: (k2_xboole_0(B_272, k4_xboole_0(A_271, A_271))=B_272)), inference(superposition, [status(thm), theory('equality')], [c_8403, c_2])).
% 56.09/44.73  tff(c_48, plain, (r1_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_78])).
% 56.09/44.73  tff(c_85, plain, (![A_41, B_42]: (k2_xboole_0(A_41, B_42)=B_42 | ~r1_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_51])).
% 56.09/44.73  tff(c_97, plain, (k2_xboole_0('#skF_5', '#skF_6')='#skF_6'), inference(resolution, [status(thm)], [c_48, c_85])).
% 56.09/44.73  tff(c_190, plain, (![A_51, B_52]: (r1_tarski(A_51, k2_xboole_0(A_51, B_52)))), inference(resolution, [status(thm)], [c_26, c_163])).
% 56.09/44.73  tff(c_28, plain, (![A_11, C_13, B_12]: (r1_tarski(A_11, C_13) | ~r1_tarski(k2_xboole_0(A_11, B_12), C_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 56.09/44.73  tff(c_272, plain, (![A_56, B_57, B_58]: (r1_tarski(A_56, k2_xboole_0(k2_xboole_0(A_56, B_57), B_58)))), inference(resolution, [status(thm)], [c_190, c_28])).
% 56.09/44.73  tff(c_295, plain, (![B_58]: (r1_tarski('#skF_5', k2_xboole_0('#skF_6', B_58)))), inference(superposition, [status(thm), theory('equality')], [c_97, c_272])).
% 56.09/44.73  tff(c_9205, plain, (![B_277]: (k2_xboole_0(k4_xboole_0('#skF_5', '#skF_6'), B_277)=B_277)), inference(resolution, [status(thm)], [c_295, c_8127])).
% 56.09/44.73  tff(c_9461, plain, (![A_271]: (k4_xboole_0(A_271, A_271)=k4_xboole_0('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_8653, c_9205])).
% 56.09/44.73  tff(c_4, plain, (![D_8, A_3, B_4]: (r2_hidden(D_8, k4_xboole_0(A_3, B_4)) | r2_hidden(D_8, B_4) | ~r2_hidden(D_8, A_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 56.09/44.73  tff(c_3257, plain, (![A_159, B_160, C_161]: (r2_hidden('#skF_4'(A_159, B_160, C_161), B_160) | ~r2_hidden(C_161, A_159) | ~r1_setfam_1(A_159, B_160))), inference(cnfTransformation, [status(thm)], [f_73])).
% 56.09/44.73  tff(c_12636, plain, (![A_322, A_323, B_324, C_325]: (r2_hidden('#skF_4'(A_322, k4_xboole_0(A_323, B_324), C_325), A_323) | ~r2_hidden(C_325, A_322) | ~r1_setfam_1(A_322, k4_xboole_0(A_323, B_324)))), inference(resolution, [status(thm)], [c_3257, c_8])).
% 56.09/44.73  tff(c_3267, plain, (![A_159, A_3, B_4, C_161]: (~r2_hidden('#skF_4'(A_159, k4_xboole_0(A_3, B_4), C_161), B_4) | ~r2_hidden(C_161, A_159) | ~r1_setfam_1(A_159, k4_xboole_0(A_3, B_4)))), inference(resolution, [status(thm)], [c_3257, c_6])).
% 56.09/44.73  tff(c_16056, plain, (![C_372, A_373, A_374]: (~r2_hidden(C_372, A_373) | ~r1_setfam_1(A_373, k4_xboole_0(A_374, A_374)))), inference(resolution, [status(thm)], [c_12636, c_3267])).
% 56.09/44.73  tff(c_228710, plain, (![A_1660, B_1661, A_1662, D_1663]: (~r1_setfam_1(k4_xboole_0(A_1660, B_1661), k4_xboole_0(A_1662, A_1662)) | r2_hidden(D_1663, B_1661) | ~r2_hidden(D_1663, A_1660))), inference(resolution, [status(thm)], [c_4, c_16056])).
% 56.09/44.73  tff(c_228844, plain, (![A_271, A_1662, D_1663]: (~r1_setfam_1(k4_xboole_0(A_271, A_271), k4_xboole_0(A_1662, A_1662)) | r2_hidden(D_1663, '#skF_6') | ~r2_hidden(D_1663, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_9461, c_228710])).
% 56.09/44.73  tff(c_228943, plain, (![D_1664]: (r2_hidden(D_1664, '#skF_6') | ~r2_hidden(D_1664, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_10790, c_228844])).
% 56.09/44.73  tff(c_236237, plain, (![B_1696]: (r2_hidden('#skF_3'('#skF_5', B_1696), '#skF_6') | r1_setfam_1('#skF_5', B_1696))), inference(resolution, [status(thm)], [c_44, c_228943])).
% 56.09/44.73  tff(c_1628, plain, (![A_127, B_128, D_129]: (~r1_tarski('#skF_3'(A_127, B_128), D_129) | ~r2_hidden(D_129, B_128) | r1_setfam_1(A_127, B_128))), inference(cnfTransformation, [status(thm)], [f_73])).
% 56.09/44.73  tff(c_1668, plain, (![A_127, B_128]: (~r2_hidden('#skF_3'(A_127, B_128), B_128) | r1_setfam_1(A_127, B_128))), inference(resolution, [status(thm)], [c_26, c_1628])).
% 56.09/44.73  tff(c_236253, plain, (r1_setfam_1('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_236237, c_1668])).
% 56.09/44.73  tff(c_236262, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_46, c_236253])).
% 56.09/44.73  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 56.09/44.73  
% 56.09/44.73  Inference rules
% 56.09/44.73  ----------------------
% 56.09/44.73  #Ref     : 0
% 56.09/44.73  #Sup     : 57579
% 56.09/44.73  #Fact    : 2
% 56.09/44.73  #Define  : 0
% 56.09/44.73  #Split   : 2
% 56.09/44.73  #Chain   : 0
% 56.09/44.73  #Close   : 0
% 56.09/44.73  
% 56.09/44.73  Ordering : KBO
% 56.09/44.73  
% 56.09/44.73  Simplification rules
% 56.09/44.73  ----------------------
% 56.09/44.73  #Subsume      : 7473
% 56.09/44.73  #Demod        : 63015
% 56.09/44.73  #Tautology    : 30926
% 56.09/44.73  #SimpNegUnit  : 5
% 56.09/44.73  #BackRed      : 129
% 56.09/44.73  
% 56.09/44.73  #Partial instantiations: 0
% 56.09/44.73  #Strategies tried      : 1
% 56.09/44.73  
% 56.09/44.73  Timing (in seconds)
% 56.09/44.73  ----------------------
% 56.09/44.73  Preprocessing        : 0.28
% 56.09/44.73  Parsing              : 0.15
% 56.09/44.73  CNF conversion       : 0.02
% 56.09/44.73  Main loop            : 43.68
% 56.09/44.73  Inferencing          : 3.43
% 56.09/44.74  Reduction            : 25.50
% 56.09/44.74  Demodulation         : 23.44
% 56.09/44.74  BG Simplification    : 0.43
% 56.09/44.74  Subsumption          : 12.49
% 56.09/44.74  Abstraction          : 0.74
% 56.09/44.74  MUC search           : 0.00
% 56.09/44.74  Cooper               : 0.00
% 56.09/44.74  Total                : 44.00
% 56.09/44.74  Index Insertion      : 0.00
% 56.09/44.74  Index Deletion       : 0.00
% 56.09/44.74  Index Matching       : 0.00
% 56.09/44.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
