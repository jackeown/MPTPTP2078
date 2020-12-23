%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:01 EST 2020

% Result     : Theorem 5.48s
% Output     : CNFRefutation 5.48s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 129 expanded)
%              Number of leaves         :   27 (  56 expanded)
%              Depth                    :   15
%              Number of atoms          :  112 ( 251 expanded)
%              Number of equality atoms :   34 ( 110 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_2 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_6 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_94,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( A != k1_tarski(B)
          & A != k1_xboole_0
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & C != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).

tff(f_57,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_69,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_65,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_62,plain,(
    k1_tarski('#skF_8') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_60,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_85,plain,(
    ! [A_37] :
      ( r2_hidden('#skF_6'(A_37),A_37)
      | k1_xboole_0 = A_37 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_58,plain,(
    ! [C_31] :
      ( C_31 = '#skF_8'
      | ~ r2_hidden(C_31,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_89,plain,
    ( '#skF_6'('#skF_7') = '#skF_8'
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_85,c_58])).

tff(c_92,plain,(
    '#skF_6'('#skF_7') = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_89])).

tff(c_34,plain,(
    ! [A_15] :
      ( r2_hidden('#skF_6'(A_15),A_15)
      | k1_xboole_0 = A_15 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_96,plain,
    ( r2_hidden('#skF_8','#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_34])).

tff(c_99,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_96])).

tff(c_136,plain,(
    ! [A_48,B_49] :
      ( r2_hidden('#skF_1'(A_48,B_49),A_48)
      | r1_tarski(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_141,plain,(
    ! [B_49] :
      ( '#skF_1'('#skF_7',B_49) = '#skF_8'
      | r1_tarski('#skF_7',B_49) ) ),
    inference(resolution,[status(thm)],[c_136,c_58])).

tff(c_46,plain,(
    ! [A_21] : k2_tarski(A_21,A_21) = k1_tarski(A_21) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_327,plain,(
    ! [A_80,B_81,C_82] :
      ( r1_tarski(k2_tarski(A_80,B_81),C_82)
      | ~ r2_hidden(B_81,C_82)
      | ~ r2_hidden(A_80,C_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_572,plain,(
    ! [A_102,C_103] :
      ( r1_tarski(k1_tarski(A_102),C_103)
      | ~ r2_hidden(A_102,C_103)
      | ~ r2_hidden(A_102,C_103) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_327])).

tff(c_36,plain,(
    ! [B_18,A_17] :
      ( B_18 = A_17
      | ~ r1_tarski(B_18,A_17)
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_913,plain,(
    ! [A_116,C_117] :
      ( k1_tarski(A_116) = C_117
      | ~ r1_tarski(C_117,k1_tarski(A_116))
      | ~ r2_hidden(A_116,C_117) ) ),
    inference(resolution,[status(thm)],[c_572,c_36])).

tff(c_936,plain,(
    ! [A_116] :
      ( k1_tarski(A_116) = '#skF_7'
      | ~ r2_hidden(A_116,'#skF_7')
      | '#skF_1'('#skF_7',k1_tarski(A_116)) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_141,c_913])).

tff(c_42,plain,(
    ! [A_19] : r1_tarski(k1_xboole_0,A_19) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_40,plain,(
    ! [B_18] : r1_tarski(B_18,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_115,plain,(
    ! [A_40,C_41,B_42] :
      ( r2_hidden(A_40,C_41)
      | ~ r1_tarski(k2_tarski(A_40,B_42),C_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_124,plain,(
    ! [A_43,B_44] : r2_hidden(A_43,k2_tarski(A_43,B_44)) ),
    inference(resolution,[status(thm)],[c_40,c_115])).

tff(c_127,plain,(
    ! [A_21] : r2_hidden(A_21,k1_tarski(A_21)) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_124])).

tff(c_209,plain,(
    ! [D_61,A_62,B_63] :
      ( r2_hidden(D_61,A_62)
      | ~ r2_hidden(D_61,k4_xboole_0(A_62,B_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_616,plain,(
    ! [A_105,B_106] :
      ( r2_hidden('#skF_6'(k4_xboole_0(A_105,B_106)),A_105)
      | k4_xboole_0(A_105,B_106) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_34,c_209])).

tff(c_798,plain,(
    ! [B_111] :
      ( '#skF_6'(k4_xboole_0('#skF_7',B_111)) = '#skF_8'
      | k4_xboole_0('#skF_7',B_111) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_616,c_58])).

tff(c_223,plain,(
    ! [D_64,B_65,A_66] :
      ( ~ r2_hidden(D_64,B_65)
      | ~ r2_hidden(D_64,k4_xboole_0(A_66,B_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_236,plain,(
    ! [A_66,B_65] :
      ( ~ r2_hidden('#skF_6'(k4_xboole_0(A_66,B_65)),B_65)
      | k4_xboole_0(A_66,B_65) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_34,c_223])).

tff(c_1281,plain,(
    ! [B_142] :
      ( ~ r2_hidden('#skF_8',B_142)
      | k4_xboole_0('#skF_7',B_142) = k1_xboole_0
      | k4_xboole_0('#skF_7',B_142) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_798,c_236])).

tff(c_1311,plain,(
    k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_127,c_1281])).

tff(c_526,plain,(
    ! [D_96,A_97,B_98] :
      ( r2_hidden(D_96,k4_xboole_0(A_97,B_98))
      | r2_hidden(D_96,B_98)
      | ~ r2_hidden(D_96,A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_5056,plain,(
    ! [D_268,B_269,A_270,B_271] :
      ( r2_hidden(D_268,B_269)
      | ~ r1_tarski(k4_xboole_0(A_270,B_271),B_269)
      | r2_hidden(D_268,B_271)
      | ~ r2_hidden(D_268,A_270) ) ),
    inference(resolution,[status(thm)],[c_526,c_2])).

tff(c_5074,plain,(
    ! [D_268,B_269] :
      ( r2_hidden(D_268,B_269)
      | ~ r1_tarski(k1_xboole_0,B_269)
      | r2_hidden(D_268,k1_tarski('#skF_8'))
      | ~ r2_hidden(D_268,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1311,c_5056])).

tff(c_5095,plain,(
    ! [D_268,B_269] :
      ( r2_hidden(D_268,B_269)
      | r2_hidden(D_268,k1_tarski('#skF_8'))
      | ~ r2_hidden(D_268,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_5074])).

tff(c_5303,plain,(
    ! [D_274] :
      ( ~ r2_hidden(D_274,'#skF_7')
      | r2_hidden(D_274,k1_tarski('#skF_8')) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_5095])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_5497,plain,(
    ! [A_277] :
      ( r1_tarski(A_277,k1_tarski('#skF_8'))
      | ~ r2_hidden('#skF_1'(A_277,k1_tarski('#skF_8')),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_5303,c_4])).

tff(c_5513,plain,
    ( r1_tarski('#skF_7',k1_tarski('#skF_8'))
    | ~ r2_hidden('#skF_8','#skF_7')
    | k1_tarski('#skF_8') = '#skF_7'
    | ~ r2_hidden('#skF_8','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_936,c_5497])).

tff(c_5528,plain,
    ( r1_tarski('#skF_7',k1_tarski('#skF_8'))
    | k1_tarski('#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_99,c_5513])).

tff(c_5529,plain,(
    r1_tarski('#skF_7',k1_tarski('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_5528])).

tff(c_596,plain,(
    ! [A_102,C_103] :
      ( k1_tarski(A_102) = C_103
      | ~ r1_tarski(C_103,k1_tarski(A_102))
      | ~ r2_hidden(A_102,C_103) ) ),
    inference(resolution,[status(thm)],[c_572,c_36])).

tff(c_5544,plain,
    ( k1_tarski('#skF_8') = '#skF_7'
    | ~ r2_hidden('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_5529,c_596])).

tff(c_5558,plain,(
    k1_tarski('#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_5544])).

tff(c_5560,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_5558])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:08:24 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.48/2.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.48/2.19  
% 5.48/2.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.48/2.20  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_2 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_6 > #skF_4
% 5.48/2.20  
% 5.48/2.20  %Foreground sorts:
% 5.48/2.20  
% 5.48/2.20  
% 5.48/2.20  %Background operators:
% 5.48/2.20  
% 5.48/2.20  
% 5.48/2.20  %Foreground operators:
% 5.48/2.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.48/2.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.48/2.20  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.48/2.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.48/2.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.48/2.20  tff('#skF_7', type, '#skF_7': $i).
% 5.48/2.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.48/2.20  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.48/2.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.48/2.20  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.48/2.20  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.48/2.20  tff('#skF_8', type, '#skF_8': $i).
% 5.48/2.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.48/2.20  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 5.48/2.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.48/2.20  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.48/2.20  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 5.48/2.20  tff('#skF_6', type, '#skF_6': $i > $i).
% 5.48/2.20  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 5.48/2.20  
% 5.48/2.21  tff(f_94, negated_conjecture, ~(![A, B]: ~((~(A = k1_tarski(B)) & ~(A = k1_xboole_0)) & (![C]: ~(r2_hidden(C, A) & ~(C = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_zfmisc_1)).
% 5.48/2.21  tff(f_57, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 5.48/2.21  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.48/2.21  tff(f_69, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 5.48/2.21  tff(f_79, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 5.48/2.21  tff(f_63, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.48/2.21  tff(f_65, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.48/2.21  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 5.48/2.21  tff(c_62, plain, (k1_tarski('#skF_8')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.48/2.21  tff(c_60, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.48/2.21  tff(c_85, plain, (![A_37]: (r2_hidden('#skF_6'(A_37), A_37) | k1_xboole_0=A_37)), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.48/2.21  tff(c_58, plain, (![C_31]: (C_31='#skF_8' | ~r2_hidden(C_31, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.48/2.21  tff(c_89, plain, ('#skF_6'('#skF_7')='#skF_8' | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_85, c_58])).
% 5.48/2.21  tff(c_92, plain, ('#skF_6'('#skF_7')='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_60, c_89])).
% 5.48/2.21  tff(c_34, plain, (![A_15]: (r2_hidden('#skF_6'(A_15), A_15) | k1_xboole_0=A_15)), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.48/2.21  tff(c_96, plain, (r2_hidden('#skF_8', '#skF_7') | k1_xboole_0='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_92, c_34])).
% 5.48/2.21  tff(c_99, plain, (r2_hidden('#skF_8', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_60, c_96])).
% 5.48/2.21  tff(c_136, plain, (![A_48, B_49]: (r2_hidden('#skF_1'(A_48, B_49), A_48) | r1_tarski(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.48/2.21  tff(c_141, plain, (![B_49]: ('#skF_1'('#skF_7', B_49)='#skF_8' | r1_tarski('#skF_7', B_49))), inference(resolution, [status(thm)], [c_136, c_58])).
% 5.48/2.21  tff(c_46, plain, (![A_21]: (k2_tarski(A_21, A_21)=k1_tarski(A_21))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.48/2.21  tff(c_327, plain, (![A_80, B_81, C_82]: (r1_tarski(k2_tarski(A_80, B_81), C_82) | ~r2_hidden(B_81, C_82) | ~r2_hidden(A_80, C_82))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.48/2.21  tff(c_572, plain, (![A_102, C_103]: (r1_tarski(k1_tarski(A_102), C_103) | ~r2_hidden(A_102, C_103) | ~r2_hidden(A_102, C_103))), inference(superposition, [status(thm), theory('equality')], [c_46, c_327])).
% 5.48/2.21  tff(c_36, plain, (![B_18, A_17]: (B_18=A_17 | ~r1_tarski(B_18, A_17) | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.48/2.21  tff(c_913, plain, (![A_116, C_117]: (k1_tarski(A_116)=C_117 | ~r1_tarski(C_117, k1_tarski(A_116)) | ~r2_hidden(A_116, C_117))), inference(resolution, [status(thm)], [c_572, c_36])).
% 5.48/2.21  tff(c_936, plain, (![A_116]: (k1_tarski(A_116)='#skF_7' | ~r2_hidden(A_116, '#skF_7') | '#skF_1'('#skF_7', k1_tarski(A_116))='#skF_8')), inference(resolution, [status(thm)], [c_141, c_913])).
% 5.48/2.21  tff(c_42, plain, (![A_19]: (r1_tarski(k1_xboole_0, A_19))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.48/2.21  tff(c_40, plain, (![B_18]: (r1_tarski(B_18, B_18))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.48/2.21  tff(c_115, plain, (![A_40, C_41, B_42]: (r2_hidden(A_40, C_41) | ~r1_tarski(k2_tarski(A_40, B_42), C_41))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.48/2.21  tff(c_124, plain, (![A_43, B_44]: (r2_hidden(A_43, k2_tarski(A_43, B_44)))), inference(resolution, [status(thm)], [c_40, c_115])).
% 5.48/2.21  tff(c_127, plain, (![A_21]: (r2_hidden(A_21, k1_tarski(A_21)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_124])).
% 5.48/2.21  tff(c_209, plain, (![D_61, A_62, B_63]: (r2_hidden(D_61, A_62) | ~r2_hidden(D_61, k4_xboole_0(A_62, B_63)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.48/2.21  tff(c_616, plain, (![A_105, B_106]: (r2_hidden('#skF_6'(k4_xboole_0(A_105, B_106)), A_105) | k4_xboole_0(A_105, B_106)=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_209])).
% 5.48/2.21  tff(c_798, plain, (![B_111]: ('#skF_6'(k4_xboole_0('#skF_7', B_111))='#skF_8' | k4_xboole_0('#skF_7', B_111)=k1_xboole_0)), inference(resolution, [status(thm)], [c_616, c_58])).
% 5.48/2.21  tff(c_223, plain, (![D_64, B_65, A_66]: (~r2_hidden(D_64, B_65) | ~r2_hidden(D_64, k4_xboole_0(A_66, B_65)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.48/2.21  tff(c_236, plain, (![A_66, B_65]: (~r2_hidden('#skF_6'(k4_xboole_0(A_66, B_65)), B_65) | k4_xboole_0(A_66, B_65)=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_223])).
% 5.48/2.21  tff(c_1281, plain, (![B_142]: (~r2_hidden('#skF_8', B_142) | k4_xboole_0('#skF_7', B_142)=k1_xboole_0 | k4_xboole_0('#skF_7', B_142)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_798, c_236])).
% 5.48/2.21  tff(c_1311, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_8'))=k1_xboole_0), inference(resolution, [status(thm)], [c_127, c_1281])).
% 5.48/2.21  tff(c_526, plain, (![D_96, A_97, B_98]: (r2_hidden(D_96, k4_xboole_0(A_97, B_98)) | r2_hidden(D_96, B_98) | ~r2_hidden(D_96, A_97))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.48/2.21  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.48/2.21  tff(c_5056, plain, (![D_268, B_269, A_270, B_271]: (r2_hidden(D_268, B_269) | ~r1_tarski(k4_xboole_0(A_270, B_271), B_269) | r2_hidden(D_268, B_271) | ~r2_hidden(D_268, A_270))), inference(resolution, [status(thm)], [c_526, c_2])).
% 5.48/2.21  tff(c_5074, plain, (![D_268, B_269]: (r2_hidden(D_268, B_269) | ~r1_tarski(k1_xboole_0, B_269) | r2_hidden(D_268, k1_tarski('#skF_8')) | ~r2_hidden(D_268, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_1311, c_5056])).
% 5.48/2.21  tff(c_5095, plain, (![D_268, B_269]: (r2_hidden(D_268, B_269) | r2_hidden(D_268, k1_tarski('#skF_8')) | ~r2_hidden(D_268, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_5074])).
% 5.48/2.21  tff(c_5303, plain, (![D_274]: (~r2_hidden(D_274, '#skF_7') | r2_hidden(D_274, k1_tarski('#skF_8')))), inference(factorization, [status(thm), theory('equality')], [c_5095])).
% 5.48/2.21  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.48/2.21  tff(c_5497, plain, (![A_277]: (r1_tarski(A_277, k1_tarski('#skF_8')) | ~r2_hidden('#skF_1'(A_277, k1_tarski('#skF_8')), '#skF_7'))), inference(resolution, [status(thm)], [c_5303, c_4])).
% 5.48/2.21  tff(c_5513, plain, (r1_tarski('#skF_7', k1_tarski('#skF_8')) | ~r2_hidden('#skF_8', '#skF_7') | k1_tarski('#skF_8')='#skF_7' | ~r2_hidden('#skF_8', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_936, c_5497])).
% 5.48/2.21  tff(c_5528, plain, (r1_tarski('#skF_7', k1_tarski('#skF_8')) | k1_tarski('#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_99, c_99, c_5513])).
% 5.48/2.21  tff(c_5529, plain, (r1_tarski('#skF_7', k1_tarski('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_62, c_5528])).
% 5.48/2.21  tff(c_596, plain, (![A_102, C_103]: (k1_tarski(A_102)=C_103 | ~r1_tarski(C_103, k1_tarski(A_102)) | ~r2_hidden(A_102, C_103))), inference(resolution, [status(thm)], [c_572, c_36])).
% 5.48/2.21  tff(c_5544, plain, (k1_tarski('#skF_8')='#skF_7' | ~r2_hidden('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_5529, c_596])).
% 5.48/2.21  tff(c_5558, plain, (k1_tarski('#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_99, c_5544])).
% 5.48/2.21  tff(c_5560, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_5558])).
% 5.48/2.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.48/2.21  
% 5.48/2.21  Inference rules
% 5.48/2.21  ----------------------
% 5.48/2.21  #Ref     : 0
% 5.48/2.21  #Sup     : 1232
% 5.48/2.21  #Fact    : 2
% 5.48/2.21  #Define  : 0
% 5.48/2.21  #Split   : 2
% 5.48/2.21  #Chain   : 0
% 5.48/2.21  #Close   : 0
% 5.48/2.21  
% 5.48/2.21  Ordering : KBO
% 5.48/2.21  
% 5.48/2.21  Simplification rules
% 5.48/2.21  ----------------------
% 5.48/2.21  #Subsume      : 324
% 5.48/2.21  #Demod        : 539
% 5.48/2.21  #Tautology    : 515
% 5.48/2.21  #SimpNegUnit  : 114
% 5.48/2.21  #BackRed      : 0
% 5.48/2.21  
% 5.48/2.21  #Partial instantiations: 0
% 5.48/2.21  #Strategies tried      : 1
% 5.48/2.21  
% 5.48/2.21  Timing (in seconds)
% 5.48/2.21  ----------------------
% 5.48/2.21  Preprocessing        : 0.36
% 5.48/2.21  Parsing              : 0.19
% 5.48/2.21  CNF conversion       : 0.03
% 5.48/2.21  Main loop            : 1.03
% 5.48/2.21  Inferencing          : 0.34
% 5.48/2.21  Reduction            : 0.34
% 5.48/2.21  Demodulation         : 0.23
% 5.48/2.21  BG Simplification    : 0.04
% 5.48/2.21  Subsumption          : 0.23
% 5.48/2.21  Abstraction          : 0.04
% 5.48/2.21  MUC search           : 0.00
% 5.48/2.21  Cooper               : 0.00
% 5.48/2.22  Total                : 1.43
% 5.85/2.22  Index Insertion      : 0.00
% 5.85/2.22  Index Deletion       : 0.00
% 5.85/2.22  Index Matching       : 0.00
% 5.85/2.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
