%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:18 EST 2020

% Result     : Theorem 3.48s
% Output     : CNFRefutation 3.48s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 104 expanded)
%              Number of leaves         :   30 (  49 expanded)
%              Depth                    :   15
%              Number of atoms          :   85 ( 190 expanded)
%              Number of equality atoms :   37 (  74 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_2 > #skF_4 > #skF_8 > #skF_3 > #skF_7 > #skF_5

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

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_96,negated_conjecture,(
    ~ ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_43,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),k1_tarski(B))
        & A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_93,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_tarski(B,C) )
     => ( A = k1_xboole_0
        | r1_tarski(B,k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_setfam_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

tff(c_82,plain,(
    k1_setfam_1(k1_tarski('#skF_8')) != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_58,plain,(
    ! [C_23] : r2_hidden(C_23,k1_tarski(C_23)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_469,plain,(
    ! [A_112,B_113,C_114] :
      ( r2_hidden('#skF_1'(A_112,B_113,C_114),A_112)
      | r2_hidden('#skF_2'(A_112,B_113,C_114),C_114)
      | k4_xboole_0(A_112,B_113) = C_114 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_16,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),B_2)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_517,plain,(
    ! [A_112,C_114] :
      ( r2_hidden('#skF_2'(A_112,A_112,C_114),C_114)
      | k4_xboole_0(A_112,A_112) = C_114 ) ),
    inference(resolution,[status(thm)],[c_469,c_16])).

tff(c_529,plain,(
    ! [A_115,C_116] :
      ( r2_hidden('#skF_2'(A_115,A_115,C_116),C_116)
      | k4_xboole_0(A_115,A_115) = C_116 ) ),
    inference(resolution,[status(thm)],[c_469,c_16])).

tff(c_26,plain,(
    ! [A_9] : k4_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_155,plain,(
    ! [D_66,B_67,A_68] :
      ( ~ r2_hidden(D_66,B_67)
      | ~ r2_hidden(D_66,k4_xboole_0(A_68,B_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_158,plain,(
    ! [D_66,A_9] :
      ( ~ r2_hidden(D_66,k1_xboole_0)
      | ~ r2_hidden(D_66,A_9) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_155])).

tff(c_559,plain,(
    ! [A_117,A_118] :
      ( ~ r2_hidden('#skF_2'(A_117,A_117,k1_xboole_0),A_118)
      | k4_xboole_0(A_117,A_117) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_529,c_158])).

tff(c_588,plain,(
    ! [A_112] : k4_xboole_0(A_112,A_112) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_517,c_559])).

tff(c_144,plain,(
    ! [A_61,B_62] :
      ( r1_xboole_0(A_61,B_62)
      | k4_xboole_0(A_61,B_62) != A_61 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_74,plain,(
    ! [B_31] : ~ r1_xboole_0(k1_tarski(B_31),k1_tarski(B_31)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_148,plain,(
    ! [B_31] : k4_xboole_0(k1_tarski(B_31),k1_tarski(B_31)) != k1_tarski(B_31) ),
    inference(resolution,[status(thm)],[c_144,c_74])).

tff(c_598,plain,(
    ! [B_31] : k1_tarski(B_31) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_588,c_148])).

tff(c_24,plain,(
    ! [B_8] : r1_tarski(B_8,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_195,plain,(
    ! [A_81,B_82] :
      ( r2_hidden('#skF_7'(A_81,B_82),A_81)
      | r1_tarski(B_82,k1_setfam_1(A_81))
      | k1_xboole_0 = A_81 ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_56,plain,(
    ! [C_23,A_19] :
      ( C_23 = A_19
      | ~ r2_hidden(C_23,k1_tarski(A_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_215,plain,(
    ! [A_19,B_82] :
      ( '#skF_7'(k1_tarski(A_19),B_82) = A_19
      | r1_tarski(B_82,k1_setfam_1(k1_tarski(A_19)))
      | k1_tarski(A_19) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_195,c_56])).

tff(c_1354,plain,(
    ! [A_188,B_189] :
      ( '#skF_7'(k1_tarski(A_188),B_189) = A_188
      | r1_tarski(B_189,k1_setfam_1(k1_tarski(A_188))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_598,c_215])).

tff(c_76,plain,(
    ! [B_33,A_32] :
      ( r1_tarski(k1_setfam_1(B_33),A_32)
      | ~ r2_hidden(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_164,plain,(
    ! [B_74,A_75] :
      ( B_74 = A_75
      | ~ r1_tarski(B_74,A_75)
      | ~ r1_tarski(A_75,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_169,plain,(
    ! [B_33,A_32] :
      ( k1_setfam_1(B_33) = A_32
      | ~ r1_tarski(A_32,k1_setfam_1(B_33))
      | ~ r2_hidden(A_32,B_33) ) ),
    inference(resolution,[status(thm)],[c_76,c_164])).

tff(c_1400,plain,(
    ! [A_196,B_197] :
      ( k1_setfam_1(k1_tarski(A_196)) = B_197
      | ~ r2_hidden(B_197,k1_tarski(A_196))
      | '#skF_7'(k1_tarski(A_196),B_197) = A_196 ) ),
    inference(resolution,[status(thm)],[c_1354,c_169])).

tff(c_1476,plain,(
    ! [C_198] :
      ( k1_setfam_1(k1_tarski(C_198)) = C_198
      | '#skF_7'(k1_tarski(C_198),C_198) = C_198 ) ),
    inference(resolution,[status(thm)],[c_58,c_1400])).

tff(c_1520,plain,(
    '#skF_7'(k1_tarski('#skF_8'),'#skF_8') = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_1476,c_82])).

tff(c_78,plain,(
    ! [B_35,A_34] :
      ( ~ r1_tarski(B_35,'#skF_7'(A_34,B_35))
      | r1_tarski(B_35,k1_setfam_1(A_34))
      | k1_xboole_0 = A_34 ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1533,plain,
    ( ~ r1_tarski('#skF_8','#skF_8')
    | r1_tarski('#skF_8',k1_setfam_1(k1_tarski('#skF_8')))
    | k1_tarski('#skF_8') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1520,c_78])).

tff(c_1541,plain,
    ( r1_tarski('#skF_8',k1_setfam_1(k1_tarski('#skF_8')))
    | k1_tarski('#skF_8') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1533])).

tff(c_1542,plain,(
    r1_tarski('#skF_8',k1_setfam_1(k1_tarski('#skF_8'))) ),
    inference(negUnitSimplification,[status(thm)],[c_598,c_1541])).

tff(c_1548,plain,
    ( k1_setfam_1(k1_tarski('#skF_8')) = '#skF_8'
    | ~ r2_hidden('#skF_8',k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_1542,c_169])).

tff(c_1556,plain,(
    k1_setfam_1(k1_tarski('#skF_8')) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1548])).

tff(c_1558,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_1556])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n024.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 20:07:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.48/1.58  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.48/1.59  
% 3.48/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.48/1.59  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_2 > #skF_4 > #skF_8 > #skF_3 > #skF_7 > #skF_5
% 3.48/1.59  
% 3.48/1.59  %Foreground sorts:
% 3.48/1.59  
% 3.48/1.59  
% 3.48/1.59  %Background operators:
% 3.48/1.59  
% 3.48/1.59  
% 3.48/1.59  %Foreground operators:
% 3.48/1.59  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.48/1.59  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.48/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.48/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.48/1.59  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.48/1.59  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.48/1.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.48/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.48/1.59  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.48/1.59  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.48/1.59  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.48/1.59  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.48/1.59  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.48/1.59  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 3.48/1.59  tff('#skF_8', type, '#skF_8': $i).
% 3.48/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.48/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.48/1.59  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.48/1.59  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 3.48/1.59  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.48/1.59  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.48/1.59  
% 3.48/1.60  tff(f_96, negated_conjecture, ~(![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_setfam_1)).
% 3.48/1.60  tff(f_69, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 3.48/1.60  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.48/1.60  tff(f_43, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.48/1.60  tff(f_47, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.48/1.60  tff(f_80, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), k1_tarski(B)) & (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_zfmisc_1)).
% 3.48/1.60  tff(f_41, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.48/1.60  tff(f_93, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_tarski(B, C))) => ((A = k1_xboole_0) | r1_tarski(B, k1_setfam_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_setfam_1)).
% 3.48/1.60  tff(f_84, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_setfam_1)).
% 3.48/1.60  tff(c_82, plain, (k1_setfam_1(k1_tarski('#skF_8'))!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.48/1.60  tff(c_58, plain, (![C_23]: (r2_hidden(C_23, k1_tarski(C_23)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.48/1.60  tff(c_469, plain, (![A_112, B_113, C_114]: (r2_hidden('#skF_1'(A_112, B_113, C_114), A_112) | r2_hidden('#skF_2'(A_112, B_113, C_114), C_114) | k4_xboole_0(A_112, B_113)=C_114)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.48/1.60  tff(c_16, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), B_2) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.48/1.60  tff(c_517, plain, (![A_112, C_114]: (r2_hidden('#skF_2'(A_112, A_112, C_114), C_114) | k4_xboole_0(A_112, A_112)=C_114)), inference(resolution, [status(thm)], [c_469, c_16])).
% 3.48/1.60  tff(c_529, plain, (![A_115, C_116]: (r2_hidden('#skF_2'(A_115, A_115, C_116), C_116) | k4_xboole_0(A_115, A_115)=C_116)), inference(resolution, [status(thm)], [c_469, c_16])).
% 3.48/1.60  tff(c_26, plain, (![A_9]: (k4_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.48/1.60  tff(c_155, plain, (![D_66, B_67, A_68]: (~r2_hidden(D_66, B_67) | ~r2_hidden(D_66, k4_xboole_0(A_68, B_67)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.48/1.60  tff(c_158, plain, (![D_66, A_9]: (~r2_hidden(D_66, k1_xboole_0) | ~r2_hidden(D_66, A_9))), inference(superposition, [status(thm), theory('equality')], [c_26, c_155])).
% 3.48/1.60  tff(c_559, plain, (![A_117, A_118]: (~r2_hidden('#skF_2'(A_117, A_117, k1_xboole_0), A_118) | k4_xboole_0(A_117, A_117)=k1_xboole_0)), inference(resolution, [status(thm)], [c_529, c_158])).
% 3.48/1.60  tff(c_588, plain, (![A_112]: (k4_xboole_0(A_112, A_112)=k1_xboole_0)), inference(resolution, [status(thm)], [c_517, c_559])).
% 3.48/1.60  tff(c_144, plain, (![A_61, B_62]: (r1_xboole_0(A_61, B_62) | k4_xboole_0(A_61, B_62)!=A_61)), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.48/1.60  tff(c_74, plain, (![B_31]: (~r1_xboole_0(k1_tarski(B_31), k1_tarski(B_31)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.48/1.60  tff(c_148, plain, (![B_31]: (k4_xboole_0(k1_tarski(B_31), k1_tarski(B_31))!=k1_tarski(B_31))), inference(resolution, [status(thm)], [c_144, c_74])).
% 3.48/1.60  tff(c_598, plain, (![B_31]: (k1_tarski(B_31)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_588, c_148])).
% 3.48/1.60  tff(c_24, plain, (![B_8]: (r1_tarski(B_8, B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.48/1.60  tff(c_195, plain, (![A_81, B_82]: (r2_hidden('#skF_7'(A_81, B_82), A_81) | r1_tarski(B_82, k1_setfam_1(A_81)) | k1_xboole_0=A_81)), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.48/1.60  tff(c_56, plain, (![C_23, A_19]: (C_23=A_19 | ~r2_hidden(C_23, k1_tarski(A_19)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.48/1.60  tff(c_215, plain, (![A_19, B_82]: ('#skF_7'(k1_tarski(A_19), B_82)=A_19 | r1_tarski(B_82, k1_setfam_1(k1_tarski(A_19))) | k1_tarski(A_19)=k1_xboole_0)), inference(resolution, [status(thm)], [c_195, c_56])).
% 3.48/1.60  tff(c_1354, plain, (![A_188, B_189]: ('#skF_7'(k1_tarski(A_188), B_189)=A_188 | r1_tarski(B_189, k1_setfam_1(k1_tarski(A_188))))), inference(negUnitSimplification, [status(thm)], [c_598, c_215])).
% 3.48/1.60  tff(c_76, plain, (![B_33, A_32]: (r1_tarski(k1_setfam_1(B_33), A_32) | ~r2_hidden(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.48/1.60  tff(c_164, plain, (![B_74, A_75]: (B_74=A_75 | ~r1_tarski(B_74, A_75) | ~r1_tarski(A_75, B_74))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.48/1.60  tff(c_169, plain, (![B_33, A_32]: (k1_setfam_1(B_33)=A_32 | ~r1_tarski(A_32, k1_setfam_1(B_33)) | ~r2_hidden(A_32, B_33))), inference(resolution, [status(thm)], [c_76, c_164])).
% 3.48/1.60  tff(c_1400, plain, (![A_196, B_197]: (k1_setfam_1(k1_tarski(A_196))=B_197 | ~r2_hidden(B_197, k1_tarski(A_196)) | '#skF_7'(k1_tarski(A_196), B_197)=A_196)), inference(resolution, [status(thm)], [c_1354, c_169])).
% 3.48/1.60  tff(c_1476, plain, (![C_198]: (k1_setfam_1(k1_tarski(C_198))=C_198 | '#skF_7'(k1_tarski(C_198), C_198)=C_198)), inference(resolution, [status(thm)], [c_58, c_1400])).
% 3.48/1.60  tff(c_1520, plain, ('#skF_7'(k1_tarski('#skF_8'), '#skF_8')='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_1476, c_82])).
% 3.48/1.60  tff(c_78, plain, (![B_35, A_34]: (~r1_tarski(B_35, '#skF_7'(A_34, B_35)) | r1_tarski(B_35, k1_setfam_1(A_34)) | k1_xboole_0=A_34)), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.48/1.60  tff(c_1533, plain, (~r1_tarski('#skF_8', '#skF_8') | r1_tarski('#skF_8', k1_setfam_1(k1_tarski('#skF_8'))) | k1_tarski('#skF_8')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1520, c_78])).
% 3.48/1.60  tff(c_1541, plain, (r1_tarski('#skF_8', k1_setfam_1(k1_tarski('#skF_8'))) | k1_tarski('#skF_8')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_24, c_1533])).
% 3.48/1.60  tff(c_1542, plain, (r1_tarski('#skF_8', k1_setfam_1(k1_tarski('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_598, c_1541])).
% 3.48/1.60  tff(c_1548, plain, (k1_setfam_1(k1_tarski('#skF_8'))='#skF_8' | ~r2_hidden('#skF_8', k1_tarski('#skF_8'))), inference(resolution, [status(thm)], [c_1542, c_169])).
% 3.48/1.60  tff(c_1556, plain, (k1_setfam_1(k1_tarski('#skF_8'))='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1548])).
% 3.48/1.60  tff(c_1558, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_1556])).
% 3.48/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.48/1.60  
% 3.48/1.60  Inference rules
% 3.48/1.60  ----------------------
% 3.48/1.60  #Ref     : 0
% 3.48/1.60  #Sup     : 295
% 3.48/1.60  #Fact    : 0
% 3.48/1.60  #Define  : 0
% 3.48/1.60  #Split   : 0
% 3.48/1.60  #Chain   : 0
% 3.48/1.60  #Close   : 0
% 3.48/1.60  
% 3.48/1.60  Ordering : KBO
% 3.48/1.60  
% 3.48/1.60  Simplification rules
% 3.48/1.60  ----------------------
% 3.48/1.60  #Subsume      : 41
% 3.48/1.60  #Demod        : 89
% 3.48/1.60  #Tautology    : 117
% 3.48/1.60  #SimpNegUnit  : 38
% 3.48/1.60  #BackRed      : 2
% 3.48/1.60  
% 3.48/1.60  #Partial instantiations: 0
% 3.48/1.60  #Strategies tried      : 1
% 3.48/1.60  
% 3.48/1.60  Timing (in seconds)
% 3.48/1.60  ----------------------
% 3.48/1.61  Preprocessing        : 0.34
% 3.48/1.61  Parsing              : 0.17
% 3.48/1.61  CNF conversion       : 0.03
% 3.48/1.61  Main loop            : 0.49
% 3.48/1.61  Inferencing          : 0.18
% 3.48/1.61  Reduction            : 0.14
% 3.48/1.61  Demodulation         : 0.10
% 3.48/1.61  BG Simplification    : 0.03
% 3.48/1.61  Subsumption          : 0.10
% 3.48/1.61  Abstraction          : 0.04
% 3.48/1.61  MUC search           : 0.00
% 3.48/1.61  Cooper               : 0.00
% 3.48/1.61  Total                : 0.87
% 3.48/1.61  Index Insertion      : 0.00
% 3.48/1.61  Index Deletion       : 0.00
% 3.48/1.61  Index Matching       : 0.00
% 3.48/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
