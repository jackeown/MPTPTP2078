%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:18 EST 2020

% Result     : Theorem 3.47s
% Output     : CNFRefutation 3.47s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 109 expanded)
%              Number of leaves         :   30 (  50 expanded)
%              Depth                    :   17
%              Number of atoms          :   95 ( 204 expanded)
%              Number of equality atoms :   44 (  86 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_2 > #skF_4 > #skF_8 > #skF_3 > #skF_7 > #skF_5

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

tff(f_97,negated_conjecture,(
    ~ ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_58,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_43,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_81,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_94,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_tarski(B,C) )
     => ( A = k1_xboole_0
        | r1_tarski(B,k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_setfam_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

tff(c_84,plain,(
    k1_setfam_1(k1_tarski('#skF_8')) != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_54,plain,(
    ! [C_21] : r2_hidden(C_21,k1_tarski(C_21)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_610,plain,(
    ! [A_124,B_125,C_126] :
      ( r2_hidden('#skF_1'(A_124,B_125,C_126),A_124)
      | r2_hidden('#skF_2'(A_124,B_125,C_126),C_126)
      | k4_xboole_0(A_124,B_125) = C_126 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_16,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),B_2)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_682,plain,(
    ! [A_124,C_126] :
      ( r2_hidden('#skF_2'(A_124,A_124,C_126),C_126)
      | k4_xboole_0(A_124,A_124) = C_126 ) ),
    inference(resolution,[status(thm)],[c_610,c_16])).

tff(c_32,plain,(
    ! [E_16,A_10,C_12] : r2_hidden(E_16,k1_enumset1(A_10,E_16,C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_14,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_698,plain,(
    ! [A_127,B_128] :
      ( r2_hidden('#skF_2'(A_127,B_128,A_127),A_127)
      | k4_xboole_0(A_127,B_128) = A_127 ) ),
    inference(resolution,[status(thm)],[c_610,c_14])).

tff(c_26,plain,(
    ! [A_9] : k4_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_178,plain,(
    ! [D_68,B_69,A_70] :
      ( ~ r2_hidden(D_68,B_69)
      | ~ r2_hidden(D_68,k4_xboole_0(A_70,B_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_184,plain,(
    ! [D_68,A_9] :
      ( ~ r2_hidden(D_68,k1_xboole_0)
      | ~ r2_hidden(D_68,A_9) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_178])).

tff(c_784,plain,(
    ! [B_131,A_132] :
      ( ~ r2_hidden('#skF_2'(k1_xboole_0,B_131,k1_xboole_0),A_132)
      | k4_xboole_0(k1_xboole_0,B_131) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_698,c_184])).

tff(c_834,plain,(
    ! [B_137] : k4_xboole_0(k1_xboole_0,B_137) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_784])).

tff(c_74,plain,(
    ! [B_31,A_30] :
      ( ~ r2_hidden(B_31,A_30)
      | k4_xboole_0(A_30,k1_tarski(B_31)) != A_30 ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_875,plain,(
    ! [B_138] : ~ r2_hidden(B_138,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_834,c_74])).

tff(c_902,plain,(
    ! [A_124] : k4_xboole_0(A_124,A_124) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_682,c_875])).

tff(c_70,plain,(
    ! [B_29] : k4_xboole_0(k1_tarski(B_29),k1_tarski(B_29)) != k1_tarski(B_29) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_932,plain,(
    ! [B_29] : k1_tarski(B_29) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_902,c_70])).

tff(c_24,plain,(
    ! [B_8] : r1_tarski(B_8,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_273,plain,(
    ! [A_91,B_92] :
      ( r2_hidden('#skF_7'(A_91,B_92),A_91)
      | r1_tarski(B_92,k1_setfam_1(A_91))
      | k1_xboole_0 = A_91 ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_52,plain,(
    ! [C_21,A_17] :
      ( C_21 = A_17
      | ~ r2_hidden(C_21,k1_tarski(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_301,plain,(
    ! [A_17,B_92] :
      ( '#skF_7'(k1_tarski(A_17),B_92) = A_17
      | r1_tarski(B_92,k1_setfam_1(k1_tarski(A_17)))
      | k1_tarski(A_17) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_273,c_52])).

tff(c_1536,plain,(
    ! [A_184,B_185] :
      ( '#skF_7'(k1_tarski(A_184),B_185) = A_184
      | r1_tarski(B_185,k1_setfam_1(k1_tarski(A_184))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_932,c_301])).

tff(c_78,plain,(
    ! [B_33,A_32] :
      ( r1_tarski(k1_setfam_1(B_33),A_32)
      | ~ r2_hidden(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_161,plain,(
    ! [B_63,A_64] :
      ( B_63 = A_64
      | ~ r1_tarski(B_63,A_64)
      | ~ r1_tarski(A_64,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_166,plain,(
    ! [B_33,A_32] :
      ( k1_setfam_1(B_33) = A_32
      | ~ r1_tarski(A_32,k1_setfam_1(B_33))
      | ~ r2_hidden(A_32,B_33) ) ),
    inference(resolution,[status(thm)],[c_78,c_161])).

tff(c_1584,plain,(
    ! [A_192,B_193] :
      ( k1_setfam_1(k1_tarski(A_192)) = B_193
      | ~ r2_hidden(B_193,k1_tarski(A_192))
      | '#skF_7'(k1_tarski(A_192),B_193) = A_192 ) ),
    inference(resolution,[status(thm)],[c_1536,c_166])).

tff(c_1660,plain,(
    ! [C_194] :
      ( k1_setfam_1(k1_tarski(C_194)) = C_194
      | '#skF_7'(k1_tarski(C_194),C_194) = C_194 ) ),
    inference(resolution,[status(thm)],[c_54,c_1584])).

tff(c_1704,plain,(
    '#skF_7'(k1_tarski('#skF_8'),'#skF_8') = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_1660,c_84])).

tff(c_80,plain,(
    ! [B_35,A_34] :
      ( ~ r1_tarski(B_35,'#skF_7'(A_34,B_35))
      | r1_tarski(B_35,k1_setfam_1(A_34))
      | k1_xboole_0 = A_34 ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1717,plain,
    ( ~ r1_tarski('#skF_8','#skF_8')
    | r1_tarski('#skF_8',k1_setfam_1(k1_tarski('#skF_8')))
    | k1_tarski('#skF_8') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1704,c_80])).

tff(c_1725,plain,
    ( r1_tarski('#skF_8',k1_setfam_1(k1_tarski('#skF_8')))
    | k1_tarski('#skF_8') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1717])).

tff(c_1726,plain,(
    r1_tarski('#skF_8',k1_setfam_1(k1_tarski('#skF_8'))) ),
    inference(negUnitSimplification,[status(thm)],[c_932,c_1725])).

tff(c_1732,plain,
    ( k1_setfam_1(k1_tarski('#skF_8')) = '#skF_8'
    | ~ r2_hidden('#skF_8',k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_1726,c_166])).

tff(c_1740,plain,(
    k1_setfam_1(k1_tarski('#skF_8')) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1732])).

tff(c_1742,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_1740])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:26:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.47/1.54  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.47/1.55  
% 3.47/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.47/1.55  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_2 > #skF_4 > #skF_8 > #skF_3 > #skF_7 > #skF_5
% 3.47/1.55  
% 3.47/1.55  %Foreground sorts:
% 3.47/1.55  
% 3.47/1.55  
% 3.47/1.55  %Background operators:
% 3.47/1.55  
% 3.47/1.55  
% 3.47/1.55  %Foreground operators:
% 3.47/1.55  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.47/1.55  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.47/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.47/1.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.47/1.55  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.47/1.55  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.47/1.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.47/1.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.47/1.55  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.47/1.55  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.47/1.55  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.47/1.55  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.47/1.55  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 3.47/1.55  tff('#skF_8', type, '#skF_8': $i).
% 3.47/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.47/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.47/1.55  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.47/1.55  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 3.47/1.55  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.47/1.55  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.47/1.55  
% 3.47/1.56  tff(f_97, negated_conjecture, ~(![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_setfam_1)).
% 3.47/1.56  tff(f_65, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 3.47/1.56  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.47/1.56  tff(f_58, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 3.47/1.56  tff(f_43, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 3.47/1.56  tff(f_81, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 3.47/1.56  tff(f_76, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 3.47/1.56  tff(f_41, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.47/1.56  tff(f_94, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_tarski(B, C))) => ((A = k1_xboole_0) | r1_tarski(B, k1_setfam_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_setfam_1)).
% 3.47/1.56  tff(f_85, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_setfam_1)).
% 3.47/1.56  tff(c_84, plain, (k1_setfam_1(k1_tarski('#skF_8'))!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.47/1.56  tff(c_54, plain, (![C_21]: (r2_hidden(C_21, k1_tarski(C_21)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.47/1.56  tff(c_610, plain, (![A_124, B_125, C_126]: (r2_hidden('#skF_1'(A_124, B_125, C_126), A_124) | r2_hidden('#skF_2'(A_124, B_125, C_126), C_126) | k4_xboole_0(A_124, B_125)=C_126)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.47/1.56  tff(c_16, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), B_2) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.47/1.56  tff(c_682, plain, (![A_124, C_126]: (r2_hidden('#skF_2'(A_124, A_124, C_126), C_126) | k4_xboole_0(A_124, A_124)=C_126)), inference(resolution, [status(thm)], [c_610, c_16])).
% 3.47/1.56  tff(c_32, plain, (![E_16, A_10, C_12]: (r2_hidden(E_16, k1_enumset1(A_10, E_16, C_12)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.47/1.56  tff(c_14, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.47/1.56  tff(c_698, plain, (![A_127, B_128]: (r2_hidden('#skF_2'(A_127, B_128, A_127), A_127) | k4_xboole_0(A_127, B_128)=A_127)), inference(resolution, [status(thm)], [c_610, c_14])).
% 3.47/1.56  tff(c_26, plain, (![A_9]: (k4_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.47/1.56  tff(c_178, plain, (![D_68, B_69, A_70]: (~r2_hidden(D_68, B_69) | ~r2_hidden(D_68, k4_xboole_0(A_70, B_69)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.47/1.56  tff(c_184, plain, (![D_68, A_9]: (~r2_hidden(D_68, k1_xboole_0) | ~r2_hidden(D_68, A_9))), inference(superposition, [status(thm), theory('equality')], [c_26, c_178])).
% 3.47/1.56  tff(c_784, plain, (![B_131, A_132]: (~r2_hidden('#skF_2'(k1_xboole_0, B_131, k1_xboole_0), A_132) | k4_xboole_0(k1_xboole_0, B_131)=k1_xboole_0)), inference(resolution, [status(thm)], [c_698, c_184])).
% 3.47/1.56  tff(c_834, plain, (![B_137]: (k4_xboole_0(k1_xboole_0, B_137)=k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_784])).
% 3.47/1.56  tff(c_74, plain, (![B_31, A_30]: (~r2_hidden(B_31, A_30) | k4_xboole_0(A_30, k1_tarski(B_31))!=A_30)), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.47/1.56  tff(c_875, plain, (![B_138]: (~r2_hidden(B_138, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_834, c_74])).
% 3.47/1.56  tff(c_902, plain, (![A_124]: (k4_xboole_0(A_124, A_124)=k1_xboole_0)), inference(resolution, [status(thm)], [c_682, c_875])).
% 3.47/1.56  tff(c_70, plain, (![B_29]: (k4_xboole_0(k1_tarski(B_29), k1_tarski(B_29))!=k1_tarski(B_29))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.47/1.56  tff(c_932, plain, (![B_29]: (k1_tarski(B_29)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_902, c_70])).
% 3.47/1.56  tff(c_24, plain, (![B_8]: (r1_tarski(B_8, B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.47/1.56  tff(c_273, plain, (![A_91, B_92]: (r2_hidden('#skF_7'(A_91, B_92), A_91) | r1_tarski(B_92, k1_setfam_1(A_91)) | k1_xboole_0=A_91)), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.47/1.56  tff(c_52, plain, (![C_21, A_17]: (C_21=A_17 | ~r2_hidden(C_21, k1_tarski(A_17)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.47/1.56  tff(c_301, plain, (![A_17, B_92]: ('#skF_7'(k1_tarski(A_17), B_92)=A_17 | r1_tarski(B_92, k1_setfam_1(k1_tarski(A_17))) | k1_tarski(A_17)=k1_xboole_0)), inference(resolution, [status(thm)], [c_273, c_52])).
% 3.47/1.56  tff(c_1536, plain, (![A_184, B_185]: ('#skF_7'(k1_tarski(A_184), B_185)=A_184 | r1_tarski(B_185, k1_setfam_1(k1_tarski(A_184))))), inference(negUnitSimplification, [status(thm)], [c_932, c_301])).
% 3.47/1.56  tff(c_78, plain, (![B_33, A_32]: (r1_tarski(k1_setfam_1(B_33), A_32) | ~r2_hidden(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.47/1.56  tff(c_161, plain, (![B_63, A_64]: (B_63=A_64 | ~r1_tarski(B_63, A_64) | ~r1_tarski(A_64, B_63))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.47/1.56  tff(c_166, plain, (![B_33, A_32]: (k1_setfam_1(B_33)=A_32 | ~r1_tarski(A_32, k1_setfam_1(B_33)) | ~r2_hidden(A_32, B_33))), inference(resolution, [status(thm)], [c_78, c_161])).
% 3.47/1.56  tff(c_1584, plain, (![A_192, B_193]: (k1_setfam_1(k1_tarski(A_192))=B_193 | ~r2_hidden(B_193, k1_tarski(A_192)) | '#skF_7'(k1_tarski(A_192), B_193)=A_192)), inference(resolution, [status(thm)], [c_1536, c_166])).
% 3.47/1.56  tff(c_1660, plain, (![C_194]: (k1_setfam_1(k1_tarski(C_194))=C_194 | '#skF_7'(k1_tarski(C_194), C_194)=C_194)), inference(resolution, [status(thm)], [c_54, c_1584])).
% 3.47/1.56  tff(c_1704, plain, ('#skF_7'(k1_tarski('#skF_8'), '#skF_8')='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_1660, c_84])).
% 3.47/1.56  tff(c_80, plain, (![B_35, A_34]: (~r1_tarski(B_35, '#skF_7'(A_34, B_35)) | r1_tarski(B_35, k1_setfam_1(A_34)) | k1_xboole_0=A_34)), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.47/1.56  tff(c_1717, plain, (~r1_tarski('#skF_8', '#skF_8') | r1_tarski('#skF_8', k1_setfam_1(k1_tarski('#skF_8'))) | k1_tarski('#skF_8')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1704, c_80])).
% 3.47/1.56  tff(c_1725, plain, (r1_tarski('#skF_8', k1_setfam_1(k1_tarski('#skF_8'))) | k1_tarski('#skF_8')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_24, c_1717])).
% 3.47/1.56  tff(c_1726, plain, (r1_tarski('#skF_8', k1_setfam_1(k1_tarski('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_932, c_1725])).
% 3.47/1.56  tff(c_1732, plain, (k1_setfam_1(k1_tarski('#skF_8'))='#skF_8' | ~r2_hidden('#skF_8', k1_tarski('#skF_8'))), inference(resolution, [status(thm)], [c_1726, c_166])).
% 3.47/1.56  tff(c_1740, plain, (k1_setfam_1(k1_tarski('#skF_8'))='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1732])).
% 3.47/1.56  tff(c_1742, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_1740])).
% 3.47/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.47/1.56  
% 3.47/1.56  Inference rules
% 3.47/1.56  ----------------------
% 3.47/1.56  #Ref     : 0
% 3.47/1.56  #Sup     : 340
% 3.47/1.56  #Fact    : 0
% 3.47/1.56  #Define  : 0
% 3.47/1.56  #Split   : 0
% 3.47/1.56  #Chain   : 0
% 3.47/1.56  #Close   : 0
% 3.47/1.56  
% 3.47/1.56  Ordering : KBO
% 3.47/1.56  
% 3.47/1.56  Simplification rules
% 3.47/1.56  ----------------------
% 3.47/1.56  #Subsume      : 32
% 3.47/1.56  #Demod        : 109
% 3.47/1.56  #Tautology    : 142
% 3.47/1.56  #SimpNegUnit  : 34
% 3.47/1.56  #BackRed      : 2
% 3.47/1.56  
% 3.47/1.56  #Partial instantiations: 0
% 3.47/1.56  #Strategies tried      : 1
% 3.47/1.56  
% 3.47/1.56  Timing (in seconds)
% 3.47/1.56  ----------------------
% 3.60/1.57  Preprocessing        : 0.32
% 3.60/1.57  Parsing              : 0.16
% 3.60/1.57  CNF conversion       : 0.03
% 3.60/1.57  Main loop            : 0.48
% 3.60/1.57  Inferencing          : 0.17
% 3.60/1.57  Reduction            : 0.14
% 3.60/1.57  Demodulation         : 0.10
% 3.60/1.57  BG Simplification    : 0.03
% 3.60/1.57  Subsumption          : 0.10
% 3.60/1.57  Abstraction          : 0.04
% 3.60/1.57  MUC search           : 0.00
% 3.60/1.57  Cooper               : 0.00
% 3.60/1.57  Total                : 0.83
% 3.60/1.57  Index Insertion      : 0.00
% 3.60/1.57  Index Deletion       : 0.00
% 3.60/1.57  Index Matching       : 0.00
% 3.60/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
