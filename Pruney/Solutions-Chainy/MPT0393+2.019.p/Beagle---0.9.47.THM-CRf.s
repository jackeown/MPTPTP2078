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
% DateTime   : Thu Dec  3 09:57:19 EST 2020

% Result     : Theorem 4.66s
% Output     : CNFRefutation 4.66s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 281 expanded)
%              Number of leaves         :   27 ( 108 expanded)
%              Depth                    :   13
%              Number of atoms          :  114 ( 620 expanded)
%              Number of equality atoms :   57 ( 375 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_7 > #skF_2 > #skF_3 > #skF_5 > #skF_4

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_46,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_88,negated_conjecture,(
    ~ ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( ( A != k1_xboole_0
       => ( B = k1_setfam_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ! [D] :
                  ( r2_hidden(D,A)
                 => r2_hidden(C,D) ) ) ) )
      & ( A = k1_xboole_0
       => ( B = k1_setfam_1(A)
        <=> B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_setfam_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(c_30,plain,(
    ! [A_11] : k2_tarski(A_11,A_11) = k1_tarski(A_11) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_91,plain,(
    ! [D_45,B_46] : r2_hidden(D_45,k2_tarski(D_45,B_46)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_94,plain,(
    ! [A_11] : r2_hidden(A_11,k1_tarski(A_11)) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_91])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_101,plain,(
    ! [A_50,B_51] :
      ( k4_xboole_0(A_50,B_51) = k1_xboole_0
      | ~ r1_tarski(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_109,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_101])).

tff(c_42,plain,(
    ! [B_20] : k4_xboole_0(k1_tarski(B_20),k1_tarski(B_20)) != k1_tarski(B_20) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_111,plain,(
    ! [B_20] : k1_tarski(B_20) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_42])).

tff(c_72,plain,(
    k1_setfam_1(k1_tarski('#skF_7')) != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_60,plain,(
    ! [A_23,B_24,D_40] :
      ( r2_hidden('#skF_4'(A_23,B_24),D_40)
      | ~ r2_hidden(D_40,A_23)
      | r2_hidden('#skF_5'(A_23,B_24),B_24)
      | k1_setfam_1(A_23) = B_24
      | k1_xboole_0 = A_23 ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_665,plain,(
    ! [A_134,B_135,D_136] :
      ( r2_hidden('#skF_4'(A_134,B_135),D_136)
      | ~ r2_hidden(D_136,A_134)
      | r2_hidden('#skF_6'(A_134,B_135),A_134)
      | k1_setfam_1(A_134) = B_135
      | k1_xboole_0 = A_134 ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_54,plain,(
    ! [A_23,B_24] :
      ( ~ r2_hidden('#skF_4'(A_23,B_24),B_24)
      | r2_hidden('#skF_6'(A_23,B_24),A_23)
      | k1_setfam_1(A_23) = B_24
      | k1_xboole_0 = A_23 ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_749,plain,(
    ! [D_137,A_138] :
      ( ~ r2_hidden(D_137,A_138)
      | r2_hidden('#skF_6'(A_138,D_137),A_138)
      | k1_setfam_1(A_138) = D_137
      | k1_xboole_0 = A_138 ) ),
    inference(resolution,[status(thm)],[c_665,c_54])).

tff(c_218,plain,(
    ! [A_72,B_73] :
      ( k4_xboole_0(k1_tarski(A_72),k1_tarski(B_73)) = k1_tarski(A_72)
      | B_73 = A_72 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_46,plain,(
    ! [B_22,A_21] :
      ( ~ r2_hidden(B_22,A_21)
      | k4_xboole_0(A_21,k1_tarski(B_22)) != A_21 ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_244,plain,(
    ! [B_73,A_72] :
      ( ~ r2_hidden(B_73,k1_tarski(A_72))
      | B_73 = A_72 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_218,c_46])).

tff(c_774,plain,(
    ! [A_72,D_137] :
      ( '#skF_6'(k1_tarski(A_72),D_137) = A_72
      | ~ r2_hidden(D_137,k1_tarski(A_72))
      | k1_setfam_1(k1_tarski(A_72)) = D_137
      | k1_tarski(A_72) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_749,c_244])).

tff(c_790,plain,(
    ! [A_139,D_140] :
      ( '#skF_6'(k1_tarski(A_139),D_140) = A_139
      | ~ r2_hidden(D_140,k1_tarski(A_139))
      | k1_setfam_1(k1_tarski(A_139)) = D_140 ) ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_774])).

tff(c_836,plain,(
    ! [A_141] :
      ( '#skF_6'(k1_tarski(A_141),A_141) = A_141
      | k1_setfam_1(k1_tarski(A_141)) = A_141 ) ),
    inference(resolution,[status(thm)],[c_94,c_790])).

tff(c_892,plain,(
    '#skF_6'(k1_tarski('#skF_7'),'#skF_7') = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_836,c_72])).

tff(c_50,plain,(
    ! [A_23,B_24] :
      ( ~ r2_hidden('#skF_4'(A_23,B_24),B_24)
      | ~ r2_hidden('#skF_5'(A_23,B_24),'#skF_6'(A_23,B_24))
      | k1_setfam_1(A_23) = B_24
      | k1_xboole_0 = A_23 ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_905,plain,
    ( ~ r2_hidden('#skF_4'(k1_tarski('#skF_7'),'#skF_7'),'#skF_7')
    | ~ r2_hidden('#skF_5'(k1_tarski('#skF_7'),'#skF_7'),'#skF_7')
    | k1_setfam_1(k1_tarski('#skF_7')) = '#skF_7'
    | k1_tarski('#skF_7') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_892,c_50])).

tff(c_914,plain,
    ( ~ r2_hidden('#skF_4'(k1_tarski('#skF_7'),'#skF_7'),'#skF_7')
    | ~ r2_hidden('#skF_5'(k1_tarski('#skF_7'),'#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_72,c_905])).

tff(c_916,plain,(
    ~ r2_hidden('#skF_5'(k1_tarski('#skF_7'),'#skF_7'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_914])).

tff(c_1343,plain,(
    ! [D_40] :
      ( r2_hidden('#skF_4'(k1_tarski('#skF_7'),'#skF_7'),D_40)
      | ~ r2_hidden(D_40,k1_tarski('#skF_7'))
      | k1_setfam_1(k1_tarski('#skF_7')) = '#skF_7'
      | k1_tarski('#skF_7') = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_60,c_916])).

tff(c_1356,plain,(
    ! [D_1726] :
      ( r2_hidden('#skF_4'(k1_tarski('#skF_7'),'#skF_7'),D_1726)
      | ~ r2_hidden(D_1726,k1_tarski('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_72,c_1343])).

tff(c_58,plain,(
    ! [A_23,B_24] :
      ( ~ r2_hidden('#skF_4'(A_23,B_24),B_24)
      | r2_hidden('#skF_5'(A_23,B_24),B_24)
      | k1_setfam_1(A_23) = B_24
      | k1_xboole_0 = A_23 ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1346,plain,
    ( ~ r2_hidden('#skF_4'(k1_tarski('#skF_7'),'#skF_7'),'#skF_7')
    | k1_setfam_1(k1_tarski('#skF_7')) = '#skF_7'
    | k1_tarski('#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_58,c_916])).

tff(c_1352,plain,(
    ~ r2_hidden('#skF_4'(k1_tarski('#skF_7'),'#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_72,c_1346])).

tff(c_1359,plain,(
    ~ r2_hidden('#skF_7',k1_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_1356,c_1352])).

tff(c_1404,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_1359])).

tff(c_1406,plain,(
    r2_hidden('#skF_5'(k1_tarski('#skF_7'),'#skF_7'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_914])).

tff(c_3593,plain,(
    ! [A_7654,B_7655,D_7656] :
      ( r2_hidden('#skF_4'(A_7654,B_7655),D_7656)
      | ~ r2_hidden(D_7656,A_7654)
      | ~ r2_hidden('#skF_5'(A_7654,B_7655),'#skF_6'(A_7654,B_7655))
      | k1_setfam_1(A_7654) = B_7655
      | k1_xboole_0 = A_7654 ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_3601,plain,(
    ! [D_7656] :
      ( r2_hidden('#skF_4'(k1_tarski('#skF_7'),'#skF_7'),D_7656)
      | ~ r2_hidden(D_7656,k1_tarski('#skF_7'))
      | ~ r2_hidden('#skF_5'(k1_tarski('#skF_7'),'#skF_7'),'#skF_7')
      | k1_setfam_1(k1_tarski('#skF_7')) = '#skF_7'
      | k1_tarski('#skF_7') = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_892,c_3593])).

tff(c_3605,plain,(
    ! [D_7656] :
      ( r2_hidden('#skF_4'(k1_tarski('#skF_7'),'#skF_7'),D_7656)
      | ~ r2_hidden(D_7656,k1_tarski('#skF_7'))
      | k1_setfam_1(k1_tarski('#skF_7')) = '#skF_7'
      | k1_tarski('#skF_7') = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1406,c_3601])).

tff(c_3731,plain,(
    ! [D_7910] :
      ( r2_hidden('#skF_4'(k1_tarski('#skF_7'),'#skF_7'),D_7910)
      | ~ r2_hidden(D_7910,k1_tarski('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_72,c_3605])).

tff(c_1405,plain,(
    ~ r2_hidden('#skF_4'(k1_tarski('#skF_7'),'#skF_7'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_914])).

tff(c_3734,plain,(
    ~ r2_hidden('#skF_7',k1_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_3731,c_1405])).

tff(c_3812,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_3734])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:50:39 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.66/1.87  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.66/1.88  
% 4.66/1.88  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.66/1.88  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_7 > #skF_2 > #skF_3 > #skF_5 > #skF_4
% 4.66/1.88  
% 4.66/1.88  %Foreground sorts:
% 4.66/1.88  
% 4.66/1.88  
% 4.66/1.88  %Background operators:
% 4.66/1.88  
% 4.66/1.88  
% 4.66/1.88  %Foreground operators:
% 4.66/1.88  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 4.66/1.88  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.66/1.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.66/1.88  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.66/1.88  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.66/1.88  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.66/1.88  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.66/1.88  tff('#skF_7', type, '#skF_7': $i).
% 4.66/1.88  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.66/1.88  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.66/1.88  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.66/1.88  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.66/1.88  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.66/1.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.66/1.88  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.66/1.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.66/1.88  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 4.66/1.88  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.66/1.88  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.66/1.88  
% 4.66/1.91  tff(f_46, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 4.66/1.91  tff(f_44, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 4.66/1.91  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.66/1.91  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.66/1.91  tff(f_61, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 4.66/1.91  tff(f_88, negated_conjecture, ~(![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_setfam_1)).
% 4.66/1.91  tff(f_85, axiom, (![A, B]: ((~(A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (![D]: (r2_hidden(D, A) => r2_hidden(C, D))))))) & ((A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (B = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_setfam_1)).
% 4.66/1.91  tff(f_66, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 4.66/1.91  tff(c_30, plain, (![A_11]: (k2_tarski(A_11, A_11)=k1_tarski(A_11))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.66/1.91  tff(c_91, plain, (![D_45, B_46]: (r2_hidden(D_45, k2_tarski(D_45, B_46)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.66/1.91  tff(c_94, plain, (![A_11]: (r2_hidden(A_11, k1_tarski(A_11)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_91])).
% 4.66/1.91  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.66/1.91  tff(c_101, plain, (![A_50, B_51]: (k4_xboole_0(A_50, B_51)=k1_xboole_0 | ~r1_tarski(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.66/1.91  tff(c_109, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_101])).
% 4.66/1.91  tff(c_42, plain, (![B_20]: (k4_xboole_0(k1_tarski(B_20), k1_tarski(B_20))!=k1_tarski(B_20))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.66/1.91  tff(c_111, plain, (![B_20]: (k1_tarski(B_20)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_109, c_42])).
% 4.66/1.91  tff(c_72, plain, (k1_setfam_1(k1_tarski('#skF_7'))!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.66/1.91  tff(c_60, plain, (![A_23, B_24, D_40]: (r2_hidden('#skF_4'(A_23, B_24), D_40) | ~r2_hidden(D_40, A_23) | r2_hidden('#skF_5'(A_23, B_24), B_24) | k1_setfam_1(A_23)=B_24 | k1_xboole_0=A_23)), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.66/1.91  tff(c_665, plain, (![A_134, B_135, D_136]: (r2_hidden('#skF_4'(A_134, B_135), D_136) | ~r2_hidden(D_136, A_134) | r2_hidden('#skF_6'(A_134, B_135), A_134) | k1_setfam_1(A_134)=B_135 | k1_xboole_0=A_134)), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.66/1.91  tff(c_54, plain, (![A_23, B_24]: (~r2_hidden('#skF_4'(A_23, B_24), B_24) | r2_hidden('#skF_6'(A_23, B_24), A_23) | k1_setfam_1(A_23)=B_24 | k1_xboole_0=A_23)), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.66/1.91  tff(c_749, plain, (![D_137, A_138]: (~r2_hidden(D_137, A_138) | r2_hidden('#skF_6'(A_138, D_137), A_138) | k1_setfam_1(A_138)=D_137 | k1_xboole_0=A_138)), inference(resolution, [status(thm)], [c_665, c_54])).
% 4.66/1.91  tff(c_218, plain, (![A_72, B_73]: (k4_xboole_0(k1_tarski(A_72), k1_tarski(B_73))=k1_tarski(A_72) | B_73=A_72)), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.66/1.91  tff(c_46, plain, (![B_22, A_21]: (~r2_hidden(B_22, A_21) | k4_xboole_0(A_21, k1_tarski(B_22))!=A_21)), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.66/1.91  tff(c_244, plain, (![B_73, A_72]: (~r2_hidden(B_73, k1_tarski(A_72)) | B_73=A_72)), inference(superposition, [status(thm), theory('equality')], [c_218, c_46])).
% 4.66/1.91  tff(c_774, plain, (![A_72, D_137]: ('#skF_6'(k1_tarski(A_72), D_137)=A_72 | ~r2_hidden(D_137, k1_tarski(A_72)) | k1_setfam_1(k1_tarski(A_72))=D_137 | k1_tarski(A_72)=k1_xboole_0)), inference(resolution, [status(thm)], [c_749, c_244])).
% 4.66/1.91  tff(c_790, plain, (![A_139, D_140]: ('#skF_6'(k1_tarski(A_139), D_140)=A_139 | ~r2_hidden(D_140, k1_tarski(A_139)) | k1_setfam_1(k1_tarski(A_139))=D_140)), inference(negUnitSimplification, [status(thm)], [c_111, c_774])).
% 4.66/1.91  tff(c_836, plain, (![A_141]: ('#skF_6'(k1_tarski(A_141), A_141)=A_141 | k1_setfam_1(k1_tarski(A_141))=A_141)), inference(resolution, [status(thm)], [c_94, c_790])).
% 4.66/1.91  tff(c_892, plain, ('#skF_6'(k1_tarski('#skF_7'), '#skF_7')='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_836, c_72])).
% 4.66/1.91  tff(c_50, plain, (![A_23, B_24]: (~r2_hidden('#skF_4'(A_23, B_24), B_24) | ~r2_hidden('#skF_5'(A_23, B_24), '#skF_6'(A_23, B_24)) | k1_setfam_1(A_23)=B_24 | k1_xboole_0=A_23)), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.66/1.91  tff(c_905, plain, (~r2_hidden('#skF_4'(k1_tarski('#skF_7'), '#skF_7'), '#skF_7') | ~r2_hidden('#skF_5'(k1_tarski('#skF_7'), '#skF_7'), '#skF_7') | k1_setfam_1(k1_tarski('#skF_7'))='#skF_7' | k1_tarski('#skF_7')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_892, c_50])).
% 4.66/1.91  tff(c_914, plain, (~r2_hidden('#skF_4'(k1_tarski('#skF_7'), '#skF_7'), '#skF_7') | ~r2_hidden('#skF_5'(k1_tarski('#skF_7'), '#skF_7'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_111, c_72, c_905])).
% 4.66/1.91  tff(c_916, plain, (~r2_hidden('#skF_5'(k1_tarski('#skF_7'), '#skF_7'), '#skF_7')), inference(splitLeft, [status(thm)], [c_914])).
% 4.66/1.91  tff(c_1343, plain, (![D_40]: (r2_hidden('#skF_4'(k1_tarski('#skF_7'), '#skF_7'), D_40) | ~r2_hidden(D_40, k1_tarski('#skF_7')) | k1_setfam_1(k1_tarski('#skF_7'))='#skF_7' | k1_tarski('#skF_7')=k1_xboole_0)), inference(resolution, [status(thm)], [c_60, c_916])).
% 4.66/1.91  tff(c_1356, plain, (![D_1726]: (r2_hidden('#skF_4'(k1_tarski('#skF_7'), '#skF_7'), D_1726) | ~r2_hidden(D_1726, k1_tarski('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_111, c_72, c_1343])).
% 4.66/1.91  tff(c_58, plain, (![A_23, B_24]: (~r2_hidden('#skF_4'(A_23, B_24), B_24) | r2_hidden('#skF_5'(A_23, B_24), B_24) | k1_setfam_1(A_23)=B_24 | k1_xboole_0=A_23)), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.66/1.91  tff(c_1346, plain, (~r2_hidden('#skF_4'(k1_tarski('#skF_7'), '#skF_7'), '#skF_7') | k1_setfam_1(k1_tarski('#skF_7'))='#skF_7' | k1_tarski('#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_58, c_916])).
% 4.66/1.91  tff(c_1352, plain, (~r2_hidden('#skF_4'(k1_tarski('#skF_7'), '#skF_7'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_111, c_72, c_1346])).
% 4.66/1.91  tff(c_1359, plain, (~r2_hidden('#skF_7', k1_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_1356, c_1352])).
% 4.66/1.91  tff(c_1404, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_1359])).
% 4.66/1.91  tff(c_1406, plain, (r2_hidden('#skF_5'(k1_tarski('#skF_7'), '#skF_7'), '#skF_7')), inference(splitRight, [status(thm)], [c_914])).
% 4.66/1.91  tff(c_3593, plain, (![A_7654, B_7655, D_7656]: (r2_hidden('#skF_4'(A_7654, B_7655), D_7656) | ~r2_hidden(D_7656, A_7654) | ~r2_hidden('#skF_5'(A_7654, B_7655), '#skF_6'(A_7654, B_7655)) | k1_setfam_1(A_7654)=B_7655 | k1_xboole_0=A_7654)), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.66/1.91  tff(c_3601, plain, (![D_7656]: (r2_hidden('#skF_4'(k1_tarski('#skF_7'), '#skF_7'), D_7656) | ~r2_hidden(D_7656, k1_tarski('#skF_7')) | ~r2_hidden('#skF_5'(k1_tarski('#skF_7'), '#skF_7'), '#skF_7') | k1_setfam_1(k1_tarski('#skF_7'))='#skF_7' | k1_tarski('#skF_7')=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_892, c_3593])).
% 4.66/1.91  tff(c_3605, plain, (![D_7656]: (r2_hidden('#skF_4'(k1_tarski('#skF_7'), '#skF_7'), D_7656) | ~r2_hidden(D_7656, k1_tarski('#skF_7')) | k1_setfam_1(k1_tarski('#skF_7'))='#skF_7' | k1_tarski('#skF_7')=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1406, c_3601])).
% 4.66/1.91  tff(c_3731, plain, (![D_7910]: (r2_hidden('#skF_4'(k1_tarski('#skF_7'), '#skF_7'), D_7910) | ~r2_hidden(D_7910, k1_tarski('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_111, c_72, c_3605])).
% 4.66/1.91  tff(c_1405, plain, (~r2_hidden('#skF_4'(k1_tarski('#skF_7'), '#skF_7'), '#skF_7')), inference(splitRight, [status(thm)], [c_914])).
% 4.66/1.91  tff(c_3734, plain, (~r2_hidden('#skF_7', k1_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_3731, c_1405])).
% 4.66/1.91  tff(c_3812, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_3734])).
% 4.66/1.91  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.66/1.91  
% 4.66/1.91  Inference rules
% 4.66/1.91  ----------------------
% 4.66/1.91  #Ref     : 0
% 4.66/1.91  #Sup     : 433
% 4.66/1.91  #Fact    : 8
% 4.66/1.91  #Define  : 0
% 4.66/1.91  #Split   : 3
% 4.66/1.91  #Chain   : 0
% 4.66/1.91  #Close   : 0
% 4.66/1.91  
% 4.66/1.91  Ordering : KBO
% 4.66/1.91  
% 4.66/1.91  Simplification rules
% 4.66/1.91  ----------------------
% 4.66/1.91  #Subsume      : 69
% 4.66/1.91  #Demod        : 106
% 4.66/1.91  #Tautology    : 108
% 4.66/1.91  #SimpNegUnit  : 71
% 4.66/1.91  #BackRed      : 30
% 4.66/1.91  
% 4.66/1.91  #Partial instantiations: 3892
% 4.66/1.91  #Strategies tried      : 1
% 4.66/1.91  
% 4.66/1.91  Timing (in seconds)
% 4.66/1.91  ----------------------
% 4.66/1.91  Preprocessing        : 0.34
% 4.66/1.91  Parsing              : 0.17
% 4.66/1.91  CNF conversion       : 0.03
% 4.66/1.91  Main loop            : 0.76
% 4.66/1.91  Inferencing          : 0.38
% 4.66/1.91  Reduction            : 0.17
% 4.66/1.91  Demodulation         : 0.11
% 4.66/1.91  BG Simplification    : 0.03
% 4.66/1.91  Subsumption          : 0.13
% 4.66/1.91  Abstraction          : 0.04
% 4.66/1.92  MUC search           : 0.00
% 4.66/1.92  Cooper               : 0.00
% 4.66/1.92  Total                : 1.14
% 4.66/1.92  Index Insertion      : 0.00
% 4.66/1.92  Index Deletion       : 0.00
% 4.66/1.92  Index Matching       : 0.00
% 4.66/1.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
