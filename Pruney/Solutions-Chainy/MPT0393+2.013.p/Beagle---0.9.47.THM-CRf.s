%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:18 EST 2020

% Result     : Theorem 7.97s
% Output     : CNFRefutation 7.97s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 171 expanded)
%              Number of leaves         :   29 (  71 expanded)
%              Depth                    :   17
%              Number of atoms          :  112 ( 307 expanded)
%              Number of equality atoms :   57 ( 143 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_4 > #skF_8 > #skF_2 > #skF_3 > #skF_7 > #skF_1 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_106,negated_conjecture,(
    ~ ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_97,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_tarski(B,C) )
     => ( A = k1_xboole_0
        | r1_tarski(B,k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_setfam_1)).

tff(f_103,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(k1_setfam_1(B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_setfam_1)).

tff(c_84,plain,(
    k1_setfam_1(k1_tarski('#skF_8')) != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_46,plain,(
    ! [C_19] : r2_hidden(C_19,k1_tarski(C_19)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_14,plain,(
    ! [B_5] : r1_tarski(B_5,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_110,plain,(
    ! [A_58,B_59] :
      ( k4_xboole_0(A_58,B_59) = k1_xboole_0
      | ~ r1_tarski(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_122,plain,(
    ! [B_5] : k4_xboole_0(B_5,B_5) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_110])).

tff(c_206,plain,(
    ! [B_71,A_72] :
      ( ~ r2_hidden(B_71,A_72)
      | k4_xboole_0(A_72,k1_tarski(B_71)) != A_72 ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_216,plain,(
    ! [B_71] :
      ( ~ r2_hidden(B_71,k1_tarski(B_71))
      | k1_tarski(B_71) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_206])).

tff(c_220,plain,(
    ! [B_71] : k1_tarski(B_71) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_216])).

tff(c_1411,plain,(
    ! [A_159,B_160] :
      ( r2_hidden('#skF_1'(A_159,B_160),B_160)
      | r2_hidden('#skF_2'(A_159,B_160),A_159)
      | B_160 = A_159 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_123,plain,(
    ! [B_60] : k4_xboole_0(B_60,B_60) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_110])).

tff(c_70,plain,(
    ! [C_30,B_29] : ~ r2_hidden(C_30,k4_xboole_0(B_29,k1_tarski(C_30))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_128,plain,(
    ! [C_30] : ~ r2_hidden(C_30,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_70])).

tff(c_1463,plain,(
    ! [B_161] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_161),B_161)
      | k1_xboole_0 = B_161 ) ),
    inference(resolution,[status(thm)],[c_1411,c_128])).

tff(c_44,plain,(
    ! [C_19,A_15] :
      ( C_19 = A_15
      | ~ r2_hidden(C_19,k1_tarski(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1482,plain,(
    ! [A_15] :
      ( '#skF_1'(k1_xboole_0,k1_tarski(A_15)) = A_15
      | k1_tarski(A_15) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1463,c_44])).

tff(c_1490,plain,(
    ! [A_15] : '#skF_1'(k1_xboole_0,k1_tarski(A_15)) = A_15 ),
    inference(negUnitSimplification,[status(thm)],[c_220,c_1482])).

tff(c_1461,plain,(
    ! [B_160] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_160),B_160)
      | k1_xboole_0 = B_160 ) ),
    inference(resolution,[status(thm)],[c_1411,c_128])).

tff(c_452,plain,(
    ! [A_101,B_102] :
      ( r2_hidden('#skF_7'(A_101,B_102),A_101)
      | r1_tarski(B_102,k1_setfam_1(A_101))
      | k1_xboole_0 = A_101 ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_464,plain,(
    ! [A_15,B_102] :
      ( '#skF_7'(k1_tarski(A_15),B_102) = A_15
      | r1_tarski(B_102,k1_setfam_1(k1_tarski(A_15)))
      | k1_tarski(A_15) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_452,c_44])).

tff(c_471,plain,(
    ! [A_103,B_104] :
      ( '#skF_7'(k1_tarski(A_103),B_104) = A_103
      | r1_tarski(B_104,k1_setfam_1(k1_tarski(A_103))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_220,c_464])).

tff(c_18,plain,(
    ! [A_6,B_7] :
      ( k4_xboole_0(A_6,B_7) = k1_xboole_0
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_3940,plain,(
    ! [B_272,A_273] :
      ( k4_xboole_0(B_272,k1_setfam_1(k1_tarski(A_273))) = k1_xboole_0
      | '#skF_7'(k1_tarski(A_273),B_272) = A_273 ) ),
    inference(resolution,[status(thm)],[c_471,c_18])).

tff(c_302,plain,(
    ! [B_88,C_89,A_90] :
      ( r1_tarski(k1_setfam_1(B_88),C_89)
      | ~ r1_tarski(A_90,C_89)
      | ~ r2_hidden(A_90,B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_312,plain,(
    ! [B_91,B_92] :
      ( r1_tarski(k1_setfam_1(B_91),B_92)
      | ~ r2_hidden(B_92,B_91) ) ),
    inference(resolution,[status(thm)],[c_14,c_302])).

tff(c_16,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | k4_xboole_0(A_6,B_7) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_222,plain,(
    ! [B_74,A_75] :
      ( B_74 = A_75
      | ~ r1_tarski(B_74,A_75)
      | ~ r1_tarski(A_75,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_229,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | k4_xboole_0(A_6,B_7) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_16,c_222])).

tff(c_328,plain,(
    ! [B_91,B_92] :
      ( k1_setfam_1(B_91) = B_92
      | k4_xboole_0(B_92,k1_setfam_1(B_91)) != k1_xboole_0
      | ~ r2_hidden(B_92,B_91) ) ),
    inference(resolution,[status(thm)],[c_312,c_229])).

tff(c_15523,plain,(
    ! [A_474,B_475] :
      ( k1_setfam_1(k1_tarski(A_474)) = B_475
      | ~ r2_hidden(B_475,k1_tarski(A_474))
      | '#skF_7'(k1_tarski(A_474),B_475) = A_474 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3940,c_328])).

tff(c_15579,plain,(
    ! [A_474] :
      ( k1_setfam_1(k1_tarski(A_474)) = '#skF_1'(k1_xboole_0,k1_tarski(A_474))
      | '#skF_7'(k1_tarski(A_474),'#skF_1'(k1_xboole_0,k1_tarski(A_474))) = A_474
      | k1_tarski(A_474) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1461,c_15523])).

tff(c_15619,plain,(
    ! [A_474] :
      ( k1_setfam_1(k1_tarski(A_474)) = A_474
      | '#skF_7'(k1_tarski(A_474),A_474) = A_474
      | k1_tarski(A_474) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1490,c_1490,c_15579])).

tff(c_15629,plain,(
    ! [A_476] :
      ( k1_setfam_1(k1_tarski(A_476)) = A_476
      | '#skF_7'(k1_tarski(A_476),A_476) = A_476 ) ),
    inference(negUnitSimplification,[status(thm)],[c_220,c_15619])).

tff(c_15889,plain,(
    '#skF_7'(k1_tarski('#skF_8'),'#skF_8') = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_15629,c_84])).

tff(c_686,plain,(
    ! [B_123,A_124] :
      ( ~ r1_tarski(B_123,'#skF_7'(A_124,B_123))
      | r1_tarski(B_123,k1_setfam_1(A_124))
      | k1_xboole_0 = A_124 ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_704,plain,(
    ! [A_6,A_124] :
      ( r1_tarski(A_6,k1_setfam_1(A_124))
      | k1_xboole_0 = A_124
      | k4_xboole_0(A_6,'#skF_7'(A_124,A_6)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_16,c_686])).

tff(c_15909,plain,
    ( r1_tarski('#skF_8',k1_setfam_1(k1_tarski('#skF_8')))
    | k1_tarski('#skF_8') = k1_xboole_0
    | k4_xboole_0('#skF_8','#skF_8') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_15889,c_704])).

tff(c_15922,plain,
    ( r1_tarski('#skF_8',k1_setfam_1(k1_tarski('#skF_8')))
    | k1_tarski('#skF_8') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_15909])).

tff(c_15923,plain,(
    r1_tarski('#skF_8',k1_setfam_1(k1_tarski('#skF_8'))) ),
    inference(negUnitSimplification,[status(thm)],[c_220,c_15922])).

tff(c_10,plain,(
    ! [B_5,A_4] :
      ( B_5 = A_4
      | ~ r1_tarski(B_5,A_4)
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_330,plain,(
    ! [B_91,B_92] :
      ( k1_setfam_1(B_91) = B_92
      | ~ r1_tarski(B_92,k1_setfam_1(B_91))
      | ~ r2_hidden(B_92,B_91) ) ),
    inference(resolution,[status(thm)],[c_312,c_10])).

tff(c_15935,plain,
    ( k1_setfam_1(k1_tarski('#skF_8')) = '#skF_8'
    | ~ r2_hidden('#skF_8',k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_15923,c_330])).

tff(c_15957,plain,(
    k1_setfam_1(k1_tarski('#skF_8')) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_15935])).

tff(c_15959,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_15957])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:54:14 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.97/3.00  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.97/3.01  
% 7.97/3.01  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.97/3.01  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_4 > #skF_8 > #skF_2 > #skF_3 > #skF_7 > #skF_1 > #skF_5
% 7.97/3.01  
% 7.97/3.01  %Foreground sorts:
% 7.97/3.01  
% 7.97/3.01  
% 7.97/3.01  %Background operators:
% 7.97/3.01  
% 7.97/3.01  
% 7.97/3.01  %Foreground operators:
% 7.97/3.01  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 7.97/3.01  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.97/3.01  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.97/3.01  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.97/3.01  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.97/3.01  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.97/3.01  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.97/3.01  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.97/3.01  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.97/3.01  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.97/3.01  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 7.97/3.01  tff('#skF_8', type, '#skF_8': $i).
% 7.97/3.01  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.97/3.01  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.97/3.01  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.97/3.01  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 7.97/3.01  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 7.97/3.01  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.97/3.01  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 7.97/3.01  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 7.97/3.01  
% 7.97/3.02  tff(f_106, negated_conjecture, ~(![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_setfam_1)).
% 7.97/3.02  tff(f_64, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 7.97/3.02  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.97/3.02  tff(f_42, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 7.97/3.02  tff(f_88, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 7.97/3.02  tff(f_32, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 7.97/3.02  tff(f_83, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 7.97/3.02  tff(f_97, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_tarski(B, C))) => ((A = k1_xboole_0) | r1_tarski(B, k1_setfam_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_setfam_1)).
% 7.97/3.02  tff(f_103, axiom, (![A, B, C]: ((r2_hidden(A, B) & r1_tarski(A, C)) => r1_tarski(k1_setfam_1(B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_setfam_1)).
% 7.97/3.02  tff(c_84, plain, (k1_setfam_1(k1_tarski('#skF_8'))!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.97/3.02  tff(c_46, plain, (![C_19]: (r2_hidden(C_19, k1_tarski(C_19)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.97/3.02  tff(c_14, plain, (![B_5]: (r1_tarski(B_5, B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.97/3.02  tff(c_110, plain, (![A_58, B_59]: (k4_xboole_0(A_58, B_59)=k1_xboole_0 | ~r1_tarski(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.97/3.02  tff(c_122, plain, (![B_5]: (k4_xboole_0(B_5, B_5)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_110])).
% 7.97/3.02  tff(c_206, plain, (![B_71, A_72]: (~r2_hidden(B_71, A_72) | k4_xboole_0(A_72, k1_tarski(B_71))!=A_72)), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.97/3.02  tff(c_216, plain, (![B_71]: (~r2_hidden(B_71, k1_tarski(B_71)) | k1_tarski(B_71)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_122, c_206])).
% 7.97/3.02  tff(c_220, plain, (![B_71]: (k1_tarski(B_71)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_216])).
% 7.97/3.02  tff(c_1411, plain, (![A_159, B_160]: (r2_hidden('#skF_1'(A_159, B_160), B_160) | r2_hidden('#skF_2'(A_159, B_160), A_159) | B_160=A_159)), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.97/3.02  tff(c_123, plain, (![B_60]: (k4_xboole_0(B_60, B_60)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_110])).
% 7.97/3.02  tff(c_70, plain, (![C_30, B_29]: (~r2_hidden(C_30, k4_xboole_0(B_29, k1_tarski(C_30))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.97/3.02  tff(c_128, plain, (![C_30]: (~r2_hidden(C_30, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_123, c_70])).
% 7.97/3.02  tff(c_1463, plain, (![B_161]: (r2_hidden('#skF_1'(k1_xboole_0, B_161), B_161) | k1_xboole_0=B_161)), inference(resolution, [status(thm)], [c_1411, c_128])).
% 7.97/3.02  tff(c_44, plain, (![C_19, A_15]: (C_19=A_15 | ~r2_hidden(C_19, k1_tarski(A_15)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.97/3.02  tff(c_1482, plain, (![A_15]: ('#skF_1'(k1_xboole_0, k1_tarski(A_15))=A_15 | k1_tarski(A_15)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1463, c_44])).
% 7.97/3.02  tff(c_1490, plain, (![A_15]: ('#skF_1'(k1_xboole_0, k1_tarski(A_15))=A_15)), inference(negUnitSimplification, [status(thm)], [c_220, c_1482])).
% 7.97/3.02  tff(c_1461, plain, (![B_160]: (r2_hidden('#skF_1'(k1_xboole_0, B_160), B_160) | k1_xboole_0=B_160)), inference(resolution, [status(thm)], [c_1411, c_128])).
% 7.97/3.02  tff(c_452, plain, (![A_101, B_102]: (r2_hidden('#skF_7'(A_101, B_102), A_101) | r1_tarski(B_102, k1_setfam_1(A_101)) | k1_xboole_0=A_101)), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.97/3.03  tff(c_464, plain, (![A_15, B_102]: ('#skF_7'(k1_tarski(A_15), B_102)=A_15 | r1_tarski(B_102, k1_setfam_1(k1_tarski(A_15))) | k1_tarski(A_15)=k1_xboole_0)), inference(resolution, [status(thm)], [c_452, c_44])).
% 7.97/3.03  tff(c_471, plain, (![A_103, B_104]: ('#skF_7'(k1_tarski(A_103), B_104)=A_103 | r1_tarski(B_104, k1_setfam_1(k1_tarski(A_103))))), inference(negUnitSimplification, [status(thm)], [c_220, c_464])).
% 7.97/3.03  tff(c_18, plain, (![A_6, B_7]: (k4_xboole_0(A_6, B_7)=k1_xboole_0 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.97/3.03  tff(c_3940, plain, (![B_272, A_273]: (k4_xboole_0(B_272, k1_setfam_1(k1_tarski(A_273)))=k1_xboole_0 | '#skF_7'(k1_tarski(A_273), B_272)=A_273)), inference(resolution, [status(thm)], [c_471, c_18])).
% 7.97/3.03  tff(c_302, plain, (![B_88, C_89, A_90]: (r1_tarski(k1_setfam_1(B_88), C_89) | ~r1_tarski(A_90, C_89) | ~r2_hidden(A_90, B_88))), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.97/3.03  tff(c_312, plain, (![B_91, B_92]: (r1_tarski(k1_setfam_1(B_91), B_92) | ~r2_hidden(B_92, B_91))), inference(resolution, [status(thm)], [c_14, c_302])).
% 7.97/3.03  tff(c_16, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | k4_xboole_0(A_6, B_7)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.97/3.03  tff(c_222, plain, (![B_74, A_75]: (B_74=A_75 | ~r1_tarski(B_74, A_75) | ~r1_tarski(A_75, B_74))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.97/3.03  tff(c_229, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | k4_xboole_0(A_6, B_7)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_222])).
% 7.97/3.03  tff(c_328, plain, (![B_91, B_92]: (k1_setfam_1(B_91)=B_92 | k4_xboole_0(B_92, k1_setfam_1(B_91))!=k1_xboole_0 | ~r2_hidden(B_92, B_91))), inference(resolution, [status(thm)], [c_312, c_229])).
% 7.97/3.03  tff(c_15523, plain, (![A_474, B_475]: (k1_setfam_1(k1_tarski(A_474))=B_475 | ~r2_hidden(B_475, k1_tarski(A_474)) | '#skF_7'(k1_tarski(A_474), B_475)=A_474)), inference(superposition, [status(thm), theory('equality')], [c_3940, c_328])).
% 7.97/3.03  tff(c_15579, plain, (![A_474]: (k1_setfam_1(k1_tarski(A_474))='#skF_1'(k1_xboole_0, k1_tarski(A_474)) | '#skF_7'(k1_tarski(A_474), '#skF_1'(k1_xboole_0, k1_tarski(A_474)))=A_474 | k1_tarski(A_474)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1461, c_15523])).
% 7.97/3.03  tff(c_15619, plain, (![A_474]: (k1_setfam_1(k1_tarski(A_474))=A_474 | '#skF_7'(k1_tarski(A_474), A_474)=A_474 | k1_tarski(A_474)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1490, c_1490, c_15579])).
% 7.97/3.03  tff(c_15629, plain, (![A_476]: (k1_setfam_1(k1_tarski(A_476))=A_476 | '#skF_7'(k1_tarski(A_476), A_476)=A_476)), inference(negUnitSimplification, [status(thm)], [c_220, c_15619])).
% 7.97/3.03  tff(c_15889, plain, ('#skF_7'(k1_tarski('#skF_8'), '#skF_8')='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_15629, c_84])).
% 7.97/3.03  tff(c_686, plain, (![B_123, A_124]: (~r1_tarski(B_123, '#skF_7'(A_124, B_123)) | r1_tarski(B_123, k1_setfam_1(A_124)) | k1_xboole_0=A_124)), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.97/3.03  tff(c_704, plain, (![A_6, A_124]: (r1_tarski(A_6, k1_setfam_1(A_124)) | k1_xboole_0=A_124 | k4_xboole_0(A_6, '#skF_7'(A_124, A_6))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_686])).
% 7.97/3.03  tff(c_15909, plain, (r1_tarski('#skF_8', k1_setfam_1(k1_tarski('#skF_8'))) | k1_tarski('#skF_8')=k1_xboole_0 | k4_xboole_0('#skF_8', '#skF_8')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_15889, c_704])).
% 7.97/3.03  tff(c_15922, plain, (r1_tarski('#skF_8', k1_setfam_1(k1_tarski('#skF_8'))) | k1_tarski('#skF_8')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_122, c_15909])).
% 7.97/3.03  tff(c_15923, plain, (r1_tarski('#skF_8', k1_setfam_1(k1_tarski('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_220, c_15922])).
% 7.97/3.03  tff(c_10, plain, (![B_5, A_4]: (B_5=A_4 | ~r1_tarski(B_5, A_4) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.97/3.03  tff(c_330, plain, (![B_91, B_92]: (k1_setfam_1(B_91)=B_92 | ~r1_tarski(B_92, k1_setfam_1(B_91)) | ~r2_hidden(B_92, B_91))), inference(resolution, [status(thm)], [c_312, c_10])).
% 7.97/3.03  tff(c_15935, plain, (k1_setfam_1(k1_tarski('#skF_8'))='#skF_8' | ~r2_hidden('#skF_8', k1_tarski('#skF_8'))), inference(resolution, [status(thm)], [c_15923, c_330])).
% 7.97/3.03  tff(c_15957, plain, (k1_setfam_1(k1_tarski('#skF_8'))='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_15935])).
% 7.97/3.03  tff(c_15959, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_15957])).
% 7.97/3.03  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.97/3.03  
% 7.97/3.03  Inference rules
% 7.97/3.03  ----------------------
% 7.97/3.03  #Ref     : 0
% 7.97/3.03  #Sup     : 3972
% 7.97/3.03  #Fact    : 1
% 7.97/3.03  #Define  : 0
% 7.97/3.03  #Split   : 4
% 7.97/3.03  #Chain   : 0
% 7.97/3.03  #Close   : 0
% 7.97/3.03  
% 7.97/3.03  Ordering : KBO
% 7.97/3.03  
% 7.97/3.03  Simplification rules
% 7.97/3.03  ----------------------
% 7.97/3.03  #Subsume      : 1146
% 7.97/3.03  #Demod        : 2231
% 7.97/3.03  #Tautology    : 1659
% 7.97/3.03  #SimpNegUnit  : 126
% 7.97/3.03  #BackRed      : 0
% 7.97/3.03  
% 7.97/3.03  #Partial instantiations: 0
% 7.97/3.03  #Strategies tried      : 1
% 7.97/3.03  
% 7.97/3.03  Timing (in seconds)
% 7.97/3.03  ----------------------
% 7.97/3.03  Preprocessing        : 0.32
% 7.97/3.03  Parsing              : 0.16
% 7.97/3.03  CNF conversion       : 0.03
% 7.97/3.03  Main loop            : 1.94
% 7.97/3.03  Inferencing          : 0.53
% 7.97/3.03  Reduction            : 0.62
% 7.97/3.03  Demodulation         : 0.43
% 7.97/3.03  BG Simplification    : 0.07
% 7.97/3.03  Subsumption          : 0.60
% 7.97/3.03  Abstraction          : 0.09
% 7.97/3.03  MUC search           : 0.00
% 7.97/3.03  Cooper               : 0.00
% 7.97/3.03  Total                : 2.29
% 7.97/3.03  Index Insertion      : 0.00
% 7.97/3.03  Index Deletion       : 0.00
% 7.97/3.03  Index Matching       : 0.00
% 7.97/3.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------
