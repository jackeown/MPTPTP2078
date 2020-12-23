%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:25 EST 2020

% Result     : Theorem 5.08s
% Output     : CNFRefutation 5.08s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 119 expanded)
%              Number of leaves         :   16 (  47 expanded)
%              Depth                    :    6
%              Number of atoms          :  103 ( 262 expanded)
%              Number of equality atoms :   26 (  68 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > #nlpp > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff(f_58,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_xboole_0(A,B)
      <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_53,axiom,(
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

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_30,plain,
    ( ~ r1_xboole_0('#skF_4','#skF_5')
    | r1_xboole_0('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_33,plain,(
    ~ r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_24,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_3'(A_7,B_8),A_7)
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1597,plain,(
    ! [A_227,B_228] :
      ( r2_hidden('#skF_3'(A_227,B_228),B_228)
      | r1_xboole_0(A_227,B_228) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1544,plain,(
    ! [A_218,B_219] :
      ( r2_hidden('#skF_3'(A_218,B_219),B_219)
      | r1_xboole_0(A_218,B_219) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_28,plain,
    ( k4_xboole_0('#skF_4','#skF_5') = '#skF_4'
    | k4_xboole_0('#skF_6','#skF_7') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_36,plain,(
    k4_xboole_0('#skF_6','#skF_7') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_289,plain,(
    ! [A_71,B_72,C_73] :
      ( r2_hidden('#skF_1'(A_71,B_72,C_73),A_71)
      | r2_hidden('#skF_2'(A_71,B_72,C_73),C_73)
      | k4_xboole_0(A_71,B_72) = C_73 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_339,plain,(
    ! [A_71,B_72] :
      ( r2_hidden('#skF_2'(A_71,B_72,A_71),A_71)
      | k4_xboole_0(A_71,B_72) = A_71 ) ),
    inference(resolution,[status(thm)],[c_289,c_14])).

tff(c_12,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),A_1)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),A_1)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_895,plain,(
    ! [A_144,B_145,C_146] :
      ( ~ r2_hidden('#skF_1'(A_144,B_145,C_146),C_146)
      | r2_hidden('#skF_2'(A_144,B_145,C_146),B_145)
      | ~ r2_hidden('#skF_2'(A_144,B_145,C_146),A_144)
      | k4_xboole_0(A_144,B_145) = C_146 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1274,plain,(
    ! [A_204,B_205] :
      ( r2_hidden('#skF_2'(A_204,B_205,A_204),B_205)
      | ~ r2_hidden('#skF_2'(A_204,B_205,A_204),A_204)
      | k4_xboole_0(A_204,B_205) = A_204 ) ),
    inference(resolution,[status(thm)],[c_12,c_895])).

tff(c_1288,plain,(
    ! [A_206,B_207] :
      ( r2_hidden('#skF_2'(A_206,B_207,A_206),B_207)
      | k4_xboole_0(A_206,B_207) = A_206 ) ),
    inference(resolution,[status(thm)],[c_339,c_1274])).

tff(c_32,plain,
    ( k4_xboole_0('#skF_4','#skF_5') = '#skF_4'
    | r1_xboole_0('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_34,plain,(
    r1_xboole_0('#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_60,plain,(
    ! [A_22,B_23,C_24] :
      ( ~ r1_xboole_0(A_22,B_23)
      | ~ r2_hidden(C_24,B_23)
      | ~ r2_hidden(C_24,A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_63,plain,(
    ! [C_24] :
      ( ~ r2_hidden(C_24,'#skF_7')
      | ~ r2_hidden(C_24,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_34,c_60])).

tff(c_1487,plain,(
    ! [A_210] :
      ( ~ r2_hidden('#skF_2'(A_210,'#skF_7',A_210),'#skF_6')
      | k4_xboole_0(A_210,'#skF_7') = A_210 ) ),
    inference(resolution,[status(thm)],[c_1288,c_63])).

tff(c_1491,plain,(
    k4_xboole_0('#skF_6','#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_339,c_1487])).

tff(c_1497,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_36,c_1491])).

tff(c_1498,plain,(
    k4_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1503,plain,(
    ! [D_6] :
      ( ~ r2_hidden(D_6,'#skF_5')
      | ~ r2_hidden(D_6,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1498,c_4])).

tff(c_1577,plain,(
    ! [A_222] :
      ( ~ r2_hidden('#skF_3'(A_222,'#skF_5'),'#skF_4')
      | r1_xboole_0(A_222,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1544,c_1503])).

tff(c_1581,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_24,c_1577])).

tff(c_1585,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_33,c_33,c_1581])).

tff(c_1586,plain,(
    k4_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_1592,plain,(
    ! [D_223,B_224,A_225] :
      ( ~ r2_hidden(D_223,B_224)
      | ~ r2_hidden(D_223,k4_xboole_0(A_225,B_224)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1595,plain,(
    ! [D_223] :
      ( ~ r2_hidden(D_223,'#skF_5')
      | ~ r2_hidden(D_223,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1586,c_1592])).

tff(c_1634,plain,(
    ! [A_234] :
      ( ~ r2_hidden('#skF_3'(A_234,'#skF_5'),'#skF_4')
      | r1_xboole_0(A_234,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1597,c_1595])).

tff(c_1638,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_24,c_1634])).

tff(c_1642,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_33,c_33,c_1638])).

tff(c_1644,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_26,plain,
    ( ~ r1_xboole_0('#skF_4','#skF_5')
    | k4_xboole_0('#skF_6','#skF_7') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1647,plain,(
    k4_xboole_0('#skF_6','#skF_7') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1644,c_26])).

tff(c_1916,plain,(
    ! [A_290,B_291,C_292] :
      ( r2_hidden('#skF_1'(A_290,B_291,C_292),A_290)
      | r2_hidden('#skF_2'(A_290,B_291,C_292),C_292)
      | k4_xboole_0(A_290,B_291) = C_292 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1990,plain,(
    ! [A_290,B_291] :
      ( r2_hidden('#skF_2'(A_290,B_291,A_290),A_290)
      | k4_xboole_0(A_290,B_291) = A_290 ) ),
    inference(resolution,[status(thm)],[c_1916,c_14])).

tff(c_2667,plain,(
    ! [A_368,B_369,C_370] :
      ( ~ r2_hidden('#skF_1'(A_368,B_369,C_370),C_370)
      | r2_hidden('#skF_2'(A_368,B_369,C_370),B_369)
      | ~ r2_hidden('#skF_2'(A_368,B_369,C_370),A_368)
      | k4_xboole_0(A_368,B_369) = C_370 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_3201,plain,(
    ! [A_389,B_390] :
      ( r2_hidden('#skF_2'(A_389,B_390,A_389),B_390)
      | ~ r2_hidden('#skF_2'(A_389,B_390,A_389),A_389)
      | k4_xboole_0(A_389,B_390) = A_389 ) ),
    inference(resolution,[status(thm)],[c_12,c_2667])).

tff(c_3269,plain,(
    ! [A_396,B_397] :
      ( r2_hidden('#skF_2'(A_396,B_397,A_396),B_397)
      | k4_xboole_0(A_396,B_397) = A_396 ) ),
    inference(resolution,[status(thm)],[c_1990,c_3201])).

tff(c_1643,plain,(
    r1_xboole_0('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_1672,plain,(
    ! [A_245,B_246,C_247] :
      ( ~ r1_xboole_0(A_245,B_246)
      | ~ r2_hidden(C_247,B_246)
      | ~ r2_hidden(C_247,A_245) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1678,plain,(
    ! [C_247] :
      ( ~ r2_hidden(C_247,'#skF_7')
      | ~ r2_hidden(C_247,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1643,c_1672])).

tff(c_3520,plain,(
    ! [A_398] :
      ( ~ r2_hidden('#skF_2'(A_398,'#skF_7',A_398),'#skF_6')
      | k4_xboole_0(A_398,'#skF_7') = A_398 ) ),
    inference(resolution,[status(thm)],[c_3269,c_1678])).

tff(c_3524,plain,(
    k4_xboole_0('#skF_6','#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1990,c_3520])).

tff(c_3530,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1647,c_1647,c_3524])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n002.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 16:07:37 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.08/1.94  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.08/1.95  
% 5.08/1.95  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.08/1.95  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > #nlpp > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 5.08/1.95  
% 5.08/1.95  %Foreground sorts:
% 5.08/1.95  
% 5.08/1.95  
% 5.08/1.95  %Background operators:
% 5.08/1.95  
% 5.08/1.95  
% 5.08/1.95  %Foreground operators:
% 5.08/1.95  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.08/1.95  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.08/1.95  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.08/1.95  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.08/1.95  tff('#skF_7', type, '#skF_7': $i).
% 5.08/1.95  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.08/1.95  tff('#skF_5', type, '#skF_5': $i).
% 5.08/1.95  tff('#skF_6', type, '#skF_6': $i).
% 5.08/1.95  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.08/1.95  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.08/1.95  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.08/1.95  tff('#skF_4', type, '#skF_4': $i).
% 5.08/1.95  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.08/1.95  
% 5.08/1.96  tff(f_58, negated_conjecture, ~(![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 5.08/1.96  tff(f_53, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 5.08/1.96  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 5.08/1.96  tff(c_30, plain, (~r1_xboole_0('#skF_4', '#skF_5') | r1_xboole_0('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.08/1.96  tff(c_33, plain, (~r1_xboole_0('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_30])).
% 5.08/1.96  tff(c_24, plain, (![A_7, B_8]: (r2_hidden('#skF_3'(A_7, B_8), A_7) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.08/1.96  tff(c_1597, plain, (![A_227, B_228]: (r2_hidden('#skF_3'(A_227, B_228), B_228) | r1_xboole_0(A_227, B_228))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.08/1.96  tff(c_1544, plain, (![A_218, B_219]: (r2_hidden('#skF_3'(A_218, B_219), B_219) | r1_xboole_0(A_218, B_219))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.08/1.96  tff(c_28, plain, (k4_xboole_0('#skF_4', '#skF_5')='#skF_4' | k4_xboole_0('#skF_6', '#skF_7')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.08/1.96  tff(c_36, plain, (k4_xboole_0('#skF_6', '#skF_7')!='#skF_6'), inference(splitLeft, [status(thm)], [c_28])).
% 5.08/1.96  tff(c_289, plain, (![A_71, B_72, C_73]: (r2_hidden('#skF_1'(A_71, B_72, C_73), A_71) | r2_hidden('#skF_2'(A_71, B_72, C_73), C_73) | k4_xboole_0(A_71, B_72)=C_73)), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.08/1.96  tff(c_14, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.08/1.96  tff(c_339, plain, (![A_71, B_72]: (r2_hidden('#skF_2'(A_71, B_72, A_71), A_71) | k4_xboole_0(A_71, B_72)=A_71)), inference(resolution, [status(thm)], [c_289, c_14])).
% 5.08/1.96  tff(c_12, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), A_1) | r2_hidden('#skF_2'(A_1, B_2, C_3), B_2) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), A_1) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.08/1.96  tff(c_895, plain, (![A_144, B_145, C_146]: (~r2_hidden('#skF_1'(A_144, B_145, C_146), C_146) | r2_hidden('#skF_2'(A_144, B_145, C_146), B_145) | ~r2_hidden('#skF_2'(A_144, B_145, C_146), A_144) | k4_xboole_0(A_144, B_145)=C_146)), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.08/1.96  tff(c_1274, plain, (![A_204, B_205]: (r2_hidden('#skF_2'(A_204, B_205, A_204), B_205) | ~r2_hidden('#skF_2'(A_204, B_205, A_204), A_204) | k4_xboole_0(A_204, B_205)=A_204)), inference(resolution, [status(thm)], [c_12, c_895])).
% 5.08/1.96  tff(c_1288, plain, (![A_206, B_207]: (r2_hidden('#skF_2'(A_206, B_207, A_206), B_207) | k4_xboole_0(A_206, B_207)=A_206)), inference(resolution, [status(thm)], [c_339, c_1274])).
% 5.08/1.96  tff(c_32, plain, (k4_xboole_0('#skF_4', '#skF_5')='#skF_4' | r1_xboole_0('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.08/1.96  tff(c_34, plain, (r1_xboole_0('#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_32])).
% 5.08/1.96  tff(c_60, plain, (![A_22, B_23, C_24]: (~r1_xboole_0(A_22, B_23) | ~r2_hidden(C_24, B_23) | ~r2_hidden(C_24, A_22))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.08/1.96  tff(c_63, plain, (![C_24]: (~r2_hidden(C_24, '#skF_7') | ~r2_hidden(C_24, '#skF_6'))), inference(resolution, [status(thm)], [c_34, c_60])).
% 5.08/1.96  tff(c_1487, plain, (![A_210]: (~r2_hidden('#skF_2'(A_210, '#skF_7', A_210), '#skF_6') | k4_xboole_0(A_210, '#skF_7')=A_210)), inference(resolution, [status(thm)], [c_1288, c_63])).
% 5.08/1.96  tff(c_1491, plain, (k4_xboole_0('#skF_6', '#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_339, c_1487])).
% 5.08/1.96  tff(c_1497, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_36, c_1491])).
% 5.08/1.96  tff(c_1498, plain, (k4_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(splitRight, [status(thm)], [c_28])).
% 5.08/1.96  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.08/1.96  tff(c_1503, plain, (![D_6]: (~r2_hidden(D_6, '#skF_5') | ~r2_hidden(D_6, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1498, c_4])).
% 5.08/1.96  tff(c_1577, plain, (![A_222]: (~r2_hidden('#skF_3'(A_222, '#skF_5'), '#skF_4') | r1_xboole_0(A_222, '#skF_5'))), inference(resolution, [status(thm)], [c_1544, c_1503])).
% 5.08/1.96  tff(c_1581, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_24, c_1577])).
% 5.08/1.96  tff(c_1585, plain, $false, inference(negUnitSimplification, [status(thm)], [c_33, c_33, c_1581])).
% 5.08/1.96  tff(c_1586, plain, (k4_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(splitRight, [status(thm)], [c_32])).
% 5.08/1.96  tff(c_1592, plain, (![D_223, B_224, A_225]: (~r2_hidden(D_223, B_224) | ~r2_hidden(D_223, k4_xboole_0(A_225, B_224)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.08/1.96  tff(c_1595, plain, (![D_223]: (~r2_hidden(D_223, '#skF_5') | ~r2_hidden(D_223, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1586, c_1592])).
% 5.08/1.96  tff(c_1634, plain, (![A_234]: (~r2_hidden('#skF_3'(A_234, '#skF_5'), '#skF_4') | r1_xboole_0(A_234, '#skF_5'))), inference(resolution, [status(thm)], [c_1597, c_1595])).
% 5.08/1.96  tff(c_1638, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_24, c_1634])).
% 5.08/1.96  tff(c_1642, plain, $false, inference(negUnitSimplification, [status(thm)], [c_33, c_33, c_1638])).
% 5.08/1.96  tff(c_1644, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_30])).
% 5.08/1.96  tff(c_26, plain, (~r1_xboole_0('#skF_4', '#skF_5') | k4_xboole_0('#skF_6', '#skF_7')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.08/1.96  tff(c_1647, plain, (k4_xboole_0('#skF_6', '#skF_7')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1644, c_26])).
% 5.08/1.96  tff(c_1916, plain, (![A_290, B_291, C_292]: (r2_hidden('#skF_1'(A_290, B_291, C_292), A_290) | r2_hidden('#skF_2'(A_290, B_291, C_292), C_292) | k4_xboole_0(A_290, B_291)=C_292)), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.08/1.96  tff(c_1990, plain, (![A_290, B_291]: (r2_hidden('#skF_2'(A_290, B_291, A_290), A_290) | k4_xboole_0(A_290, B_291)=A_290)), inference(resolution, [status(thm)], [c_1916, c_14])).
% 5.08/1.96  tff(c_2667, plain, (![A_368, B_369, C_370]: (~r2_hidden('#skF_1'(A_368, B_369, C_370), C_370) | r2_hidden('#skF_2'(A_368, B_369, C_370), B_369) | ~r2_hidden('#skF_2'(A_368, B_369, C_370), A_368) | k4_xboole_0(A_368, B_369)=C_370)), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.08/1.96  tff(c_3201, plain, (![A_389, B_390]: (r2_hidden('#skF_2'(A_389, B_390, A_389), B_390) | ~r2_hidden('#skF_2'(A_389, B_390, A_389), A_389) | k4_xboole_0(A_389, B_390)=A_389)), inference(resolution, [status(thm)], [c_12, c_2667])).
% 5.08/1.96  tff(c_3269, plain, (![A_396, B_397]: (r2_hidden('#skF_2'(A_396, B_397, A_396), B_397) | k4_xboole_0(A_396, B_397)=A_396)), inference(resolution, [status(thm)], [c_1990, c_3201])).
% 5.08/1.96  tff(c_1643, plain, (r1_xboole_0('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_30])).
% 5.08/1.96  tff(c_1672, plain, (![A_245, B_246, C_247]: (~r1_xboole_0(A_245, B_246) | ~r2_hidden(C_247, B_246) | ~r2_hidden(C_247, A_245))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.08/1.96  tff(c_1678, plain, (![C_247]: (~r2_hidden(C_247, '#skF_7') | ~r2_hidden(C_247, '#skF_6'))), inference(resolution, [status(thm)], [c_1643, c_1672])).
% 5.08/1.96  tff(c_3520, plain, (![A_398]: (~r2_hidden('#skF_2'(A_398, '#skF_7', A_398), '#skF_6') | k4_xboole_0(A_398, '#skF_7')=A_398)), inference(resolution, [status(thm)], [c_3269, c_1678])).
% 5.08/1.96  tff(c_3524, plain, (k4_xboole_0('#skF_6', '#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_1990, c_3520])).
% 5.08/1.96  tff(c_3530, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1647, c_1647, c_3524])).
% 5.08/1.96  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.08/1.96  
% 5.08/1.96  Inference rules
% 5.08/1.96  ----------------------
% 5.08/1.96  #Ref     : 0
% 5.08/1.96  #Sup     : 793
% 5.08/1.96  #Fact    : 0
% 5.08/1.96  #Define  : 0
% 5.08/1.96  #Split   : 3
% 5.08/1.96  #Chain   : 0
% 5.08/1.96  #Close   : 0
% 5.08/1.96  
% 5.08/1.96  Ordering : KBO
% 5.08/1.96  
% 5.08/1.96  Simplification rules
% 5.08/1.96  ----------------------
% 5.08/1.96  #Subsume      : 155
% 5.08/1.96  #Demod        : 168
% 5.08/1.96  #Tautology    : 177
% 5.08/1.96  #SimpNegUnit  : 4
% 5.08/1.96  #BackRed      : 0
% 5.08/1.96  
% 5.08/1.96  #Partial instantiations: 0
% 5.08/1.96  #Strategies tried      : 1
% 5.08/1.96  
% 5.08/1.96  Timing (in seconds)
% 5.08/1.96  ----------------------
% 5.08/1.97  Preprocessing        : 0.28
% 5.08/1.97  Parsing              : 0.15
% 5.08/1.97  CNF conversion       : 0.02
% 5.08/1.97  Main loop            : 0.94
% 5.08/1.97  Inferencing          : 0.34
% 5.08/1.97  Reduction            : 0.24
% 5.08/1.97  Demodulation         : 0.17
% 5.08/1.97  BG Simplification    : 0.04
% 5.08/1.97  Subsumption          : 0.24
% 5.08/1.97  Abstraction          : 0.05
% 5.08/1.97  MUC search           : 0.00
% 5.08/1.97  Cooper               : 0.00
% 5.08/1.97  Total                : 1.25
% 5.08/1.97  Index Insertion      : 0.00
% 5.08/1.97  Index Deletion       : 0.00
% 5.08/1.97  Index Matching       : 0.00
% 5.08/1.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
