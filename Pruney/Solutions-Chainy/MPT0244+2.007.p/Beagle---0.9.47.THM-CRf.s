%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:57 EST 2020

% Result     : Theorem 2.87s
% Output     : CNFRefutation 2.87s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 178 expanded)
%              Number of leaves         :   25 (  65 expanded)
%              Depth                    :    7
%              Number of atoms          :  115 ( 315 expanded)
%              Number of equality atoms :   51 ( 163 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_46,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_72,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,k1_tarski(B))
      <=> ( A = k1_xboole_0
          | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_40,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_55,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_48,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_14,plain,(
    ! [B_9] : r1_tarski(B_9,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_44,plain,
    ( ~ r1_tarski('#skF_5',k1_tarski('#skF_6'))
    | k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_70,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_38,plain,(
    ! [A_22,B_23] :
      ( r1_tarski(k1_tarski(A_22),B_23)
      | ~ r2_hidden(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_40,plain,
    ( ~ r1_tarski('#skF_5',k1_tarski('#skF_6'))
    | k1_tarski('#skF_8') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_98,plain,(
    k1_tarski('#skF_8') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_50,plain,
    ( k1_tarski('#skF_6') = '#skF_5'
    | k1_xboole_0 = '#skF_5'
    | r1_tarski('#skF_7',k1_tarski('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_190,plain,(
    r1_tarski('#skF_7',k1_tarski('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( B_9 = A_8
      | ~ r1_tarski(B_9,A_8)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_192,plain,
    ( k1_tarski('#skF_8') = '#skF_7'
    | ~ r1_tarski(k1_tarski('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_190,c_10])).

tff(c_195,plain,(
    ~ r1_tarski(k1_tarski('#skF_8'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_192])).

tff(c_199,plain,(
    ~ r2_hidden('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_38,c_195])).

tff(c_8,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_171,plain,(
    ! [C_46,B_47,A_48] :
      ( r2_hidden(C_46,B_47)
      | ~ r2_hidden(C_46,A_48)
      | ~ r1_tarski(A_48,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_530,plain,(
    ! [A_509,B_510] :
      ( r2_hidden('#skF_2'(A_509),B_510)
      | ~ r1_tarski(A_509,B_510)
      | k1_xboole_0 = A_509 ) ),
    inference(resolution,[status(thm)],[c_8,c_171])).

tff(c_18,plain,(
    ! [C_15,A_11] :
      ( C_15 = A_11
      | ~ r2_hidden(C_15,k1_tarski(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_853,plain,(
    ! [A_620,A_621] :
      ( A_620 = '#skF_2'(A_621)
      | ~ r1_tarski(A_621,k1_tarski(A_620))
      | k1_xboole_0 = A_621 ) ),
    inference(resolution,[status(thm)],[c_530,c_18])).

tff(c_864,plain,
    ( '#skF_2'('#skF_7') = '#skF_8'
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_190,c_853])).

tff(c_880,plain,(
    '#skF_2'('#skF_7') = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_864])).

tff(c_891,plain,
    ( r2_hidden('#skF_8','#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_880,c_8])).

tff(c_896,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_199,c_891])).

tff(c_897,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_tarski('#skF_6') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_899,plain,(
    k1_tarski('#skF_6') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_897])).

tff(c_48,plain,
    ( ~ r1_tarski('#skF_5',k1_tarski('#skF_6'))
    | r1_tarski('#skF_7',k1_tarski('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_151,plain,(
    ~ r1_tarski('#skF_5',k1_tarski('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_900,plain,(
    ~ r1_tarski('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_899,c_151])).

tff(c_903,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_900])).

tff(c_904,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_897])).

tff(c_16,plain,(
    ! [A_10] : r1_tarski(k1_xboole_0,A_10) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_911,plain,(
    ! [A_10] : r1_tarski('#skF_5',A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_904,c_16])).

tff(c_918,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_911,c_151])).

tff(c_919,plain,(
    r1_tarski('#skF_7',k1_tarski('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_922,plain,
    ( k1_tarski('#skF_8') = '#skF_7'
    | ~ r1_tarski(k1_tarski('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_919,c_10])).

tff(c_925,plain,(
    ~ r1_tarski(k1_tarski('#skF_8'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_922])).

tff(c_932,plain,(
    ~ r2_hidden('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_38,c_925])).

tff(c_958,plain,(
    ! [C_660,B_661,A_662] :
      ( r2_hidden(C_660,B_661)
      | ~ r2_hidden(C_660,A_662)
      | ~ r1_tarski(A_662,B_661) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_977,plain,(
    ! [A_666,B_667] :
      ( r2_hidden('#skF_2'(A_666),B_667)
      | ~ r1_tarski(A_666,B_667)
      | k1_xboole_0 = A_666 ) ),
    inference(resolution,[status(thm)],[c_8,c_958])).

tff(c_1103,plain,(
    ! [A_673,A_674] :
      ( A_673 = '#skF_2'(A_674)
      | ~ r1_tarski(A_674,k1_tarski(A_673))
      | k1_xboole_0 = A_674 ) ),
    inference(resolution,[status(thm)],[c_977,c_18])).

tff(c_1113,plain,
    ( '#skF_2'('#skF_7') = '#skF_8'
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_919,c_1103])).

tff(c_1130,plain,(
    '#skF_2'('#skF_7') = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1113])).

tff(c_1141,plain,
    ( r2_hidden('#skF_8','#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_1130,c_8])).

tff(c_1146,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_932,c_1141])).

tff(c_1148,plain,(
    k1_tarski('#skF_8') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_42,plain,
    ( k1_tarski('#skF_6') = '#skF_5'
    | k1_xboole_0 = '#skF_5'
    | k1_tarski('#skF_8') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1245,plain,
    ( k1_tarski('#skF_6') = '#skF_5'
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1148,c_42])).

tff(c_1246,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_1245])).

tff(c_1250,plain,(
    ! [A_10] : r1_tarski('#skF_5',A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1246,c_16])).

tff(c_1147,plain,(
    ~ r1_tarski('#skF_5',k1_tarski('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_1257,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1250,c_1147])).

tff(c_1258,plain,(
    k1_tarski('#skF_6') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1245])).

tff(c_1261,plain,(
    ~ r1_tarski('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1258,c_1147])).

tff(c_1264,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1261])).

tff(c_1266,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_46,plain,
    ( k1_tarski('#skF_6') = '#skF_5'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1302,plain,
    ( k1_tarski('#skF_6') = '#skF_5'
    | '#skF_7' = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1266,c_1266,c_46])).

tff(c_1303,plain,(
    '#skF_7' = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_1302])).

tff(c_1267,plain,(
    ! [A_10] : r1_tarski('#skF_7',A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1266,c_16])).

tff(c_1305,plain,(
    ! [A_10] : r1_tarski('#skF_5',A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1303,c_1267])).

tff(c_1265,plain,(
    ~ r1_tarski('#skF_5',k1_tarski('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1317,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1305,c_1265])).

tff(c_1318,plain,(
    k1_tarski('#skF_6') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1302])).

tff(c_1320,plain,(
    ~ r1_tarski('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1318,c_1265])).

tff(c_1323,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1320])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:38:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.87/1.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.87/1.50  
% 2.87/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.87/1.50  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_1 > #skF_4
% 2.87/1.50  
% 2.87/1.50  %Foreground sorts:
% 2.87/1.50  
% 2.87/1.50  
% 2.87/1.50  %Background operators:
% 2.87/1.50  
% 2.87/1.50  
% 2.87/1.50  %Foreground operators:
% 2.87/1.50  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.87/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.87/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.87/1.50  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.87/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.87/1.50  tff('#skF_7', type, '#skF_7': $i).
% 2.87/1.50  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.87/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.87/1.50  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.87/1.50  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.87/1.50  tff('#skF_5', type, '#skF_5': $i).
% 2.87/1.50  tff('#skF_6', type, '#skF_6': $i).
% 2.87/1.50  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.87/1.50  tff('#skF_8', type, '#skF_8': $i).
% 2.87/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.87/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.87/1.50  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.87/1.50  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.87/1.50  
% 2.87/1.52  tff(f_46, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.87/1.52  tff(f_72, negated_conjecture, ~(![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_zfmisc_1)).
% 2.87/1.52  tff(f_65, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.87/1.52  tff(f_40, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.87/1.52  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.87/1.52  tff(f_55, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.87/1.52  tff(f_48, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.87/1.52  tff(c_14, plain, (![B_9]: (r1_tarski(B_9, B_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.87/1.52  tff(c_44, plain, (~r1_tarski('#skF_5', k1_tarski('#skF_6')) | k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.87/1.52  tff(c_70, plain, (k1_xboole_0!='#skF_7'), inference(splitLeft, [status(thm)], [c_44])).
% 2.87/1.52  tff(c_38, plain, (![A_22, B_23]: (r1_tarski(k1_tarski(A_22), B_23) | ~r2_hidden(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.87/1.52  tff(c_40, plain, (~r1_tarski('#skF_5', k1_tarski('#skF_6')) | k1_tarski('#skF_8')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.87/1.52  tff(c_98, plain, (k1_tarski('#skF_8')!='#skF_7'), inference(splitLeft, [status(thm)], [c_40])).
% 2.87/1.52  tff(c_50, plain, (k1_tarski('#skF_6')='#skF_5' | k1_xboole_0='#skF_5' | r1_tarski('#skF_7', k1_tarski('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.87/1.52  tff(c_190, plain, (r1_tarski('#skF_7', k1_tarski('#skF_8'))), inference(splitLeft, [status(thm)], [c_50])).
% 2.87/1.52  tff(c_10, plain, (![B_9, A_8]: (B_9=A_8 | ~r1_tarski(B_9, A_8) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.87/1.52  tff(c_192, plain, (k1_tarski('#skF_8')='#skF_7' | ~r1_tarski(k1_tarski('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_190, c_10])).
% 2.87/1.52  tff(c_195, plain, (~r1_tarski(k1_tarski('#skF_8'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_98, c_192])).
% 2.87/1.52  tff(c_199, plain, (~r2_hidden('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_38, c_195])).
% 2.87/1.52  tff(c_8, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.87/1.52  tff(c_171, plain, (![C_46, B_47, A_48]: (r2_hidden(C_46, B_47) | ~r2_hidden(C_46, A_48) | ~r1_tarski(A_48, B_47))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.87/1.52  tff(c_530, plain, (![A_509, B_510]: (r2_hidden('#skF_2'(A_509), B_510) | ~r1_tarski(A_509, B_510) | k1_xboole_0=A_509)), inference(resolution, [status(thm)], [c_8, c_171])).
% 2.87/1.52  tff(c_18, plain, (![C_15, A_11]: (C_15=A_11 | ~r2_hidden(C_15, k1_tarski(A_11)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.87/1.52  tff(c_853, plain, (![A_620, A_621]: (A_620='#skF_2'(A_621) | ~r1_tarski(A_621, k1_tarski(A_620)) | k1_xboole_0=A_621)), inference(resolution, [status(thm)], [c_530, c_18])).
% 2.87/1.52  tff(c_864, plain, ('#skF_2'('#skF_7')='#skF_8' | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_190, c_853])).
% 2.87/1.52  tff(c_880, plain, ('#skF_2'('#skF_7')='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_70, c_864])).
% 2.87/1.52  tff(c_891, plain, (r2_hidden('#skF_8', '#skF_7') | k1_xboole_0='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_880, c_8])).
% 2.87/1.52  tff(c_896, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_199, c_891])).
% 2.87/1.52  tff(c_897, plain, (k1_xboole_0='#skF_5' | k1_tarski('#skF_6')='#skF_5'), inference(splitRight, [status(thm)], [c_50])).
% 2.87/1.52  tff(c_899, plain, (k1_tarski('#skF_6')='#skF_5'), inference(splitLeft, [status(thm)], [c_897])).
% 2.87/1.52  tff(c_48, plain, (~r1_tarski('#skF_5', k1_tarski('#skF_6')) | r1_tarski('#skF_7', k1_tarski('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.87/1.52  tff(c_151, plain, (~r1_tarski('#skF_5', k1_tarski('#skF_6'))), inference(splitLeft, [status(thm)], [c_48])).
% 2.87/1.52  tff(c_900, plain, (~r1_tarski('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_899, c_151])).
% 2.87/1.52  tff(c_903, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_900])).
% 2.87/1.52  tff(c_904, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_897])).
% 2.87/1.52  tff(c_16, plain, (![A_10]: (r1_tarski(k1_xboole_0, A_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.87/1.52  tff(c_911, plain, (![A_10]: (r1_tarski('#skF_5', A_10))), inference(demodulation, [status(thm), theory('equality')], [c_904, c_16])).
% 2.87/1.52  tff(c_918, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_911, c_151])).
% 2.87/1.52  tff(c_919, plain, (r1_tarski('#skF_7', k1_tarski('#skF_8'))), inference(splitRight, [status(thm)], [c_48])).
% 2.87/1.52  tff(c_922, plain, (k1_tarski('#skF_8')='#skF_7' | ~r1_tarski(k1_tarski('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_919, c_10])).
% 2.87/1.52  tff(c_925, plain, (~r1_tarski(k1_tarski('#skF_8'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_98, c_922])).
% 2.87/1.52  tff(c_932, plain, (~r2_hidden('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_38, c_925])).
% 2.87/1.52  tff(c_958, plain, (![C_660, B_661, A_662]: (r2_hidden(C_660, B_661) | ~r2_hidden(C_660, A_662) | ~r1_tarski(A_662, B_661))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.87/1.52  tff(c_977, plain, (![A_666, B_667]: (r2_hidden('#skF_2'(A_666), B_667) | ~r1_tarski(A_666, B_667) | k1_xboole_0=A_666)), inference(resolution, [status(thm)], [c_8, c_958])).
% 2.87/1.52  tff(c_1103, plain, (![A_673, A_674]: (A_673='#skF_2'(A_674) | ~r1_tarski(A_674, k1_tarski(A_673)) | k1_xboole_0=A_674)), inference(resolution, [status(thm)], [c_977, c_18])).
% 2.87/1.52  tff(c_1113, plain, ('#skF_2'('#skF_7')='#skF_8' | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_919, c_1103])).
% 2.87/1.52  tff(c_1130, plain, ('#skF_2'('#skF_7')='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_70, c_1113])).
% 2.87/1.52  tff(c_1141, plain, (r2_hidden('#skF_8', '#skF_7') | k1_xboole_0='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_1130, c_8])).
% 2.87/1.52  tff(c_1146, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_932, c_1141])).
% 2.87/1.52  tff(c_1148, plain, (k1_tarski('#skF_8')='#skF_7'), inference(splitRight, [status(thm)], [c_40])).
% 2.87/1.52  tff(c_42, plain, (k1_tarski('#skF_6')='#skF_5' | k1_xboole_0='#skF_5' | k1_tarski('#skF_8')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.87/1.52  tff(c_1245, plain, (k1_tarski('#skF_6')='#skF_5' | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1148, c_42])).
% 2.87/1.52  tff(c_1246, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_1245])).
% 2.87/1.52  tff(c_1250, plain, (![A_10]: (r1_tarski('#skF_5', A_10))), inference(demodulation, [status(thm), theory('equality')], [c_1246, c_16])).
% 2.87/1.52  tff(c_1147, plain, (~r1_tarski('#skF_5', k1_tarski('#skF_6'))), inference(splitRight, [status(thm)], [c_40])).
% 2.87/1.52  tff(c_1257, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1250, c_1147])).
% 2.87/1.52  tff(c_1258, plain, (k1_tarski('#skF_6')='#skF_5'), inference(splitRight, [status(thm)], [c_1245])).
% 2.87/1.52  tff(c_1261, plain, (~r1_tarski('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1258, c_1147])).
% 2.87/1.52  tff(c_1264, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_1261])).
% 2.87/1.52  tff(c_1266, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_44])).
% 2.87/1.52  tff(c_46, plain, (k1_tarski('#skF_6')='#skF_5' | k1_xboole_0='#skF_5' | k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.87/1.52  tff(c_1302, plain, (k1_tarski('#skF_6')='#skF_5' | '#skF_7'='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1266, c_1266, c_46])).
% 2.87/1.52  tff(c_1303, plain, ('#skF_7'='#skF_5'), inference(splitLeft, [status(thm)], [c_1302])).
% 2.87/1.52  tff(c_1267, plain, (![A_10]: (r1_tarski('#skF_7', A_10))), inference(demodulation, [status(thm), theory('equality')], [c_1266, c_16])).
% 2.87/1.52  tff(c_1305, plain, (![A_10]: (r1_tarski('#skF_5', A_10))), inference(demodulation, [status(thm), theory('equality')], [c_1303, c_1267])).
% 2.87/1.52  tff(c_1265, plain, (~r1_tarski('#skF_5', k1_tarski('#skF_6'))), inference(splitRight, [status(thm)], [c_44])).
% 2.87/1.52  tff(c_1317, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1305, c_1265])).
% 2.87/1.52  tff(c_1318, plain, (k1_tarski('#skF_6')='#skF_5'), inference(splitRight, [status(thm)], [c_1302])).
% 2.87/1.52  tff(c_1320, plain, (~r1_tarski('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1318, c_1265])).
% 2.87/1.52  tff(c_1323, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_1320])).
% 2.87/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.87/1.52  
% 2.87/1.52  Inference rules
% 2.87/1.52  ----------------------
% 2.87/1.52  #Ref     : 0
% 2.87/1.52  #Sup     : 211
% 2.87/1.52  #Fact    : 0
% 2.87/1.52  #Define  : 0
% 2.87/1.52  #Split   : 8
% 2.87/1.52  #Chain   : 0
% 2.87/1.52  #Close   : 0
% 2.87/1.52  
% 2.87/1.52  Ordering : KBO
% 2.87/1.52  
% 2.87/1.52  Simplification rules
% 2.87/1.52  ----------------------
% 2.87/1.52  #Subsume      : 21
% 2.87/1.52  #Demod        : 62
% 2.87/1.52  #Tautology    : 94
% 2.87/1.52  #SimpNegUnit  : 23
% 2.87/1.52  #BackRed      : 20
% 2.87/1.52  
% 2.87/1.52  #Partial instantiations: 429
% 2.87/1.52  #Strategies tried      : 1
% 2.87/1.52  
% 2.87/1.52  Timing (in seconds)
% 2.87/1.52  ----------------------
% 2.87/1.52  Preprocessing        : 0.32
% 2.87/1.52  Parsing              : 0.17
% 2.87/1.52  CNF conversion       : 0.02
% 2.87/1.52  Main loop            : 0.37
% 2.87/1.52  Inferencing          : 0.17
% 2.87/1.52  Reduction            : 0.09
% 2.87/1.52  Demodulation         : 0.06
% 2.87/1.52  BG Simplification    : 0.02
% 2.87/1.52  Subsumption          : 0.06
% 2.87/1.52  Abstraction          : 0.02
% 2.87/1.52  MUC search           : 0.00
% 2.87/1.52  Cooper               : 0.00
% 2.87/1.52  Total                : 0.72
% 2.87/1.52  Index Insertion      : 0.00
% 2.87/1.52  Index Deletion       : 0.00
% 2.87/1.52  Index Matching       : 0.00
% 2.87/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
