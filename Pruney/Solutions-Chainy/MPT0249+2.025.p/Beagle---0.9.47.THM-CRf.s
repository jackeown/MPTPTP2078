%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:27 EST 2020

% Result     : Theorem 3.16s
% Output     : CNFRefutation 3.16s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 318 expanded)
%              Number of leaves         :   31 ( 121 expanded)
%              Depth                    :   14
%              Number of atoms          :  112 ( 664 expanded)
%              Number of equality atoms :   39 ( 237 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_6 > #skF_4 > #skF_7 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_1 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(f_93,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & B != C
          & B != k1_xboole_0
          & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_49,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_70,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_68,plain,(
    '#skF_9' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_70,plain,(
    k2_xboole_0('#skF_8','#skF_9') = k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_153,plain,(
    ! [D_54,A_55,B_56] :
      ( ~ r2_hidden(D_54,A_55)
      | r2_hidden(D_54,k2_xboole_0(A_55,B_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_156,plain,(
    ! [D_54] :
      ( ~ r2_hidden(D_54,'#skF_8')
      | r2_hidden(D_54,k1_tarski('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_153])).

tff(c_234,plain,(
    ! [A_62,B_63] :
      ( ~ r2_hidden('#skF_1'(A_62,B_63),B_63)
      | r1_tarski(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_588,plain,(
    ! [A_91] :
      ( r1_tarski(A_91,k1_tarski('#skF_7'))
      | ~ r2_hidden('#skF_1'(A_91,k1_tarski('#skF_7')),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_156,c_234])).

tff(c_593,plain,(
    r1_tarski('#skF_8',k1_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_6,c_588])).

tff(c_28,plain,(
    ! [B_15,A_14] :
      ( B_15 = A_14
      | ~ r1_tarski(B_15,A_14)
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_600,plain,
    ( k1_tarski('#skF_7') = '#skF_8'
    | ~ r1_tarski(k1_tarski('#skF_7'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_593,c_28])).

tff(c_680,plain,(
    ~ r1_tarski(k1_tarski('#skF_7'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_600])).

tff(c_66,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_26,plain,(
    ! [A_12] :
      ( r2_hidden('#skF_4'(A_12),A_12)
      | k1_xboole_0 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_194,plain,(
    ! [D_59] :
      ( ~ r2_hidden(D_59,'#skF_8')
      | r2_hidden(D_59,k1_tarski('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_153])).

tff(c_42,plain,(
    ! [C_27,A_23] :
      ( C_27 = A_23
      | ~ r2_hidden(C_27,k1_tarski(A_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_199,plain,(
    ! [D_60] :
      ( D_60 = '#skF_7'
      | ~ r2_hidden(D_60,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_194,c_42])).

tff(c_203,plain,
    ( '#skF_4'('#skF_8') = '#skF_7'
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_26,c_199])).

tff(c_206,plain,(
    '#skF_4'('#skF_8') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_203])).

tff(c_210,plain,
    ( r2_hidden('#skF_7','#skF_8')
    | k1_xboole_0 = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_26])).

tff(c_213,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_210])).

tff(c_403,plain,(
    ! [A_79,B_80] :
      ( r2_hidden('#skF_1'(A_79,B_80),A_79)
      | r1_tarski(A_79,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_917,plain,(
    ! [A_115,B_116] :
      ( '#skF_1'(k1_tarski(A_115),B_116) = A_115
      | r1_tarski(k1_tarski(A_115),B_116) ) ),
    inference(resolution,[status(thm)],[c_403,c_42])).

tff(c_941,plain,(
    '#skF_1'(k1_tarski('#skF_7'),'#skF_8') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_917,c_680])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_952,plain,
    ( ~ r2_hidden('#skF_7','#skF_8')
    | r1_tarski(k1_tarski('#skF_7'),'#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_941,c_4])).

tff(c_958,plain,(
    r1_tarski(k1_tarski('#skF_7'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_952])).

tff(c_960,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_680,c_958])).

tff(c_961,plain,(
    k1_tarski('#skF_7') = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_600])).

tff(c_245,plain,(
    ! [D_64,B_65,A_66] :
      ( ~ r2_hidden(D_64,B_65)
      | r2_hidden(D_64,k2_xboole_0(A_66,B_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_342,plain,(
    ! [D_73] :
      ( ~ r2_hidden(D_73,'#skF_9')
      | r2_hidden(D_73,k1_tarski('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_245])).

tff(c_437,plain,(
    ! [A_83] :
      ( r1_tarski(A_83,k1_tarski('#skF_7'))
      | ~ r2_hidden('#skF_1'(A_83,k1_tarski('#skF_7')),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_342,c_4])).

tff(c_442,plain,(
    r1_tarski('#skF_9',k1_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_6,c_437])).

tff(c_445,plain,
    ( k1_tarski('#skF_7') = '#skF_9'
    | ~ r1_tarski(k1_tarski('#skF_7'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_442,c_28])).

tff(c_446,plain,(
    ~ r1_tarski(k1_tarski('#skF_7'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_445])).

tff(c_966,plain,(
    ~ r1_tarski('#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_961,c_446])).

tff(c_64,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_352,plain,(
    ! [D_74] :
      ( D_74 = '#skF_7'
      | ~ r2_hidden(D_74,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_342,c_42])).

tff(c_356,plain,
    ( '#skF_4'('#skF_9') = '#skF_7'
    | k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_26,c_352])).

tff(c_359,plain,(
    '#skF_4'('#skF_9') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_356])).

tff(c_363,plain,
    ( r2_hidden('#skF_7','#skF_9')
    | k1_xboole_0 = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_359,c_26])).

tff(c_366,plain,(
    r2_hidden('#skF_7','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_363])).

tff(c_198,plain,(
    ! [D_59] :
      ( D_59 = '#skF_7'
      | ~ r2_hidden(D_59,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_194,c_42])).

tff(c_427,plain,(
    ! [B_80] :
      ( '#skF_1'('#skF_8',B_80) = '#skF_7'
      | r1_tarski('#skF_8',B_80) ) ),
    inference(resolution,[status(thm)],[c_403,c_198])).

tff(c_1017,plain,(
    '#skF_1'('#skF_8','#skF_9') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_427,c_966])).

tff(c_1091,plain,
    ( ~ r2_hidden('#skF_7','#skF_9')
    | r1_tarski('#skF_8','#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_1017,c_4])).

tff(c_1097,plain,(
    r1_tarski('#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_366,c_1091])).

tff(c_1099,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_966,c_1097])).

tff(c_1100,plain,(
    k1_tarski('#skF_7') = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_445])).

tff(c_243,plain,(
    ! [A_62] :
      ( r1_tarski(A_62,k1_tarski('#skF_7'))
      | ~ r2_hidden('#skF_1'(A_62,k1_tarski('#skF_7')),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_156,c_234])).

tff(c_1299,plain,(
    ! [A_129] :
      ( r1_tarski(A_129,'#skF_9')
      | ~ r2_hidden('#skF_1'(A_129,'#skF_9'),'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1100,c_1100,c_243])).

tff(c_1304,plain,(
    r1_tarski('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_6,c_1299])).

tff(c_1306,plain,
    ( '#skF_9' = '#skF_8'
    | ~ r1_tarski('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_1304,c_28])).

tff(c_1309,plain,(
    ~ r1_tarski('#skF_9','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1306])).

tff(c_351,plain,(
    ! [D_73] :
      ( D_73 = '#skF_7'
      | ~ r2_hidden(D_73,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_342,c_42])).

tff(c_423,plain,(
    ! [B_80] :
      ( '#skF_1'('#skF_9',B_80) = '#skF_7'
      | r1_tarski('#skF_9',B_80) ) ),
    inference(resolution,[status(thm)],[c_403,c_351])).

tff(c_1313,plain,(
    '#skF_1'('#skF_9','#skF_8') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_423,c_1309])).

tff(c_1320,plain,
    ( ~ r2_hidden('#skF_7','#skF_8')
    | r1_tarski('#skF_9','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_1313,c_4])).

tff(c_1326,plain,(
    r1_tarski('#skF_9','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_1320])).

tff(c_1328,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1309,c_1326])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:34:10 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.16/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.47  
% 3.16/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.47  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_6 > #skF_4 > #skF_7 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_1 > #skF_5
% 3.16/1.47  
% 3.16/1.47  %Foreground sorts:
% 3.16/1.47  
% 3.16/1.47  
% 3.16/1.47  %Background operators:
% 3.16/1.47  
% 3.16/1.47  
% 3.16/1.47  %Foreground operators:
% 3.16/1.47  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.16/1.47  tff('#skF_4', type, '#skF_4': $i > $i).
% 3.16/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.16/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.16/1.47  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.16/1.47  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.16/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.16/1.47  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.16/1.47  tff('#skF_7', type, '#skF_7': $i).
% 3.16/1.47  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.16/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.16/1.47  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.16/1.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.16/1.47  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.16/1.47  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.16/1.47  tff('#skF_9', type, '#skF_9': $i).
% 3.16/1.47  tff('#skF_8', type, '#skF_8': $i).
% 3.16/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.16/1.47  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.16/1.47  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.16/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.16/1.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.16/1.47  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.16/1.47  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.16/1.47  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.16/1.47  
% 3.16/1.49  tff(f_93, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 3.16/1.49  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.16/1.49  tff(f_41, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 3.16/1.49  tff(f_55, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.16/1.49  tff(f_49, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.16/1.49  tff(f_70, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 3.16/1.49  tff(c_68, plain, ('#skF_9'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.16/1.49  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.16/1.49  tff(c_70, plain, (k2_xboole_0('#skF_8', '#skF_9')=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.16/1.49  tff(c_153, plain, (![D_54, A_55, B_56]: (~r2_hidden(D_54, A_55) | r2_hidden(D_54, k2_xboole_0(A_55, B_56)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.16/1.49  tff(c_156, plain, (![D_54]: (~r2_hidden(D_54, '#skF_8') | r2_hidden(D_54, k1_tarski('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_70, c_153])).
% 3.16/1.49  tff(c_234, plain, (![A_62, B_63]: (~r2_hidden('#skF_1'(A_62, B_63), B_63) | r1_tarski(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.16/1.49  tff(c_588, plain, (![A_91]: (r1_tarski(A_91, k1_tarski('#skF_7')) | ~r2_hidden('#skF_1'(A_91, k1_tarski('#skF_7')), '#skF_8'))), inference(resolution, [status(thm)], [c_156, c_234])).
% 3.16/1.49  tff(c_593, plain, (r1_tarski('#skF_8', k1_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_6, c_588])).
% 3.16/1.49  tff(c_28, plain, (![B_15, A_14]: (B_15=A_14 | ~r1_tarski(B_15, A_14) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.16/1.49  tff(c_600, plain, (k1_tarski('#skF_7')='#skF_8' | ~r1_tarski(k1_tarski('#skF_7'), '#skF_8')), inference(resolution, [status(thm)], [c_593, c_28])).
% 3.16/1.49  tff(c_680, plain, (~r1_tarski(k1_tarski('#skF_7'), '#skF_8')), inference(splitLeft, [status(thm)], [c_600])).
% 3.16/1.49  tff(c_66, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.16/1.49  tff(c_26, plain, (![A_12]: (r2_hidden('#skF_4'(A_12), A_12) | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.16/1.49  tff(c_194, plain, (![D_59]: (~r2_hidden(D_59, '#skF_8') | r2_hidden(D_59, k1_tarski('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_70, c_153])).
% 3.16/1.49  tff(c_42, plain, (![C_27, A_23]: (C_27=A_23 | ~r2_hidden(C_27, k1_tarski(A_23)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.16/1.49  tff(c_199, plain, (![D_60]: (D_60='#skF_7' | ~r2_hidden(D_60, '#skF_8'))), inference(resolution, [status(thm)], [c_194, c_42])).
% 3.16/1.49  tff(c_203, plain, ('#skF_4'('#skF_8')='#skF_7' | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_26, c_199])).
% 3.16/1.49  tff(c_206, plain, ('#skF_4'('#skF_8')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_66, c_203])).
% 3.16/1.49  tff(c_210, plain, (r2_hidden('#skF_7', '#skF_8') | k1_xboole_0='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_206, c_26])).
% 3.16/1.49  tff(c_213, plain, (r2_hidden('#skF_7', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_66, c_210])).
% 3.16/1.49  tff(c_403, plain, (![A_79, B_80]: (r2_hidden('#skF_1'(A_79, B_80), A_79) | r1_tarski(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.16/1.49  tff(c_917, plain, (![A_115, B_116]: ('#skF_1'(k1_tarski(A_115), B_116)=A_115 | r1_tarski(k1_tarski(A_115), B_116))), inference(resolution, [status(thm)], [c_403, c_42])).
% 3.16/1.49  tff(c_941, plain, ('#skF_1'(k1_tarski('#skF_7'), '#skF_8')='#skF_7'), inference(resolution, [status(thm)], [c_917, c_680])).
% 3.16/1.49  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.16/1.49  tff(c_952, plain, (~r2_hidden('#skF_7', '#skF_8') | r1_tarski(k1_tarski('#skF_7'), '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_941, c_4])).
% 3.16/1.49  tff(c_958, plain, (r1_tarski(k1_tarski('#skF_7'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_213, c_952])).
% 3.16/1.49  tff(c_960, plain, $false, inference(negUnitSimplification, [status(thm)], [c_680, c_958])).
% 3.16/1.49  tff(c_961, plain, (k1_tarski('#skF_7')='#skF_8'), inference(splitRight, [status(thm)], [c_600])).
% 3.16/1.49  tff(c_245, plain, (![D_64, B_65, A_66]: (~r2_hidden(D_64, B_65) | r2_hidden(D_64, k2_xboole_0(A_66, B_65)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.16/1.49  tff(c_342, plain, (![D_73]: (~r2_hidden(D_73, '#skF_9') | r2_hidden(D_73, k1_tarski('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_70, c_245])).
% 3.16/1.49  tff(c_437, plain, (![A_83]: (r1_tarski(A_83, k1_tarski('#skF_7')) | ~r2_hidden('#skF_1'(A_83, k1_tarski('#skF_7')), '#skF_9'))), inference(resolution, [status(thm)], [c_342, c_4])).
% 3.16/1.49  tff(c_442, plain, (r1_tarski('#skF_9', k1_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_6, c_437])).
% 3.16/1.49  tff(c_445, plain, (k1_tarski('#skF_7')='#skF_9' | ~r1_tarski(k1_tarski('#skF_7'), '#skF_9')), inference(resolution, [status(thm)], [c_442, c_28])).
% 3.16/1.49  tff(c_446, plain, (~r1_tarski(k1_tarski('#skF_7'), '#skF_9')), inference(splitLeft, [status(thm)], [c_445])).
% 3.16/1.49  tff(c_966, plain, (~r1_tarski('#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_961, c_446])).
% 3.16/1.49  tff(c_64, plain, (k1_xboole_0!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.16/1.49  tff(c_352, plain, (![D_74]: (D_74='#skF_7' | ~r2_hidden(D_74, '#skF_9'))), inference(resolution, [status(thm)], [c_342, c_42])).
% 3.16/1.49  tff(c_356, plain, ('#skF_4'('#skF_9')='#skF_7' | k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_26, c_352])).
% 3.16/1.49  tff(c_359, plain, ('#skF_4'('#skF_9')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_64, c_356])).
% 3.16/1.49  tff(c_363, plain, (r2_hidden('#skF_7', '#skF_9') | k1_xboole_0='#skF_9'), inference(superposition, [status(thm), theory('equality')], [c_359, c_26])).
% 3.16/1.49  tff(c_366, plain, (r2_hidden('#skF_7', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_64, c_363])).
% 3.16/1.49  tff(c_198, plain, (![D_59]: (D_59='#skF_7' | ~r2_hidden(D_59, '#skF_8'))), inference(resolution, [status(thm)], [c_194, c_42])).
% 3.16/1.49  tff(c_427, plain, (![B_80]: ('#skF_1'('#skF_8', B_80)='#skF_7' | r1_tarski('#skF_8', B_80))), inference(resolution, [status(thm)], [c_403, c_198])).
% 3.16/1.49  tff(c_1017, plain, ('#skF_1'('#skF_8', '#skF_9')='#skF_7'), inference(resolution, [status(thm)], [c_427, c_966])).
% 3.16/1.49  tff(c_1091, plain, (~r2_hidden('#skF_7', '#skF_9') | r1_tarski('#skF_8', '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_1017, c_4])).
% 3.16/1.49  tff(c_1097, plain, (r1_tarski('#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_366, c_1091])).
% 3.16/1.49  tff(c_1099, plain, $false, inference(negUnitSimplification, [status(thm)], [c_966, c_1097])).
% 3.16/1.49  tff(c_1100, plain, (k1_tarski('#skF_7')='#skF_9'), inference(splitRight, [status(thm)], [c_445])).
% 3.16/1.49  tff(c_243, plain, (![A_62]: (r1_tarski(A_62, k1_tarski('#skF_7')) | ~r2_hidden('#skF_1'(A_62, k1_tarski('#skF_7')), '#skF_8'))), inference(resolution, [status(thm)], [c_156, c_234])).
% 3.16/1.49  tff(c_1299, plain, (![A_129]: (r1_tarski(A_129, '#skF_9') | ~r2_hidden('#skF_1'(A_129, '#skF_9'), '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_1100, c_1100, c_243])).
% 3.16/1.49  tff(c_1304, plain, (r1_tarski('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_6, c_1299])).
% 3.16/1.49  tff(c_1306, plain, ('#skF_9'='#skF_8' | ~r1_tarski('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_1304, c_28])).
% 3.16/1.49  tff(c_1309, plain, (~r1_tarski('#skF_9', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_68, c_1306])).
% 3.16/1.49  tff(c_351, plain, (![D_73]: (D_73='#skF_7' | ~r2_hidden(D_73, '#skF_9'))), inference(resolution, [status(thm)], [c_342, c_42])).
% 3.16/1.49  tff(c_423, plain, (![B_80]: ('#skF_1'('#skF_9', B_80)='#skF_7' | r1_tarski('#skF_9', B_80))), inference(resolution, [status(thm)], [c_403, c_351])).
% 3.16/1.49  tff(c_1313, plain, ('#skF_1'('#skF_9', '#skF_8')='#skF_7'), inference(resolution, [status(thm)], [c_423, c_1309])).
% 3.16/1.49  tff(c_1320, plain, (~r2_hidden('#skF_7', '#skF_8') | r1_tarski('#skF_9', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_1313, c_4])).
% 3.16/1.49  tff(c_1326, plain, (r1_tarski('#skF_9', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_213, c_1320])).
% 3.16/1.49  tff(c_1328, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1309, c_1326])).
% 3.16/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.49  
% 3.16/1.49  Inference rules
% 3.16/1.49  ----------------------
% 3.16/1.49  #Ref     : 0
% 3.16/1.49  #Sup     : 294
% 3.16/1.49  #Fact    : 0
% 3.16/1.49  #Define  : 0
% 3.16/1.49  #Split   : 4
% 3.16/1.49  #Chain   : 0
% 3.16/1.49  #Close   : 0
% 3.16/1.49  
% 3.16/1.49  Ordering : KBO
% 3.16/1.49  
% 3.16/1.49  Simplification rules
% 3.16/1.49  ----------------------
% 3.16/1.49  #Subsume      : 23
% 3.16/1.49  #Demod        : 122
% 3.16/1.49  #Tautology    : 178
% 3.16/1.49  #SimpNegUnit  : 22
% 3.16/1.49  #BackRed      : 18
% 3.16/1.49  
% 3.16/1.49  #Partial instantiations: 0
% 3.16/1.49  #Strategies tried      : 1
% 3.16/1.49  
% 3.16/1.49  Timing (in seconds)
% 3.16/1.49  ----------------------
% 3.16/1.49  Preprocessing        : 0.32
% 3.16/1.49  Parsing              : 0.16
% 3.16/1.49  CNF conversion       : 0.02
% 3.16/1.49  Main loop            : 0.40
% 3.16/1.49  Inferencing          : 0.14
% 3.16/1.49  Reduction            : 0.13
% 3.16/1.49  Demodulation         : 0.09
% 3.16/1.49  BG Simplification    : 0.02
% 3.16/1.49  Subsumption          : 0.08
% 3.16/1.49  Abstraction          : 0.02
% 3.16/1.49  MUC search           : 0.00
% 3.16/1.49  Cooper               : 0.00
% 3.16/1.49  Total                : 0.75
% 3.16/1.49  Index Insertion      : 0.00
% 3.16/1.49  Index Deletion       : 0.00
% 3.16/1.49  Index Matching       : 0.00
% 3.16/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
