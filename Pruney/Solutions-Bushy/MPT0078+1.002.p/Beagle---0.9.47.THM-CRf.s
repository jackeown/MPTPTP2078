%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0078+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:35:41 EST 2020

% Result     : Theorem 11.82s
% Output     : CNFRefutation 12.04s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 832 expanded)
%              Number of leaves         :   21 ( 288 expanded)
%              Depth                    :   16
%              Number of atoms          :  203 (2299 expanded)
%              Number of equality atoms :   63 ( 730 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_61,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( k2_xboole_0(A,B) = k2_xboole_0(C,B)
          & r1_xboole_0(A,B)
          & r1_xboole_0(C,B) )
       => A = C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_26,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_52,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(c_48,plain,(
    '#skF_7' != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1568,plain,(
    ! [A_117,B_118,C_119] :
      ( r2_hidden('#skF_1'(A_117,B_118,C_119),B_118)
      | r2_hidden('#skF_1'(A_117,B_118,C_119),A_117)
      | r2_hidden('#skF_2'(A_117,B_118,C_119),C_119)
      | k2_xboole_0(A_117,B_118) = C_119 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_20,plain,(
    ! [A_5,B_6,C_7] :
      ( ~ r2_hidden('#skF_1'(A_5,B_6,C_7),C_7)
      | r2_hidden('#skF_2'(A_5,B_6,C_7),C_7)
      | k2_xboole_0(A_5,B_6) = C_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1781,plain,(
    ! [A_123,B_124] :
      ( r2_hidden('#skF_1'(A_123,B_124,A_123),B_124)
      | r2_hidden('#skF_2'(A_123,B_124,A_123),A_123)
      | k2_xboole_0(A_123,B_124) = A_123 ) ),
    inference(resolution,[status(thm)],[c_1568,c_20])).

tff(c_1855,plain,(
    ! [B_124] :
      ( r2_hidden('#skF_2'(B_124,B_124,B_124),B_124)
      | k2_xboole_0(B_124,B_124) = B_124 ) ),
    inference(resolution,[status(thm)],[c_1781,c_20])).

tff(c_5205,plain,(
    ! [A_199,B_200,C_201] :
      ( r2_hidden('#skF_1'(A_199,B_200,C_201),B_200)
      | r2_hidden('#skF_1'(A_199,B_200,C_201),A_199)
      | ~ r2_hidden('#skF_2'(A_199,B_200,C_201),A_199)
      | k2_xboole_0(A_199,B_200) = C_201 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,(
    ! [A_5,B_6,C_7] :
      ( ~ r2_hidden('#skF_1'(A_5,B_6,C_7),C_7)
      | ~ r2_hidden('#skF_2'(A_5,B_6,C_7),A_5)
      | k2_xboole_0(A_5,B_6) = C_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_5684,plain,(
    ! [A_213,B_214] :
      ( r2_hidden('#skF_1'(A_213,B_214,B_214),A_213)
      | ~ r2_hidden('#skF_2'(A_213,B_214,B_214),A_213)
      | k2_xboole_0(A_213,B_214) = B_214 ) ),
    inference(resolution,[status(thm)],[c_5205,c_16])).

tff(c_12,plain,(
    ! [A_5,B_6,C_7] :
      ( ~ r2_hidden('#skF_1'(A_5,B_6,C_7),C_7)
      | ~ r2_hidden('#skF_2'(A_5,B_6,C_7),B_6)
      | k2_xboole_0(A_5,B_6) = C_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_5741,plain,(
    ! [A_215] :
      ( ~ r2_hidden('#skF_2'(A_215,A_215,A_215),A_215)
      | k2_xboole_0(A_215,A_215) = A_215 ) ),
    inference(resolution,[status(thm)],[c_5684,c_12])).

tff(c_5784,plain,(
    ! [B_124] : k2_xboole_0(B_124,B_124) = B_124 ),
    inference(resolution,[status(thm)],[c_1855,c_5741])).

tff(c_22,plain,(
    ! [A_5,B_6,C_7] :
      ( r2_hidden('#skF_1'(A_5,B_6,C_7),B_6)
      | r2_hidden('#skF_1'(A_5,B_6,C_7),A_5)
      | r2_hidden('#skF_2'(A_5,B_6,C_7),C_7)
      | k2_xboole_0(A_5,B_6) = C_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1567,plain,(
    ! [A_5,C_7] :
      ( r2_hidden('#skF_2'(A_5,A_5,C_7),C_7)
      | k2_xboole_0(A_5,A_5) = C_7
      | r2_hidden('#skF_1'(A_5,A_5,C_7),A_5) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_22])).

tff(c_5792,plain,(
    ! [A_5,C_7] :
      ( r2_hidden('#skF_2'(A_5,A_5,C_7),C_7)
      | C_7 = A_5
      | r2_hidden('#skF_1'(A_5,A_5,C_7),A_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5784,c_1567])).

tff(c_1696,plain,(
    ! [A_117,B_118] :
      ( r2_hidden('#skF_1'(A_117,B_118,A_117),B_118)
      | r2_hidden('#skF_2'(A_117,B_118,A_117),A_117)
      | k2_xboole_0(A_117,B_118) = A_117 ) ),
    inference(resolution,[status(thm)],[c_1568,c_20])).

tff(c_9999,plain,(
    ! [A_341,B_342] :
      ( r2_hidden('#skF_1'(A_341,B_342,A_341),B_342)
      | ~ r2_hidden('#skF_2'(A_341,B_342,A_341),A_341)
      | k2_xboole_0(A_341,B_342) = A_341 ) ),
    inference(resolution,[status(thm)],[c_5205,c_16])).

tff(c_10037,plain,(
    ! [A_343,B_344] :
      ( r2_hidden('#skF_1'(A_343,B_344,A_343),B_344)
      | k2_xboole_0(A_343,B_344) = A_343 ) ),
    inference(resolution,[status(thm)],[c_1696,c_9999])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_54,plain,(
    k2_xboole_0('#skF_7','#skF_6') = k2_xboole_0('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_55,plain,(
    k2_xboole_0('#skF_6','#skF_7') = k2_xboole_0('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_54])).

tff(c_249,plain,(
    ! [D_30,B_31,A_32] :
      ( ~ r2_hidden(D_30,B_31)
      | r2_hidden(D_30,k2_xboole_0(A_32,B_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_252,plain,(
    ! [D_30] :
      ( ~ r2_hidden(D_30,'#skF_7')
      | r2_hidden(D_30,k2_xboole_0('#skF_6','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_249])).

tff(c_321,plain,(
    ! [D_45,B_46,A_47] :
      ( r2_hidden(D_45,B_46)
      | r2_hidden(D_45,A_47)
      | ~ r2_hidden(D_45,k2_xboole_0(A_47,B_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_346,plain,(
    ! [D_30] :
      ( r2_hidden(D_30,'#skF_5')
      | r2_hidden(D_30,'#skF_6')
      | ~ r2_hidden(D_30,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_252,c_321])).

tff(c_12087,plain,(
    ! [A_410] :
      ( r2_hidden('#skF_1'(A_410,'#skF_7',A_410),'#skF_5')
      | r2_hidden('#skF_1'(A_410,'#skF_7',A_410),'#skF_6')
      | k2_xboole_0(A_410,'#skF_7') = A_410 ) ),
    inference(resolution,[status(thm)],[c_10037,c_346])).

tff(c_12107,plain,
    ( r2_hidden('#skF_2'('#skF_5','#skF_7','#skF_5'),'#skF_5')
    | r2_hidden('#skF_1'('#skF_5','#skF_7','#skF_5'),'#skF_6')
    | k2_xboole_0('#skF_5','#skF_7') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_12087,c_20])).

tff(c_12951,plain,(
    k2_xboole_0('#skF_5','#skF_7') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_12107])).

tff(c_8,plain,(
    ! [D_10,B_6,A_5] :
      ( ~ r2_hidden(D_10,B_6)
      | r2_hidden(D_10,k2_xboole_0(A_5,B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_12975,plain,(
    ! [D_441] :
      ( ~ r2_hidden(D_441,'#skF_7')
      | r2_hidden(D_441,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12951,c_8])).

tff(c_13919,plain,(
    ! [C_472] :
      ( r2_hidden('#skF_1'('#skF_7','#skF_7',C_472),'#skF_5')
      | r2_hidden('#skF_2'('#skF_7','#skF_7',C_472),C_472)
      | C_472 = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_5792,c_12975])).

tff(c_13926,plain,
    ( k2_xboole_0('#skF_7','#skF_7') = '#skF_5'
    | r2_hidden('#skF_2'('#skF_7','#skF_7','#skF_5'),'#skF_5')
    | '#skF_7' = '#skF_5' ),
    inference(resolution,[status(thm)],[c_13919,c_20])).

tff(c_13962,plain,
    ( '#skF_7' = '#skF_5'
    | r2_hidden('#skF_2'('#skF_7','#skF_7','#skF_5'),'#skF_5')
    | '#skF_7' = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5784,c_13926])).

tff(c_13963,plain,(
    r2_hidden('#skF_2'('#skF_7','#skF_7','#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_48,c_13962])).

tff(c_52,plain,(
    r1_xboole_0('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_189,plain,(
    ! [A_26,B_27] :
      ( k3_xboole_0(A_26,B_27) = k1_xboole_0
      | ~ r1_xboole_0(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_197,plain,(
    k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_52,c_189])).

tff(c_350,plain,(
    ! [D_49,A_50,B_51] :
      ( r2_hidden(D_49,k3_xboole_0(A_50,B_51))
      | ~ r2_hidden(D_49,B_51)
      | ~ r2_hidden(D_49,A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_377,plain,(
    ! [D_52] :
      ( r2_hidden(D_52,k1_xboole_0)
      | ~ r2_hidden(D_52,'#skF_6')
      | ~ r2_hidden(D_52,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_350])).

tff(c_46,plain,(
    ! [A_19] : k2_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_264,plain,(
    ! [D_30,A_19] :
      ( ~ r2_hidden(D_30,k1_xboole_0)
      | r2_hidden(D_30,A_19) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_249])).

tff(c_380,plain,(
    ! [D_52,A_19] :
      ( r2_hidden(D_52,A_19)
      | ~ r2_hidden(D_52,'#skF_6')
      | ~ r2_hidden(D_52,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_377,c_264])).

tff(c_13975,plain,(
    ! [A_19] :
      ( r2_hidden('#skF_2'('#skF_7','#skF_7','#skF_5'),A_19)
      | ~ r2_hidden('#skF_2'('#skF_7','#skF_7','#skF_5'),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_13963,c_380])).

tff(c_13976,plain,(
    ~ r2_hidden('#skF_2'('#skF_7','#skF_7','#skF_5'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_13975])).

tff(c_385,plain,(
    ! [D_54] :
      ( r2_hidden(D_54,'#skF_7')
      | r2_hidden(D_54,'#skF_6')
      | ~ r2_hidden(D_54,k2_xboole_0('#skF_6','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_321])).

tff(c_399,plain,(
    ! [D_10] :
      ( r2_hidden(D_10,'#skF_7')
      | r2_hidden(D_10,'#skF_6')
      | ~ r2_hidden(D_10,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_8,c_385])).

tff(c_18,plain,(
    ! [A_5,B_6,C_7] :
      ( r2_hidden('#skF_1'(A_5,B_6,C_7),B_6)
      | r2_hidden('#skF_1'(A_5,B_6,C_7),A_5)
      | ~ r2_hidden('#skF_2'(A_5,B_6,C_7),A_5)
      | k2_xboole_0(A_5,B_6) = C_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_5204,plain,(
    ! [A_5,C_7] :
      ( ~ r2_hidden('#skF_2'(A_5,A_5,C_7),A_5)
      | k2_xboole_0(A_5,A_5) = C_7
      | r2_hidden('#skF_1'(A_5,A_5,C_7),A_5) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_18])).

tff(c_5949,plain,(
    ! [A_5,C_7] :
      ( ~ r2_hidden('#skF_2'(A_5,A_5,C_7),A_5)
      | C_7 = A_5
      | r2_hidden('#skF_1'(A_5,A_5,C_7),A_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5784,c_5204])).

tff(c_14371,plain,(
    ! [C_488] :
      ( r2_hidden('#skF_1'('#skF_7','#skF_7',C_488),'#skF_5')
      | ~ r2_hidden('#skF_2'('#skF_7','#skF_7',C_488),'#skF_7')
      | C_488 = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_5949,c_12975])).

tff(c_14374,plain,
    ( k2_xboole_0('#skF_7','#skF_7') = '#skF_5'
    | ~ r2_hidden('#skF_2'('#skF_7','#skF_7','#skF_5'),'#skF_7')
    | '#skF_7' = '#skF_5' ),
    inference(resolution,[status(thm)],[c_14371,c_12])).

tff(c_14385,plain,
    ( '#skF_7' = '#skF_5'
    | ~ r2_hidden('#skF_2'('#skF_7','#skF_7','#skF_5'),'#skF_7')
    | '#skF_7' = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5784,c_14374])).

tff(c_14386,plain,(
    ~ r2_hidden('#skF_2'('#skF_7','#skF_7','#skF_5'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_48,c_14385])).

tff(c_14396,plain,
    ( r2_hidden('#skF_2'('#skF_7','#skF_7','#skF_5'),'#skF_6')
    | ~ r2_hidden('#skF_2'('#skF_7','#skF_7','#skF_5'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_399,c_14386])).

tff(c_14399,plain,(
    r2_hidden('#skF_2'('#skF_7','#skF_7','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13963,c_14396])).

tff(c_14401,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13976,c_14399])).

tff(c_14402,plain,(
    ! [A_19] : r2_hidden('#skF_2'('#skF_7','#skF_7','#skF_5'),A_19) ),
    inference(splitRight,[status(thm)],[c_13975])).

tff(c_14964,plain,(
    ! [C_509] :
      ( r2_hidden('#skF_1'('#skF_7','#skF_7',C_509),'#skF_5')
      | ~ r2_hidden('#skF_2'('#skF_7','#skF_7',C_509),'#skF_7')
      | C_509 = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_5949,c_12975])).

tff(c_14967,plain,
    ( k2_xboole_0('#skF_7','#skF_7') = '#skF_5'
    | ~ r2_hidden('#skF_2'('#skF_7','#skF_7','#skF_5'),'#skF_7')
    | '#skF_7' = '#skF_5' ),
    inference(resolution,[status(thm)],[c_14964,c_12])).

tff(c_14979,plain,(
    '#skF_7' = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14402,c_5784,c_14967])).

tff(c_14981,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_14979])).

tff(c_14983,plain,(
    k2_xboole_0('#skF_5','#skF_7') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_12107])).

tff(c_14982,plain,
    ( r2_hidden('#skF_1'('#skF_5','#skF_7','#skF_5'),'#skF_6')
    | r2_hidden('#skF_2'('#skF_5','#skF_7','#skF_5'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_12107])).

tff(c_15138,plain,(
    r2_hidden('#skF_2'('#skF_5','#skF_7','#skF_5'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_14982])).

tff(c_12108,plain,
    ( ~ r2_hidden('#skF_2'('#skF_5','#skF_7','#skF_5'),'#skF_5')
    | r2_hidden('#skF_1'('#skF_5','#skF_7','#skF_5'),'#skF_6')
    | k2_xboole_0('#skF_5','#skF_7') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_12087,c_16])).

tff(c_15656,plain,
    ( r2_hidden('#skF_1'('#skF_5','#skF_7','#skF_5'),'#skF_6')
    | k2_xboole_0('#skF_5','#skF_7') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15138,c_12108])).

tff(c_15657,plain,(
    r2_hidden('#skF_1'('#skF_5','#skF_7','#skF_5'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_14983,c_15656])).

tff(c_50,plain,(
    r1_xboole_0('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_196,plain,(
    k3_xboole_0('#skF_7','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_50,c_189])).

tff(c_381,plain,(
    ! [D_53] :
      ( r2_hidden(D_53,k1_xboole_0)
      | ~ r2_hidden(D_53,'#skF_6')
      | ~ r2_hidden(D_53,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_196,c_350])).

tff(c_384,plain,(
    ! [D_53,A_19] :
      ( r2_hidden(D_53,A_19)
      | ~ r2_hidden(D_53,'#skF_6')
      | ~ r2_hidden(D_53,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_381,c_264])).

tff(c_10089,plain,(
    ! [A_343,A_19] :
      ( r2_hidden('#skF_1'(A_343,'#skF_7',A_343),A_19)
      | ~ r2_hidden('#skF_1'(A_343,'#skF_7',A_343),'#skF_6')
      | k2_xboole_0(A_343,'#skF_7') = A_343 ) ),
    inference(resolution,[status(thm)],[c_10037,c_384])).

tff(c_15659,plain,(
    ! [A_19] :
      ( r2_hidden('#skF_1'('#skF_5','#skF_7','#skF_5'),A_19)
      | k2_xboole_0('#skF_5','#skF_7') = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_15657,c_10089])).

tff(c_15662,plain,(
    ! [A_19] : r2_hidden('#skF_1'('#skF_5','#skF_7','#skF_5'),A_19) ),
    inference(negUnitSimplification,[status(thm)],[c_14983,c_15659])).

tff(c_481,plain,(
    ! [A_66,B_67,C_68] :
      ( ~ r2_hidden('#skF_1'(A_66,B_67,C_68),C_68)
      | ~ r2_hidden('#skF_2'(A_66,B_67,C_68),A_66)
      | k2_xboole_0(A_66,B_67) = C_68 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10444,plain,(
    ! [A_356,B_357,A_358,B_359] :
      ( ~ r2_hidden('#skF_2'(A_356,B_357,k2_xboole_0(A_358,B_359)),A_356)
      | k2_xboole_0(A_358,B_359) = k2_xboole_0(A_356,B_357)
      | ~ r2_hidden('#skF_1'(A_356,B_357,k2_xboole_0(A_358,B_359)),B_359) ) ),
    inference(resolution,[status(thm)],[c_8,c_481])).

tff(c_10484,plain,(
    ! [A_356,B_357,A_19] :
      ( ~ r2_hidden('#skF_2'(A_356,B_357,A_19),A_356)
      | k2_xboole_0(A_356,B_357) = k2_xboole_0(A_19,k1_xboole_0)
      | ~ r2_hidden('#skF_1'(A_356,B_357,k2_xboole_0(A_19,k1_xboole_0)),k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_10444])).

tff(c_10498,plain,(
    ! [A_356,B_357,A_19] :
      ( ~ r2_hidden('#skF_2'(A_356,B_357,A_19),A_356)
      | k2_xboole_0(A_356,B_357) = A_19
      | ~ r2_hidden('#skF_1'(A_356,B_357,A_19),k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_46,c_10484])).

tff(c_15140,plain,
    ( k2_xboole_0('#skF_5','#skF_7') = '#skF_5'
    | ~ r2_hidden('#skF_1'('#skF_5','#skF_7','#skF_5'),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_15138,c_10498])).

tff(c_15145,plain,(
    ~ r2_hidden('#skF_1'('#skF_5','#skF_7','#skF_5'),k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_14983,c_15140])).

tff(c_15817,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15662,c_15145])).

tff(c_15819,plain,(
    ~ r2_hidden('#skF_2'('#skF_5','#skF_7','#skF_5'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_14982])).

tff(c_15818,plain,(
    r2_hidden('#skF_1'('#skF_5','#skF_7','#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_14982])).

tff(c_15821,plain,(
    ! [A_19] :
      ( r2_hidden('#skF_1'('#skF_5','#skF_7','#skF_5'),A_19)
      | k2_xboole_0('#skF_5','#skF_7') = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_15818,c_10089])).

tff(c_15900,plain,(
    ! [A_538] : r2_hidden('#skF_1'('#skF_5','#skF_7','#skF_5'),A_538) ),
    inference(negUnitSimplification,[status(thm)],[c_14983,c_15821])).

tff(c_15910,plain,
    ( r2_hidden('#skF_2'('#skF_5','#skF_7','#skF_5'),'#skF_5')
    | k2_xboole_0('#skF_5','#skF_7') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_15900,c_20])).

tff(c_15956,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14983,c_15819,c_15910])).

%------------------------------------------------------------------------------
