%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:15 EST 2020

% Result     : Theorem 4.20s
% Output     : CNFRefutation 4.30s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 207 expanded)
%              Number of leaves         :   24 (  78 expanded)
%              Depth                    :   12
%              Number of atoms          :  126 ( 435 expanded)
%              Number of equality atoms :   33 ( 177 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_77,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( k2_zfmisc_1(A,B) = k2_zfmisc_1(C,D)
       => ( A = k1_xboole_0
          | B = k1_xboole_0
          | ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_52,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_66,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_42,plain,
    ( '#skF_6' != '#skF_8'
    | '#skF_7' != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_49,plain,(
    '#skF_7' != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_44,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_28,plain,(
    ! [A_14] :
      ( r2_hidden('#skF_4'(A_14),A_14)
      | k1_xboole_0 = A_14 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_586,plain,(
    ! [A_86,B_87,C_88,D_89] :
      ( r2_hidden(k4_tarski(A_86,B_87),k2_zfmisc_1(C_88,D_89))
      | ~ r2_hidden(B_87,D_89)
      | ~ r2_hidden(A_86,C_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_48,plain,(
    k2_zfmisc_1('#skF_7','#skF_8') = k2_zfmisc_1('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_343,plain,(
    ! [A_60,C_61,B_62,D_63] :
      ( r2_hidden(A_60,C_61)
      | ~ r2_hidden(k4_tarski(A_60,B_62),k2_zfmisc_1(C_61,D_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_346,plain,(
    ! [A_60,B_62] :
      ( r2_hidden(A_60,'#skF_7')
      | ~ r2_hidden(k4_tarski(A_60,B_62),k2_zfmisc_1('#skF_5','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_343])).

tff(c_608,plain,(
    ! [A_86,B_87] :
      ( r2_hidden(A_86,'#skF_7')
      | ~ r2_hidden(B_87,'#skF_6')
      | ~ r2_hidden(A_86,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_586,c_346])).

tff(c_639,plain,(
    ! [B_93] : ~ r2_hidden(B_93,'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_608])).

tff(c_651,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_28,c_639])).

tff(c_657,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_651])).

tff(c_664,plain,(
    ! [A_97] :
      ( r2_hidden(A_97,'#skF_7')
      | ~ r2_hidden(A_97,'#skF_5') ) ),
    inference(splitRight,[status(thm)],[c_608])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_677,plain,(
    ! [A_98] :
      ( r1_tarski(A_98,'#skF_7')
      | ~ r2_hidden('#skF_1'(A_98,'#skF_7'),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_664,c_6])).

tff(c_682,plain,(
    r1_tarski('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_8,c_677])).

tff(c_30,plain,(
    ! [A_16,B_17] :
      ( k3_xboole_0(A_16,B_17) = A_16
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_686,plain,(
    k3_xboole_0('#skF_5','#skF_7') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_682,c_30])).

tff(c_687,plain,(
    ! [A_99,B_100] :
      ( r2_hidden(k4_tarski(A_99,B_100),k2_zfmisc_1('#skF_5','#skF_6'))
      | ~ r2_hidden(B_100,'#skF_8')
      | ~ r2_hidden(A_99,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_586])).

tff(c_40,plain,(
    ! [A_21,C_23,B_22,D_24] :
      ( r2_hidden(A_21,C_23)
      | ~ r2_hidden(k4_tarski(A_21,B_22),k2_zfmisc_1(C_23,D_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_705,plain,(
    ! [A_99,B_100] :
      ( r2_hidden(A_99,'#skF_5')
      | ~ r2_hidden(B_100,'#skF_8')
      | ~ r2_hidden(A_99,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_687,c_40])).

tff(c_809,plain,(
    ! [B_100] : ~ r2_hidden(B_100,'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_705])).

tff(c_46,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_490,plain,(
    ! [B_72,D_73,A_74,C_75] :
      ( r2_hidden(B_72,D_73)
      | ~ r2_hidden(k4_tarski(A_74,B_72),k2_zfmisc_1(C_75,D_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_493,plain,(
    ! [B_72,A_74] :
      ( r2_hidden(B_72,'#skF_8')
      | ~ r2_hidden(k4_tarski(A_74,B_72),k2_zfmisc_1('#skF_5','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_490])).

tff(c_606,plain,(
    ! [B_87,A_86] :
      ( r2_hidden(B_87,'#skF_8')
      | ~ r2_hidden(B_87,'#skF_6')
      | ~ r2_hidden(A_86,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_586,c_493])).

tff(c_718,plain,(
    ! [A_101] : ~ r2_hidden(A_101,'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_606])).

tff(c_730,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_28,c_718])).

tff(c_736,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_730])).

tff(c_738,plain,(
    ! [B_102] :
      ( r2_hidden(B_102,'#skF_8')
      | ~ r2_hidden(B_102,'#skF_6') ) ),
    inference(splitRight,[status(thm)],[c_606])).

tff(c_750,plain,
    ( r2_hidden('#skF_4'('#skF_6'),'#skF_8')
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_28,c_738])).

tff(c_755,plain,(
    r2_hidden('#skF_4'('#skF_6'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_750])).

tff(c_813,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_809,c_755])).

tff(c_815,plain,(
    ! [A_107] :
      ( r2_hidden(A_107,'#skF_5')
      | ~ r2_hidden(A_107,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_705])).

tff(c_1618,plain,(
    ! [B_143] :
      ( r2_hidden('#skF_1'('#skF_7',B_143),'#skF_5')
      | r1_tarski('#skF_7',B_143) ) ),
    inference(resolution,[status(thm)],[c_8,c_815])).

tff(c_1632,plain,(
    r1_tarski('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_1618,c_6])).

tff(c_1654,plain,(
    k3_xboole_0('#skF_7','#skF_5') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_1632,c_30])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1666,plain,(
    k3_xboole_0('#skF_5','#skF_7') = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_1654,c_2])).

tff(c_1678,plain,(
    '#skF_7' = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_686,c_1666])).

tff(c_1680,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_49,c_1678])).

tff(c_1681,plain,(
    '#skF_6' != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_2189,plain,(
    ! [A_203,B_204,C_205,D_206] :
      ( r2_hidden(k4_tarski(A_203,B_204),k2_zfmisc_1(C_205,D_206))
      | ~ r2_hidden(B_204,D_206)
      | ~ r2_hidden(A_203,C_205) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1682,plain,(
    '#skF_7' = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_1730,plain,(
    k2_zfmisc_1('#skF_5','#skF_6') = k2_zfmisc_1('#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1682,c_48])).

tff(c_2086,plain,(
    ! [B_188,D_189,A_190,C_191] :
      ( r2_hidden(B_188,D_189)
      | ~ r2_hidden(k4_tarski(A_190,B_188),k2_zfmisc_1(C_191,D_189)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2089,plain,(
    ! [B_188,A_190] :
      ( r2_hidden(B_188,'#skF_6')
      | ~ r2_hidden(k4_tarski(A_190,B_188),k2_zfmisc_1('#skF_5','#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1730,c_2086])).

tff(c_2205,plain,(
    ! [B_204,A_203] :
      ( r2_hidden(B_204,'#skF_6')
      | ~ r2_hidden(B_204,'#skF_8')
      | ~ r2_hidden(A_203,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_2189,c_2089])).

tff(c_2260,plain,(
    ! [A_211] : ~ r2_hidden(A_211,'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_2205])).

tff(c_2272,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_28,c_2260])).

tff(c_2278,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_2272])).

tff(c_2280,plain,(
    ! [B_212] :
      ( r2_hidden(B_212,'#skF_6')
      | ~ r2_hidden(B_212,'#skF_8') ) ),
    inference(splitRight,[status(thm)],[c_2205])).

tff(c_2289,plain,(
    ! [A_213] :
      ( r1_tarski(A_213,'#skF_6')
      | ~ r2_hidden('#skF_1'(A_213,'#skF_6'),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_2280,c_6])).

tff(c_2294,plain,(
    r1_tarski('#skF_8','#skF_6') ),
    inference(resolution,[status(thm)],[c_8,c_2289])).

tff(c_2298,plain,(
    k3_xboole_0('#skF_8','#skF_6') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_2294,c_30])).

tff(c_2243,plain,(
    ! [A_209,B_210] :
      ( r2_hidden(k4_tarski(A_209,B_210),k2_zfmisc_1('#skF_5','#skF_8'))
      | ~ r2_hidden(B_210,'#skF_6')
      | ~ r2_hidden(A_209,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1730,c_2189])).

tff(c_38,plain,(
    ! [B_22,D_24,A_21,C_23] :
      ( r2_hidden(B_22,D_24)
      | ~ r2_hidden(k4_tarski(A_21,B_22),k2_zfmisc_1(C_23,D_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2256,plain,(
    ! [B_210,A_209] :
      ( r2_hidden(B_210,'#skF_8')
      | ~ r2_hidden(B_210,'#skF_6')
      | ~ r2_hidden(A_209,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_2243,c_38])).

tff(c_2353,plain,(
    ! [A_220] : ~ r2_hidden(A_220,'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_2256])).

tff(c_2365,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_28,c_2353])).

tff(c_2371,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_2365])).

tff(c_2373,plain,(
    ! [B_221] :
      ( r2_hidden(B_221,'#skF_8')
      | ~ r2_hidden(B_221,'#skF_6') ) ),
    inference(splitRight,[status(thm)],[c_2256])).

tff(c_2447,plain,(
    ! [B_226] :
      ( r2_hidden('#skF_1'('#skF_6',B_226),'#skF_8')
      | r1_tarski('#skF_6',B_226) ) ),
    inference(resolution,[status(thm)],[c_8,c_2373])).

tff(c_2461,plain,(
    r1_tarski('#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_2447,c_6])).

tff(c_2494,plain,(
    k3_xboole_0('#skF_6','#skF_8') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_2461,c_30])).

tff(c_2504,plain,(
    k3_xboole_0('#skF_8','#skF_6') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_2494,c_2])).

tff(c_2516,plain,(
    '#skF_6' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2298,c_2504])).

tff(c_2518,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1681,c_2516])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:55:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.20/1.78  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.20/1.79  
% 4.20/1.79  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.20/1.79  %$ r2_hidden > r1_tarski > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_3 > #skF_1
% 4.20/1.79  
% 4.20/1.79  %Foreground sorts:
% 4.20/1.79  
% 4.20/1.79  
% 4.20/1.79  %Background operators:
% 4.20/1.79  
% 4.20/1.79  
% 4.20/1.79  %Foreground operators:
% 4.20/1.79  tff('#skF_4', type, '#skF_4': $i > $i).
% 4.20/1.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.20/1.79  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.20/1.79  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.20/1.79  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.20/1.79  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.20/1.79  tff('#skF_7', type, '#skF_7': $i).
% 4.20/1.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.20/1.79  tff('#skF_5', type, '#skF_5': $i).
% 4.20/1.79  tff('#skF_6', type, '#skF_6': $i).
% 4.20/1.79  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.20/1.79  tff('#skF_8', type, '#skF_8': $i).
% 4.20/1.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.20/1.79  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.20/1.79  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.20/1.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.20/1.79  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.20/1.79  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.20/1.79  
% 4.30/1.80  tff(f_77, negated_conjecture, ~(![A, B, C, D]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(C, D)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | ((A = C) & (B = D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t134_zfmisc_1)).
% 4.30/1.80  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.30/1.80  tff(f_52, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 4.30/1.80  tff(f_66, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 4.30/1.80  tff(f_56, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.30/1.80  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.30/1.80  tff(c_42, plain, ('#skF_6'!='#skF_8' | '#skF_7'!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.30/1.80  tff(c_49, plain, ('#skF_7'!='#skF_5'), inference(splitLeft, [status(thm)], [c_42])).
% 4.30/1.80  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.30/1.80  tff(c_44, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.30/1.80  tff(c_28, plain, (![A_14]: (r2_hidden('#skF_4'(A_14), A_14) | k1_xboole_0=A_14)), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.30/1.80  tff(c_586, plain, (![A_86, B_87, C_88, D_89]: (r2_hidden(k4_tarski(A_86, B_87), k2_zfmisc_1(C_88, D_89)) | ~r2_hidden(B_87, D_89) | ~r2_hidden(A_86, C_88))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.30/1.80  tff(c_48, plain, (k2_zfmisc_1('#skF_7', '#skF_8')=k2_zfmisc_1('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.30/1.80  tff(c_343, plain, (![A_60, C_61, B_62, D_63]: (r2_hidden(A_60, C_61) | ~r2_hidden(k4_tarski(A_60, B_62), k2_zfmisc_1(C_61, D_63)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.30/1.80  tff(c_346, plain, (![A_60, B_62]: (r2_hidden(A_60, '#skF_7') | ~r2_hidden(k4_tarski(A_60, B_62), k2_zfmisc_1('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_48, c_343])).
% 4.30/1.80  tff(c_608, plain, (![A_86, B_87]: (r2_hidden(A_86, '#skF_7') | ~r2_hidden(B_87, '#skF_6') | ~r2_hidden(A_86, '#skF_5'))), inference(resolution, [status(thm)], [c_586, c_346])).
% 4.30/1.80  tff(c_639, plain, (![B_93]: (~r2_hidden(B_93, '#skF_6'))), inference(splitLeft, [status(thm)], [c_608])).
% 4.30/1.80  tff(c_651, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_28, c_639])).
% 4.30/1.80  tff(c_657, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_651])).
% 4.30/1.80  tff(c_664, plain, (![A_97]: (r2_hidden(A_97, '#skF_7') | ~r2_hidden(A_97, '#skF_5'))), inference(splitRight, [status(thm)], [c_608])).
% 4.30/1.80  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.30/1.80  tff(c_677, plain, (![A_98]: (r1_tarski(A_98, '#skF_7') | ~r2_hidden('#skF_1'(A_98, '#skF_7'), '#skF_5'))), inference(resolution, [status(thm)], [c_664, c_6])).
% 4.30/1.80  tff(c_682, plain, (r1_tarski('#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_8, c_677])).
% 4.30/1.80  tff(c_30, plain, (![A_16, B_17]: (k3_xboole_0(A_16, B_17)=A_16 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.30/1.80  tff(c_686, plain, (k3_xboole_0('#skF_5', '#skF_7')='#skF_5'), inference(resolution, [status(thm)], [c_682, c_30])).
% 4.30/1.80  tff(c_687, plain, (![A_99, B_100]: (r2_hidden(k4_tarski(A_99, B_100), k2_zfmisc_1('#skF_5', '#skF_6')) | ~r2_hidden(B_100, '#skF_8') | ~r2_hidden(A_99, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_48, c_586])).
% 4.30/1.80  tff(c_40, plain, (![A_21, C_23, B_22, D_24]: (r2_hidden(A_21, C_23) | ~r2_hidden(k4_tarski(A_21, B_22), k2_zfmisc_1(C_23, D_24)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.30/1.80  tff(c_705, plain, (![A_99, B_100]: (r2_hidden(A_99, '#skF_5') | ~r2_hidden(B_100, '#skF_8') | ~r2_hidden(A_99, '#skF_7'))), inference(resolution, [status(thm)], [c_687, c_40])).
% 4.30/1.80  tff(c_809, plain, (![B_100]: (~r2_hidden(B_100, '#skF_8'))), inference(splitLeft, [status(thm)], [c_705])).
% 4.30/1.80  tff(c_46, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.30/1.80  tff(c_490, plain, (![B_72, D_73, A_74, C_75]: (r2_hidden(B_72, D_73) | ~r2_hidden(k4_tarski(A_74, B_72), k2_zfmisc_1(C_75, D_73)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.30/1.80  tff(c_493, plain, (![B_72, A_74]: (r2_hidden(B_72, '#skF_8') | ~r2_hidden(k4_tarski(A_74, B_72), k2_zfmisc_1('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_48, c_490])).
% 4.30/1.80  tff(c_606, plain, (![B_87, A_86]: (r2_hidden(B_87, '#skF_8') | ~r2_hidden(B_87, '#skF_6') | ~r2_hidden(A_86, '#skF_5'))), inference(resolution, [status(thm)], [c_586, c_493])).
% 4.30/1.80  tff(c_718, plain, (![A_101]: (~r2_hidden(A_101, '#skF_5'))), inference(splitLeft, [status(thm)], [c_606])).
% 4.30/1.80  tff(c_730, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_28, c_718])).
% 4.30/1.80  tff(c_736, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_730])).
% 4.30/1.80  tff(c_738, plain, (![B_102]: (r2_hidden(B_102, '#skF_8') | ~r2_hidden(B_102, '#skF_6'))), inference(splitRight, [status(thm)], [c_606])).
% 4.30/1.80  tff(c_750, plain, (r2_hidden('#skF_4'('#skF_6'), '#skF_8') | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_28, c_738])).
% 4.30/1.80  tff(c_755, plain, (r2_hidden('#skF_4'('#skF_6'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_44, c_750])).
% 4.30/1.80  tff(c_813, plain, $false, inference(negUnitSimplification, [status(thm)], [c_809, c_755])).
% 4.30/1.80  tff(c_815, plain, (![A_107]: (r2_hidden(A_107, '#skF_5') | ~r2_hidden(A_107, '#skF_7'))), inference(splitRight, [status(thm)], [c_705])).
% 4.30/1.80  tff(c_1618, plain, (![B_143]: (r2_hidden('#skF_1'('#skF_7', B_143), '#skF_5') | r1_tarski('#skF_7', B_143))), inference(resolution, [status(thm)], [c_8, c_815])).
% 4.30/1.80  tff(c_1632, plain, (r1_tarski('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_1618, c_6])).
% 4.30/1.80  tff(c_1654, plain, (k3_xboole_0('#skF_7', '#skF_5')='#skF_7'), inference(resolution, [status(thm)], [c_1632, c_30])).
% 4.30/1.80  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.30/1.80  tff(c_1666, plain, (k3_xboole_0('#skF_5', '#skF_7')='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_1654, c_2])).
% 4.30/1.80  tff(c_1678, plain, ('#skF_7'='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_686, c_1666])).
% 4.30/1.80  tff(c_1680, plain, $false, inference(negUnitSimplification, [status(thm)], [c_49, c_1678])).
% 4.30/1.80  tff(c_1681, plain, ('#skF_6'!='#skF_8'), inference(splitRight, [status(thm)], [c_42])).
% 4.30/1.80  tff(c_2189, plain, (![A_203, B_204, C_205, D_206]: (r2_hidden(k4_tarski(A_203, B_204), k2_zfmisc_1(C_205, D_206)) | ~r2_hidden(B_204, D_206) | ~r2_hidden(A_203, C_205))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.30/1.80  tff(c_1682, plain, ('#skF_7'='#skF_5'), inference(splitRight, [status(thm)], [c_42])).
% 4.30/1.80  tff(c_1730, plain, (k2_zfmisc_1('#skF_5', '#skF_6')=k2_zfmisc_1('#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1682, c_48])).
% 4.30/1.80  tff(c_2086, plain, (![B_188, D_189, A_190, C_191]: (r2_hidden(B_188, D_189) | ~r2_hidden(k4_tarski(A_190, B_188), k2_zfmisc_1(C_191, D_189)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.30/1.80  tff(c_2089, plain, (![B_188, A_190]: (r2_hidden(B_188, '#skF_6') | ~r2_hidden(k4_tarski(A_190, B_188), k2_zfmisc_1('#skF_5', '#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_1730, c_2086])).
% 4.30/1.80  tff(c_2205, plain, (![B_204, A_203]: (r2_hidden(B_204, '#skF_6') | ~r2_hidden(B_204, '#skF_8') | ~r2_hidden(A_203, '#skF_5'))), inference(resolution, [status(thm)], [c_2189, c_2089])).
% 4.30/1.80  tff(c_2260, plain, (![A_211]: (~r2_hidden(A_211, '#skF_5'))), inference(splitLeft, [status(thm)], [c_2205])).
% 4.30/1.80  tff(c_2272, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_28, c_2260])).
% 4.30/1.80  tff(c_2278, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_2272])).
% 4.30/1.80  tff(c_2280, plain, (![B_212]: (r2_hidden(B_212, '#skF_6') | ~r2_hidden(B_212, '#skF_8'))), inference(splitRight, [status(thm)], [c_2205])).
% 4.30/1.80  tff(c_2289, plain, (![A_213]: (r1_tarski(A_213, '#skF_6') | ~r2_hidden('#skF_1'(A_213, '#skF_6'), '#skF_8'))), inference(resolution, [status(thm)], [c_2280, c_6])).
% 4.30/1.80  tff(c_2294, plain, (r1_tarski('#skF_8', '#skF_6')), inference(resolution, [status(thm)], [c_8, c_2289])).
% 4.30/1.80  tff(c_2298, plain, (k3_xboole_0('#skF_8', '#skF_6')='#skF_8'), inference(resolution, [status(thm)], [c_2294, c_30])).
% 4.30/1.80  tff(c_2243, plain, (![A_209, B_210]: (r2_hidden(k4_tarski(A_209, B_210), k2_zfmisc_1('#skF_5', '#skF_8')) | ~r2_hidden(B_210, '#skF_6') | ~r2_hidden(A_209, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1730, c_2189])).
% 4.30/1.80  tff(c_38, plain, (![B_22, D_24, A_21, C_23]: (r2_hidden(B_22, D_24) | ~r2_hidden(k4_tarski(A_21, B_22), k2_zfmisc_1(C_23, D_24)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.30/1.80  tff(c_2256, plain, (![B_210, A_209]: (r2_hidden(B_210, '#skF_8') | ~r2_hidden(B_210, '#skF_6') | ~r2_hidden(A_209, '#skF_5'))), inference(resolution, [status(thm)], [c_2243, c_38])).
% 4.30/1.80  tff(c_2353, plain, (![A_220]: (~r2_hidden(A_220, '#skF_5'))), inference(splitLeft, [status(thm)], [c_2256])).
% 4.30/1.80  tff(c_2365, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_28, c_2353])).
% 4.30/1.80  tff(c_2371, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_2365])).
% 4.30/1.80  tff(c_2373, plain, (![B_221]: (r2_hidden(B_221, '#skF_8') | ~r2_hidden(B_221, '#skF_6'))), inference(splitRight, [status(thm)], [c_2256])).
% 4.30/1.80  tff(c_2447, plain, (![B_226]: (r2_hidden('#skF_1'('#skF_6', B_226), '#skF_8') | r1_tarski('#skF_6', B_226))), inference(resolution, [status(thm)], [c_8, c_2373])).
% 4.30/1.80  tff(c_2461, plain, (r1_tarski('#skF_6', '#skF_8')), inference(resolution, [status(thm)], [c_2447, c_6])).
% 4.30/1.80  tff(c_2494, plain, (k3_xboole_0('#skF_6', '#skF_8')='#skF_6'), inference(resolution, [status(thm)], [c_2461, c_30])).
% 4.30/1.80  tff(c_2504, plain, (k3_xboole_0('#skF_8', '#skF_6')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_2494, c_2])).
% 4.30/1.80  tff(c_2516, plain, ('#skF_6'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_2298, c_2504])).
% 4.30/1.80  tff(c_2518, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1681, c_2516])).
% 4.30/1.80  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.30/1.80  
% 4.30/1.80  Inference rules
% 4.30/1.80  ----------------------
% 4.30/1.80  #Ref     : 0
% 4.30/1.80  #Sup     : 560
% 4.30/1.80  #Fact    : 0
% 4.30/1.80  #Define  : 0
% 4.30/1.80  #Split   : 14
% 4.30/1.80  #Chain   : 0
% 4.30/1.81  #Close   : 0
% 4.30/1.81  
% 4.30/1.81  Ordering : KBO
% 4.30/1.81  
% 4.30/1.81  Simplification rules
% 4.30/1.81  ----------------------
% 4.30/1.81  #Subsume      : 68
% 4.30/1.81  #Demod        : 113
% 4.30/1.81  #Tautology    : 220
% 4.30/1.81  #SimpNegUnit  : 21
% 4.30/1.81  #BackRed      : 28
% 4.30/1.81  
% 4.30/1.81  #Partial instantiations: 0
% 4.30/1.81  #Strategies tried      : 1
% 4.30/1.81  
% 4.30/1.81  Timing (in seconds)
% 4.30/1.81  ----------------------
% 4.30/1.81  Preprocessing        : 0.32
% 4.30/1.81  Parsing              : 0.16
% 4.30/1.81  CNF conversion       : 0.03
% 4.30/1.81  Main loop            : 0.70
% 4.30/1.81  Inferencing          : 0.25
% 4.30/1.81  Reduction            : 0.21
% 4.30/1.81  Demodulation         : 0.15
% 4.30/1.81  BG Simplification    : 0.03
% 4.30/1.81  Subsumption          : 0.14
% 4.30/1.81  Abstraction          : 0.03
% 4.30/1.81  MUC search           : 0.00
% 4.30/1.81  Cooper               : 0.00
% 4.30/1.81  Total                : 1.06
% 4.30/1.81  Index Insertion      : 0.00
% 4.30/1.81  Index Deletion       : 0.00
% 4.30/1.81  Index Matching       : 0.00
% 4.30/1.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
