%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:55 EST 2020

% Result     : Theorem 8.20s
% Output     : CNFRefutation 8.20s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 186 expanded)
%              Number of leaves         :   27 (  71 expanded)
%              Depth                    :    8
%              Number of atoms          :  137 ( 356 expanded)
%              Number of equality atoms :    8 (  10 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_67,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_76,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_tarski(A,B),C)
      <=> ( r2_hidden(A,C)
          & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_69,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_59,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_61,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4534,plain,(
    ! [A_6025,B_6026] :
      ( ~ r2_hidden('#skF_1'(A_6025,B_6026),B_6026)
      | r1_tarski(A_6025,B_6026) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4540,plain,(
    ! [A_6027] : r1_tarski(A_6027,A_6027) ),
    inference(resolution,[status(thm)],[c_6,c_4534])).

tff(c_40,plain,(
    ! [A_23,B_24] :
      ( r2_hidden(A_23,B_24)
      | ~ r1_tarski(k1_tarski(A_23),B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_4545,plain,(
    ! [A_23] : r2_hidden(A_23,k1_tarski(A_23)) ),
    inference(resolution,[status(thm)],[c_4540,c_40])).

tff(c_105,plain,(
    ! [A_52,B_53] :
      ( r2_hidden('#skF_1'(A_52,B_53),A_52)
      | r1_tarski(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_111,plain,(
    ! [A_54] : r1_tarski(A_54,A_54) ),
    inference(resolution,[status(thm)],[c_105,c_4])).

tff(c_116,plain,(
    ! [A_23] : r2_hidden(A_23,k1_tarski(A_23)) ),
    inference(resolution,[status(thm)],[c_111,c_40])).

tff(c_50,plain,
    ( r2_hidden('#skF_4','#skF_6')
    | ~ r2_hidden('#skF_8','#skF_9')
    | ~ r2_hidden('#skF_7','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_118,plain,(
    ~ r2_hidden('#skF_7','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_44,plain,(
    ! [A_25,B_26] : r1_tarski(k1_tarski(A_25),k2_tarski(A_25,B_26)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_56,plain,
    ( r2_hidden('#skF_4','#skF_6')
    | r1_tarski(k2_tarski('#skF_7','#skF_8'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_87,plain,(
    r1_tarski(k2_tarski('#skF_7','#skF_8'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_159,plain,(
    ! [A_63,C_64,B_65] :
      ( r1_tarski(A_63,C_64)
      | ~ r1_tarski(B_65,C_64)
      | ~ r1_tarski(A_63,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_172,plain,(
    ! [A_66] :
      ( r1_tarski(A_66,'#skF_9')
      | ~ r1_tarski(A_66,k2_tarski('#skF_7','#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_87,c_159])).

tff(c_188,plain,(
    r1_tarski(k1_tarski('#skF_7'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_44,c_172])).

tff(c_193,plain,(
    r2_hidden('#skF_7','#skF_9') ),
    inference(resolution,[status(thm)],[c_188,c_40])).

tff(c_198,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_193])).

tff(c_200,plain,(
    r2_hidden('#skF_7','#skF_9') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_48,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | ~ r2_hidden('#skF_8','#skF_9')
    | ~ r2_hidden('#skF_7','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_202,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | ~ r2_hidden('#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_48])).

tff(c_203,plain,(
    ~ r2_hidden('#skF_8','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_202])).

tff(c_66,plain,(
    ! [A_40,B_41] : k1_enumset1(A_40,A_40,B_41) = k2_tarski(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_14,plain,(
    ! [E_18,A_12,B_13] : r2_hidden(E_18,k1_enumset1(A_12,B_13,E_18)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_72,plain,(
    ! [B_41,A_40] : r2_hidden(B_41,k2_tarski(A_40,B_41)) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_14])).

tff(c_242,plain,(
    ! [C_71,B_72,A_73] :
      ( r2_hidden(C_71,B_72)
      | ~ r2_hidden(C_71,A_73)
      | ~ r1_tarski(A_73,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_283,plain,(
    ! [B_76,B_77,A_78] :
      ( r2_hidden(B_76,B_77)
      | ~ r1_tarski(k2_tarski(A_78,B_76),B_77) ) ),
    inference(resolution,[status(thm)],[c_72,c_242])).

tff(c_290,plain,(
    r2_hidden('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_87,c_283])).

tff(c_296,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_203,c_290])).

tff(c_298,plain,(
    r2_hidden('#skF_8','#skF_9') ),
    inference(splitRight,[status(thm)],[c_202])).

tff(c_199,plain,
    ( ~ r2_hidden('#skF_8','#skF_9')
    | r2_hidden('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_301,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_298,c_199])).

tff(c_42,plain,(
    ! [A_23,B_24] :
      ( r1_tarski(k1_tarski(A_23),B_24)
      | ~ r2_hidden(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_302,plain,(
    ! [A_79,C_80,B_81] :
      ( r1_tarski(A_79,C_80)
      | ~ r1_tarski(B_81,C_80)
      | ~ r1_tarski(A_79,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_868,plain,(
    ! [A_152,B_153,A_154] :
      ( r1_tarski(A_152,B_153)
      | ~ r1_tarski(A_152,k1_tarski(A_154))
      | ~ r2_hidden(A_154,B_153) ) ),
    inference(resolution,[status(thm)],[c_42,c_302])).

tff(c_1639,plain,(
    ! [A_1694,B_1695,A_1696] :
      ( r1_tarski(k1_tarski(A_1694),B_1695)
      | ~ r2_hidden(A_1696,B_1695)
      | ~ r2_hidden(A_1694,k1_tarski(A_1696)) ) ),
    inference(resolution,[status(thm)],[c_42,c_868])).

tff(c_1703,plain,(
    ! [A_1715] :
      ( r1_tarski(k1_tarski(A_1715),'#skF_6')
      | ~ r2_hidden(A_1715,k1_tarski('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_301,c_1639])).

tff(c_1737,plain,(
    r1_tarski(k1_tarski('#skF_4'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_116,c_1703])).

tff(c_297,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_202])).

tff(c_2488,plain,(
    ! [A_3377] :
      ( r1_tarski(k1_tarski(A_3377),'#skF_6')
      | ~ r2_hidden(A_3377,k1_tarski('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_297,c_1639])).

tff(c_2523,plain,(
    r1_tarski(k1_tarski('#skF_5'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_116,c_2488])).

tff(c_36,plain,(
    ! [A_19,B_20] : k2_xboole_0(k1_tarski(A_19),k1_tarski(B_20)) = k2_tarski(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_428,plain,(
    ! [A_97,C_98,B_99] :
      ( r1_tarski(k2_xboole_0(A_97,C_98),B_99)
      | ~ r1_tarski(C_98,B_99)
      | ~ r1_tarski(A_97,B_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_4446,plain,(
    ! [A_5962,B_5963,B_5964] :
      ( r1_tarski(k2_tarski(A_5962,B_5963),B_5964)
      | ~ r1_tarski(k1_tarski(B_5963),B_5964)
      | ~ r1_tarski(k1_tarski(A_5962),B_5964) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_428])).

tff(c_46,plain,
    ( ~ r1_tarski(k2_tarski('#skF_4','#skF_5'),'#skF_6')
    | ~ r2_hidden('#skF_8','#skF_9')
    | ~ r2_hidden('#skF_7','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_383,plain,(
    ~ r1_tarski(k2_tarski('#skF_4','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_298,c_46])).

tff(c_4488,plain,
    ( ~ r1_tarski(k1_tarski('#skF_5'),'#skF_6')
    | ~ r1_tarski(k1_tarski('#skF_4'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_4446,c_383])).

tff(c_4514,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1737,c_2523,c_4488])).

tff(c_4515,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_4599,plain,(
    ! [A_6040,C_6041,B_6042] :
      ( r1_tarski(A_6040,C_6041)
      | ~ r1_tarski(B_6042,C_6041)
      | ~ r1_tarski(A_6040,B_6042) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_4708,plain,(
    ! [A_6066,B_6067,A_6068] :
      ( r1_tarski(A_6066,B_6067)
      | ~ r1_tarski(A_6066,k1_tarski(A_6068))
      | ~ r2_hidden(A_6068,B_6067) ) ),
    inference(resolution,[status(thm)],[c_42,c_4599])).

tff(c_4764,plain,(
    ! [A_6085,B_6086,A_6087] :
      ( r1_tarski(k1_tarski(A_6085),B_6086)
      | ~ r2_hidden(A_6087,B_6086)
      | ~ r2_hidden(A_6085,k1_tarski(A_6087)) ) ),
    inference(resolution,[status(thm)],[c_42,c_4708])).

tff(c_4908,plain,(
    ! [A_6094] :
      ( r1_tarski(k1_tarski(A_6094),'#skF_6')
      | ~ r2_hidden(A_6094,k1_tarski('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_4515,c_4764])).

tff(c_4933,plain,(
    r1_tarski(k1_tarski('#skF_4'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_4545,c_4908])).

tff(c_4516,plain,(
    ~ r1_tarski(k2_tarski('#skF_7','#skF_8'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_54,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | r1_tarski(k2_tarski('#skF_7','#skF_8'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_4518,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_4516,c_54])).

tff(c_4810,plain,(
    ! [A_6088] :
      ( r1_tarski(k1_tarski(A_6088),'#skF_6')
      | ~ r2_hidden(A_6088,k1_tarski('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_4518,c_4764])).

tff(c_4834,plain,(
    r1_tarski(k1_tarski('#skF_5'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_4545,c_4810])).

tff(c_4717,plain,(
    ! [A_6069,C_6070,B_6071] :
      ( r1_tarski(k2_xboole_0(A_6069,C_6070),B_6071)
      | ~ r1_tarski(C_6070,B_6071)
      | ~ r1_tarski(A_6069,B_6071) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_11083,plain,(
    ! [A_12955,B_12956,B_12957] :
      ( r1_tarski(k2_tarski(A_12955,B_12956),B_12957)
      | ~ r1_tarski(k1_tarski(B_12956),B_12957)
      | ~ r1_tarski(k1_tarski(A_12955),B_12957) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_4717])).

tff(c_52,plain,
    ( ~ r1_tarski(k2_tarski('#skF_4','#skF_5'),'#skF_6')
    | r1_tarski(k2_tarski('#skF_7','#skF_8'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_4619,plain,(
    ~ r1_tarski(k2_tarski('#skF_4','#skF_5'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_4516,c_52])).

tff(c_11140,plain,
    ( ~ r1_tarski(k1_tarski('#skF_5'),'#skF_6')
    | ~ r1_tarski(k1_tarski('#skF_4'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_11083,c_4619])).

tff(c_11177,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4933,c_4834,c_11140])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:40:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.20/2.84  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.20/2.85  
% 8.20/2.85  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.20/2.85  %$ r2_hidden > r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_4 > #skF_3 > #skF_1
% 8.20/2.85  
% 8.20/2.85  %Foreground sorts:
% 8.20/2.85  
% 8.20/2.85  
% 8.20/2.85  %Background operators:
% 8.20/2.85  
% 8.20/2.85  
% 8.20/2.85  %Foreground operators:
% 8.20/2.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.20/2.85  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.20/2.85  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.20/2.85  tff('#skF_7', type, '#skF_7': $i).
% 8.20/2.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.20/2.85  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.20/2.85  tff('#skF_5', type, '#skF_5': $i).
% 8.20/2.85  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 8.20/2.85  tff('#skF_6', type, '#skF_6': $i).
% 8.20/2.85  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.20/2.85  tff('#skF_9', type, '#skF_9': $i).
% 8.20/2.85  tff('#skF_8', type, '#skF_8': $i).
% 8.20/2.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.20/2.85  tff('#skF_4', type, '#skF_4': $i).
% 8.20/2.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.20/2.85  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 8.20/2.85  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.20/2.85  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.20/2.85  
% 8.20/2.87  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 8.20/2.87  tff(f_67, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 8.20/2.87  tff(f_76, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 8.20/2.87  tff(f_69, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 8.20/2.87  tff(f_38, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 8.20/2.87  tff(f_63, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 8.20/2.87  tff(f_59, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 8.20/2.87  tff(f_61, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 8.20/2.87  tff(f_44, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 8.20/2.87  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.20/2.87  tff(c_4534, plain, (![A_6025, B_6026]: (~r2_hidden('#skF_1'(A_6025, B_6026), B_6026) | r1_tarski(A_6025, B_6026))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.20/2.87  tff(c_4540, plain, (![A_6027]: (r1_tarski(A_6027, A_6027))), inference(resolution, [status(thm)], [c_6, c_4534])).
% 8.20/2.87  tff(c_40, plain, (![A_23, B_24]: (r2_hidden(A_23, B_24) | ~r1_tarski(k1_tarski(A_23), B_24))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.20/2.87  tff(c_4545, plain, (![A_23]: (r2_hidden(A_23, k1_tarski(A_23)))), inference(resolution, [status(thm)], [c_4540, c_40])).
% 8.20/2.87  tff(c_105, plain, (![A_52, B_53]: (r2_hidden('#skF_1'(A_52, B_53), A_52) | r1_tarski(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.20/2.87  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.20/2.87  tff(c_111, plain, (![A_54]: (r1_tarski(A_54, A_54))), inference(resolution, [status(thm)], [c_105, c_4])).
% 8.20/2.87  tff(c_116, plain, (![A_23]: (r2_hidden(A_23, k1_tarski(A_23)))), inference(resolution, [status(thm)], [c_111, c_40])).
% 8.20/2.87  tff(c_50, plain, (r2_hidden('#skF_4', '#skF_6') | ~r2_hidden('#skF_8', '#skF_9') | ~r2_hidden('#skF_7', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.20/2.87  tff(c_118, plain, (~r2_hidden('#skF_7', '#skF_9')), inference(splitLeft, [status(thm)], [c_50])).
% 8.20/2.87  tff(c_44, plain, (![A_25, B_26]: (r1_tarski(k1_tarski(A_25), k2_tarski(A_25, B_26)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.20/2.87  tff(c_56, plain, (r2_hidden('#skF_4', '#skF_6') | r1_tarski(k2_tarski('#skF_7', '#skF_8'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.20/2.87  tff(c_87, plain, (r1_tarski(k2_tarski('#skF_7', '#skF_8'), '#skF_9')), inference(splitLeft, [status(thm)], [c_56])).
% 8.20/2.87  tff(c_159, plain, (![A_63, C_64, B_65]: (r1_tarski(A_63, C_64) | ~r1_tarski(B_65, C_64) | ~r1_tarski(A_63, B_65))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.20/2.87  tff(c_172, plain, (![A_66]: (r1_tarski(A_66, '#skF_9') | ~r1_tarski(A_66, k2_tarski('#skF_7', '#skF_8')))), inference(resolution, [status(thm)], [c_87, c_159])).
% 8.20/2.87  tff(c_188, plain, (r1_tarski(k1_tarski('#skF_7'), '#skF_9')), inference(resolution, [status(thm)], [c_44, c_172])).
% 8.20/2.87  tff(c_193, plain, (r2_hidden('#skF_7', '#skF_9')), inference(resolution, [status(thm)], [c_188, c_40])).
% 8.20/2.87  tff(c_198, plain, $false, inference(negUnitSimplification, [status(thm)], [c_118, c_193])).
% 8.20/2.87  tff(c_200, plain, (r2_hidden('#skF_7', '#skF_9')), inference(splitRight, [status(thm)], [c_50])).
% 8.20/2.87  tff(c_48, plain, (r2_hidden('#skF_5', '#skF_6') | ~r2_hidden('#skF_8', '#skF_9') | ~r2_hidden('#skF_7', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.20/2.87  tff(c_202, plain, (r2_hidden('#skF_5', '#skF_6') | ~r2_hidden('#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_200, c_48])).
% 8.20/2.87  tff(c_203, plain, (~r2_hidden('#skF_8', '#skF_9')), inference(splitLeft, [status(thm)], [c_202])).
% 8.20/2.87  tff(c_66, plain, (![A_40, B_41]: (k1_enumset1(A_40, A_40, B_41)=k2_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.20/2.87  tff(c_14, plain, (![E_18, A_12, B_13]: (r2_hidden(E_18, k1_enumset1(A_12, B_13, E_18)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.20/2.87  tff(c_72, plain, (![B_41, A_40]: (r2_hidden(B_41, k2_tarski(A_40, B_41)))), inference(superposition, [status(thm), theory('equality')], [c_66, c_14])).
% 8.20/2.87  tff(c_242, plain, (![C_71, B_72, A_73]: (r2_hidden(C_71, B_72) | ~r2_hidden(C_71, A_73) | ~r1_tarski(A_73, B_72))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.20/2.87  tff(c_283, plain, (![B_76, B_77, A_78]: (r2_hidden(B_76, B_77) | ~r1_tarski(k2_tarski(A_78, B_76), B_77))), inference(resolution, [status(thm)], [c_72, c_242])).
% 8.20/2.87  tff(c_290, plain, (r2_hidden('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_87, c_283])).
% 8.20/2.87  tff(c_296, plain, $false, inference(negUnitSimplification, [status(thm)], [c_203, c_290])).
% 8.20/2.87  tff(c_298, plain, (r2_hidden('#skF_8', '#skF_9')), inference(splitRight, [status(thm)], [c_202])).
% 8.20/2.87  tff(c_199, plain, (~r2_hidden('#skF_8', '#skF_9') | r2_hidden('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_50])).
% 8.20/2.87  tff(c_301, plain, (r2_hidden('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_298, c_199])).
% 8.20/2.87  tff(c_42, plain, (![A_23, B_24]: (r1_tarski(k1_tarski(A_23), B_24) | ~r2_hidden(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.20/2.87  tff(c_302, plain, (![A_79, C_80, B_81]: (r1_tarski(A_79, C_80) | ~r1_tarski(B_81, C_80) | ~r1_tarski(A_79, B_81))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.20/2.87  tff(c_868, plain, (![A_152, B_153, A_154]: (r1_tarski(A_152, B_153) | ~r1_tarski(A_152, k1_tarski(A_154)) | ~r2_hidden(A_154, B_153))), inference(resolution, [status(thm)], [c_42, c_302])).
% 8.20/2.87  tff(c_1639, plain, (![A_1694, B_1695, A_1696]: (r1_tarski(k1_tarski(A_1694), B_1695) | ~r2_hidden(A_1696, B_1695) | ~r2_hidden(A_1694, k1_tarski(A_1696)))), inference(resolution, [status(thm)], [c_42, c_868])).
% 8.20/2.87  tff(c_1703, plain, (![A_1715]: (r1_tarski(k1_tarski(A_1715), '#skF_6') | ~r2_hidden(A_1715, k1_tarski('#skF_4')))), inference(resolution, [status(thm)], [c_301, c_1639])).
% 8.20/2.87  tff(c_1737, plain, (r1_tarski(k1_tarski('#skF_4'), '#skF_6')), inference(resolution, [status(thm)], [c_116, c_1703])).
% 8.20/2.87  tff(c_297, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_202])).
% 8.20/2.87  tff(c_2488, plain, (![A_3377]: (r1_tarski(k1_tarski(A_3377), '#skF_6') | ~r2_hidden(A_3377, k1_tarski('#skF_5')))), inference(resolution, [status(thm)], [c_297, c_1639])).
% 8.20/2.87  tff(c_2523, plain, (r1_tarski(k1_tarski('#skF_5'), '#skF_6')), inference(resolution, [status(thm)], [c_116, c_2488])).
% 8.20/2.87  tff(c_36, plain, (![A_19, B_20]: (k2_xboole_0(k1_tarski(A_19), k1_tarski(B_20))=k2_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.20/2.87  tff(c_428, plain, (![A_97, C_98, B_99]: (r1_tarski(k2_xboole_0(A_97, C_98), B_99) | ~r1_tarski(C_98, B_99) | ~r1_tarski(A_97, B_99))), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.20/2.87  tff(c_4446, plain, (![A_5962, B_5963, B_5964]: (r1_tarski(k2_tarski(A_5962, B_5963), B_5964) | ~r1_tarski(k1_tarski(B_5963), B_5964) | ~r1_tarski(k1_tarski(A_5962), B_5964))), inference(superposition, [status(thm), theory('equality')], [c_36, c_428])).
% 8.20/2.87  tff(c_46, plain, (~r1_tarski(k2_tarski('#skF_4', '#skF_5'), '#skF_6') | ~r2_hidden('#skF_8', '#skF_9') | ~r2_hidden('#skF_7', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.20/2.87  tff(c_383, plain, (~r1_tarski(k2_tarski('#skF_4', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_200, c_298, c_46])).
% 8.20/2.87  tff(c_4488, plain, (~r1_tarski(k1_tarski('#skF_5'), '#skF_6') | ~r1_tarski(k1_tarski('#skF_4'), '#skF_6')), inference(resolution, [status(thm)], [c_4446, c_383])).
% 8.20/2.87  tff(c_4514, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1737, c_2523, c_4488])).
% 8.20/2.87  tff(c_4515, plain, (r2_hidden('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_56])).
% 8.20/2.87  tff(c_4599, plain, (![A_6040, C_6041, B_6042]: (r1_tarski(A_6040, C_6041) | ~r1_tarski(B_6042, C_6041) | ~r1_tarski(A_6040, B_6042))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.20/2.87  tff(c_4708, plain, (![A_6066, B_6067, A_6068]: (r1_tarski(A_6066, B_6067) | ~r1_tarski(A_6066, k1_tarski(A_6068)) | ~r2_hidden(A_6068, B_6067))), inference(resolution, [status(thm)], [c_42, c_4599])).
% 8.20/2.87  tff(c_4764, plain, (![A_6085, B_6086, A_6087]: (r1_tarski(k1_tarski(A_6085), B_6086) | ~r2_hidden(A_6087, B_6086) | ~r2_hidden(A_6085, k1_tarski(A_6087)))), inference(resolution, [status(thm)], [c_42, c_4708])).
% 8.20/2.87  tff(c_4908, plain, (![A_6094]: (r1_tarski(k1_tarski(A_6094), '#skF_6') | ~r2_hidden(A_6094, k1_tarski('#skF_4')))), inference(resolution, [status(thm)], [c_4515, c_4764])).
% 8.20/2.87  tff(c_4933, plain, (r1_tarski(k1_tarski('#skF_4'), '#skF_6')), inference(resolution, [status(thm)], [c_4545, c_4908])).
% 8.20/2.87  tff(c_4516, plain, (~r1_tarski(k2_tarski('#skF_7', '#skF_8'), '#skF_9')), inference(splitRight, [status(thm)], [c_56])).
% 8.20/2.87  tff(c_54, plain, (r2_hidden('#skF_5', '#skF_6') | r1_tarski(k2_tarski('#skF_7', '#skF_8'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.20/2.87  tff(c_4518, plain, (r2_hidden('#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_4516, c_54])).
% 8.20/2.87  tff(c_4810, plain, (![A_6088]: (r1_tarski(k1_tarski(A_6088), '#skF_6') | ~r2_hidden(A_6088, k1_tarski('#skF_5')))), inference(resolution, [status(thm)], [c_4518, c_4764])).
% 8.20/2.87  tff(c_4834, plain, (r1_tarski(k1_tarski('#skF_5'), '#skF_6')), inference(resolution, [status(thm)], [c_4545, c_4810])).
% 8.20/2.87  tff(c_4717, plain, (![A_6069, C_6070, B_6071]: (r1_tarski(k2_xboole_0(A_6069, C_6070), B_6071) | ~r1_tarski(C_6070, B_6071) | ~r1_tarski(A_6069, B_6071))), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.20/2.87  tff(c_11083, plain, (![A_12955, B_12956, B_12957]: (r1_tarski(k2_tarski(A_12955, B_12956), B_12957) | ~r1_tarski(k1_tarski(B_12956), B_12957) | ~r1_tarski(k1_tarski(A_12955), B_12957))), inference(superposition, [status(thm), theory('equality')], [c_36, c_4717])).
% 8.20/2.87  tff(c_52, plain, (~r1_tarski(k2_tarski('#skF_4', '#skF_5'), '#skF_6') | r1_tarski(k2_tarski('#skF_7', '#skF_8'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.20/2.87  tff(c_4619, plain, (~r1_tarski(k2_tarski('#skF_4', '#skF_5'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_4516, c_52])).
% 8.20/2.87  tff(c_11140, plain, (~r1_tarski(k1_tarski('#skF_5'), '#skF_6') | ~r1_tarski(k1_tarski('#skF_4'), '#skF_6')), inference(resolution, [status(thm)], [c_11083, c_4619])).
% 8.20/2.87  tff(c_11177, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4933, c_4834, c_11140])).
% 8.20/2.87  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.20/2.87  
% 8.20/2.87  Inference rules
% 8.20/2.87  ----------------------
% 8.20/2.87  #Ref     : 0
% 8.20/2.87  #Sup     : 1895
% 8.20/2.87  #Fact    : 36
% 8.20/2.87  #Define  : 0
% 8.20/2.87  #Split   : 15
% 8.20/2.87  #Chain   : 0
% 8.20/2.87  #Close   : 0
% 8.20/2.87  
% 8.20/2.87  Ordering : KBO
% 8.20/2.87  
% 8.20/2.87  Simplification rules
% 8.20/2.87  ----------------------
% 8.20/2.87  #Subsume      : 353
% 8.20/2.87  #Demod        : 159
% 8.20/2.87  #Tautology    : 235
% 8.20/2.87  #SimpNegUnit  : 4
% 8.20/2.87  #BackRed      : 0
% 8.20/2.87  
% 8.20/2.87  #Partial instantiations: 8970
% 8.20/2.87  #Strategies tried      : 1
% 8.20/2.87  
% 8.20/2.87  Timing (in seconds)
% 8.20/2.87  ----------------------
% 8.20/2.87  Preprocessing        : 0.32
% 8.20/2.87  Parsing              : 0.17
% 8.20/2.87  CNF conversion       : 0.02
% 8.20/2.87  Main loop            : 1.69
% 8.20/2.87  Inferencing          : 0.82
% 8.20/2.87  Reduction            : 0.35
% 8.20/2.87  Demodulation         : 0.24
% 8.20/2.87  BG Simplification    : 0.09
% 8.20/2.87  Subsumption          : 0.34
% 8.20/2.87  Abstraction          : 0.10
% 8.20/2.87  MUC search           : 0.00
% 8.20/2.87  Cooper               : 0.00
% 8.20/2.87  Total                : 2.05
% 8.20/2.87  Index Insertion      : 0.00
% 8.20/2.87  Index Deletion       : 0.00
% 8.20/2.87  Index Matching       : 0.00
% 8.20/2.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
