%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:41 EST 2020

% Result     : Theorem 5.87s
% Output     : CNFRefutation 6.05s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 110 expanded)
%              Number of leaves         :   28 (  49 expanded)
%              Depth                    :   12
%              Number of atoms          :  113 ( 210 expanded)
%              Number of equality atoms :   22 (  44 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k7_relat_1 > k4_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_92,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k7_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_69,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_49,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_47,axiom,(
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

tff(f_85,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
      <=> ( r2_hidden(A,B)
          & r2_hidden(A,k1_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(c_50,plain,
    ( k7_relat_1('#skF_7','#skF_6') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_7'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_80,plain,(
    r1_xboole_0(k1_relat_1('#skF_7'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_44,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_7'),'#skF_6')
    | k7_relat_1('#skF_7','#skF_6') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_106,plain,(
    k7_relat_1('#skF_7','#skF_6') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_44])).

tff(c_42,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_30,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_240,plain,(
    ! [A_80,B_81] :
      ( r2_hidden(k4_tarski('#skF_2'(A_80,B_81),'#skF_3'(A_80,B_81)),A_80)
      | r2_hidden('#skF_4'(A_80,B_81),B_81)
      | k1_relat_1(A_80) = B_81 ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_10,plain,(
    ! [A_8] : r1_xboole_0(A_8,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_98,plain,(
    ! [A_44,B_45] :
      ( ~ r2_hidden(A_44,B_45)
      | ~ r1_xboole_0(k1_tarski(A_44),B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_103,plain,(
    ! [A_44] : ~ r2_hidden(A_44,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10,c_98])).

tff(c_259,plain,(
    ! [B_81] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_81),B_81)
      | k1_relat_1(k1_xboole_0) = B_81 ) ),
    inference(resolution,[status(thm)],[c_240,c_103])).

tff(c_265,plain,(
    ! [B_81] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_81),B_81)
      | k1_xboole_0 = B_81 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_259])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_146,plain,(
    ! [A_58,B_59,C_60] :
      ( r2_hidden(A_58,B_59)
      | ~ r2_hidden(A_58,k1_relat_1(k7_relat_1(C_60,B_59)))
      | ~ v1_relat_1(C_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_156,plain,(
    ! [A_3,C_60,B_59] :
      ( r2_hidden('#skF_1'(A_3,k1_relat_1(k7_relat_1(C_60,B_59))),B_59)
      | ~ v1_relat_1(C_60)
      | r1_xboole_0(A_3,k1_relat_1(k7_relat_1(C_60,B_59))) ) ),
    inference(resolution,[status(thm)],[c_6,c_146])).

tff(c_172,plain,(
    ! [A_65,C_66,B_67] :
      ( r2_hidden(A_65,k1_relat_1(C_66))
      | ~ r2_hidden(A_65,k1_relat_1(k7_relat_1(C_66,B_67)))
      | ~ v1_relat_1(C_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1527,plain,(
    ! [A_132,C_133,B_134] :
      ( r2_hidden('#skF_1'(A_132,k1_relat_1(k7_relat_1(C_133,B_134))),k1_relat_1(C_133))
      | ~ v1_relat_1(C_133)
      | r1_xboole_0(A_132,k1_relat_1(k7_relat_1(C_133,B_134))) ) ),
    inference(resolution,[status(thm)],[c_6,c_172])).

tff(c_122,plain,(
    ! [A_54,B_55,C_56] :
      ( ~ r1_xboole_0(A_54,B_55)
      | ~ r2_hidden(C_56,B_55)
      | ~ r2_hidden(C_56,A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_132,plain,(
    ! [C_56] :
      ( ~ r2_hidden(C_56,'#skF_6')
      | ~ r2_hidden(C_56,k1_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_80,c_122])).

tff(c_1547,plain,(
    ! [A_132,B_134] :
      ( ~ r2_hidden('#skF_1'(A_132,k1_relat_1(k7_relat_1('#skF_7',B_134))),'#skF_6')
      | ~ v1_relat_1('#skF_7')
      | r1_xboole_0(A_132,k1_relat_1(k7_relat_1('#skF_7',B_134))) ) ),
    inference(resolution,[status(thm)],[c_1527,c_132])).

tff(c_5233,plain,(
    ! [A_228,B_229] :
      ( ~ r2_hidden('#skF_1'(A_228,k1_relat_1(k7_relat_1('#skF_7',B_229))),'#skF_6')
      | r1_xboole_0(A_228,k1_relat_1(k7_relat_1('#skF_7',B_229))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1547])).

tff(c_5261,plain,(
    ! [A_3] :
      ( ~ v1_relat_1('#skF_7')
      | r1_xboole_0(A_3,k1_relat_1(k7_relat_1('#skF_7','#skF_6'))) ) ),
    inference(resolution,[status(thm)],[c_156,c_5233])).

tff(c_5297,plain,(
    ! [A_230] : r1_xboole_0(A_230,k1_relat_1(k7_relat_1('#skF_7','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_5261])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( ~ r2_hidden(A_9,B_10)
      | ~ r1_xboole_0(k1_tarski(A_9),B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_5365,plain,(
    ! [A_232] : ~ r2_hidden(A_232,k1_relat_1(k7_relat_1('#skF_7','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_5297,c_12])).

tff(c_5455,plain,(
    k1_relat_1(k7_relat_1('#skF_7','#skF_6')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_265,c_5365])).

tff(c_26,plain,(
    ! [A_30,B_31] :
      ( v1_relat_1(k7_relat_1(A_30,B_31))
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_70,plain,(
    ! [A_42] :
      ( k1_relat_1(A_42) != k1_xboole_0
      | k1_xboole_0 = A_42
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_77,plain,(
    ! [A_30,B_31] :
      ( k1_relat_1(k7_relat_1(A_30,B_31)) != k1_xboole_0
      | k7_relat_1(A_30,B_31) = k1_xboole_0
      | ~ v1_relat_1(A_30) ) ),
    inference(resolution,[status(thm)],[c_26,c_70])).

tff(c_5608,plain,
    ( k7_relat_1('#skF_7','#skF_6') = k1_xboole_0
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_5455,c_77])).

tff(c_5671,plain,(
    k7_relat_1('#skF_7','#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_5608])).

tff(c_5673,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_5671])).

tff(c_5674,plain,(
    k7_relat_1('#skF_7','#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_5686,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_7'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5674,c_44])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_5694,plain,(
    ! [A_237,B_238] :
      ( ~ r2_hidden(A_237,B_238)
      | ~ r1_xboole_0(k1_tarski(A_237),B_238) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_5699,plain,(
    ! [A_237] : ~ r2_hidden(A_237,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10,c_5694])).

tff(c_5812,plain,(
    ! [A_268,C_269,B_270] :
      ( r2_hidden(A_268,k1_relat_1(k7_relat_1(C_269,B_270)))
      | ~ r2_hidden(A_268,k1_relat_1(C_269))
      | ~ r2_hidden(A_268,B_270)
      | ~ v1_relat_1(C_269) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_5832,plain,(
    ! [A_268] :
      ( r2_hidden(A_268,k1_relat_1(k1_xboole_0))
      | ~ r2_hidden(A_268,k1_relat_1('#skF_7'))
      | ~ r2_hidden(A_268,'#skF_6')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5674,c_5812])).

tff(c_5839,plain,(
    ! [A_268] :
      ( r2_hidden(A_268,k1_xboole_0)
      | ~ r2_hidden(A_268,k1_relat_1('#skF_7'))
      | ~ r2_hidden(A_268,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_30,c_5832])).

tff(c_5841,plain,(
    ! [A_271] :
      ( ~ r2_hidden(A_271,k1_relat_1('#skF_7'))
      | ~ r2_hidden(A_271,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_5699,c_5839])).

tff(c_5857,plain,(
    ! [B_272] :
      ( ~ r2_hidden('#skF_1'(k1_relat_1('#skF_7'),B_272),'#skF_6')
      | r1_xboole_0(k1_relat_1('#skF_7'),B_272) ) ),
    inference(resolution,[status(thm)],[c_8,c_5841])).

tff(c_5861,plain,(
    r1_xboole_0(k1_relat_1('#skF_7'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_6,c_5857])).

tff(c_5865,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5686,c_5686,c_5861])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:40:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.87/2.10  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.98/2.11  
% 5.98/2.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.98/2.11  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k7_relat_1 > k4_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_1 > #skF_4
% 5.98/2.11  
% 5.98/2.11  %Foreground sorts:
% 5.98/2.11  
% 5.98/2.11  
% 5.98/2.11  %Background operators:
% 5.98/2.11  
% 5.98/2.11  
% 5.98/2.11  %Foreground operators:
% 5.98/2.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.98/2.11  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.98/2.11  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.98/2.11  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.98/2.11  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.98/2.11  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.98/2.11  tff('#skF_7', type, '#skF_7': $i).
% 5.98/2.11  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.98/2.11  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.98/2.11  tff('#skF_6', type, '#skF_6': $i).
% 5.98/2.11  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 5.98/2.11  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.98/2.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.98/2.11  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.98/2.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.98/2.11  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.98/2.11  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.98/2.11  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.98/2.11  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 5.98/2.11  
% 5.98/2.12  tff(f_92, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 5.98/2.12  tff(f_69, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 5.98/2.12  tff(f_62, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 5.98/2.12  tff(f_49, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 5.98/2.12  tff(f_54, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 5.98/2.12  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 6.05/2.12  tff(f_85, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) <=> (r2_hidden(A, B) & r2_hidden(A, k1_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_relat_1)).
% 6.05/2.12  tff(f_66, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 6.05/2.12  tff(f_77, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 6.05/2.12  tff(c_50, plain, (k7_relat_1('#skF_7', '#skF_6')=k1_xboole_0 | r1_xboole_0(k1_relat_1('#skF_7'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_92])).
% 6.05/2.12  tff(c_80, plain, (r1_xboole_0(k1_relat_1('#skF_7'), '#skF_6')), inference(splitLeft, [status(thm)], [c_50])).
% 6.05/2.12  tff(c_44, plain, (~r1_xboole_0(k1_relat_1('#skF_7'), '#skF_6') | k7_relat_1('#skF_7', '#skF_6')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_92])).
% 6.05/2.12  tff(c_106, plain, (k7_relat_1('#skF_7', '#skF_6')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_80, c_44])).
% 6.05/2.12  tff(c_42, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_92])).
% 6.05/2.12  tff(c_30, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.05/2.12  tff(c_240, plain, (![A_80, B_81]: (r2_hidden(k4_tarski('#skF_2'(A_80, B_81), '#skF_3'(A_80, B_81)), A_80) | r2_hidden('#skF_4'(A_80, B_81), B_81) | k1_relat_1(A_80)=B_81)), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.05/2.12  tff(c_10, plain, (![A_8]: (r1_xboole_0(A_8, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.05/2.12  tff(c_98, plain, (![A_44, B_45]: (~r2_hidden(A_44, B_45) | ~r1_xboole_0(k1_tarski(A_44), B_45))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.05/2.12  tff(c_103, plain, (![A_44]: (~r2_hidden(A_44, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_98])).
% 6.05/2.12  tff(c_259, plain, (![B_81]: (r2_hidden('#skF_4'(k1_xboole_0, B_81), B_81) | k1_relat_1(k1_xboole_0)=B_81)), inference(resolution, [status(thm)], [c_240, c_103])).
% 6.05/2.12  tff(c_265, plain, (![B_81]: (r2_hidden('#skF_4'(k1_xboole_0, B_81), B_81) | k1_xboole_0=B_81)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_259])).
% 6.05/2.12  tff(c_6, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.05/2.12  tff(c_146, plain, (![A_58, B_59, C_60]: (r2_hidden(A_58, B_59) | ~r2_hidden(A_58, k1_relat_1(k7_relat_1(C_60, B_59))) | ~v1_relat_1(C_60))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.05/2.12  tff(c_156, plain, (![A_3, C_60, B_59]: (r2_hidden('#skF_1'(A_3, k1_relat_1(k7_relat_1(C_60, B_59))), B_59) | ~v1_relat_1(C_60) | r1_xboole_0(A_3, k1_relat_1(k7_relat_1(C_60, B_59))))), inference(resolution, [status(thm)], [c_6, c_146])).
% 6.05/2.12  tff(c_172, plain, (![A_65, C_66, B_67]: (r2_hidden(A_65, k1_relat_1(C_66)) | ~r2_hidden(A_65, k1_relat_1(k7_relat_1(C_66, B_67))) | ~v1_relat_1(C_66))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.05/2.12  tff(c_1527, plain, (![A_132, C_133, B_134]: (r2_hidden('#skF_1'(A_132, k1_relat_1(k7_relat_1(C_133, B_134))), k1_relat_1(C_133)) | ~v1_relat_1(C_133) | r1_xboole_0(A_132, k1_relat_1(k7_relat_1(C_133, B_134))))), inference(resolution, [status(thm)], [c_6, c_172])).
% 6.05/2.12  tff(c_122, plain, (![A_54, B_55, C_56]: (~r1_xboole_0(A_54, B_55) | ~r2_hidden(C_56, B_55) | ~r2_hidden(C_56, A_54))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.05/2.12  tff(c_132, plain, (![C_56]: (~r2_hidden(C_56, '#skF_6') | ~r2_hidden(C_56, k1_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_80, c_122])).
% 6.05/2.12  tff(c_1547, plain, (![A_132, B_134]: (~r2_hidden('#skF_1'(A_132, k1_relat_1(k7_relat_1('#skF_7', B_134))), '#skF_6') | ~v1_relat_1('#skF_7') | r1_xboole_0(A_132, k1_relat_1(k7_relat_1('#skF_7', B_134))))), inference(resolution, [status(thm)], [c_1527, c_132])).
% 6.05/2.12  tff(c_5233, plain, (![A_228, B_229]: (~r2_hidden('#skF_1'(A_228, k1_relat_1(k7_relat_1('#skF_7', B_229))), '#skF_6') | r1_xboole_0(A_228, k1_relat_1(k7_relat_1('#skF_7', B_229))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1547])).
% 6.05/2.12  tff(c_5261, plain, (![A_3]: (~v1_relat_1('#skF_7') | r1_xboole_0(A_3, k1_relat_1(k7_relat_1('#skF_7', '#skF_6'))))), inference(resolution, [status(thm)], [c_156, c_5233])).
% 6.05/2.12  tff(c_5297, plain, (![A_230]: (r1_xboole_0(A_230, k1_relat_1(k7_relat_1('#skF_7', '#skF_6'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_5261])).
% 6.05/2.12  tff(c_12, plain, (![A_9, B_10]: (~r2_hidden(A_9, B_10) | ~r1_xboole_0(k1_tarski(A_9), B_10))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.05/2.12  tff(c_5365, plain, (![A_232]: (~r2_hidden(A_232, k1_relat_1(k7_relat_1('#skF_7', '#skF_6'))))), inference(resolution, [status(thm)], [c_5297, c_12])).
% 6.05/2.12  tff(c_5455, plain, (k1_relat_1(k7_relat_1('#skF_7', '#skF_6'))=k1_xboole_0), inference(resolution, [status(thm)], [c_265, c_5365])).
% 6.05/2.12  tff(c_26, plain, (![A_30, B_31]: (v1_relat_1(k7_relat_1(A_30, B_31)) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.05/2.12  tff(c_70, plain, (![A_42]: (k1_relat_1(A_42)!=k1_xboole_0 | k1_xboole_0=A_42 | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.05/2.12  tff(c_77, plain, (![A_30, B_31]: (k1_relat_1(k7_relat_1(A_30, B_31))!=k1_xboole_0 | k7_relat_1(A_30, B_31)=k1_xboole_0 | ~v1_relat_1(A_30))), inference(resolution, [status(thm)], [c_26, c_70])).
% 6.05/2.12  tff(c_5608, plain, (k7_relat_1('#skF_7', '#skF_6')=k1_xboole_0 | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_5455, c_77])).
% 6.05/2.12  tff(c_5671, plain, (k7_relat_1('#skF_7', '#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_42, c_5608])).
% 6.05/2.12  tff(c_5673, plain, $false, inference(negUnitSimplification, [status(thm)], [c_106, c_5671])).
% 6.05/2.12  tff(c_5674, plain, (k7_relat_1('#skF_7', '#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_50])).
% 6.05/2.12  tff(c_5686, plain, (~r1_xboole_0(k1_relat_1('#skF_7'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_5674, c_44])).
% 6.05/2.12  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.05/2.12  tff(c_5694, plain, (![A_237, B_238]: (~r2_hidden(A_237, B_238) | ~r1_xboole_0(k1_tarski(A_237), B_238))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.05/2.12  tff(c_5699, plain, (![A_237]: (~r2_hidden(A_237, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_5694])).
% 6.05/2.12  tff(c_5812, plain, (![A_268, C_269, B_270]: (r2_hidden(A_268, k1_relat_1(k7_relat_1(C_269, B_270))) | ~r2_hidden(A_268, k1_relat_1(C_269)) | ~r2_hidden(A_268, B_270) | ~v1_relat_1(C_269))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.05/2.12  tff(c_5832, plain, (![A_268]: (r2_hidden(A_268, k1_relat_1(k1_xboole_0)) | ~r2_hidden(A_268, k1_relat_1('#skF_7')) | ~r2_hidden(A_268, '#skF_6') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_5674, c_5812])).
% 6.05/2.12  tff(c_5839, plain, (![A_268]: (r2_hidden(A_268, k1_xboole_0) | ~r2_hidden(A_268, k1_relat_1('#skF_7')) | ~r2_hidden(A_268, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_30, c_5832])).
% 6.05/2.12  tff(c_5841, plain, (![A_271]: (~r2_hidden(A_271, k1_relat_1('#skF_7')) | ~r2_hidden(A_271, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_5699, c_5839])).
% 6.05/2.12  tff(c_5857, plain, (![B_272]: (~r2_hidden('#skF_1'(k1_relat_1('#skF_7'), B_272), '#skF_6') | r1_xboole_0(k1_relat_1('#skF_7'), B_272))), inference(resolution, [status(thm)], [c_8, c_5841])).
% 6.05/2.12  tff(c_5861, plain, (r1_xboole_0(k1_relat_1('#skF_7'), '#skF_6')), inference(resolution, [status(thm)], [c_6, c_5857])).
% 6.05/2.12  tff(c_5865, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5686, c_5686, c_5861])).
% 6.05/2.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.05/2.12  
% 6.05/2.12  Inference rules
% 6.05/2.12  ----------------------
% 6.05/2.12  #Ref     : 0
% 6.05/2.12  #Sup     : 1307
% 6.05/2.12  #Fact    : 0
% 6.05/2.12  #Define  : 0
% 6.05/2.12  #Split   : 4
% 6.05/2.12  #Chain   : 0
% 6.05/2.12  #Close   : 0
% 6.05/2.12  
% 6.05/2.12  Ordering : KBO
% 6.05/2.12  
% 6.05/2.12  Simplification rules
% 6.05/2.12  ----------------------
% 6.05/2.12  #Subsume      : 492
% 6.05/2.12  #Demod        : 1440
% 6.05/2.12  #Tautology    : 299
% 6.05/2.12  #SimpNegUnit  : 147
% 6.05/2.12  #BackRed      : 7
% 6.05/2.12  
% 6.05/2.12  #Partial instantiations: 0
% 6.05/2.12  #Strategies tried      : 1
% 6.05/2.12  
% 6.05/2.12  Timing (in seconds)
% 6.05/2.12  ----------------------
% 6.05/2.13  Preprocessing        : 0.29
% 6.05/2.13  Parsing              : 0.15
% 6.05/2.13  CNF conversion       : 0.02
% 6.05/2.13  Main loop            : 1.04
% 6.05/2.13  Inferencing          : 0.36
% 6.05/2.13  Reduction            : 0.31
% 6.05/2.13  Demodulation         : 0.21
% 6.05/2.13  BG Simplification    : 0.04
% 6.05/2.13  Subsumption          : 0.27
% 6.05/2.13  Abstraction          : 0.05
% 6.05/2.13  MUC search           : 0.00
% 6.05/2.13  Cooper               : 0.00
% 6.05/2.13  Total                : 1.36
% 6.05/2.13  Index Insertion      : 0.00
% 6.05/2.13  Index Deletion       : 0.00
% 6.05/2.13  Index Matching       : 0.00
% 6.05/2.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
