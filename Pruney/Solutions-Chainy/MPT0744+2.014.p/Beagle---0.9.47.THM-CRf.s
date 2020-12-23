%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:16 EST 2020

% Result     : Theorem 43.76s
% Output     : CNFRefutation 43.76s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 130 expanded)
%              Number of leaves         :   34 (  60 expanded)
%              Depth                    :    8
%              Number of atoms          :  123 ( 252 expanded)
%              Number of equality atoms :   15 (  32 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_1 > #skF_7 > #skF_3 > #skF_2 > #skF_8 > #skF_6 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_132,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,k1_ordinal1(B))
            <=> r1_ordinal1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_108,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_100,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_117,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r1_ordinal1(A,B)
            | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(c_120,plain,(
    v3_ordinal1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_26,plain,(
    ! [B_10] : r1_tarski(B_10,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_72820,plain,(
    ! [A_89898,B_89899] :
      ( r1_ordinal1(A_89898,B_89899)
      | ~ r1_tarski(A_89898,B_89899)
      | ~ v3_ordinal1(B_89899)
      | ~ v3_ordinal1(A_89898) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_72828,plain,(
    ! [B_10] :
      ( r1_ordinal1(B_10,B_10)
      | ~ v3_ordinal1(B_10) ) ),
    inference(resolution,[status(thm)],[c_26,c_72820])).

tff(c_30,plain,(
    ! [C_15] : r2_hidden(C_15,k1_tarski(C_15)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_110,plain,(
    ! [A_58] : k2_xboole_0(A_58,k1_tarski(A_58)) = k1_ordinal1(A_58) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_209,plain,(
    ! [D_84,B_85,A_86] :
      ( ~ r2_hidden(D_84,B_85)
      | r2_hidden(D_84,k2_xboole_0(A_86,B_85)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1510,plain,(
    ! [D_4754,A_4755] :
      ( ~ r2_hidden(D_4754,k1_tarski(A_4755))
      | r2_hidden(D_4754,k1_ordinal1(A_4755)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_209])).

tff(c_1523,plain,(
    ! [C_15] : r2_hidden(C_15,k1_ordinal1(C_15)) ),
    inference(resolution,[status(thm)],[c_30,c_1510])).

tff(c_122,plain,(
    v3_ordinal1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_517,plain,(
    ! [B_120,A_121] :
      ( r2_hidden(B_120,A_121)
      | r1_ordinal1(A_121,B_120)
      | ~ v3_ordinal1(B_120)
      | ~ v3_ordinal1(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_257,plain,(
    ! [D_93,A_94,B_95] :
      ( ~ r2_hidden(D_93,A_94)
      | r2_hidden(D_93,k2_xboole_0(A_94,B_95)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_323,plain,(
    ! [D_102,A_103] :
      ( ~ r2_hidden(D_102,A_103)
      | r2_hidden(D_102,k1_ordinal1(A_103)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_257])).

tff(c_124,plain,
    ( ~ r1_ordinal1('#skF_7','#skF_8')
    | ~ r2_hidden('#skF_7',k1_ordinal1('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_163,plain,(
    ~ r2_hidden('#skF_7',k1_ordinal1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_124])).

tff(c_357,plain,(
    ~ r2_hidden('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_323,c_163])).

tff(c_548,plain,
    ( r1_ordinal1('#skF_8','#skF_7')
    | ~ v3_ordinal1('#skF_7')
    | ~ v3_ordinal1('#skF_8') ),
    inference(resolution,[status(thm)],[c_517,c_357])).

tff(c_593,plain,(
    r1_ordinal1('#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_122,c_548])).

tff(c_130,plain,
    ( r2_hidden('#skF_7',k1_ordinal1('#skF_8'))
    | r1_ordinal1('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_208,plain,(
    r1_ordinal1('#skF_7','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_163,c_130])).

tff(c_114,plain,(
    ! [A_59,B_60] :
      ( r1_tarski(A_59,B_60)
      | ~ r1_ordinal1(A_59,B_60)
      | ~ v3_ordinal1(B_60)
      | ~ v3_ordinal1(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_376,plain,(
    ! [A_105,B_106] :
      ( r1_tarski(A_105,B_106)
      | ~ r1_ordinal1(A_105,B_106)
      | ~ v3_ordinal1(B_106)
      | ~ v3_ordinal1(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_22,plain,(
    ! [B_10,A_9] :
      ( B_10 = A_9
      | ~ r1_tarski(B_10,A_9)
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_18796,plain,(
    ! [B_30775,A_30776] :
      ( B_30775 = A_30776
      | ~ r1_tarski(B_30775,A_30776)
      | ~ r1_ordinal1(A_30776,B_30775)
      | ~ v3_ordinal1(B_30775)
      | ~ v3_ordinal1(A_30776) ) ),
    inference(resolution,[status(thm)],[c_376,c_22])).

tff(c_72172,plain,(
    ! [B_89775,A_89776] :
      ( B_89775 = A_89776
      | ~ r1_ordinal1(B_89775,A_89776)
      | ~ r1_ordinal1(A_89776,B_89775)
      | ~ v3_ordinal1(B_89775)
      | ~ v3_ordinal1(A_89776) ) ),
    inference(resolution,[status(thm)],[c_114,c_18796])).

tff(c_72210,plain,
    ( '#skF_7' = '#skF_8'
    | ~ r1_ordinal1('#skF_8','#skF_7')
    | ~ v3_ordinal1('#skF_7')
    | ~ v3_ordinal1('#skF_8') ),
    inference(resolution,[status(thm)],[c_208,c_72172])).

tff(c_72234,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_122,c_593,c_72210])).

tff(c_72243,plain,(
    ~ r2_hidden('#skF_8',k1_ordinal1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72234,c_163])).

tff(c_72247,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1523,c_72243])).

tff(c_72248,plain,(
    ~ r1_ordinal1('#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_124])).

tff(c_72249,plain,(
    r2_hidden('#skF_7',k1_ordinal1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_124])).

tff(c_73088,plain,(
    ! [D_89933,B_89934,A_89935] :
      ( r2_hidden(D_89933,B_89934)
      | r2_hidden(D_89933,A_89935)
      | ~ r2_hidden(D_89933,k2_xboole_0(A_89935,B_89934)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_89035,plain,(
    ! [D_119901,A_119902] :
      ( r2_hidden(D_119901,k1_tarski(A_119902))
      | r2_hidden(D_119901,A_119902)
      | ~ r2_hidden(D_119901,k1_ordinal1(A_119902)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_73088])).

tff(c_28,plain,(
    ! [C_15,A_11] :
      ( C_15 = A_11
      | ~ r2_hidden(C_15,k1_tarski(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_90601,plain,(
    ! [D_120040,A_120041] :
      ( D_120040 = A_120041
      | r2_hidden(D_120040,A_120041)
      | ~ r2_hidden(D_120040,k1_ordinal1(A_120041)) ) ),
    inference(resolution,[status(thm)],[c_89035,c_28])).

tff(c_90670,plain,
    ( '#skF_7' = '#skF_8'
    | r2_hidden('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_72249,c_90601])).

tff(c_90671,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_90670])).

tff(c_72686,plain,(
    ! [B_89894,A_89895] :
      ( r2_hidden(B_89894,A_89895)
      | r1_ordinal1(A_89895,B_89894)
      | ~ v3_ordinal1(B_89894)
      | ~ v3_ordinal1(A_89895) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_72792,plain,(
    ! [A_89895,B_89894] :
      ( ~ r2_hidden(A_89895,B_89894)
      | r1_ordinal1(A_89895,B_89894)
      | ~ v3_ordinal1(B_89894)
      | ~ v3_ordinal1(A_89895) ) ),
    inference(resolution,[status(thm)],[c_72686,c_2])).

tff(c_90674,plain,
    ( r1_ordinal1('#skF_7','#skF_8')
    | ~ v3_ordinal1('#skF_8')
    | ~ v3_ordinal1('#skF_7') ),
    inference(resolution,[status(thm)],[c_90671,c_72792])).

tff(c_90682,plain,(
    r1_ordinal1('#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_120,c_90674])).

tff(c_90684,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72248,c_90682])).

tff(c_90685,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_90670])).

tff(c_90692,plain,(
    ~ r1_ordinal1('#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90685,c_72248])).

tff(c_90713,plain,(
    ~ v3_ordinal1('#skF_8') ),
    inference(resolution,[status(thm)],[c_72828,c_90692])).

tff(c_90717,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_90713])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:19:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 43.76/31.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 43.76/31.35  
% 43.76/31.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 43.76/31.35  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_1 > #skF_7 > #skF_3 > #skF_2 > #skF_8 > #skF_6 > #skF_5 > #skF_4
% 43.76/31.35  
% 43.76/31.35  %Foreground sorts:
% 43.76/31.35  
% 43.76/31.35  
% 43.76/31.35  %Background operators:
% 43.76/31.35  
% 43.76/31.35  
% 43.76/31.35  %Foreground operators:
% 43.76/31.35  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 43.76/31.35  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 43.76/31.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 43.76/31.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 43.76/31.35  tff(k1_tarski, type, k1_tarski: $i > $i).
% 43.76/31.35  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 43.76/31.35  tff('#skF_7', type, '#skF_7': $i).
% 43.76/31.35  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 43.76/31.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 43.76/31.35  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 43.76/31.35  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 43.76/31.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 43.76/31.35  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 43.76/31.35  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 43.76/31.36  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 43.76/31.36  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 43.76/31.36  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 43.76/31.36  tff('#skF_8', type, '#skF_8': $i).
% 43.76/31.36  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 43.76/31.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 43.76/31.36  tff(k3_tarski, type, k3_tarski: $i > $i).
% 43.76/31.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 43.76/31.36  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 43.76/31.36  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 43.76/31.36  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 43.76/31.36  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 43.76/31.36  
% 43.76/31.37  tff(f_132, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, k1_ordinal1(B)) <=> r1_ordinal1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_ordinal1)).
% 43.76/31.37  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 43.76/31.37  tff(f_108, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 43.76/31.37  tff(f_52, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 43.76/31.37  tff(f_100, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_ordinal1)).
% 43.76/31.37  tff(f_39, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 43.76/31.37  tff(f_117, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_ordinal1)).
% 43.76/31.37  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 43.76/31.37  tff(c_120, plain, (v3_ordinal1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_132])).
% 43.76/31.37  tff(c_26, plain, (![B_10]: (r1_tarski(B_10, B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 43.76/31.37  tff(c_72820, plain, (![A_89898, B_89899]: (r1_ordinal1(A_89898, B_89899) | ~r1_tarski(A_89898, B_89899) | ~v3_ordinal1(B_89899) | ~v3_ordinal1(A_89898))), inference(cnfTransformation, [status(thm)], [f_108])).
% 43.76/31.37  tff(c_72828, plain, (![B_10]: (r1_ordinal1(B_10, B_10) | ~v3_ordinal1(B_10))), inference(resolution, [status(thm)], [c_26, c_72820])).
% 43.76/31.37  tff(c_30, plain, (![C_15]: (r2_hidden(C_15, k1_tarski(C_15)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 43.76/31.37  tff(c_110, plain, (![A_58]: (k2_xboole_0(A_58, k1_tarski(A_58))=k1_ordinal1(A_58))), inference(cnfTransformation, [status(thm)], [f_100])).
% 43.76/31.37  tff(c_209, plain, (![D_84, B_85, A_86]: (~r2_hidden(D_84, B_85) | r2_hidden(D_84, k2_xboole_0(A_86, B_85)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 43.76/31.37  tff(c_1510, plain, (![D_4754, A_4755]: (~r2_hidden(D_4754, k1_tarski(A_4755)) | r2_hidden(D_4754, k1_ordinal1(A_4755)))), inference(superposition, [status(thm), theory('equality')], [c_110, c_209])).
% 43.76/31.37  tff(c_1523, plain, (![C_15]: (r2_hidden(C_15, k1_ordinal1(C_15)))), inference(resolution, [status(thm)], [c_30, c_1510])).
% 43.76/31.37  tff(c_122, plain, (v3_ordinal1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_132])).
% 43.76/31.37  tff(c_517, plain, (![B_120, A_121]: (r2_hidden(B_120, A_121) | r1_ordinal1(A_121, B_120) | ~v3_ordinal1(B_120) | ~v3_ordinal1(A_121))), inference(cnfTransformation, [status(thm)], [f_117])).
% 43.76/31.37  tff(c_257, plain, (![D_93, A_94, B_95]: (~r2_hidden(D_93, A_94) | r2_hidden(D_93, k2_xboole_0(A_94, B_95)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 43.76/31.37  tff(c_323, plain, (![D_102, A_103]: (~r2_hidden(D_102, A_103) | r2_hidden(D_102, k1_ordinal1(A_103)))), inference(superposition, [status(thm), theory('equality')], [c_110, c_257])).
% 43.76/31.37  tff(c_124, plain, (~r1_ordinal1('#skF_7', '#skF_8') | ~r2_hidden('#skF_7', k1_ordinal1('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_132])).
% 43.76/31.37  tff(c_163, plain, (~r2_hidden('#skF_7', k1_ordinal1('#skF_8'))), inference(splitLeft, [status(thm)], [c_124])).
% 43.76/31.37  tff(c_357, plain, (~r2_hidden('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_323, c_163])).
% 43.76/31.37  tff(c_548, plain, (r1_ordinal1('#skF_8', '#skF_7') | ~v3_ordinal1('#skF_7') | ~v3_ordinal1('#skF_8')), inference(resolution, [status(thm)], [c_517, c_357])).
% 43.76/31.37  tff(c_593, plain, (r1_ordinal1('#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_120, c_122, c_548])).
% 43.76/31.37  tff(c_130, plain, (r2_hidden('#skF_7', k1_ordinal1('#skF_8')) | r1_ordinal1('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_132])).
% 43.76/31.37  tff(c_208, plain, (r1_ordinal1('#skF_7', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_163, c_130])).
% 43.76/31.37  tff(c_114, plain, (![A_59, B_60]: (r1_tarski(A_59, B_60) | ~r1_ordinal1(A_59, B_60) | ~v3_ordinal1(B_60) | ~v3_ordinal1(A_59))), inference(cnfTransformation, [status(thm)], [f_108])).
% 43.76/31.37  tff(c_376, plain, (![A_105, B_106]: (r1_tarski(A_105, B_106) | ~r1_ordinal1(A_105, B_106) | ~v3_ordinal1(B_106) | ~v3_ordinal1(A_105))), inference(cnfTransformation, [status(thm)], [f_108])).
% 43.76/31.37  tff(c_22, plain, (![B_10, A_9]: (B_10=A_9 | ~r1_tarski(B_10, A_9) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 43.76/31.37  tff(c_18796, plain, (![B_30775, A_30776]: (B_30775=A_30776 | ~r1_tarski(B_30775, A_30776) | ~r1_ordinal1(A_30776, B_30775) | ~v3_ordinal1(B_30775) | ~v3_ordinal1(A_30776))), inference(resolution, [status(thm)], [c_376, c_22])).
% 43.76/31.37  tff(c_72172, plain, (![B_89775, A_89776]: (B_89775=A_89776 | ~r1_ordinal1(B_89775, A_89776) | ~r1_ordinal1(A_89776, B_89775) | ~v3_ordinal1(B_89775) | ~v3_ordinal1(A_89776))), inference(resolution, [status(thm)], [c_114, c_18796])).
% 43.76/31.37  tff(c_72210, plain, ('#skF_7'='#skF_8' | ~r1_ordinal1('#skF_8', '#skF_7') | ~v3_ordinal1('#skF_7') | ~v3_ordinal1('#skF_8')), inference(resolution, [status(thm)], [c_208, c_72172])).
% 43.76/31.37  tff(c_72234, plain, ('#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_120, c_122, c_593, c_72210])).
% 43.76/31.37  tff(c_72243, plain, (~r2_hidden('#skF_8', k1_ordinal1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_72234, c_163])).
% 43.76/31.37  tff(c_72247, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1523, c_72243])).
% 43.76/31.37  tff(c_72248, plain, (~r1_ordinal1('#skF_7', '#skF_8')), inference(splitRight, [status(thm)], [c_124])).
% 43.76/31.37  tff(c_72249, plain, (r2_hidden('#skF_7', k1_ordinal1('#skF_8'))), inference(splitRight, [status(thm)], [c_124])).
% 43.76/31.37  tff(c_73088, plain, (![D_89933, B_89934, A_89935]: (r2_hidden(D_89933, B_89934) | r2_hidden(D_89933, A_89935) | ~r2_hidden(D_89933, k2_xboole_0(A_89935, B_89934)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 43.76/31.37  tff(c_89035, plain, (![D_119901, A_119902]: (r2_hidden(D_119901, k1_tarski(A_119902)) | r2_hidden(D_119901, A_119902) | ~r2_hidden(D_119901, k1_ordinal1(A_119902)))), inference(superposition, [status(thm), theory('equality')], [c_110, c_73088])).
% 43.76/31.37  tff(c_28, plain, (![C_15, A_11]: (C_15=A_11 | ~r2_hidden(C_15, k1_tarski(A_11)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 43.76/31.37  tff(c_90601, plain, (![D_120040, A_120041]: (D_120040=A_120041 | r2_hidden(D_120040, A_120041) | ~r2_hidden(D_120040, k1_ordinal1(A_120041)))), inference(resolution, [status(thm)], [c_89035, c_28])).
% 43.76/31.37  tff(c_90670, plain, ('#skF_7'='#skF_8' | r2_hidden('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_72249, c_90601])).
% 43.76/31.37  tff(c_90671, plain, (r2_hidden('#skF_7', '#skF_8')), inference(splitLeft, [status(thm)], [c_90670])).
% 43.76/31.37  tff(c_72686, plain, (![B_89894, A_89895]: (r2_hidden(B_89894, A_89895) | r1_ordinal1(A_89895, B_89894) | ~v3_ordinal1(B_89894) | ~v3_ordinal1(A_89895))), inference(cnfTransformation, [status(thm)], [f_117])).
% 43.76/31.37  tff(c_2, plain, (![B_2, A_1]: (~r2_hidden(B_2, A_1) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 43.76/31.37  tff(c_72792, plain, (![A_89895, B_89894]: (~r2_hidden(A_89895, B_89894) | r1_ordinal1(A_89895, B_89894) | ~v3_ordinal1(B_89894) | ~v3_ordinal1(A_89895))), inference(resolution, [status(thm)], [c_72686, c_2])).
% 43.76/31.37  tff(c_90674, plain, (r1_ordinal1('#skF_7', '#skF_8') | ~v3_ordinal1('#skF_8') | ~v3_ordinal1('#skF_7')), inference(resolution, [status(thm)], [c_90671, c_72792])).
% 43.76/31.37  tff(c_90682, plain, (r1_ordinal1('#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_122, c_120, c_90674])).
% 43.76/31.37  tff(c_90684, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72248, c_90682])).
% 43.76/31.37  tff(c_90685, plain, ('#skF_7'='#skF_8'), inference(splitRight, [status(thm)], [c_90670])).
% 43.76/31.37  tff(c_90692, plain, (~r1_ordinal1('#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_90685, c_72248])).
% 43.76/31.37  tff(c_90713, plain, (~v3_ordinal1('#skF_8')), inference(resolution, [status(thm)], [c_72828, c_90692])).
% 43.76/31.37  tff(c_90717, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_120, c_90713])).
% 43.76/31.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 43.76/31.37  
% 43.76/31.37  Inference rules
% 43.76/31.37  ----------------------
% 43.76/31.37  #Ref     : 0
% 43.76/31.37  #Sup     : 18310
% 43.76/31.37  #Fact    : 110
% 43.76/31.37  #Define  : 0
% 43.76/31.37  #Split   : 8
% 43.76/31.37  #Chain   : 0
% 43.76/31.37  #Close   : 0
% 43.76/31.37  
% 43.76/31.37  Ordering : KBO
% 43.76/31.37  
% 43.76/31.37  Simplification rules
% 43.76/31.37  ----------------------
% 43.76/31.37  #Subsume      : 4921
% 43.76/31.37  #Demod        : 2360
% 43.76/31.37  #Tautology    : 264
% 43.76/31.37  #SimpNegUnit  : 164
% 43.76/31.37  #BackRed      : 229
% 43.76/31.37  
% 43.76/31.37  #Partial instantiations: 32015
% 43.76/31.37  #Strategies tried      : 1
% 43.76/31.37  
% 43.76/31.37  Timing (in seconds)
% 43.76/31.37  ----------------------
% 43.76/31.37  Preprocessing        : 0.37
% 43.76/31.37  Parsing              : 0.18
% 43.76/31.37  CNF conversion       : 0.03
% 43.76/31.37  Main loop            : 30.23
% 43.76/31.37  Inferencing          : 3.78
% 43.76/31.37  Reduction            : 7.44
% 43.76/31.37  Demodulation         : 3.54
% 43.76/31.37  BG Simplification    : 0.42
% 43.76/31.37  Subsumption          : 16.86
% 43.76/31.37  Abstraction          : 0.88
% 43.76/31.37  MUC search           : 0.00
% 43.76/31.37  Cooper               : 0.00
% 43.76/31.37  Total                : 30.63
% 43.76/31.37  Index Insertion      : 0.00
% 43.76/31.37  Index Deletion       : 0.00
% 43.76/31.37  Index Matching       : 0.00
% 43.76/31.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
