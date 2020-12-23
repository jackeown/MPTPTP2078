%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:56 EST 2020

% Result     : Theorem 7.67s
% Output     : CNFRefutation 7.80s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 272 expanded)
%              Number of leaves         :   37 ( 103 expanded)
%              Depth                    :   13
%              Number of atoms          :  160 ( 487 expanded)
%              Number of equality atoms :   62 ( 187 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_11 > #skF_3 > #skF_10 > #skF_6 > #skF_8 > #skF_9 > #skF_5 > #skF_2 > #skF_7 > #skF_1 > #skF_12 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_59,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_110,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,k1_tarski(B))
      <=> ( A = k1_xboole_0
          | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_zfmisc_1)).

tff(f_103,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

tff(f_63,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_61,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_24,plain,(
    ! [B_15] : r1_tarski(B_15,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_88,plain,
    ( ~ r1_tarski('#skF_9',k1_tarski('#skF_10'))
    | k1_xboole_0 != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_112,plain,(
    k1_xboole_0 != '#skF_11' ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_82,plain,(
    ! [A_58,B_59] :
      ( r1_tarski(k1_tarski(A_58),B_59)
      | ~ r2_hidden(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_84,plain,
    ( ~ r1_tarski('#skF_9',k1_tarski('#skF_10'))
    | k1_tarski('#skF_12') != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_120,plain,(
    k1_tarski('#skF_12') != '#skF_11' ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_94,plain,
    ( k1_tarski('#skF_10') = '#skF_9'
    | k1_xboole_0 = '#skF_9'
    | r1_tarski('#skF_11',k1_tarski('#skF_12')) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_214,plain,(
    r1_tarski('#skF_11',k1_tarski('#skF_12')) ),
    inference(splitLeft,[status(thm)],[c_94])).

tff(c_20,plain,(
    ! [B_15,A_14] :
      ( B_15 = A_14
      | ~ r1_tarski(B_15,A_14)
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_216,plain,
    ( k1_tarski('#skF_12') = '#skF_11'
    | ~ r1_tarski(k1_tarski('#skF_12'),'#skF_11') ),
    inference(resolution,[status(thm)],[c_214,c_20])).

tff(c_219,plain,(
    ~ r1_tarski(k1_tarski('#skF_12'),'#skF_11') ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_216])).

tff(c_223,plain,(
    ~ r2_hidden('#skF_12','#skF_11') ),
    inference(resolution,[status(thm)],[c_82,c_219])).

tff(c_547,plain,(
    ! [A_148,B_149] :
      ( r2_hidden('#skF_2'(A_148,B_149),B_149)
      | r2_hidden('#skF_3'(A_148,B_149),A_148)
      | B_149 = A_148 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_28,plain,(
    ! [A_17] : r1_xboole_0(A_17,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_224,plain,(
    ! [A_94,B_95,C_96] :
      ( ~ r1_xboole_0(A_94,B_95)
      | ~ r2_hidden(C_96,k3_xboole_0(A_94,B_95)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_230,plain,(
    ! [A_97,B_98,B_99] :
      ( ~ r1_xboole_0(A_97,B_98)
      | r1_tarski(k3_xboole_0(A_97,B_98),B_99) ) ),
    inference(resolution,[status(thm)],[c_6,c_224])).

tff(c_26,plain,(
    ! [A_16] : r1_tarski(k1_xboole_0,A_16) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_162,plain,(
    ! [B_86,A_87] :
      ( B_86 = A_87
      | ~ r1_tarski(B_86,A_87)
      | ~ r1_tarski(A_87,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_174,plain,(
    ! [A_16] :
      ( k1_xboole_0 = A_16
      | ~ r1_tarski(A_16,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_26,c_162])).

tff(c_261,plain,(
    ! [A_103,B_104] :
      ( k3_xboole_0(A_103,B_104) = k1_xboole_0
      | ~ r1_xboole_0(A_103,B_104) ) ),
    inference(resolution,[status(thm)],[c_230,c_174])).

tff(c_266,plain,(
    ! [A_105] : k3_xboole_0(A_105,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_261])).

tff(c_18,plain,(
    ! [A_9,B_10,C_13] :
      ( ~ r1_xboole_0(A_9,B_10)
      | ~ r2_hidden(C_13,k3_xboole_0(A_9,B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_274,plain,(
    ! [A_105,C_13] :
      ( ~ r1_xboole_0(A_105,k1_xboole_0)
      | ~ r2_hidden(C_13,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_266,c_18])).

tff(c_281,plain,(
    ! [C_13] : ~ r2_hidden(C_13,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_274])).

tff(c_581,plain,(
    ! [B_150] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_150),B_150)
      | k1_xboole_0 = B_150 ) ),
    inference(resolution,[status(thm)],[c_547,c_281])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_9909,plain,(
    ! [B_6510,B_6511] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_6510),B_6511)
      | ~ r1_tarski(B_6510,B_6511)
      | k1_xboole_0 = B_6510 ) ),
    inference(resolution,[status(thm)],[c_581,c_2])).

tff(c_54,plain,(
    ! [C_29,A_25] :
      ( C_29 = A_25
      | ~ r2_hidden(C_29,k1_tarski(A_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_9968,plain,(
    ! [A_6515,B_6516] :
      ( A_6515 = '#skF_2'(k1_xboole_0,B_6516)
      | ~ r1_tarski(B_6516,k1_tarski(A_6515))
      | k1_xboole_0 = B_6516 ) ),
    inference(resolution,[status(thm)],[c_9909,c_54])).

tff(c_9979,plain,
    ( '#skF_2'(k1_xboole_0,'#skF_11') = '#skF_12'
    | k1_xboole_0 = '#skF_11' ),
    inference(resolution,[status(thm)],[c_214,c_9968])).

tff(c_9996,plain,(
    '#skF_2'(k1_xboole_0,'#skF_11') = '#skF_12' ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_9979])).

tff(c_577,plain,(
    ! [B_149] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_149),B_149)
      | k1_xboole_0 = B_149 ) ),
    inference(resolution,[status(thm)],[c_547,c_281])).

tff(c_10007,plain,
    ( r2_hidden('#skF_12','#skF_11')
    | k1_xboole_0 = '#skF_11' ),
    inference(superposition,[status(thm),theory(equality)],[c_9996,c_577])).

tff(c_10013,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_223,c_10007])).

tff(c_10014,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_tarski('#skF_10') = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_10016,plain,(
    k1_tarski('#skF_10') = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_10014])).

tff(c_92,plain,
    ( ~ r1_tarski('#skF_9',k1_tarski('#skF_10'))
    | r1_tarski('#skF_11',k1_tarski('#skF_12')) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_213,plain,(
    ~ r1_tarski('#skF_9',k1_tarski('#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_92])).

tff(c_10017,plain,(
    ~ r1_tarski('#skF_9','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10016,c_213])).

tff(c_10020,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_10017])).

tff(c_10021,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_10014])).

tff(c_10026,plain,(
    ! [A_16] : r1_tarski('#skF_9',A_16) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10021,c_26])).

tff(c_10035,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10026,c_213])).

tff(c_10036,plain,(
    r1_tarski('#skF_11',k1_tarski('#skF_12')) ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_10039,plain,
    ( k1_tarski('#skF_12') = '#skF_11'
    | ~ r1_tarski(k1_tarski('#skF_12'),'#skF_11') ),
    inference(resolution,[status(thm)],[c_10036,c_20])).

tff(c_10042,plain,(
    ~ r1_tarski(k1_tarski('#skF_12'),'#skF_11') ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_10039])).

tff(c_10055,plain,(
    ~ r2_hidden('#skF_12','#skF_11') ),
    inference(resolution,[status(thm)],[c_82,c_10042])).

tff(c_10617,plain,(
    ! [A_6580,B_6581] :
      ( r2_hidden('#skF_2'(A_6580,B_6581),B_6581)
      | r2_hidden('#skF_3'(A_6580,B_6581),A_6580)
      | B_6581 = A_6580 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_10046,plain,(
    ! [A_6518,B_6519,C_6520] :
      ( ~ r1_xboole_0(A_6518,B_6519)
      | ~ r2_hidden(C_6520,k3_xboole_0(A_6518,B_6519)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_10062,plain,(
    ! [A_6521,B_6522,B_6523] :
      ( ~ r1_xboole_0(A_6521,B_6522)
      | r1_tarski(k3_xboole_0(A_6521,B_6522),B_6523) ) ),
    inference(resolution,[status(thm)],[c_6,c_10046])).

tff(c_10071,plain,(
    ! [A_6524,B_6525] :
      ( k3_xboole_0(A_6524,B_6525) = k1_xboole_0
      | ~ r1_xboole_0(A_6524,B_6525) ) ),
    inference(resolution,[status(thm)],[c_10062,c_174])).

tff(c_10076,plain,(
    ! [A_6526] : k3_xboole_0(A_6526,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_10071])).

tff(c_10084,plain,(
    ! [A_6526,C_13] :
      ( ~ r1_xboole_0(A_6526,k1_xboole_0)
      | ~ r2_hidden(C_13,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10076,c_18])).

tff(c_10091,plain,(
    ! [C_13] : ~ r2_hidden(C_13,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_10084])).

tff(c_10661,plain,(
    ! [B_6582] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_6582),B_6582)
      | k1_xboole_0 = B_6582 ) ),
    inference(resolution,[status(thm)],[c_10617,c_10091])).

tff(c_20380,plain,(
    ! [B_13327,B_13328] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_13327),B_13328)
      | ~ r1_tarski(B_13327,B_13328)
      | k1_xboole_0 = B_13327 ) ),
    inference(resolution,[status(thm)],[c_10661,c_2])).

tff(c_20443,plain,(
    ! [A_13332,B_13333] :
      ( A_13332 = '#skF_2'(k1_xboole_0,B_13333)
      | ~ r1_tarski(B_13333,k1_tarski(A_13332))
      | k1_xboole_0 = B_13333 ) ),
    inference(resolution,[status(thm)],[c_20380,c_54])).

tff(c_20457,plain,
    ( '#skF_2'(k1_xboole_0,'#skF_11') = '#skF_12'
    | k1_xboole_0 = '#skF_11' ),
    inference(resolution,[status(thm)],[c_10036,c_20443])).

tff(c_20475,plain,(
    '#skF_2'(k1_xboole_0,'#skF_11') = '#skF_12' ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_20457])).

tff(c_10657,plain,(
    ! [B_6581] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_6581),B_6581)
      | k1_xboole_0 = B_6581 ) ),
    inference(resolution,[status(thm)],[c_10617,c_10091])).

tff(c_20488,plain,
    ( r2_hidden('#skF_12','#skF_11')
    | k1_xboole_0 = '#skF_11' ),
    inference(superposition,[status(thm),theory(equality)],[c_20475,c_10657])).

tff(c_20495,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_10055,c_20488])).

tff(c_20497,plain,(
    k1_tarski('#skF_12') = '#skF_11' ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_86,plain,
    ( k1_tarski('#skF_10') = '#skF_9'
    | k1_xboole_0 = '#skF_9'
    | k1_tarski('#skF_12') != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_20525,plain,
    ( k1_tarski('#skF_10') = '#skF_9'
    | k1_xboole_0 = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20497,c_86])).

tff(c_20526,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_20525])).

tff(c_20528,plain,(
    ! [A_16] : r1_tarski('#skF_9',A_16) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20526,c_26])).

tff(c_20496,plain,(
    ~ r1_tarski('#skF_9',k1_tarski('#skF_10')) ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_20536,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20528,c_20496])).

tff(c_20537,plain,(
    k1_tarski('#skF_10') = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_20525])).

tff(c_20539,plain,(
    ~ r1_tarski('#skF_9','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20537,c_20496])).

tff(c_20542,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_20539])).

tff(c_20544,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_90,plain,
    ( k1_tarski('#skF_10') = '#skF_9'
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_20554,plain,
    ( k1_tarski('#skF_10') = '#skF_9'
    | '#skF_11' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20544,c_20544,c_90])).

tff(c_20555,plain,(
    '#skF_11' = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_20554])).

tff(c_20545,plain,(
    ! [A_16] : r1_tarski('#skF_11',A_16) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20544,c_26])).

tff(c_20557,plain,(
    ! [A_16] : r1_tarski('#skF_9',A_16) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20555,c_20545])).

tff(c_20543,plain,(
    ~ r1_tarski('#skF_9',k1_tarski('#skF_10')) ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_20570,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20557,c_20543])).

tff(c_20571,plain,(
    k1_tarski('#skF_10') = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_20554])).

tff(c_20573,plain,(
    ~ r1_tarski('#skF_9','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20571,c_20543])).

tff(c_20576,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_20573])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:53:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.67/2.69  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.67/2.70  
% 7.67/2.70  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.67/2.70  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_11 > #skF_3 > #skF_10 > #skF_6 > #skF_8 > #skF_9 > #skF_5 > #skF_2 > #skF_7 > #skF_1 > #skF_12 > #skF_4
% 7.67/2.70  
% 7.67/2.70  %Foreground sorts:
% 7.67/2.70  
% 7.67/2.70  
% 7.67/2.70  %Background operators:
% 7.67/2.70  
% 7.67/2.70  
% 7.67/2.70  %Foreground operators:
% 7.67/2.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.67/2.70  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.67/2.70  tff('#skF_11', type, '#skF_11': $i).
% 7.67/2.70  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.67/2.70  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.67/2.70  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.67/2.70  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 7.67/2.70  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.67/2.70  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.67/2.70  tff('#skF_10', type, '#skF_10': $i).
% 7.67/2.70  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.67/2.70  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.67/2.70  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.67/2.70  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 7.67/2.70  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 7.67/2.70  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.67/2.70  tff('#skF_9', type, '#skF_9': $i).
% 7.67/2.70  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 7.67/2.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.67/2.70  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 7.67/2.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.67/2.70  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.67/2.70  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.67/2.70  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 7.67/2.70  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 7.67/2.70  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.67/2.70  tff('#skF_12', type, '#skF_12': $i).
% 7.67/2.70  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 7.67/2.70  
% 7.80/2.72  tff(f_59, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.80/2.72  tff(f_110, negated_conjecture, ~(![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_zfmisc_1)).
% 7.80/2.72  tff(f_103, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 7.80/2.72  tff(f_39, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 7.80/2.72  tff(f_63, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 7.80/2.72  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 7.80/2.72  tff(f_53, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 7.80/2.72  tff(f_61, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 7.80/2.72  tff(f_85, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 7.80/2.72  tff(c_24, plain, (![B_15]: (r1_tarski(B_15, B_15))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.80/2.72  tff(c_88, plain, (~r1_tarski('#skF_9', k1_tarski('#skF_10')) | k1_xboole_0!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_110])).
% 7.80/2.72  tff(c_112, plain, (k1_xboole_0!='#skF_11'), inference(splitLeft, [status(thm)], [c_88])).
% 7.80/2.72  tff(c_82, plain, (![A_58, B_59]: (r1_tarski(k1_tarski(A_58), B_59) | ~r2_hidden(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.80/2.72  tff(c_84, plain, (~r1_tarski('#skF_9', k1_tarski('#skF_10')) | k1_tarski('#skF_12')!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_110])).
% 7.80/2.72  tff(c_120, plain, (k1_tarski('#skF_12')!='#skF_11'), inference(splitLeft, [status(thm)], [c_84])).
% 7.80/2.72  tff(c_94, plain, (k1_tarski('#skF_10')='#skF_9' | k1_xboole_0='#skF_9' | r1_tarski('#skF_11', k1_tarski('#skF_12'))), inference(cnfTransformation, [status(thm)], [f_110])).
% 7.80/2.72  tff(c_214, plain, (r1_tarski('#skF_11', k1_tarski('#skF_12'))), inference(splitLeft, [status(thm)], [c_94])).
% 7.80/2.72  tff(c_20, plain, (![B_15, A_14]: (B_15=A_14 | ~r1_tarski(B_15, A_14) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.80/2.72  tff(c_216, plain, (k1_tarski('#skF_12')='#skF_11' | ~r1_tarski(k1_tarski('#skF_12'), '#skF_11')), inference(resolution, [status(thm)], [c_214, c_20])).
% 7.80/2.72  tff(c_219, plain, (~r1_tarski(k1_tarski('#skF_12'), '#skF_11')), inference(negUnitSimplification, [status(thm)], [c_120, c_216])).
% 7.80/2.72  tff(c_223, plain, (~r2_hidden('#skF_12', '#skF_11')), inference(resolution, [status(thm)], [c_82, c_219])).
% 7.80/2.72  tff(c_547, plain, (![A_148, B_149]: (r2_hidden('#skF_2'(A_148, B_149), B_149) | r2_hidden('#skF_3'(A_148, B_149), A_148) | B_149=A_148)), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.80/2.72  tff(c_28, plain, (![A_17]: (r1_xboole_0(A_17, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.80/2.72  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.80/2.72  tff(c_224, plain, (![A_94, B_95, C_96]: (~r1_xboole_0(A_94, B_95) | ~r2_hidden(C_96, k3_xboole_0(A_94, B_95)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.80/2.72  tff(c_230, plain, (![A_97, B_98, B_99]: (~r1_xboole_0(A_97, B_98) | r1_tarski(k3_xboole_0(A_97, B_98), B_99))), inference(resolution, [status(thm)], [c_6, c_224])).
% 7.80/2.72  tff(c_26, plain, (![A_16]: (r1_tarski(k1_xboole_0, A_16))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.80/2.72  tff(c_162, plain, (![B_86, A_87]: (B_86=A_87 | ~r1_tarski(B_86, A_87) | ~r1_tarski(A_87, B_86))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.80/2.72  tff(c_174, plain, (![A_16]: (k1_xboole_0=A_16 | ~r1_tarski(A_16, k1_xboole_0))), inference(resolution, [status(thm)], [c_26, c_162])).
% 7.80/2.72  tff(c_261, plain, (![A_103, B_104]: (k3_xboole_0(A_103, B_104)=k1_xboole_0 | ~r1_xboole_0(A_103, B_104))), inference(resolution, [status(thm)], [c_230, c_174])).
% 7.80/2.72  tff(c_266, plain, (![A_105]: (k3_xboole_0(A_105, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_261])).
% 7.80/2.72  tff(c_18, plain, (![A_9, B_10, C_13]: (~r1_xboole_0(A_9, B_10) | ~r2_hidden(C_13, k3_xboole_0(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.80/2.72  tff(c_274, plain, (![A_105, C_13]: (~r1_xboole_0(A_105, k1_xboole_0) | ~r2_hidden(C_13, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_266, c_18])).
% 7.80/2.72  tff(c_281, plain, (![C_13]: (~r2_hidden(C_13, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_274])).
% 7.80/2.72  tff(c_581, plain, (![B_150]: (r2_hidden('#skF_2'(k1_xboole_0, B_150), B_150) | k1_xboole_0=B_150)), inference(resolution, [status(thm)], [c_547, c_281])).
% 7.80/2.72  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.80/2.72  tff(c_9909, plain, (![B_6510, B_6511]: (r2_hidden('#skF_2'(k1_xboole_0, B_6510), B_6511) | ~r1_tarski(B_6510, B_6511) | k1_xboole_0=B_6510)), inference(resolution, [status(thm)], [c_581, c_2])).
% 7.80/2.72  tff(c_54, plain, (![C_29, A_25]: (C_29=A_25 | ~r2_hidden(C_29, k1_tarski(A_25)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.80/2.72  tff(c_9968, plain, (![A_6515, B_6516]: (A_6515='#skF_2'(k1_xboole_0, B_6516) | ~r1_tarski(B_6516, k1_tarski(A_6515)) | k1_xboole_0=B_6516)), inference(resolution, [status(thm)], [c_9909, c_54])).
% 7.80/2.72  tff(c_9979, plain, ('#skF_2'(k1_xboole_0, '#skF_11')='#skF_12' | k1_xboole_0='#skF_11'), inference(resolution, [status(thm)], [c_214, c_9968])).
% 7.80/2.72  tff(c_9996, plain, ('#skF_2'(k1_xboole_0, '#skF_11')='#skF_12'), inference(negUnitSimplification, [status(thm)], [c_112, c_9979])).
% 7.80/2.72  tff(c_577, plain, (![B_149]: (r2_hidden('#skF_2'(k1_xboole_0, B_149), B_149) | k1_xboole_0=B_149)), inference(resolution, [status(thm)], [c_547, c_281])).
% 7.80/2.72  tff(c_10007, plain, (r2_hidden('#skF_12', '#skF_11') | k1_xboole_0='#skF_11'), inference(superposition, [status(thm), theory('equality')], [c_9996, c_577])).
% 7.80/2.72  tff(c_10013, plain, $false, inference(negUnitSimplification, [status(thm)], [c_112, c_223, c_10007])).
% 7.80/2.72  tff(c_10014, plain, (k1_xboole_0='#skF_9' | k1_tarski('#skF_10')='#skF_9'), inference(splitRight, [status(thm)], [c_94])).
% 7.80/2.72  tff(c_10016, plain, (k1_tarski('#skF_10')='#skF_9'), inference(splitLeft, [status(thm)], [c_10014])).
% 7.80/2.72  tff(c_92, plain, (~r1_tarski('#skF_9', k1_tarski('#skF_10')) | r1_tarski('#skF_11', k1_tarski('#skF_12'))), inference(cnfTransformation, [status(thm)], [f_110])).
% 7.80/2.72  tff(c_213, plain, (~r1_tarski('#skF_9', k1_tarski('#skF_10'))), inference(splitLeft, [status(thm)], [c_92])).
% 7.80/2.72  tff(c_10017, plain, (~r1_tarski('#skF_9', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_10016, c_213])).
% 7.80/2.72  tff(c_10020, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_10017])).
% 7.80/2.72  tff(c_10021, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_10014])).
% 7.80/2.72  tff(c_10026, plain, (![A_16]: (r1_tarski('#skF_9', A_16))), inference(demodulation, [status(thm), theory('equality')], [c_10021, c_26])).
% 7.80/2.72  tff(c_10035, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10026, c_213])).
% 7.80/2.72  tff(c_10036, plain, (r1_tarski('#skF_11', k1_tarski('#skF_12'))), inference(splitRight, [status(thm)], [c_92])).
% 7.80/2.72  tff(c_10039, plain, (k1_tarski('#skF_12')='#skF_11' | ~r1_tarski(k1_tarski('#skF_12'), '#skF_11')), inference(resolution, [status(thm)], [c_10036, c_20])).
% 7.80/2.72  tff(c_10042, plain, (~r1_tarski(k1_tarski('#skF_12'), '#skF_11')), inference(negUnitSimplification, [status(thm)], [c_120, c_10039])).
% 7.80/2.72  tff(c_10055, plain, (~r2_hidden('#skF_12', '#skF_11')), inference(resolution, [status(thm)], [c_82, c_10042])).
% 7.80/2.72  tff(c_10617, plain, (![A_6580, B_6581]: (r2_hidden('#skF_2'(A_6580, B_6581), B_6581) | r2_hidden('#skF_3'(A_6580, B_6581), A_6580) | B_6581=A_6580)), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.80/2.72  tff(c_10046, plain, (![A_6518, B_6519, C_6520]: (~r1_xboole_0(A_6518, B_6519) | ~r2_hidden(C_6520, k3_xboole_0(A_6518, B_6519)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.80/2.72  tff(c_10062, plain, (![A_6521, B_6522, B_6523]: (~r1_xboole_0(A_6521, B_6522) | r1_tarski(k3_xboole_0(A_6521, B_6522), B_6523))), inference(resolution, [status(thm)], [c_6, c_10046])).
% 7.80/2.72  tff(c_10071, plain, (![A_6524, B_6525]: (k3_xboole_0(A_6524, B_6525)=k1_xboole_0 | ~r1_xboole_0(A_6524, B_6525))), inference(resolution, [status(thm)], [c_10062, c_174])).
% 7.80/2.72  tff(c_10076, plain, (![A_6526]: (k3_xboole_0(A_6526, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_10071])).
% 7.80/2.72  tff(c_10084, plain, (![A_6526, C_13]: (~r1_xboole_0(A_6526, k1_xboole_0) | ~r2_hidden(C_13, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10076, c_18])).
% 7.80/2.72  tff(c_10091, plain, (![C_13]: (~r2_hidden(C_13, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_10084])).
% 7.80/2.72  tff(c_10661, plain, (![B_6582]: (r2_hidden('#skF_2'(k1_xboole_0, B_6582), B_6582) | k1_xboole_0=B_6582)), inference(resolution, [status(thm)], [c_10617, c_10091])).
% 7.80/2.72  tff(c_20380, plain, (![B_13327, B_13328]: (r2_hidden('#skF_2'(k1_xboole_0, B_13327), B_13328) | ~r1_tarski(B_13327, B_13328) | k1_xboole_0=B_13327)), inference(resolution, [status(thm)], [c_10661, c_2])).
% 7.80/2.72  tff(c_20443, plain, (![A_13332, B_13333]: (A_13332='#skF_2'(k1_xboole_0, B_13333) | ~r1_tarski(B_13333, k1_tarski(A_13332)) | k1_xboole_0=B_13333)), inference(resolution, [status(thm)], [c_20380, c_54])).
% 7.80/2.72  tff(c_20457, plain, ('#skF_2'(k1_xboole_0, '#skF_11')='#skF_12' | k1_xboole_0='#skF_11'), inference(resolution, [status(thm)], [c_10036, c_20443])).
% 7.80/2.72  tff(c_20475, plain, ('#skF_2'(k1_xboole_0, '#skF_11')='#skF_12'), inference(negUnitSimplification, [status(thm)], [c_112, c_20457])).
% 7.80/2.72  tff(c_10657, plain, (![B_6581]: (r2_hidden('#skF_2'(k1_xboole_0, B_6581), B_6581) | k1_xboole_0=B_6581)), inference(resolution, [status(thm)], [c_10617, c_10091])).
% 7.80/2.72  tff(c_20488, plain, (r2_hidden('#skF_12', '#skF_11') | k1_xboole_0='#skF_11'), inference(superposition, [status(thm), theory('equality')], [c_20475, c_10657])).
% 7.80/2.72  tff(c_20495, plain, $false, inference(negUnitSimplification, [status(thm)], [c_112, c_10055, c_20488])).
% 7.80/2.72  tff(c_20497, plain, (k1_tarski('#skF_12')='#skF_11'), inference(splitRight, [status(thm)], [c_84])).
% 7.80/2.72  tff(c_86, plain, (k1_tarski('#skF_10')='#skF_9' | k1_xboole_0='#skF_9' | k1_tarski('#skF_12')!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_110])).
% 7.80/2.72  tff(c_20525, plain, (k1_tarski('#skF_10')='#skF_9' | k1_xboole_0='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_20497, c_86])).
% 7.80/2.72  tff(c_20526, plain, (k1_xboole_0='#skF_9'), inference(splitLeft, [status(thm)], [c_20525])).
% 7.80/2.72  tff(c_20528, plain, (![A_16]: (r1_tarski('#skF_9', A_16))), inference(demodulation, [status(thm), theory('equality')], [c_20526, c_26])).
% 7.80/2.72  tff(c_20496, plain, (~r1_tarski('#skF_9', k1_tarski('#skF_10'))), inference(splitRight, [status(thm)], [c_84])).
% 7.80/2.72  tff(c_20536, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20528, c_20496])).
% 7.80/2.72  tff(c_20537, plain, (k1_tarski('#skF_10')='#skF_9'), inference(splitRight, [status(thm)], [c_20525])).
% 7.80/2.72  tff(c_20539, plain, (~r1_tarski('#skF_9', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_20537, c_20496])).
% 7.80/2.72  tff(c_20542, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_20539])).
% 7.80/2.72  tff(c_20544, plain, (k1_xboole_0='#skF_11'), inference(splitRight, [status(thm)], [c_88])).
% 7.80/2.72  tff(c_90, plain, (k1_tarski('#skF_10')='#skF_9' | k1_xboole_0='#skF_9' | k1_xboole_0!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_110])).
% 7.80/2.72  tff(c_20554, plain, (k1_tarski('#skF_10')='#skF_9' | '#skF_11'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_20544, c_20544, c_90])).
% 7.80/2.72  tff(c_20555, plain, ('#skF_11'='#skF_9'), inference(splitLeft, [status(thm)], [c_20554])).
% 7.80/2.72  tff(c_20545, plain, (![A_16]: (r1_tarski('#skF_11', A_16))), inference(demodulation, [status(thm), theory('equality')], [c_20544, c_26])).
% 7.80/2.72  tff(c_20557, plain, (![A_16]: (r1_tarski('#skF_9', A_16))), inference(demodulation, [status(thm), theory('equality')], [c_20555, c_20545])).
% 7.80/2.72  tff(c_20543, plain, (~r1_tarski('#skF_9', k1_tarski('#skF_10'))), inference(splitRight, [status(thm)], [c_88])).
% 7.80/2.72  tff(c_20570, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20557, c_20543])).
% 7.80/2.72  tff(c_20571, plain, (k1_tarski('#skF_10')='#skF_9'), inference(splitRight, [status(thm)], [c_20554])).
% 7.80/2.72  tff(c_20573, plain, (~r1_tarski('#skF_9', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_20571, c_20543])).
% 7.80/2.72  tff(c_20576, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_20573])).
% 7.80/2.72  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.80/2.72  
% 7.80/2.72  Inference rules
% 7.80/2.72  ----------------------
% 7.80/2.72  #Ref     : 0
% 7.80/2.72  #Sup     : 3309
% 7.80/2.72  #Fact    : 4
% 7.80/2.72  #Define  : 0
% 7.80/2.72  #Split   : 9
% 7.80/2.72  #Chain   : 0
% 7.80/2.72  #Close   : 0
% 7.80/2.72  
% 7.80/2.72  Ordering : KBO
% 7.80/2.72  
% 7.80/2.72  Simplification rules
% 7.80/2.72  ----------------------
% 7.80/2.72  #Subsume      : 1003
% 7.80/2.72  #Demod        : 847
% 7.80/2.72  #Tautology    : 524
% 7.80/2.72  #SimpNegUnit  : 70
% 7.80/2.72  #BackRed      : 19
% 7.80/2.72  
% 7.80/2.72  #Partial instantiations: 4928
% 7.80/2.72  #Strategies tried      : 1
% 7.80/2.72  
% 7.80/2.72  Timing (in seconds)
% 7.80/2.72  ----------------------
% 7.80/2.72  Preprocessing        : 0.36
% 7.80/2.72  Parsing              : 0.18
% 7.80/2.72  CNF conversion       : 0.03
% 7.80/2.72  Main loop            : 1.50
% 7.80/2.72  Inferencing          : 0.61
% 7.80/2.72  Reduction            : 0.44
% 7.80/2.72  Demodulation         : 0.29
% 7.80/2.72  BG Simplification    : 0.09
% 7.80/2.72  Subsumption          : 0.28
% 7.80/2.72  Abstraction          : 0.11
% 7.80/2.72  MUC search           : 0.00
% 7.80/2.72  Cooper               : 0.00
% 7.80/2.72  Total                : 1.90
% 7.80/2.72  Index Insertion      : 0.00
% 7.80/2.72  Index Deletion       : 0.00
% 7.80/2.72  Index Matching       : 0.00
% 7.80/2.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
