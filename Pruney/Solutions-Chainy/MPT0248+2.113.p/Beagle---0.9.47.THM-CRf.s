%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:20 EST 2020

% Result     : Theorem 4.45s
% Output     : CNFRefutation 4.56s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 199 expanded)
%              Number of leaves         :   32 (  79 expanded)
%              Depth                    :   11
%              Number of atoms          :  116 ( 443 expanded)
%              Number of equality atoms :   56 ( 276 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_1 > #skF_4 > #skF_10 > #skF_9 > #skF_8 > #skF_3 > #skF_2 > #skF_7

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_103,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_68,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(c_66,plain,
    ( k1_tarski('#skF_8') != '#skF_10'
    | k1_xboole_0 != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_88,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_64,plain,
    ( k1_xboole_0 != '#skF_10'
    | k1_tarski('#skF_8') != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_73,plain,(
    k1_tarski('#skF_8') != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_70,plain,(
    k2_xboole_0('#skF_9','#skF_10') = k1_tarski('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_34,plain,(
    ! [A_20,B_21] : r1_tarski(A_20,k2_xboole_0(A_20,B_21)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_84,plain,(
    r1_tarski('#skF_9',k1_tarski('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_34])).

tff(c_835,plain,(
    ! [B_116,A_117] :
      ( k1_tarski(B_116) = A_117
      | k1_xboole_0 = A_117
      | ~ r1_tarski(A_117,k1_tarski(B_116)) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_857,plain,
    ( k1_tarski('#skF_8') = '#skF_9'
    | k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_84,c_835])).

tff(c_872,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_73,c_857])).

tff(c_873,plain,(
    k1_tarski('#skF_8') != '#skF_10' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1044,plain,(
    ! [D_138,A_139,B_140] :
      ( ~ r2_hidden(D_138,A_139)
      | r2_hidden(D_138,k2_xboole_0(A_139,B_140)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1071,plain,(
    ! [D_144] :
      ( ~ r2_hidden(D_144,'#skF_9')
      | r2_hidden(D_144,k1_tarski('#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_1044])).

tff(c_36,plain,(
    ! [C_26,A_22] :
      ( C_26 = A_22
      | ~ r2_hidden(C_26,k1_tarski(A_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1080,plain,(
    ! [D_145] :
      ( D_145 = '#skF_8'
      | ~ r2_hidden(D_145,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_1071,c_36])).

tff(c_1091,plain,
    ( '#skF_1'('#skF_9') = '#skF_8'
    | v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_4,c_1080])).

tff(c_1092,plain,(
    v1_xboole_0('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_1091])).

tff(c_1284,plain,(
    ! [A_166,B_167] :
      ( r2_hidden('#skF_2'(A_166,B_167),A_166)
      | r1_tarski(A_166,B_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1326,plain,(
    ! [A_169,B_170] :
      ( ~ v1_xboole_0(A_169)
      | r1_tarski(A_169,B_170) ) ),
    inference(resolution,[status(thm)],[c_1284,c_2])).

tff(c_32,plain,(
    ! [A_18,B_19] :
      ( k2_xboole_0(A_18,B_19) = B_19
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1331,plain,(
    ! [A_171,B_172] :
      ( k2_xboole_0(A_171,B_172) = B_172
      | ~ v1_xboole_0(A_171) ) ),
    inference(resolution,[status(thm)],[c_1326,c_32])).

tff(c_1334,plain,(
    ! [B_172] : k2_xboole_0('#skF_9',B_172) = B_172 ),
    inference(resolution,[status(thm)],[c_1092,c_1331])).

tff(c_1336,plain,(
    k1_tarski('#skF_8') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1334,c_70])).

tff(c_1338,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_873,c_1336])).

tff(c_1340,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_1091])).

tff(c_1339,plain,(
    '#skF_1'('#skF_9') = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_1091])).

tff(c_874,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_60,plain,(
    ! [B_38] : r1_tarski(k1_xboole_0,k1_tarski(B_38)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_875,plain,(
    ! [B_38] : r1_tarski('#skF_9',k1_tarski(B_38)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_874,c_60])).

tff(c_936,plain,(
    ! [A_127,B_128] :
      ( k2_xboole_0(A_127,B_128) = B_128
      | ~ r1_tarski(A_127,B_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_947,plain,(
    ! [B_38] : k2_xboole_0('#skF_9',k1_tarski(B_38)) = k1_tarski(B_38) ),
    inference(resolution,[status(thm)],[c_875,c_936])).

tff(c_1507,plain,(
    ! [D_186,B_187] :
      ( ~ r2_hidden(D_186,'#skF_9')
      | r2_hidden(D_186,k1_tarski(B_187)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_947,c_1044])).

tff(c_1521,plain,(
    ! [D_188,B_189] :
      ( D_188 = B_189
      | ~ r2_hidden(D_188,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_1507,c_36])).

tff(c_1529,plain,(
    ! [B_189] :
      ( B_189 = '#skF_1'('#skF_9')
      | v1_xboole_0('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_4,c_1521])).

tff(c_1534,plain,(
    ! [B_189] :
      ( B_189 = '#skF_8'
      | v1_xboole_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1339,c_1529])).

tff(c_1535,plain,(
    ! [B_189] : B_189 = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_1340,c_1534])).

tff(c_1555,plain,(
    ! [B_192] : B_192 = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_1340,c_1534])).

tff(c_1654,plain,(
    '#skF_9' != '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_1555,c_73])).

tff(c_1661,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_1535,c_1654])).

tff(c_1662,plain,(
    k1_xboole_0 != '#skF_10' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_1663,plain,(
    k1_tarski('#skF_8') = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_68,plain,
    ( k1_tarski('#skF_8') != '#skF_10'
    | k1_tarski('#skF_8') != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1720,plain,(
    '#skF_10' != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1663,c_1663,c_68])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1686,plain,(
    k2_xboole_0('#skF_9','#skF_10') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1663,c_70])).

tff(c_2086,plain,(
    ! [D_1556,B_1557,A_1558] :
      ( ~ r2_hidden(D_1556,B_1557)
      | r2_hidden(D_1556,k2_xboole_0(A_1558,B_1557)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2115,plain,(
    ! [D_1559] :
      ( ~ r2_hidden(D_1559,'#skF_10')
      | r2_hidden(D_1559,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1686,c_2086])).

tff(c_2668,plain,(
    ! [B_1601] :
      ( r2_hidden('#skF_2'('#skF_10',B_1601),'#skF_9')
      | r1_tarski('#skF_10',B_1601) ) ),
    inference(resolution,[status(thm)],[c_10,c_2115])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2682,plain,(
    r1_tarski('#skF_10','#skF_9') ),
    inference(resolution,[status(thm)],[c_2668,c_8])).

tff(c_2586,plain,(
    ! [B_1594,A_1595] :
      ( k1_tarski(B_1594) = A_1595
      | k1_xboole_0 = A_1595
      | ~ r1_tarski(A_1595,k1_tarski(B_1594)) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2605,plain,(
    ! [A_1595] :
      ( k1_tarski('#skF_8') = A_1595
      | k1_xboole_0 = A_1595
      | ~ r1_tarski(A_1595,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1663,c_2586])).

tff(c_2614,plain,(
    ! [A_1595] :
      ( A_1595 = '#skF_9'
      | k1_xboole_0 = A_1595
      | ~ r1_tarski(A_1595,'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1663,c_2605])).

tff(c_2687,plain,
    ( '#skF_10' = '#skF_9'
    | k1_xboole_0 = '#skF_10' ),
    inference(resolution,[status(thm)],[c_2682,c_2614])).

tff(c_2697,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1662,c_1720,c_2687])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:51:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.45/1.79  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.56/1.79  
% 4.56/1.79  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.56/1.80  %$ r2_hidden > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_1 > #skF_4 > #skF_10 > #skF_9 > #skF_8 > #skF_3 > #skF_2 > #skF_7
% 4.56/1.80  
% 4.56/1.80  %Foreground sorts:
% 4.56/1.80  
% 4.56/1.80  
% 4.56/1.80  %Background operators:
% 4.56/1.80  
% 4.56/1.80  
% 4.56/1.80  %Foreground operators:
% 4.56/1.80  tff('#skF_5', type, '#skF_5': $i > $i).
% 4.56/1.80  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 4.56/1.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.56/1.80  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.56/1.80  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.56/1.80  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.56/1.80  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.56/1.80  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.56/1.80  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 4.56/1.80  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.56/1.80  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.56/1.80  tff('#skF_10', type, '#skF_10': $i).
% 4.56/1.80  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.56/1.80  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.56/1.80  tff('#skF_9', type, '#skF_9': $i).
% 4.56/1.80  tff('#skF_8', type, '#skF_8': $i).
% 4.56/1.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.56/1.80  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.56/1.80  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.56/1.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.56/1.80  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.56/1.80  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.56/1.80  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 4.56/1.80  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.56/1.80  
% 4.56/1.81  tff(f_103, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 4.56/1.81  tff(f_61, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.56/1.81  tff(f_82, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 4.56/1.81  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.56/1.81  tff(f_47, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 4.56/1.81  tff(f_68, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 4.56/1.81  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.56/1.81  tff(f_59, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.56/1.81  tff(c_66, plain, (k1_tarski('#skF_8')!='#skF_10' | k1_xboole_0!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.56/1.81  tff(c_88, plain, (k1_xboole_0!='#skF_9'), inference(splitLeft, [status(thm)], [c_66])).
% 4.56/1.81  tff(c_64, plain, (k1_xboole_0!='#skF_10' | k1_tarski('#skF_8')!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.56/1.81  tff(c_73, plain, (k1_tarski('#skF_8')!='#skF_9'), inference(splitLeft, [status(thm)], [c_64])).
% 4.56/1.81  tff(c_70, plain, (k2_xboole_0('#skF_9', '#skF_10')=k1_tarski('#skF_8')), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.56/1.81  tff(c_34, plain, (![A_20, B_21]: (r1_tarski(A_20, k2_xboole_0(A_20, B_21)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.56/1.81  tff(c_84, plain, (r1_tarski('#skF_9', k1_tarski('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_70, c_34])).
% 4.56/1.81  tff(c_835, plain, (![B_116, A_117]: (k1_tarski(B_116)=A_117 | k1_xboole_0=A_117 | ~r1_tarski(A_117, k1_tarski(B_116)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.56/1.81  tff(c_857, plain, (k1_tarski('#skF_8')='#skF_9' | k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_84, c_835])).
% 4.56/1.81  tff(c_872, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_73, c_857])).
% 4.56/1.81  tff(c_873, plain, (k1_tarski('#skF_8')!='#skF_10'), inference(splitRight, [status(thm)], [c_66])).
% 4.56/1.81  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.56/1.81  tff(c_1044, plain, (![D_138, A_139, B_140]: (~r2_hidden(D_138, A_139) | r2_hidden(D_138, k2_xboole_0(A_139, B_140)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.56/1.81  tff(c_1071, plain, (![D_144]: (~r2_hidden(D_144, '#skF_9') | r2_hidden(D_144, k1_tarski('#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_70, c_1044])).
% 4.56/1.81  tff(c_36, plain, (![C_26, A_22]: (C_26=A_22 | ~r2_hidden(C_26, k1_tarski(A_22)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.56/1.81  tff(c_1080, plain, (![D_145]: (D_145='#skF_8' | ~r2_hidden(D_145, '#skF_9'))), inference(resolution, [status(thm)], [c_1071, c_36])).
% 4.56/1.81  tff(c_1091, plain, ('#skF_1'('#skF_9')='#skF_8' | v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_4, c_1080])).
% 4.56/1.81  tff(c_1092, plain, (v1_xboole_0('#skF_9')), inference(splitLeft, [status(thm)], [c_1091])).
% 4.56/1.81  tff(c_1284, plain, (![A_166, B_167]: (r2_hidden('#skF_2'(A_166, B_167), A_166) | r1_tarski(A_166, B_167))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.56/1.81  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.56/1.81  tff(c_1326, plain, (![A_169, B_170]: (~v1_xboole_0(A_169) | r1_tarski(A_169, B_170))), inference(resolution, [status(thm)], [c_1284, c_2])).
% 4.56/1.81  tff(c_32, plain, (![A_18, B_19]: (k2_xboole_0(A_18, B_19)=B_19 | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.56/1.81  tff(c_1331, plain, (![A_171, B_172]: (k2_xboole_0(A_171, B_172)=B_172 | ~v1_xboole_0(A_171))), inference(resolution, [status(thm)], [c_1326, c_32])).
% 4.56/1.81  tff(c_1334, plain, (![B_172]: (k2_xboole_0('#skF_9', B_172)=B_172)), inference(resolution, [status(thm)], [c_1092, c_1331])).
% 4.56/1.81  tff(c_1336, plain, (k1_tarski('#skF_8')='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_1334, c_70])).
% 4.56/1.81  tff(c_1338, plain, $false, inference(negUnitSimplification, [status(thm)], [c_873, c_1336])).
% 4.56/1.81  tff(c_1340, plain, (~v1_xboole_0('#skF_9')), inference(splitRight, [status(thm)], [c_1091])).
% 4.56/1.81  tff(c_1339, plain, ('#skF_1'('#skF_9')='#skF_8'), inference(splitRight, [status(thm)], [c_1091])).
% 4.56/1.81  tff(c_874, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_66])).
% 4.56/1.81  tff(c_60, plain, (![B_38]: (r1_tarski(k1_xboole_0, k1_tarski(B_38)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.56/1.81  tff(c_875, plain, (![B_38]: (r1_tarski('#skF_9', k1_tarski(B_38)))), inference(demodulation, [status(thm), theory('equality')], [c_874, c_60])).
% 4.56/1.81  tff(c_936, plain, (![A_127, B_128]: (k2_xboole_0(A_127, B_128)=B_128 | ~r1_tarski(A_127, B_128))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.56/1.81  tff(c_947, plain, (![B_38]: (k2_xboole_0('#skF_9', k1_tarski(B_38))=k1_tarski(B_38))), inference(resolution, [status(thm)], [c_875, c_936])).
% 4.56/1.81  tff(c_1507, plain, (![D_186, B_187]: (~r2_hidden(D_186, '#skF_9') | r2_hidden(D_186, k1_tarski(B_187)))), inference(superposition, [status(thm), theory('equality')], [c_947, c_1044])).
% 4.56/1.81  tff(c_1521, plain, (![D_188, B_189]: (D_188=B_189 | ~r2_hidden(D_188, '#skF_9'))), inference(resolution, [status(thm)], [c_1507, c_36])).
% 4.56/1.81  tff(c_1529, plain, (![B_189]: (B_189='#skF_1'('#skF_9') | v1_xboole_0('#skF_9'))), inference(resolution, [status(thm)], [c_4, c_1521])).
% 4.56/1.81  tff(c_1534, plain, (![B_189]: (B_189='#skF_8' | v1_xboole_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_1339, c_1529])).
% 4.56/1.81  tff(c_1535, plain, (![B_189]: (B_189='#skF_8')), inference(negUnitSimplification, [status(thm)], [c_1340, c_1534])).
% 4.56/1.81  tff(c_1555, plain, (![B_192]: (B_192='#skF_8')), inference(negUnitSimplification, [status(thm)], [c_1340, c_1534])).
% 4.56/1.81  tff(c_1654, plain, ('#skF_9'!='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_1555, c_73])).
% 4.56/1.81  tff(c_1661, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_1535, c_1654])).
% 4.56/1.81  tff(c_1662, plain, (k1_xboole_0!='#skF_10'), inference(splitRight, [status(thm)], [c_64])).
% 4.56/1.81  tff(c_1663, plain, (k1_tarski('#skF_8')='#skF_9'), inference(splitRight, [status(thm)], [c_64])).
% 4.56/1.81  tff(c_68, plain, (k1_tarski('#skF_8')!='#skF_10' | k1_tarski('#skF_8')!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.56/1.81  tff(c_1720, plain, ('#skF_10'!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_1663, c_1663, c_68])).
% 4.56/1.81  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.56/1.81  tff(c_1686, plain, (k2_xboole_0('#skF_9', '#skF_10')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_1663, c_70])).
% 4.56/1.81  tff(c_2086, plain, (![D_1556, B_1557, A_1558]: (~r2_hidden(D_1556, B_1557) | r2_hidden(D_1556, k2_xboole_0(A_1558, B_1557)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.56/1.81  tff(c_2115, plain, (![D_1559]: (~r2_hidden(D_1559, '#skF_10') | r2_hidden(D_1559, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_1686, c_2086])).
% 4.56/1.81  tff(c_2668, plain, (![B_1601]: (r2_hidden('#skF_2'('#skF_10', B_1601), '#skF_9') | r1_tarski('#skF_10', B_1601))), inference(resolution, [status(thm)], [c_10, c_2115])).
% 4.56/1.81  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.56/1.81  tff(c_2682, plain, (r1_tarski('#skF_10', '#skF_9')), inference(resolution, [status(thm)], [c_2668, c_8])).
% 4.56/1.81  tff(c_2586, plain, (![B_1594, A_1595]: (k1_tarski(B_1594)=A_1595 | k1_xboole_0=A_1595 | ~r1_tarski(A_1595, k1_tarski(B_1594)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.56/1.81  tff(c_2605, plain, (![A_1595]: (k1_tarski('#skF_8')=A_1595 | k1_xboole_0=A_1595 | ~r1_tarski(A_1595, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_1663, c_2586])).
% 4.56/1.81  tff(c_2614, plain, (![A_1595]: (A_1595='#skF_9' | k1_xboole_0=A_1595 | ~r1_tarski(A_1595, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_1663, c_2605])).
% 4.56/1.81  tff(c_2687, plain, ('#skF_10'='#skF_9' | k1_xboole_0='#skF_10'), inference(resolution, [status(thm)], [c_2682, c_2614])).
% 4.56/1.81  tff(c_2697, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1662, c_1720, c_2687])).
% 4.56/1.81  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.56/1.81  
% 4.56/1.81  Inference rules
% 4.56/1.81  ----------------------
% 4.56/1.81  #Ref     : 0
% 4.56/1.81  #Sup     : 635
% 4.56/1.81  #Fact    : 0
% 4.56/1.81  #Define  : 0
% 4.56/1.81  #Split   : 14
% 4.56/1.81  #Chain   : 0
% 4.56/1.81  #Close   : 0
% 4.56/1.81  
% 4.56/1.81  Ordering : KBO
% 4.56/1.81  
% 4.56/1.81  Simplification rules
% 4.56/1.81  ----------------------
% 4.56/1.81  #Subsume      : 116
% 4.56/1.81  #Demod        : 176
% 4.56/1.81  #Tautology    : 319
% 4.56/1.81  #SimpNegUnit  : 41
% 4.56/1.81  #BackRed      : 45
% 4.56/1.81  
% 4.56/1.81  #Partial instantiations: 0
% 4.56/1.81  #Strategies tried      : 1
% 4.56/1.81  
% 4.56/1.81  Timing (in seconds)
% 4.56/1.81  ----------------------
% 4.56/1.82  Preprocessing        : 0.34
% 4.56/1.82  Parsing              : 0.17
% 4.56/1.82  CNF conversion       : 0.03
% 4.56/1.82  Main loop            : 0.70
% 4.56/1.82  Inferencing          : 0.28
% 4.56/1.82  Reduction            : 0.21
% 4.56/1.82  Demodulation         : 0.14
% 4.56/1.82  BG Simplification    : 0.03
% 4.56/1.82  Subsumption          : 0.11
% 4.56/1.82  Abstraction          : 0.03
% 4.56/1.82  MUC search           : 0.00
% 4.56/1.82  Cooper               : 0.00
% 4.56/1.82  Total                : 1.08
% 4.56/1.82  Index Insertion      : 0.00
% 4.56/1.82  Index Deletion       : 0.00
% 4.56/1.82  Index Matching       : 0.00
% 4.56/1.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
