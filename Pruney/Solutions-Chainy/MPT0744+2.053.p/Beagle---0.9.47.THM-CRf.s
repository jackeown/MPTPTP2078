%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:22 EST 2020

% Result     : Theorem 3.90s
% Output     : CNFRefutation 4.19s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 200 expanded)
%              Number of leaves         :   36 (  83 expanded)
%              Depth                    :   10
%              Number of atoms          :  125 ( 410 expanded)
%              Number of equality atoms :   29 (  94 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_1 > #skF_7 > #skF_2 > #skF_4 > #skF_8 > #skF_6 > #skF_5 > #skF_3

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_152,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,k1_ordinal1(B))
            <=> r1_ordinal1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).

tff(f_103,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
        | r1_ordinal1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

tff(f_51,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_53,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_105,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_113,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_128,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ~ ( ~ r2_hidden(A,B)
              & A != B
              & ~ r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).

tff(f_142,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_128,plain,(
    v3_ordinal1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_130,plain,(
    v3_ordinal1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_993,plain,(
    ! [B_326,A_327] :
      ( r1_ordinal1(B_326,A_327)
      | r1_ordinal1(A_327,B_326)
      | ~ v3_ordinal1(B_326)
      | ~ v3_ordinal1(A_327) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_44,plain,(
    ! [A_14] : k2_tarski(A_14,A_14) = k1_tarski(A_14) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_177,plain,(
    ! [A_92,B_93] : k1_enumset1(A_92,A_92,B_93) = k2_tarski(A_92,B_93) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_24,plain,(
    ! [E_13,A_7,C_9] : r2_hidden(E_13,k1_enumset1(A_7,E_13,C_9)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_204,plain,(
    ! [A_94,B_95] : r2_hidden(A_94,k2_tarski(A_94,B_95)) ),
    inference(superposition,[status(thm),theory(equality)],[c_177,c_24])).

tff(c_210,plain,(
    ! [A_14] : r2_hidden(A_14,k1_tarski(A_14)) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_204])).

tff(c_116,plain,(
    ! [A_58] : k2_xboole_0(A_58,k1_tarski(A_58)) = k1_ordinal1(A_58) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_250,plain,(
    ! [D_106,B_107,A_108] :
      ( ~ r2_hidden(D_106,B_107)
      | r2_hidden(D_106,k2_xboole_0(A_108,B_107)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_315,plain,(
    ! [D_123,A_124] :
      ( ~ r2_hidden(D_123,k1_tarski(A_124))
      | r2_hidden(D_123,k1_ordinal1(A_124)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_250])).

tff(c_319,plain,(
    ! [A_14] : r2_hidden(A_14,k1_ordinal1(A_14)) ),
    inference(resolution,[status(thm)],[c_210,c_315])).

tff(c_138,plain,
    ( r2_hidden('#skF_7',k1_ordinal1('#skF_8'))
    | r1_ordinal1('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_174,plain,(
    r1_ordinal1('#skF_7','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_138])).

tff(c_120,plain,(
    ! [A_59,B_60] :
      ( r1_tarski(A_59,B_60)
      | ~ r1_ordinal1(A_59,B_60)
      | ~ v3_ordinal1(B_60)
      | ~ v3_ordinal1(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_631,plain,(
    ! [B_266,A_267] :
      ( r2_hidden(B_266,A_267)
      | B_266 = A_267
      | r2_hidden(A_267,B_266)
      | ~ v3_ordinal1(B_266)
      | ~ v3_ordinal1(A_267) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_278,plain,(
    ! [D_110,A_111,B_112] :
      ( ~ r2_hidden(D_110,A_111)
      | r2_hidden(D_110,k2_xboole_0(A_111,B_112)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_298,plain,(
    ! [D_116,A_117] :
      ( ~ r2_hidden(D_116,A_117)
      | r2_hidden(D_116,k1_ordinal1(A_117)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_278])).

tff(c_132,plain,
    ( ~ r1_ordinal1('#skF_7','#skF_8')
    | ~ r2_hidden('#skF_7',k1_ordinal1('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_240,plain,(
    ~ r2_hidden('#skF_7',k1_ordinal1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_132])).

tff(c_305,plain,(
    ~ r2_hidden('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_298,c_240])).

tff(c_650,plain,
    ( '#skF_7' = '#skF_8'
    | r2_hidden('#skF_8','#skF_7')
    | ~ v3_ordinal1('#skF_7')
    | ~ v3_ordinal1('#skF_8') ),
    inference(resolution,[status(thm)],[c_631,c_305])).

tff(c_684,plain,
    ( '#skF_7' = '#skF_8'
    | r2_hidden('#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_130,c_650])).

tff(c_694,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_684])).

tff(c_126,plain,(
    ! [B_68,A_67] :
      ( ~ r1_tarski(B_68,A_67)
      | ~ r2_hidden(A_67,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_698,plain,(
    ~ r1_tarski('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_694,c_126])).

tff(c_701,plain,
    ( ~ r1_ordinal1('#skF_7','#skF_8')
    | ~ v3_ordinal1('#skF_8')
    | ~ v3_ordinal1('#skF_7') ),
    inference(resolution,[status(thm)],[c_120,c_698])).

tff(c_705,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_128,c_174,c_701])).

tff(c_706,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_684])).

tff(c_711,plain,(
    ~ r2_hidden('#skF_8',k1_ordinal1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_706,c_240])).

tff(c_716,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_319,c_711])).

tff(c_718,plain,(
    ~ r1_ordinal1('#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_138])).

tff(c_1004,plain,
    ( r1_ordinal1('#skF_8','#skF_7')
    | ~ v3_ordinal1('#skF_7')
    | ~ v3_ordinal1('#skF_8') ),
    inference(resolution,[status(thm)],[c_993,c_718])).

tff(c_1020,plain,(
    r1_ordinal1('#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_130,c_1004])).

tff(c_717,plain,(
    r2_hidden('#skF_7',k1_ordinal1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_138])).

tff(c_1069,plain,(
    ! [D_383,B_384,A_385] :
      ( r2_hidden(D_383,B_384)
      | r2_hidden(D_383,A_385)
      | ~ r2_hidden(D_383,k2_xboole_0(A_385,B_384)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1085,plain,(
    ! [D_383,A_58] :
      ( r2_hidden(D_383,k1_tarski(A_58))
      | r2_hidden(D_383,A_58)
      | ~ r2_hidden(D_383,k1_ordinal1(A_58)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_1069])).

tff(c_46,plain,(
    ! [A_15,B_16] : k1_enumset1(A_15,A_15,B_16) = k2_tarski(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1197,plain,(
    ! [E_446,C_447,B_448,A_449] :
      ( E_446 = C_447
      | E_446 = B_448
      | E_446 = A_449
      | ~ r2_hidden(E_446,k1_enumset1(A_449,B_448,C_447)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1249,plain,(
    ! [E_474,B_475,A_476] :
      ( E_474 = B_475
      | E_474 = A_476
      | E_474 = A_476
      | ~ r2_hidden(E_474,k2_tarski(A_476,B_475)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_1197])).

tff(c_1278,plain,(
    ! [E_477,A_478] :
      ( E_477 = A_478
      | E_477 = A_478
      | E_477 = A_478
      | ~ r2_hidden(E_477,k1_tarski(A_478)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_1249])).

tff(c_1312,plain,(
    ! [D_484,A_485] :
      ( D_484 = A_485
      | r2_hidden(D_484,A_485)
      | ~ r2_hidden(D_484,k1_ordinal1(A_485)) ) ),
    inference(resolution,[status(thm)],[c_1085,c_1278])).

tff(c_1340,plain,
    ( '#skF_7' = '#skF_8'
    | r2_hidden('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_717,c_1312])).

tff(c_1341,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_1340])).

tff(c_1345,plain,(
    ~ r1_tarski('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_1341,c_126])).

tff(c_1348,plain,
    ( ~ r1_ordinal1('#skF_8','#skF_7')
    | ~ v3_ordinal1('#skF_7')
    | ~ v3_ordinal1('#skF_8') ),
    inference(resolution,[status(thm)],[c_120,c_1345])).

tff(c_1352,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_130,c_1020,c_1348])).

tff(c_1353,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_1340])).

tff(c_1355,plain,(
    r1_ordinal1('#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1353,c_1020])).

tff(c_1358,plain,(
    ~ r1_ordinal1('#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1353,c_718])).

tff(c_1376,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1355,c_1358])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:12:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.90/1.67  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.90/1.68  
% 3.90/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.90/1.68  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_1 > #skF_7 > #skF_2 > #skF_4 > #skF_8 > #skF_6 > #skF_5 > #skF_3
% 3.90/1.68  
% 3.90/1.68  %Foreground sorts:
% 3.90/1.68  
% 3.90/1.68  
% 3.90/1.68  %Background operators:
% 3.90/1.68  
% 3.90/1.68  
% 3.90/1.68  %Foreground operators:
% 3.90/1.68  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.90/1.68  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 3.90/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.90/1.68  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.90/1.68  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.90/1.68  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.90/1.68  tff('#skF_7', type, '#skF_7': $i).
% 3.90/1.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.90/1.68  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.90/1.68  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 3.90/1.68  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.90/1.68  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.90/1.68  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.90/1.68  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 3.90/1.68  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.90/1.68  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 3.90/1.68  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.90/1.68  tff('#skF_8', type, '#skF_8': $i).
% 3.90/1.68  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.90/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.90/1.68  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.90/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.90/1.68  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.90/1.68  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.90/1.68  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.90/1.68  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.90/1.68  
% 4.19/1.70  tff(f_152, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, k1_ordinal1(B)) <=> r1_ordinal1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_ordinal1)).
% 4.19/1.70  tff(f_103, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) | r1_ordinal1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', connectedness_r1_ordinal1)).
% 4.19/1.70  tff(f_51, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 4.19/1.70  tff(f_53, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 4.19/1.70  tff(f_49, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 4.19/1.70  tff(f_105, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_ordinal1)).
% 4.19/1.70  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 4.19/1.70  tff(f_113, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 4.19/1.70  tff(f_128, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => ~((~r2_hidden(A, B) & ~(A = B)) & ~r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_ordinal1)).
% 4.19/1.70  tff(f_142, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 4.19/1.70  tff(c_128, plain, (v3_ordinal1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.19/1.70  tff(c_130, plain, (v3_ordinal1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.19/1.70  tff(c_993, plain, (![B_326, A_327]: (r1_ordinal1(B_326, A_327) | r1_ordinal1(A_327, B_326) | ~v3_ordinal1(B_326) | ~v3_ordinal1(A_327))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.19/1.70  tff(c_44, plain, (![A_14]: (k2_tarski(A_14, A_14)=k1_tarski(A_14))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.19/1.70  tff(c_177, plain, (![A_92, B_93]: (k1_enumset1(A_92, A_92, B_93)=k2_tarski(A_92, B_93))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.19/1.70  tff(c_24, plain, (![E_13, A_7, C_9]: (r2_hidden(E_13, k1_enumset1(A_7, E_13, C_9)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.19/1.70  tff(c_204, plain, (![A_94, B_95]: (r2_hidden(A_94, k2_tarski(A_94, B_95)))), inference(superposition, [status(thm), theory('equality')], [c_177, c_24])).
% 4.19/1.70  tff(c_210, plain, (![A_14]: (r2_hidden(A_14, k1_tarski(A_14)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_204])).
% 4.19/1.70  tff(c_116, plain, (![A_58]: (k2_xboole_0(A_58, k1_tarski(A_58))=k1_ordinal1(A_58))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.19/1.70  tff(c_250, plain, (![D_106, B_107, A_108]: (~r2_hidden(D_106, B_107) | r2_hidden(D_106, k2_xboole_0(A_108, B_107)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.19/1.70  tff(c_315, plain, (![D_123, A_124]: (~r2_hidden(D_123, k1_tarski(A_124)) | r2_hidden(D_123, k1_ordinal1(A_124)))), inference(superposition, [status(thm), theory('equality')], [c_116, c_250])).
% 4.19/1.70  tff(c_319, plain, (![A_14]: (r2_hidden(A_14, k1_ordinal1(A_14)))), inference(resolution, [status(thm)], [c_210, c_315])).
% 4.19/1.70  tff(c_138, plain, (r2_hidden('#skF_7', k1_ordinal1('#skF_8')) | r1_ordinal1('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.19/1.70  tff(c_174, plain, (r1_ordinal1('#skF_7', '#skF_8')), inference(splitLeft, [status(thm)], [c_138])).
% 4.19/1.70  tff(c_120, plain, (![A_59, B_60]: (r1_tarski(A_59, B_60) | ~r1_ordinal1(A_59, B_60) | ~v3_ordinal1(B_60) | ~v3_ordinal1(A_59))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.19/1.70  tff(c_631, plain, (![B_266, A_267]: (r2_hidden(B_266, A_267) | B_266=A_267 | r2_hidden(A_267, B_266) | ~v3_ordinal1(B_266) | ~v3_ordinal1(A_267))), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.19/1.70  tff(c_278, plain, (![D_110, A_111, B_112]: (~r2_hidden(D_110, A_111) | r2_hidden(D_110, k2_xboole_0(A_111, B_112)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.19/1.70  tff(c_298, plain, (![D_116, A_117]: (~r2_hidden(D_116, A_117) | r2_hidden(D_116, k1_ordinal1(A_117)))), inference(superposition, [status(thm), theory('equality')], [c_116, c_278])).
% 4.19/1.70  tff(c_132, plain, (~r1_ordinal1('#skF_7', '#skF_8') | ~r2_hidden('#skF_7', k1_ordinal1('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.19/1.70  tff(c_240, plain, (~r2_hidden('#skF_7', k1_ordinal1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_174, c_132])).
% 4.19/1.70  tff(c_305, plain, (~r2_hidden('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_298, c_240])).
% 4.19/1.70  tff(c_650, plain, ('#skF_7'='#skF_8' | r2_hidden('#skF_8', '#skF_7') | ~v3_ordinal1('#skF_7') | ~v3_ordinal1('#skF_8')), inference(resolution, [status(thm)], [c_631, c_305])).
% 4.19/1.70  tff(c_684, plain, ('#skF_7'='#skF_8' | r2_hidden('#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_128, c_130, c_650])).
% 4.19/1.70  tff(c_694, plain, (r2_hidden('#skF_8', '#skF_7')), inference(splitLeft, [status(thm)], [c_684])).
% 4.19/1.70  tff(c_126, plain, (![B_68, A_67]: (~r1_tarski(B_68, A_67) | ~r2_hidden(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_142])).
% 4.19/1.70  tff(c_698, plain, (~r1_tarski('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_694, c_126])).
% 4.19/1.70  tff(c_701, plain, (~r1_ordinal1('#skF_7', '#skF_8') | ~v3_ordinal1('#skF_8') | ~v3_ordinal1('#skF_7')), inference(resolution, [status(thm)], [c_120, c_698])).
% 4.19/1.70  tff(c_705, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_130, c_128, c_174, c_701])).
% 4.19/1.70  tff(c_706, plain, ('#skF_7'='#skF_8'), inference(splitRight, [status(thm)], [c_684])).
% 4.19/1.70  tff(c_711, plain, (~r2_hidden('#skF_8', k1_ordinal1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_706, c_240])).
% 4.19/1.70  tff(c_716, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_319, c_711])).
% 4.19/1.70  tff(c_718, plain, (~r1_ordinal1('#skF_7', '#skF_8')), inference(splitRight, [status(thm)], [c_138])).
% 4.19/1.70  tff(c_1004, plain, (r1_ordinal1('#skF_8', '#skF_7') | ~v3_ordinal1('#skF_7') | ~v3_ordinal1('#skF_8')), inference(resolution, [status(thm)], [c_993, c_718])).
% 4.19/1.70  tff(c_1020, plain, (r1_ordinal1('#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_128, c_130, c_1004])).
% 4.19/1.70  tff(c_717, plain, (r2_hidden('#skF_7', k1_ordinal1('#skF_8'))), inference(splitRight, [status(thm)], [c_138])).
% 4.19/1.70  tff(c_1069, plain, (![D_383, B_384, A_385]: (r2_hidden(D_383, B_384) | r2_hidden(D_383, A_385) | ~r2_hidden(D_383, k2_xboole_0(A_385, B_384)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.19/1.70  tff(c_1085, plain, (![D_383, A_58]: (r2_hidden(D_383, k1_tarski(A_58)) | r2_hidden(D_383, A_58) | ~r2_hidden(D_383, k1_ordinal1(A_58)))), inference(superposition, [status(thm), theory('equality')], [c_116, c_1069])).
% 4.19/1.70  tff(c_46, plain, (![A_15, B_16]: (k1_enumset1(A_15, A_15, B_16)=k2_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.19/1.70  tff(c_1197, plain, (![E_446, C_447, B_448, A_449]: (E_446=C_447 | E_446=B_448 | E_446=A_449 | ~r2_hidden(E_446, k1_enumset1(A_449, B_448, C_447)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.19/1.70  tff(c_1249, plain, (![E_474, B_475, A_476]: (E_474=B_475 | E_474=A_476 | E_474=A_476 | ~r2_hidden(E_474, k2_tarski(A_476, B_475)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_1197])).
% 4.19/1.70  tff(c_1278, plain, (![E_477, A_478]: (E_477=A_478 | E_477=A_478 | E_477=A_478 | ~r2_hidden(E_477, k1_tarski(A_478)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_1249])).
% 4.19/1.70  tff(c_1312, plain, (![D_484, A_485]: (D_484=A_485 | r2_hidden(D_484, A_485) | ~r2_hidden(D_484, k1_ordinal1(A_485)))), inference(resolution, [status(thm)], [c_1085, c_1278])).
% 4.19/1.70  tff(c_1340, plain, ('#skF_7'='#skF_8' | r2_hidden('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_717, c_1312])).
% 4.19/1.70  tff(c_1341, plain, (r2_hidden('#skF_7', '#skF_8')), inference(splitLeft, [status(thm)], [c_1340])).
% 4.19/1.70  tff(c_1345, plain, (~r1_tarski('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_1341, c_126])).
% 4.19/1.70  tff(c_1348, plain, (~r1_ordinal1('#skF_8', '#skF_7') | ~v3_ordinal1('#skF_7') | ~v3_ordinal1('#skF_8')), inference(resolution, [status(thm)], [c_120, c_1345])).
% 4.19/1.70  tff(c_1352, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_128, c_130, c_1020, c_1348])).
% 4.19/1.70  tff(c_1353, plain, ('#skF_7'='#skF_8'), inference(splitRight, [status(thm)], [c_1340])).
% 4.19/1.70  tff(c_1355, plain, (r1_ordinal1('#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1353, c_1020])).
% 4.19/1.70  tff(c_1358, plain, (~r1_ordinal1('#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1353, c_718])).
% 4.19/1.70  tff(c_1376, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1355, c_1358])).
% 4.19/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.19/1.70  
% 4.19/1.70  Inference rules
% 4.19/1.70  ----------------------
% 4.19/1.70  #Ref     : 0
% 4.19/1.70  #Sup     : 241
% 4.19/1.70  #Fact    : 8
% 4.19/1.70  #Define  : 0
% 4.19/1.70  #Split   : 6
% 4.19/1.70  #Chain   : 0
% 4.19/1.70  #Close   : 0
% 4.19/1.70  
% 4.19/1.70  Ordering : KBO
% 4.19/1.70  
% 4.19/1.70  Simplification rules
% 4.19/1.70  ----------------------
% 4.19/1.70  #Subsume      : 36
% 4.19/1.70  #Demod        : 41
% 4.19/1.70  #Tautology    : 64
% 4.19/1.70  #SimpNegUnit  : 0
% 4.19/1.70  #BackRed      : 10
% 4.19/1.70  
% 4.19/1.70  #Partial instantiations: 0
% 4.19/1.70  #Strategies tried      : 1
% 4.19/1.70  
% 4.19/1.70  Timing (in seconds)
% 4.19/1.70  ----------------------
% 4.19/1.70  Preprocessing        : 0.40
% 4.19/1.70  Parsing              : 0.19
% 4.19/1.70  CNF conversion       : 0.03
% 4.19/1.70  Main loop            : 0.49
% 4.19/1.70  Inferencing          : 0.16
% 4.19/1.70  Reduction            : 0.14
% 4.19/1.70  Demodulation         : 0.10
% 4.19/1.70  BG Simplification    : 0.03
% 4.19/1.70  Subsumption          : 0.12
% 4.19/1.70  Abstraction          : 0.03
% 4.19/1.70  MUC search           : 0.00
% 4.19/1.70  Cooper               : 0.00
% 4.19/1.70  Total                : 0.92
% 4.19/1.70  Index Insertion      : 0.00
% 4.19/1.70  Index Deletion       : 0.00
% 4.19/1.70  Index Matching       : 0.00
% 4.19/1.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
