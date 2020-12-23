%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:11 EST 2020

% Result     : Theorem 2.97s
% Output     : CNFRefutation 3.09s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 185 expanded)
%              Number of leaves         :   23 (  70 expanded)
%              Depth                    :   11
%              Number of atoms          :  161 ( 445 expanded)
%              Number of equality atoms :    6 (   9 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_86,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,B)
            <=> r1_ordinal1(k1_ordinal1(A),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_ordinal1)).

tff(f_67,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r1_ordinal1(A,B)
            | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(f_71,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v3_ordinal1(k1_ordinal1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( r2_hidden(A,k1_ordinal1(B))
    <=> ( r2_hidden(A,B)
        | A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).

tff(f_76,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_32,plain,(
    v3_ordinal1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_24,plain,(
    ! [B_19,A_17] :
      ( r2_hidden(B_19,A_17)
      | r1_ordinal1(A_17,B_19)
      | ~ v3_ordinal1(B_19)
      | ~ v3_ordinal1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_650,plain,(
    ! [B_125,A_126] :
      ( r2_hidden(B_125,A_126)
      | r1_ordinal1(A_126,B_125)
      | ~ v3_ordinal1(B_125)
      | ~ v3_ordinal1(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_739,plain,(
    ! [A_131,B_132] :
      ( ~ r2_hidden(A_131,B_132)
      | r1_ordinal1(A_131,B_132)
      | ~ v3_ordinal1(B_132)
      | ~ v3_ordinal1(A_131) ) ),
    inference(resolution,[status(thm)],[c_650,c_2])).

tff(c_752,plain,(
    ! [B_19,A_17] :
      ( r1_ordinal1(B_19,A_17)
      | r1_ordinal1(A_17,B_19)
      | ~ v3_ordinal1(B_19)
      | ~ v3_ordinal1(A_17) ) ),
    inference(resolution,[status(thm)],[c_24,c_739])).

tff(c_774,plain,(
    ! [B_19] :
      ( ~ v3_ordinal1(B_19)
      | r1_ordinal1(B_19,B_19) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_752])).

tff(c_26,plain,(
    ! [A_20] :
      ( v3_ordinal1(k1_ordinal1(A_20))
      | ~ v3_ordinal1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_30,plain,(
    v3_ordinal1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_40,plain,
    ( r2_hidden('#skF_1','#skF_2')
    | r1_ordinal1(k1_ordinal1('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_71,plain,(
    r1_ordinal1(k1_ordinal1('#skF_1'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_162,plain,(
    ! [A_56,B_57] :
      ( r1_tarski(A_56,B_57)
      | ~ r1_ordinal1(A_56,B_57)
      | ~ v3_ordinal1(B_57)
      | ~ v3_ordinal1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_75,plain,(
    ! [A_34,B_35] :
      ( ~ r2_hidden(A_34,B_35)
      | r2_hidden(A_34,k1_ordinal1(B_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_28,plain,(
    ! [B_22,A_21] :
      ( ~ r1_tarski(B_22,A_21)
      | ~ r2_hidden(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_85,plain,(
    ! [B_35,A_34] :
      ( ~ r1_tarski(k1_ordinal1(B_35),A_34)
      | ~ r2_hidden(A_34,B_35) ) ),
    inference(resolution,[status(thm)],[c_75,c_28])).

tff(c_371,plain,(
    ! [B_86,B_87] :
      ( ~ r2_hidden(B_86,B_87)
      | ~ r1_ordinal1(k1_ordinal1(B_87),B_86)
      | ~ v3_ordinal1(B_86)
      | ~ v3_ordinal1(k1_ordinal1(B_87)) ) ),
    inference(resolution,[status(thm)],[c_162,c_85])).

tff(c_401,plain,
    ( ~ r2_hidden('#skF_2','#skF_1')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_71,c_371])).

tff(c_411,plain,
    ( ~ r2_hidden('#skF_2','#skF_1')
    | ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_401])).

tff(c_412,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_411])).

tff(c_415,plain,(
    ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_412])).

tff(c_419,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_415])).

tff(c_421,plain,(
    v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_411])).

tff(c_199,plain,(
    ! [B_64,A_65] :
      ( r2_hidden(B_64,A_65)
      | r1_ordinal1(A_65,B_64)
      | ~ v3_ordinal1(B_64)
      | ~ v3_ordinal1(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_34,plain,
    ( ~ r1_ordinal1(k1_ordinal1('#skF_1'),'#skF_2')
    | ~ r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_74,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_34])).

tff(c_237,plain,
    ( r1_ordinal1('#skF_2','#skF_1')
    | ~ v3_ordinal1('#skF_1')
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_199,c_74])).

tff(c_258,plain,(
    r1_ordinal1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_32,c_237])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(A_13,B_14)
      | ~ r1_ordinal1(A_13,B_14)
      | ~ v3_ordinal1(B_14)
      | ~ v3_ordinal1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(B_4,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_301,plain,(
    ! [A_71,B_72,A_73] :
      ( r1_tarski(A_71,B_72)
      | ~ r1_tarski(A_71,A_73)
      | ~ r1_ordinal1(A_73,B_72)
      | ~ v3_ordinal1(B_72)
      | ~ v3_ordinal1(A_73) ) ),
    inference(resolution,[status(thm)],[c_162,c_4])).

tff(c_468,plain,(
    ! [A_93,B_94,B_95] :
      ( r1_tarski(A_93,B_94)
      | ~ r1_ordinal1(B_95,B_94)
      | ~ v3_ordinal1(B_94)
      | ~ r1_ordinal1(A_93,B_95)
      | ~ v3_ordinal1(B_95)
      | ~ v3_ordinal1(A_93) ) ),
    inference(resolution,[status(thm)],[c_16,c_301])).

tff(c_486,plain,(
    ! [A_93] :
      ( r1_tarski(A_93,'#skF_1')
      | ~ v3_ordinal1('#skF_1')
      | ~ r1_ordinal1(A_93,'#skF_2')
      | ~ v3_ordinal1('#skF_2')
      | ~ v3_ordinal1(A_93) ) ),
    inference(resolution,[status(thm)],[c_258,c_468])).

tff(c_505,plain,(
    ! [A_96] :
      ( r1_tarski(A_96,'#skF_1')
      | ~ r1_ordinal1(A_96,'#skF_2')
      | ~ v3_ordinal1(A_96) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_32,c_486])).

tff(c_20,plain,(
    ! [B_16] : r2_hidden(B_16,k1_ordinal1(B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_66,plain,(
    ! [B_31,A_32] :
      ( ~ r1_tarski(B_31,A_32)
      | ~ r2_hidden(A_32,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_70,plain,(
    ! [B_16] : ~ r1_tarski(k1_ordinal1(B_16),B_16) ),
    inference(resolution,[status(thm)],[c_20,c_66])).

tff(c_520,plain,
    ( ~ r1_ordinal1(k1_ordinal1('#skF_1'),'#skF_2')
    | ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_505,c_70])).

tff(c_532,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_421,c_71,c_520])).

tff(c_533,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_541,plain,(
    ~ r2_hidden('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_533,c_2])).

tff(c_776,plain,(
    ! [B_136,A_137] :
      ( r1_ordinal1(B_136,A_137)
      | r1_ordinal1(A_137,B_136)
      | ~ v3_ordinal1(B_136)
      | ~ v3_ordinal1(A_137) ) ),
    inference(resolution,[status(thm)],[c_24,c_739])).

tff(c_543,plain,(
    ~ r1_ordinal1(k1_ordinal1('#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_533,c_34])).

tff(c_786,plain,
    ( r1_ordinal1('#skF_2',k1_ordinal1('#skF_1'))
    | ~ v3_ordinal1(k1_ordinal1('#skF_1'))
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_776,c_543])).

tff(c_803,plain,
    ( r1_ordinal1('#skF_2',k1_ordinal1('#skF_1'))
    | ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_786])).

tff(c_812,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_803])).

tff(c_815,plain,(
    ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_812])).

tff(c_819,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_815])).

tff(c_821,plain,(
    v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_803])).

tff(c_18,plain,(
    ! [B_16,A_15] :
      ( B_16 = A_15
      | r2_hidden(A_15,B_16)
      | ~ r2_hidden(A_15,k1_ordinal1(B_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_837,plain,(
    ! [B_142,B_141] :
      ( B_142 = B_141
      | r2_hidden(B_142,B_141)
      | r1_ordinal1(k1_ordinal1(B_141),B_142)
      | ~ v3_ordinal1(B_142)
      | ~ v3_ordinal1(k1_ordinal1(B_141)) ) ),
    inference(resolution,[status(thm)],[c_650,c_18])).

tff(c_844,plain,
    ( '#skF_2' = '#skF_1'
    | r2_hidden('#skF_2','#skF_1')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_837,c_543])).

tff(c_849,plain,
    ( '#skF_2' = '#skF_1'
    | r2_hidden('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_821,c_30,c_844])).

tff(c_850,plain,(
    '#skF_2' = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_541,c_849])).

tff(c_714,plain,(
    ! [A_128,B_129] :
      ( r1_tarski(A_128,B_129)
      | ~ r1_ordinal1(A_128,B_129)
      | ~ v3_ordinal1(B_129)
      | ~ v3_ordinal1(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_540,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_533,c_28])).

tff(c_730,plain,
    ( ~ r1_ordinal1('#skF_2','#skF_1')
    | ~ v3_ordinal1('#skF_1')
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_714,c_540])).

tff(c_737,plain,(
    ~ r1_ordinal1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_32,c_730])).

tff(c_852,plain,(
    ~ r1_ordinal1('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_850,c_737])).

tff(c_866,plain,(
    ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_774,c_852])).

tff(c_872,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_866])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:56:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.97/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.97/1.47  
% 2.97/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.97/1.47  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > #skF_2 > #skF_1
% 2.97/1.47  
% 2.97/1.47  %Foreground sorts:
% 2.97/1.47  
% 2.97/1.47  
% 2.97/1.47  %Background operators:
% 2.97/1.47  
% 2.97/1.47  
% 2.97/1.47  %Foreground operators:
% 2.97/1.47  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 2.97/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.97/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.97/1.47  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.97/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.97/1.47  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.97/1.47  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 2.97/1.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.97/1.47  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.97/1.47  tff('#skF_2', type, '#skF_2': $i).
% 2.97/1.47  tff('#skF_1', type, '#skF_1': $i).
% 2.97/1.47  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 2.97/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.97/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.97/1.47  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.97/1.47  
% 3.09/1.49  tff(f_86, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, B) <=> r1_ordinal1(k1_ordinal1(A), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_ordinal1)).
% 3.09/1.49  tff(f_67, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_ordinal1)).
% 3.09/1.49  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 3.09/1.49  tff(f_71, axiom, (![A]: (v3_ordinal1(A) => v3_ordinal1(k1_ordinal1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_ordinal1)).
% 3.09/1.49  tff(f_52, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 3.09/1.49  tff(f_58, axiom, (![A, B]: (r2_hidden(A, k1_ordinal1(B)) <=> (r2_hidden(A, B) | (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_ordinal1)).
% 3.09/1.49  tff(f_76, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.09/1.49  tff(f_36, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.09/1.49  tff(c_32, plain, (v3_ordinal1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.09/1.49  tff(c_24, plain, (![B_19, A_17]: (r2_hidden(B_19, A_17) | r1_ordinal1(A_17, B_19) | ~v3_ordinal1(B_19) | ~v3_ordinal1(A_17))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.09/1.49  tff(c_650, plain, (![B_125, A_126]: (r2_hidden(B_125, A_126) | r1_ordinal1(A_126, B_125) | ~v3_ordinal1(B_125) | ~v3_ordinal1(A_126))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.09/1.49  tff(c_2, plain, (![B_2, A_1]: (~r2_hidden(B_2, A_1) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.09/1.49  tff(c_739, plain, (![A_131, B_132]: (~r2_hidden(A_131, B_132) | r1_ordinal1(A_131, B_132) | ~v3_ordinal1(B_132) | ~v3_ordinal1(A_131))), inference(resolution, [status(thm)], [c_650, c_2])).
% 3.09/1.49  tff(c_752, plain, (![B_19, A_17]: (r1_ordinal1(B_19, A_17) | r1_ordinal1(A_17, B_19) | ~v3_ordinal1(B_19) | ~v3_ordinal1(A_17))), inference(resolution, [status(thm)], [c_24, c_739])).
% 3.09/1.49  tff(c_774, plain, (![B_19]: (~v3_ordinal1(B_19) | r1_ordinal1(B_19, B_19))), inference(factorization, [status(thm), theory('equality')], [c_752])).
% 3.09/1.49  tff(c_26, plain, (![A_20]: (v3_ordinal1(k1_ordinal1(A_20)) | ~v3_ordinal1(A_20))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.09/1.49  tff(c_30, plain, (v3_ordinal1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.09/1.49  tff(c_40, plain, (r2_hidden('#skF_1', '#skF_2') | r1_ordinal1(k1_ordinal1('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.09/1.49  tff(c_71, plain, (r1_ordinal1(k1_ordinal1('#skF_1'), '#skF_2')), inference(splitLeft, [status(thm)], [c_40])).
% 3.09/1.49  tff(c_162, plain, (![A_56, B_57]: (r1_tarski(A_56, B_57) | ~r1_ordinal1(A_56, B_57) | ~v3_ordinal1(B_57) | ~v3_ordinal1(A_56))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.09/1.49  tff(c_75, plain, (![A_34, B_35]: (~r2_hidden(A_34, B_35) | r2_hidden(A_34, k1_ordinal1(B_35)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.09/1.49  tff(c_28, plain, (![B_22, A_21]: (~r1_tarski(B_22, A_21) | ~r2_hidden(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.09/1.49  tff(c_85, plain, (![B_35, A_34]: (~r1_tarski(k1_ordinal1(B_35), A_34) | ~r2_hidden(A_34, B_35))), inference(resolution, [status(thm)], [c_75, c_28])).
% 3.09/1.49  tff(c_371, plain, (![B_86, B_87]: (~r2_hidden(B_86, B_87) | ~r1_ordinal1(k1_ordinal1(B_87), B_86) | ~v3_ordinal1(B_86) | ~v3_ordinal1(k1_ordinal1(B_87)))), inference(resolution, [status(thm)], [c_162, c_85])).
% 3.09/1.49  tff(c_401, plain, (~r2_hidden('#skF_2', '#skF_1') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(resolution, [status(thm)], [c_71, c_371])).
% 3.09/1.49  tff(c_411, plain, (~r2_hidden('#skF_2', '#skF_1') | ~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_401])).
% 3.09/1.49  tff(c_412, plain, (~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(splitLeft, [status(thm)], [c_411])).
% 3.09/1.49  tff(c_415, plain, (~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_26, c_412])).
% 3.09/1.49  tff(c_419, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_415])).
% 3.09/1.49  tff(c_421, plain, (v3_ordinal1(k1_ordinal1('#skF_1'))), inference(splitRight, [status(thm)], [c_411])).
% 3.09/1.49  tff(c_199, plain, (![B_64, A_65]: (r2_hidden(B_64, A_65) | r1_ordinal1(A_65, B_64) | ~v3_ordinal1(B_64) | ~v3_ordinal1(A_65))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.09/1.49  tff(c_34, plain, (~r1_ordinal1(k1_ordinal1('#skF_1'), '#skF_2') | ~r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.09/1.49  tff(c_74, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_71, c_34])).
% 3.09/1.49  tff(c_237, plain, (r1_ordinal1('#skF_2', '#skF_1') | ~v3_ordinal1('#skF_1') | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_199, c_74])).
% 3.09/1.49  tff(c_258, plain, (r1_ordinal1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_32, c_237])).
% 3.09/1.49  tff(c_16, plain, (![A_13, B_14]: (r1_tarski(A_13, B_14) | ~r1_ordinal1(A_13, B_14) | ~v3_ordinal1(B_14) | ~v3_ordinal1(A_13))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.09/1.49  tff(c_4, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(B_4, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.09/1.49  tff(c_301, plain, (![A_71, B_72, A_73]: (r1_tarski(A_71, B_72) | ~r1_tarski(A_71, A_73) | ~r1_ordinal1(A_73, B_72) | ~v3_ordinal1(B_72) | ~v3_ordinal1(A_73))), inference(resolution, [status(thm)], [c_162, c_4])).
% 3.09/1.49  tff(c_468, plain, (![A_93, B_94, B_95]: (r1_tarski(A_93, B_94) | ~r1_ordinal1(B_95, B_94) | ~v3_ordinal1(B_94) | ~r1_ordinal1(A_93, B_95) | ~v3_ordinal1(B_95) | ~v3_ordinal1(A_93))), inference(resolution, [status(thm)], [c_16, c_301])).
% 3.09/1.49  tff(c_486, plain, (![A_93]: (r1_tarski(A_93, '#skF_1') | ~v3_ordinal1('#skF_1') | ~r1_ordinal1(A_93, '#skF_2') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1(A_93))), inference(resolution, [status(thm)], [c_258, c_468])).
% 3.09/1.49  tff(c_505, plain, (![A_96]: (r1_tarski(A_96, '#skF_1') | ~r1_ordinal1(A_96, '#skF_2') | ~v3_ordinal1(A_96))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_32, c_486])).
% 3.09/1.49  tff(c_20, plain, (![B_16]: (r2_hidden(B_16, k1_ordinal1(B_16)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.09/1.49  tff(c_66, plain, (![B_31, A_32]: (~r1_tarski(B_31, A_32) | ~r2_hidden(A_32, B_31))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.09/1.49  tff(c_70, plain, (![B_16]: (~r1_tarski(k1_ordinal1(B_16), B_16))), inference(resolution, [status(thm)], [c_20, c_66])).
% 3.09/1.49  tff(c_520, plain, (~r1_ordinal1(k1_ordinal1('#skF_1'), '#skF_2') | ~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(resolution, [status(thm)], [c_505, c_70])).
% 3.09/1.49  tff(c_532, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_421, c_71, c_520])).
% 3.09/1.49  tff(c_533, plain, (r2_hidden('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_40])).
% 3.09/1.49  tff(c_541, plain, (~r2_hidden('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_533, c_2])).
% 3.09/1.49  tff(c_776, plain, (![B_136, A_137]: (r1_ordinal1(B_136, A_137) | r1_ordinal1(A_137, B_136) | ~v3_ordinal1(B_136) | ~v3_ordinal1(A_137))), inference(resolution, [status(thm)], [c_24, c_739])).
% 3.09/1.49  tff(c_543, plain, (~r1_ordinal1(k1_ordinal1('#skF_1'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_533, c_34])).
% 3.09/1.49  tff(c_786, plain, (r1_ordinal1('#skF_2', k1_ordinal1('#skF_1')) | ~v3_ordinal1(k1_ordinal1('#skF_1')) | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_776, c_543])).
% 3.09/1.49  tff(c_803, plain, (r1_ordinal1('#skF_2', k1_ordinal1('#skF_1')) | ~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_786])).
% 3.09/1.49  tff(c_812, plain, (~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(splitLeft, [status(thm)], [c_803])).
% 3.09/1.49  tff(c_815, plain, (~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_26, c_812])).
% 3.09/1.49  tff(c_819, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_815])).
% 3.09/1.49  tff(c_821, plain, (v3_ordinal1(k1_ordinal1('#skF_1'))), inference(splitRight, [status(thm)], [c_803])).
% 3.09/1.49  tff(c_18, plain, (![B_16, A_15]: (B_16=A_15 | r2_hidden(A_15, B_16) | ~r2_hidden(A_15, k1_ordinal1(B_16)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.09/1.49  tff(c_837, plain, (![B_142, B_141]: (B_142=B_141 | r2_hidden(B_142, B_141) | r1_ordinal1(k1_ordinal1(B_141), B_142) | ~v3_ordinal1(B_142) | ~v3_ordinal1(k1_ordinal1(B_141)))), inference(resolution, [status(thm)], [c_650, c_18])).
% 3.09/1.49  tff(c_844, plain, ('#skF_2'='#skF_1' | r2_hidden('#skF_2', '#skF_1') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(resolution, [status(thm)], [c_837, c_543])).
% 3.09/1.49  tff(c_849, plain, ('#skF_2'='#skF_1' | r2_hidden('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_821, c_30, c_844])).
% 3.09/1.49  tff(c_850, plain, ('#skF_2'='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_541, c_849])).
% 3.09/1.49  tff(c_714, plain, (![A_128, B_129]: (r1_tarski(A_128, B_129) | ~r1_ordinal1(A_128, B_129) | ~v3_ordinal1(B_129) | ~v3_ordinal1(A_128))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.09/1.49  tff(c_540, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_533, c_28])).
% 3.09/1.49  tff(c_730, plain, (~r1_ordinal1('#skF_2', '#skF_1') | ~v3_ordinal1('#skF_1') | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_714, c_540])).
% 3.09/1.49  tff(c_737, plain, (~r1_ordinal1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_32, c_730])).
% 3.09/1.49  tff(c_852, plain, (~r1_ordinal1('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_850, c_737])).
% 3.09/1.49  tff(c_866, plain, (~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_774, c_852])).
% 3.09/1.49  tff(c_872, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_866])).
% 3.09/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.09/1.49  
% 3.09/1.49  Inference rules
% 3.09/1.49  ----------------------
% 3.09/1.49  #Ref     : 0
% 3.09/1.49  #Sup     : 154
% 3.09/1.49  #Fact    : 4
% 3.09/1.49  #Define  : 0
% 3.09/1.49  #Split   : 3
% 3.09/1.49  #Chain   : 0
% 3.09/1.49  #Close   : 0
% 3.09/1.49  
% 3.09/1.49  Ordering : KBO
% 3.09/1.49  
% 3.09/1.49  Simplification rules
% 3.09/1.49  ----------------------
% 3.09/1.49  #Subsume      : 30
% 3.09/1.49  #Demod        : 48
% 3.09/1.49  #Tautology    : 30
% 3.09/1.49  #SimpNegUnit  : 1
% 3.09/1.49  #BackRed      : 8
% 3.09/1.49  
% 3.09/1.49  #Partial instantiations: 0
% 3.09/1.49  #Strategies tried      : 1
% 3.09/1.49  
% 3.09/1.49  Timing (in seconds)
% 3.09/1.49  ----------------------
% 3.09/1.49  Preprocessing        : 0.30
% 3.09/1.49  Parsing              : 0.16
% 3.09/1.49  CNF conversion       : 0.02
% 3.09/1.49  Main loop            : 0.36
% 3.09/1.49  Inferencing          : 0.14
% 3.09/1.49  Reduction            : 0.09
% 3.09/1.50  Demodulation         : 0.06
% 3.09/1.50  BG Simplification    : 0.02
% 3.09/1.50  Subsumption          : 0.09
% 3.09/1.50  Abstraction          : 0.02
% 3.09/1.50  MUC search           : 0.00
% 3.09/1.50  Cooper               : 0.00
% 3.09/1.50  Total                : 0.70
% 3.09/1.50  Index Insertion      : 0.00
% 3.09/1.50  Index Deletion       : 0.00
% 3.09/1.50  Index Matching       : 0.00
% 3.09/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
