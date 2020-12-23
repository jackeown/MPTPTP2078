%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:22 EST 2020

% Result     : Theorem 3.92s
% Output     : CNFRefutation 3.92s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 182 expanded)
%              Number of leaves         :   35 (  77 expanded)
%              Depth                    :    9
%              Number of atoms          :  114 ( 365 expanded)
%              Number of equality atoms :   20 (  67 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_1 > #skF_4 > #skF_7 > #skF_2 > #skF_8 > #skF_6 > #skF_3 > #skF_5

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_137,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,k1_ordinal1(B))
            <=> r1_ordinal1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).

tff(f_97,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
        | r1_ordinal1(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

tff(f_45,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_99,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_107,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_122,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ~ ( ~ r2_hidden(A,B)
              & A != B
              & ~ r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).

tff(f_127,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_120,plain,(
    v3_ordinal1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_122,plain,(
    v3_ordinal1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_793,plain,(
    ! [B_249,A_250] :
      ( r1_ordinal1(B_249,A_250)
      | r1_ordinal1(A_250,B_249)
      | ~ v3_ordinal1(B_249)
      | ~ v3_ordinal1(A_250) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_38,plain,(
    ! [A_13] : k2_tarski(A_13,A_13) = k1_tarski(A_13) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_140,plain,(
    ! [D_67,B_68] : r2_hidden(D_67,k2_tarski(D_67,B_68)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_143,plain,(
    ! [A_13] : r2_hidden(A_13,k1_tarski(A_13)) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_140])).

tff(c_110,plain,(
    ! [A_57] : k2_xboole_0(A_57,k1_tarski(A_57)) = k1_ordinal1(A_57) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_221,plain,(
    ! [D_85,B_86,A_87] :
      ( ~ r2_hidden(D_85,B_86)
      | r2_hidden(D_85,k2_xboole_0(A_87,B_86)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_274,plain,(
    ! [D_101,A_102] :
      ( ~ r2_hidden(D_101,k1_tarski(A_102))
      | r2_hidden(D_101,k1_ordinal1(A_102)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_221])).

tff(c_278,plain,(
    ! [A_13] : r2_hidden(A_13,k1_ordinal1(A_13)) ),
    inference(resolution,[status(thm)],[c_143,c_274])).

tff(c_124,plain,
    ( ~ r1_ordinal1('#skF_7','#skF_8')
    | ~ r2_hidden('#skF_7',k1_ordinal1('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_168,plain,(
    ~ r2_hidden('#skF_7',k1_ordinal1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_124])).

tff(c_130,plain,
    ( r2_hidden('#skF_7',k1_ordinal1('#skF_8'))
    | r1_ordinal1('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_191,plain,(
    r1_ordinal1('#skF_7','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_168,c_130])).

tff(c_114,plain,(
    ! [A_58,B_59] :
      ( r1_tarski(A_58,B_59)
      | ~ r1_ordinal1(A_58,B_59)
      | ~ v3_ordinal1(B_59)
      | ~ v3_ordinal1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_517,plain,(
    ! [B_205,A_206] :
      ( r2_hidden(B_205,A_206)
      | B_205 = A_206
      | r2_hidden(A_206,B_205)
      | ~ v3_ordinal1(B_205)
      | ~ v3_ordinal1(A_206) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_232,plain,(
    ! [D_88,A_89,B_90] :
      ( ~ r2_hidden(D_88,A_89)
      | r2_hidden(D_88,k2_xboole_0(A_89,B_90)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_257,plain,(
    ! [D_94,A_95] :
      ( ~ r2_hidden(D_94,A_95)
      | r2_hidden(D_94,k1_ordinal1(A_95)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_232])).

tff(c_264,plain,(
    ~ r2_hidden('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_257,c_168])).

tff(c_540,plain,
    ( '#skF_7' = '#skF_8'
    | r2_hidden('#skF_8','#skF_7')
    | ~ v3_ordinal1('#skF_7')
    | ~ v3_ordinal1('#skF_8') ),
    inference(resolution,[status(thm)],[c_517,c_264])).

tff(c_587,plain,
    ( '#skF_7' = '#skF_8'
    | r2_hidden('#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_122,c_540])).

tff(c_600,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_587])).

tff(c_118,plain,(
    ! [B_64,A_63] :
      ( ~ r1_tarski(B_64,A_63)
      | ~ r2_hidden(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_604,plain,(
    ~ r1_tarski('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_600,c_118])).

tff(c_607,plain,
    ( ~ r1_ordinal1('#skF_7','#skF_8')
    | ~ v3_ordinal1('#skF_8')
    | ~ v3_ordinal1('#skF_7') ),
    inference(resolution,[status(thm)],[c_114,c_604])).

tff(c_611,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_120,c_191,c_607])).

tff(c_612,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_587])).

tff(c_616,plain,(
    ~ r2_hidden('#skF_8',k1_ordinal1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_612,c_168])).

tff(c_620,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_278,c_616])).

tff(c_621,plain,(
    ~ r1_ordinal1('#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_124])).

tff(c_796,plain,
    ( r1_ordinal1('#skF_8','#skF_7')
    | ~ v3_ordinal1('#skF_7')
    | ~ v3_ordinal1('#skF_8') ),
    inference(resolution,[status(thm)],[c_793,c_621])).

tff(c_802,plain,(
    r1_ordinal1('#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_122,c_796])).

tff(c_622,plain,(
    r2_hidden('#skF_7',k1_ordinal1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_124])).

tff(c_920,plain,(
    ! [D_316,B_317,A_318] :
      ( r2_hidden(D_316,B_317)
      | r2_hidden(D_316,A_318)
      | ~ r2_hidden(D_316,k2_xboole_0(A_318,B_317)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_955,plain,(
    ! [D_339,A_340] :
      ( r2_hidden(D_339,k1_tarski(A_340))
      | r2_hidden(D_339,A_340)
      | ~ r2_hidden(D_339,k1_ordinal1(A_340)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_920])).

tff(c_722,plain,(
    ! [D_231,B_232,A_233] :
      ( D_231 = B_232
      | D_231 = A_233
      | ~ r2_hidden(D_231,k2_tarski(A_233,B_232)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_731,plain,(
    ! [D_231,A_13] :
      ( D_231 = A_13
      | D_231 = A_13
      | ~ r2_hidden(D_231,k1_tarski(A_13)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_722])).

tff(c_972,plain,(
    ! [D_341,A_342] :
      ( D_341 = A_342
      | r2_hidden(D_341,A_342)
      | ~ r2_hidden(D_341,k1_ordinal1(A_342)) ) ),
    inference(resolution,[status(thm)],[c_955,c_731])).

tff(c_985,plain,
    ( '#skF_7' = '#skF_8'
    | r2_hidden('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_622,c_972])).

tff(c_986,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_985])).

tff(c_990,plain,(
    ~ r1_tarski('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_986,c_118])).

tff(c_993,plain,
    ( ~ r1_ordinal1('#skF_8','#skF_7')
    | ~ v3_ordinal1('#skF_7')
    | ~ v3_ordinal1('#skF_8') ),
    inference(resolution,[status(thm)],[c_114,c_990])).

tff(c_997,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_122,c_802,c_993])).

tff(c_998,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_985])).

tff(c_1000,plain,(
    r1_ordinal1('#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_998,c_802])).

tff(c_1003,plain,(
    ~ r1_ordinal1('#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_998,c_621])).

tff(c_1100,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1000,c_1003])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:15:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.92/1.66  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.92/1.66  
% 3.92/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.92/1.67  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_1 > #skF_4 > #skF_7 > #skF_2 > #skF_8 > #skF_6 > #skF_3 > #skF_5
% 3.92/1.67  
% 3.92/1.67  %Foreground sorts:
% 3.92/1.67  
% 3.92/1.67  
% 3.92/1.67  %Background operators:
% 3.92/1.67  
% 3.92/1.67  
% 3.92/1.67  %Foreground operators:
% 3.92/1.67  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.92/1.67  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 3.92/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.92/1.67  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.92/1.67  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.92/1.67  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.92/1.67  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.92/1.67  tff('#skF_7', type, '#skF_7': $i).
% 3.92/1.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.92/1.67  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.92/1.67  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 3.92/1.67  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.92/1.67  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.92/1.67  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.92/1.67  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 3.92/1.67  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.92/1.67  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.92/1.67  tff('#skF_8', type, '#skF_8': $i).
% 3.92/1.67  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.92/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.92/1.67  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.92/1.67  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.92/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.92/1.67  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.92/1.67  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.92/1.67  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.92/1.67  
% 3.92/1.68  tff(f_137, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, k1_ordinal1(B)) <=> r1_ordinal1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_ordinal1)).
% 3.92/1.68  tff(f_97, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) | r1_ordinal1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', connectedness_r1_ordinal1)).
% 3.92/1.68  tff(f_45, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.92/1.68  tff(f_43, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 3.92/1.68  tff(f_99, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_ordinal1)).
% 3.92/1.68  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 3.92/1.68  tff(f_107, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 3.92/1.68  tff(f_122, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => ~((~r2_hidden(A, B) & ~(A = B)) & ~r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_ordinal1)).
% 3.92/1.68  tff(f_127, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.92/1.68  tff(c_120, plain, (v3_ordinal1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.92/1.68  tff(c_122, plain, (v3_ordinal1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.92/1.68  tff(c_793, plain, (![B_249, A_250]: (r1_ordinal1(B_249, A_250) | r1_ordinal1(A_250, B_249) | ~v3_ordinal1(B_249) | ~v3_ordinal1(A_250))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.92/1.68  tff(c_38, plain, (![A_13]: (k2_tarski(A_13, A_13)=k1_tarski(A_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.92/1.68  tff(c_140, plain, (![D_67, B_68]: (r2_hidden(D_67, k2_tarski(D_67, B_68)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.92/1.68  tff(c_143, plain, (![A_13]: (r2_hidden(A_13, k1_tarski(A_13)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_140])).
% 3.92/1.68  tff(c_110, plain, (![A_57]: (k2_xboole_0(A_57, k1_tarski(A_57))=k1_ordinal1(A_57))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.92/1.68  tff(c_221, plain, (![D_85, B_86, A_87]: (~r2_hidden(D_85, B_86) | r2_hidden(D_85, k2_xboole_0(A_87, B_86)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.92/1.68  tff(c_274, plain, (![D_101, A_102]: (~r2_hidden(D_101, k1_tarski(A_102)) | r2_hidden(D_101, k1_ordinal1(A_102)))), inference(superposition, [status(thm), theory('equality')], [c_110, c_221])).
% 3.92/1.68  tff(c_278, plain, (![A_13]: (r2_hidden(A_13, k1_ordinal1(A_13)))), inference(resolution, [status(thm)], [c_143, c_274])).
% 3.92/1.68  tff(c_124, plain, (~r1_ordinal1('#skF_7', '#skF_8') | ~r2_hidden('#skF_7', k1_ordinal1('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.92/1.68  tff(c_168, plain, (~r2_hidden('#skF_7', k1_ordinal1('#skF_8'))), inference(splitLeft, [status(thm)], [c_124])).
% 3.92/1.68  tff(c_130, plain, (r2_hidden('#skF_7', k1_ordinal1('#skF_8')) | r1_ordinal1('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.92/1.68  tff(c_191, plain, (r1_ordinal1('#skF_7', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_168, c_130])).
% 3.92/1.68  tff(c_114, plain, (![A_58, B_59]: (r1_tarski(A_58, B_59) | ~r1_ordinal1(A_58, B_59) | ~v3_ordinal1(B_59) | ~v3_ordinal1(A_58))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.92/1.68  tff(c_517, plain, (![B_205, A_206]: (r2_hidden(B_205, A_206) | B_205=A_206 | r2_hidden(A_206, B_205) | ~v3_ordinal1(B_205) | ~v3_ordinal1(A_206))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.92/1.68  tff(c_232, plain, (![D_88, A_89, B_90]: (~r2_hidden(D_88, A_89) | r2_hidden(D_88, k2_xboole_0(A_89, B_90)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.92/1.68  tff(c_257, plain, (![D_94, A_95]: (~r2_hidden(D_94, A_95) | r2_hidden(D_94, k1_ordinal1(A_95)))), inference(superposition, [status(thm), theory('equality')], [c_110, c_232])).
% 3.92/1.68  tff(c_264, plain, (~r2_hidden('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_257, c_168])).
% 3.92/1.68  tff(c_540, plain, ('#skF_7'='#skF_8' | r2_hidden('#skF_8', '#skF_7') | ~v3_ordinal1('#skF_7') | ~v3_ordinal1('#skF_8')), inference(resolution, [status(thm)], [c_517, c_264])).
% 3.92/1.68  tff(c_587, plain, ('#skF_7'='#skF_8' | r2_hidden('#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_120, c_122, c_540])).
% 3.92/1.68  tff(c_600, plain, (r2_hidden('#skF_8', '#skF_7')), inference(splitLeft, [status(thm)], [c_587])).
% 3.92/1.68  tff(c_118, plain, (![B_64, A_63]: (~r1_tarski(B_64, A_63) | ~r2_hidden(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.92/1.68  tff(c_604, plain, (~r1_tarski('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_600, c_118])).
% 3.92/1.68  tff(c_607, plain, (~r1_ordinal1('#skF_7', '#skF_8') | ~v3_ordinal1('#skF_8') | ~v3_ordinal1('#skF_7')), inference(resolution, [status(thm)], [c_114, c_604])).
% 3.92/1.68  tff(c_611, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_122, c_120, c_191, c_607])).
% 3.92/1.68  tff(c_612, plain, ('#skF_7'='#skF_8'), inference(splitRight, [status(thm)], [c_587])).
% 3.92/1.68  tff(c_616, plain, (~r2_hidden('#skF_8', k1_ordinal1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_612, c_168])).
% 3.92/1.68  tff(c_620, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_278, c_616])).
% 3.92/1.68  tff(c_621, plain, (~r1_ordinal1('#skF_7', '#skF_8')), inference(splitRight, [status(thm)], [c_124])).
% 3.92/1.68  tff(c_796, plain, (r1_ordinal1('#skF_8', '#skF_7') | ~v3_ordinal1('#skF_7') | ~v3_ordinal1('#skF_8')), inference(resolution, [status(thm)], [c_793, c_621])).
% 3.92/1.68  tff(c_802, plain, (r1_ordinal1('#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_120, c_122, c_796])).
% 3.92/1.68  tff(c_622, plain, (r2_hidden('#skF_7', k1_ordinal1('#skF_8'))), inference(splitRight, [status(thm)], [c_124])).
% 3.92/1.68  tff(c_920, plain, (![D_316, B_317, A_318]: (r2_hidden(D_316, B_317) | r2_hidden(D_316, A_318) | ~r2_hidden(D_316, k2_xboole_0(A_318, B_317)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.92/1.68  tff(c_955, plain, (![D_339, A_340]: (r2_hidden(D_339, k1_tarski(A_340)) | r2_hidden(D_339, A_340) | ~r2_hidden(D_339, k1_ordinal1(A_340)))), inference(superposition, [status(thm), theory('equality')], [c_110, c_920])).
% 3.92/1.68  tff(c_722, plain, (![D_231, B_232, A_233]: (D_231=B_232 | D_231=A_233 | ~r2_hidden(D_231, k2_tarski(A_233, B_232)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.92/1.68  tff(c_731, plain, (![D_231, A_13]: (D_231=A_13 | D_231=A_13 | ~r2_hidden(D_231, k1_tarski(A_13)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_722])).
% 3.92/1.68  tff(c_972, plain, (![D_341, A_342]: (D_341=A_342 | r2_hidden(D_341, A_342) | ~r2_hidden(D_341, k1_ordinal1(A_342)))), inference(resolution, [status(thm)], [c_955, c_731])).
% 3.92/1.68  tff(c_985, plain, ('#skF_7'='#skF_8' | r2_hidden('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_622, c_972])).
% 3.92/1.68  tff(c_986, plain, (r2_hidden('#skF_7', '#skF_8')), inference(splitLeft, [status(thm)], [c_985])).
% 3.92/1.68  tff(c_990, plain, (~r1_tarski('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_986, c_118])).
% 3.92/1.68  tff(c_993, plain, (~r1_ordinal1('#skF_8', '#skF_7') | ~v3_ordinal1('#skF_7') | ~v3_ordinal1('#skF_8')), inference(resolution, [status(thm)], [c_114, c_990])).
% 3.92/1.68  tff(c_997, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_120, c_122, c_802, c_993])).
% 3.92/1.68  tff(c_998, plain, ('#skF_7'='#skF_8'), inference(splitRight, [status(thm)], [c_985])).
% 3.92/1.68  tff(c_1000, plain, (r1_ordinal1('#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_998, c_802])).
% 3.92/1.68  tff(c_1003, plain, (~r1_ordinal1('#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_998, c_621])).
% 3.92/1.68  tff(c_1100, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1000, c_1003])).
% 3.92/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.92/1.68  
% 3.92/1.68  Inference rules
% 3.92/1.68  ----------------------
% 3.92/1.68  #Ref     : 0
% 3.92/1.68  #Sup     : 187
% 3.92/1.68  #Fact    : 8
% 3.92/1.68  #Define  : 0
% 3.92/1.68  #Split   : 4
% 3.92/1.68  #Chain   : 0
% 3.92/1.68  #Close   : 0
% 3.92/1.68  
% 3.92/1.68  Ordering : KBO
% 3.92/1.68  
% 3.92/1.68  Simplification rules
% 3.92/1.68  ----------------------
% 3.92/1.68  #Subsume      : 26
% 3.92/1.68  #Demod        : 32
% 3.92/1.68  #Tautology    : 61
% 3.92/1.68  #SimpNegUnit  : 2
% 3.92/1.68  #BackRed      : 9
% 3.92/1.68  
% 3.92/1.68  #Partial instantiations: 0
% 3.92/1.68  #Strategies tried      : 1
% 3.92/1.68  
% 3.92/1.68  Timing (in seconds)
% 3.92/1.68  ----------------------
% 3.92/1.68  Preprocessing        : 0.38
% 3.92/1.68  Parsing              : 0.18
% 3.92/1.68  CNF conversion       : 0.03
% 3.92/1.68  Main loop            : 0.47
% 3.92/1.68  Inferencing          : 0.15
% 3.92/1.68  Reduction            : 0.13
% 3.92/1.68  Demodulation         : 0.09
% 3.92/1.68  BG Simplification    : 0.03
% 3.92/1.68  Subsumption          : 0.12
% 3.92/1.68  Abstraction          : 0.04
% 3.92/1.68  MUC search           : 0.00
% 3.92/1.68  Cooper               : 0.00
% 3.92/1.68  Total                : 0.89
% 3.92/1.68  Index Insertion      : 0.00
% 3.92/1.68  Index Deletion       : 0.00
% 3.92/1.68  Index Matching       : 0.00
% 3.92/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
