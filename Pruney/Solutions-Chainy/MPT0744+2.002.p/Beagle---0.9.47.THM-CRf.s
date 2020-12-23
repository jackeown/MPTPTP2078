%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:15 EST 2020

% Result     : Theorem 2.76s
% Output     : CNFRefutation 2.90s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 140 expanded)
%              Number of leaves         :   23 (  54 expanded)
%              Depth                    :    8
%              Number of atoms          :  107 ( 299 expanded)
%              Number of equality atoms :   10 (  28 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_2 > #skF_1

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

tff(v1_ordinal1,type,(
    v1_ordinal1: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(v2_ordinal1,type,(
    v2_ordinal1: $i > $o )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_69,axiom,(
    ! [A,B] :
      ( r2_hidden(A,k1_ordinal1(B))
    <=> ( r2_hidden(A,B)
        | A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).

tff(f_97,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,k1_ordinal1(B))
            <=> r1_ordinal1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_43,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( v1_ordinal1(A)
        & v2_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_78,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_xboole_0(A,B)
           => r2_hidden(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_ordinal1)).

tff(f_87,axiom,(
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

tff(c_26,plain,(
    ! [B_13] : r2_hidden(B_13,k1_ordinal1(B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_36,plain,(
    v3_ordinal1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_34,plain,(
    v3_ordinal1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_38,plain,
    ( ~ r1_ordinal1('#skF_1','#skF_2')
    | ~ r2_hidden('#skF_1',k1_ordinal1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_66,plain,(
    ~ r2_hidden('#skF_1',k1_ordinal1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_44,plain,
    ( r2_hidden('#skF_1',k1_ordinal1('#skF_2'))
    | r1_ordinal1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_82,plain,(
    r1_ordinal1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_44])).

tff(c_20,plain,(
    ! [A_9,B_10] :
      ( r1_tarski(A_9,B_10)
      | ~ r1_ordinal1(A_9,B_10)
      | ~ v3_ordinal1(B_10)
      | ~ v3_ordinal1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_48,plain,(
    ! [A_23] :
      ( v1_ordinal1(A_23)
      | ~ v3_ordinal1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_56,plain,(
    v1_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_48])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( r2_xboole_0(A_3,B_4)
      | B_4 = A_3
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_178,plain,(
    ! [A_48,B_49] :
      ( r2_hidden(A_48,B_49)
      | ~ r2_xboole_0(A_48,B_49)
      | ~ v3_ordinal1(B_49)
      | ~ v1_ordinal1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_326,plain,(
    ! [A_68,B_69] :
      ( r2_hidden(A_68,B_69)
      | ~ v3_ordinal1(B_69)
      | ~ v1_ordinal1(A_68)
      | B_69 = A_68
      | ~ r1_tarski(A_68,B_69) ) ),
    inference(resolution,[status(thm)],[c_4,c_178])).

tff(c_83,plain,(
    ! [A_31,B_32] :
      ( ~ r2_hidden(A_31,B_32)
      | r2_hidden(A_31,k1_ordinal1(B_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_95,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_83,c_66])).

tff(c_378,plain,
    ( ~ v3_ordinal1('#skF_2')
    | ~ v1_ordinal1('#skF_1')
    | '#skF_2' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_326,c_95])).

tff(c_403,plain,
    ( '#skF_2' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_34,c_378])).

tff(c_409,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_403])).

tff(c_412,plain,
    ( ~ r1_ordinal1('#skF_1','#skF_2')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_409])).

tff(c_416,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_82,c_412])).

tff(c_417,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_403])).

tff(c_423,plain,(
    ~ r2_hidden('#skF_1',k1_ordinal1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_417,c_66])).

tff(c_429,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_423])).

tff(c_430,plain,(
    ~ r1_ordinal1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_432,plain,(
    r1_ordinal1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_433,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_430,c_432])).

tff(c_435,plain,(
    ~ r1_ordinal1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_537,plain,(
    ! [B_90,A_91] :
      ( r2_hidden(B_90,A_91)
      | r1_ordinal1(A_91,B_90)
      | ~ v3_ordinal1(B_90)
      | ~ v3_ordinal1(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_431,plain,(
    r2_hidden('#skF_1',k1_ordinal1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_504,plain,(
    ! [B_85,A_86] :
      ( B_85 = A_86
      | r2_hidden(A_86,B_85)
      | ~ r2_hidden(A_86,k1_ordinal1(B_85)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_515,plain,
    ( '#skF_2' = '#skF_1'
    | r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_431,c_504])).

tff(c_518,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_515])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_521,plain,(
    ~ r2_hidden('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_518,c_2])).

tff(c_547,plain,
    ( r1_ordinal1('#skF_1','#skF_2')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_537,c_521])).

tff(c_581,plain,(
    r1_ordinal1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_547])).

tff(c_583,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_435,c_581])).

tff(c_584,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_515])).

tff(c_588,plain,(
    ~ r1_ordinal1('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_584,c_435])).

tff(c_601,plain,(
    ! [B_92,A_93] :
      ( r2_hidden(B_92,A_93)
      | r1_ordinal1(A_93,B_92)
      | ~ v3_ordinal1(B_92)
      | ~ v3_ordinal1(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_585,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_515])).

tff(c_600,plain,(
    ~ r2_hidden('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_584,c_585])).

tff(c_604,plain,
    ( r1_ordinal1('#skF_1','#skF_1')
    | ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_601,c_600])).

tff(c_633,plain,(
    r1_ordinal1('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_604])).

tff(c_635,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_588,c_633])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:49:44 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.76/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.90/1.39  
% 2.90/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.90/1.39  %$ r2_xboole_0 > r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_2 > #skF_1
% 2.90/1.39  
% 2.90/1.39  %Foreground sorts:
% 2.90/1.39  
% 2.90/1.39  
% 2.90/1.39  %Background operators:
% 2.90/1.39  
% 2.90/1.39  
% 2.90/1.39  %Foreground operators:
% 2.90/1.39  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 2.90/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.90/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.90/1.39  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.90/1.39  tff(v1_ordinal1, type, v1_ordinal1: $i > $o).
% 2.90/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.90/1.39  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 2.90/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.90/1.39  tff('#skF_1', type, '#skF_1': $i).
% 2.90/1.39  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 2.90/1.39  tff(v2_ordinal1, type, v2_ordinal1: $i > $o).
% 2.90/1.39  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.90/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.90/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.90/1.39  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.90/1.39  
% 2.90/1.40  tff(f_69, axiom, (![A, B]: (r2_hidden(A, k1_ordinal1(B)) <=> (r2_hidden(A, B) | (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_ordinal1)).
% 2.90/1.40  tff(f_97, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, k1_ordinal1(B)) <=> r1_ordinal1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_ordinal1)).
% 2.90/1.40  tff(f_61, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 2.90/1.40  tff(f_43, axiom, (![A]: (v3_ordinal1(A) => (v1_ordinal1(A) & v2_ordinal1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_ordinal1)).
% 2.90/1.40  tff(f_37, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.90/1.40  tff(f_78, axiom, (![A]: (v1_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_xboole_0(A, B) => r2_hidden(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_ordinal1)).
% 2.90/1.40  tff(f_87, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_ordinal1)).
% 2.90/1.40  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 2.90/1.40  tff(c_26, plain, (![B_13]: (r2_hidden(B_13, k1_ordinal1(B_13)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.90/1.40  tff(c_36, plain, (v3_ordinal1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.90/1.40  tff(c_34, plain, (v3_ordinal1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.90/1.40  tff(c_38, plain, (~r1_ordinal1('#skF_1', '#skF_2') | ~r2_hidden('#skF_1', k1_ordinal1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.90/1.40  tff(c_66, plain, (~r2_hidden('#skF_1', k1_ordinal1('#skF_2'))), inference(splitLeft, [status(thm)], [c_38])).
% 2.90/1.40  tff(c_44, plain, (r2_hidden('#skF_1', k1_ordinal1('#skF_2')) | r1_ordinal1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.90/1.40  tff(c_82, plain, (r1_ordinal1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_66, c_44])).
% 2.90/1.40  tff(c_20, plain, (![A_9, B_10]: (r1_tarski(A_9, B_10) | ~r1_ordinal1(A_9, B_10) | ~v3_ordinal1(B_10) | ~v3_ordinal1(A_9))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.90/1.40  tff(c_48, plain, (![A_23]: (v1_ordinal1(A_23) | ~v3_ordinal1(A_23))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.90/1.40  tff(c_56, plain, (v1_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_36, c_48])).
% 2.90/1.40  tff(c_4, plain, (![A_3, B_4]: (r2_xboole_0(A_3, B_4) | B_4=A_3 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.90/1.40  tff(c_178, plain, (![A_48, B_49]: (r2_hidden(A_48, B_49) | ~r2_xboole_0(A_48, B_49) | ~v3_ordinal1(B_49) | ~v1_ordinal1(A_48))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.90/1.40  tff(c_326, plain, (![A_68, B_69]: (r2_hidden(A_68, B_69) | ~v3_ordinal1(B_69) | ~v1_ordinal1(A_68) | B_69=A_68 | ~r1_tarski(A_68, B_69))), inference(resolution, [status(thm)], [c_4, c_178])).
% 2.90/1.40  tff(c_83, plain, (![A_31, B_32]: (~r2_hidden(A_31, B_32) | r2_hidden(A_31, k1_ordinal1(B_32)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.90/1.40  tff(c_95, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_83, c_66])).
% 2.90/1.40  tff(c_378, plain, (~v3_ordinal1('#skF_2') | ~v1_ordinal1('#skF_1') | '#skF_2'='#skF_1' | ~r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_326, c_95])).
% 2.90/1.40  tff(c_403, plain, ('#skF_2'='#skF_1' | ~r1_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_34, c_378])).
% 2.90/1.40  tff(c_409, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_403])).
% 2.90/1.40  tff(c_412, plain, (~r1_ordinal1('#skF_1', '#skF_2') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_20, c_409])).
% 2.90/1.40  tff(c_416, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_82, c_412])).
% 2.90/1.40  tff(c_417, plain, ('#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_403])).
% 2.90/1.40  tff(c_423, plain, (~r2_hidden('#skF_1', k1_ordinal1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_417, c_66])).
% 2.90/1.40  tff(c_429, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_423])).
% 2.90/1.40  tff(c_430, plain, (~r1_ordinal1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_38])).
% 2.90/1.40  tff(c_432, plain, (r1_ordinal1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_44])).
% 2.90/1.40  tff(c_433, plain, $false, inference(negUnitSimplification, [status(thm)], [c_430, c_432])).
% 2.90/1.40  tff(c_435, plain, (~r1_ordinal1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_44])).
% 2.90/1.40  tff(c_537, plain, (![B_90, A_91]: (r2_hidden(B_90, A_91) | r1_ordinal1(A_91, B_90) | ~v3_ordinal1(B_90) | ~v3_ordinal1(A_91))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.90/1.40  tff(c_431, plain, (r2_hidden('#skF_1', k1_ordinal1('#skF_2'))), inference(splitRight, [status(thm)], [c_38])).
% 2.90/1.40  tff(c_504, plain, (![B_85, A_86]: (B_85=A_86 | r2_hidden(A_86, B_85) | ~r2_hidden(A_86, k1_ordinal1(B_85)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.90/1.40  tff(c_515, plain, ('#skF_2'='#skF_1' | r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_431, c_504])).
% 2.90/1.40  tff(c_518, plain, (r2_hidden('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_515])).
% 2.90/1.40  tff(c_2, plain, (![B_2, A_1]: (~r2_hidden(B_2, A_1) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.90/1.40  tff(c_521, plain, (~r2_hidden('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_518, c_2])).
% 2.90/1.40  tff(c_547, plain, (r1_ordinal1('#skF_1', '#skF_2') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_537, c_521])).
% 2.90/1.40  tff(c_581, plain, (r1_ordinal1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_547])).
% 2.90/1.40  tff(c_583, plain, $false, inference(negUnitSimplification, [status(thm)], [c_435, c_581])).
% 2.90/1.40  tff(c_584, plain, ('#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_515])).
% 2.90/1.40  tff(c_588, plain, (~r1_ordinal1('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_584, c_435])).
% 2.90/1.40  tff(c_601, plain, (![B_92, A_93]: (r2_hidden(B_92, A_93) | r1_ordinal1(A_93, B_92) | ~v3_ordinal1(B_92) | ~v3_ordinal1(A_93))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.90/1.40  tff(c_585, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_515])).
% 2.90/1.40  tff(c_600, plain, (~r2_hidden('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_584, c_585])).
% 2.90/1.40  tff(c_604, plain, (r1_ordinal1('#skF_1', '#skF_1') | ~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_601, c_600])).
% 2.90/1.40  tff(c_633, plain, (r1_ordinal1('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_604])).
% 2.90/1.40  tff(c_635, plain, $false, inference(negUnitSimplification, [status(thm)], [c_588, c_633])).
% 2.90/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.90/1.40  
% 2.90/1.40  Inference rules
% 2.90/1.40  ----------------------
% 2.90/1.40  #Ref     : 0
% 2.90/1.40  #Sup     : 110
% 2.90/1.40  #Fact    : 2
% 2.90/1.40  #Define  : 0
% 2.90/1.40  #Split   : 5
% 2.90/1.40  #Chain   : 0
% 2.90/1.40  #Close   : 0
% 2.90/1.40  
% 2.90/1.40  Ordering : KBO
% 2.90/1.40  
% 2.90/1.40  Simplification rules
% 2.90/1.40  ----------------------
% 2.90/1.40  #Subsume      : 14
% 2.90/1.40  #Demod        : 34
% 2.90/1.40  #Tautology    : 23
% 2.90/1.40  #SimpNegUnit  : 4
% 2.90/1.40  #BackRed      : 14
% 2.90/1.40  
% 2.90/1.40  #Partial instantiations: 0
% 2.90/1.40  #Strategies tried      : 1
% 2.90/1.40  
% 2.90/1.40  Timing (in seconds)
% 2.90/1.40  ----------------------
% 2.90/1.40  Preprocessing        : 0.28
% 2.90/1.40  Parsing              : 0.15
% 2.90/1.41  CNF conversion       : 0.02
% 2.90/1.41  Main loop            : 0.30
% 2.90/1.41  Inferencing          : 0.12
% 2.90/1.41  Reduction            : 0.07
% 2.90/1.41  Demodulation         : 0.05
% 2.90/1.41  BG Simplification    : 0.02
% 2.90/1.41  Subsumption          : 0.07
% 2.90/1.41  Abstraction          : 0.01
% 2.90/1.41  MUC search           : 0.00
% 2.90/1.41  Cooper               : 0.00
% 2.90/1.41  Total                : 0.61
% 2.90/1.41  Index Insertion      : 0.00
% 2.90/1.41  Index Deletion       : 0.00
% 2.90/1.41  Index Matching       : 0.00
% 2.90/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
