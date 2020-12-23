%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:11 EST 2020

% Result     : Theorem 5.29s
% Output     : CNFRefutation 5.29s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 104 expanded)
%              Number of leaves         :   19 (  40 expanded)
%              Depth                    :    9
%              Number of atoms          :   96 ( 223 expanded)
%              Number of equality atoms :    7 (  14 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > #nlpp > k1_ordinal1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_81,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,B)
            <=> r1_ordinal1(k1_ordinal1(A),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_ordinal1)).

tff(f_66,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v3_ordinal1(k1_ordinal1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r2_hidden(A,k1_ordinal1(B))
    <=> ( r2_hidden(A,B)
        | A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(f_62,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r1_ordinal1(A,B)
            | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

tff(f_71,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_2458,plain,(
    ! [A_199,B_200] :
      ( r2_hidden('#skF_1'(A_199,B_200),A_199)
      | r1_tarski(A_199,B_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2468,plain,(
    ! [A_199] : r1_tarski(A_199,A_199) ),
    inference(resolution,[status(thm)],[c_2458,c_6])).

tff(c_30,plain,(
    v3_ordinal1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_24,plain,(
    ! [A_16] :
      ( v3_ordinal1(k1_ordinal1(A_16))
      | ~ v3_ordinal1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_38,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | r1_ordinal1(k1_ordinal1('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_66,plain,(
    r1_ordinal1(k1_ordinal1('#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_32,plain,
    ( ~ r1_ordinal1(k1_ordinal1('#skF_2'),'#skF_3')
    | ~ r2_hidden('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_80,plain,(
    ~ r2_hidden('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_32])).

tff(c_28,plain,(
    v3_ordinal1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_190,plain,(
    ! [A_59,B_60] :
      ( r1_tarski(A_59,B_60)
      | ~ r1_ordinal1(A_59,B_60)
      | ~ v3_ordinal1(B_60)
      | ~ v3_ordinal1(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_18,plain,(
    ! [B_12] : r2_hidden(B_12,k1_ordinal1(B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_118,plain,(
    ! [C_41,B_42,A_43] :
      ( r2_hidden(C_41,B_42)
      | ~ r2_hidden(C_41,A_43)
      | ~ r1_tarski(A_43,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_127,plain,(
    ! [B_12,B_42] :
      ( r2_hidden(B_12,B_42)
      | ~ r1_tarski(k1_ordinal1(B_12),B_42) ) ),
    inference(resolution,[status(thm)],[c_18,c_118])).

tff(c_2354,plain,(
    ! [B_188,B_189] :
      ( r2_hidden(B_188,B_189)
      | ~ r1_ordinal1(k1_ordinal1(B_188),B_189)
      | ~ v3_ordinal1(B_189)
      | ~ v3_ordinal1(k1_ordinal1(B_188)) ) ),
    inference(resolution,[status(thm)],[c_190,c_127])).

tff(c_2388,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_66,c_2354])).

tff(c_2402,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_2388])).

tff(c_2403,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_2402])).

tff(c_2406,plain,(
    ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_2403])).

tff(c_2410,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_2406])).

tff(c_2411,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_2419,plain,(
    ~ r2_hidden('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_2411,c_2])).

tff(c_2583,plain,(
    ! [B_225,A_226] :
      ( r2_hidden(B_225,A_226)
      | r1_ordinal1(A_226,B_225)
      | ~ v3_ordinal1(B_225)
      | ~ v3_ordinal1(A_226) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_16,plain,(
    ! [B_12,A_11] :
      ( B_12 = A_11
      | r2_hidden(A_11,B_12)
      | ~ r2_hidden(A_11,k1_ordinal1(B_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_3640,plain,(
    ! [B_298,B_297] :
      ( B_298 = B_297
      | r2_hidden(B_297,B_298)
      | r1_ordinal1(k1_ordinal1(B_298),B_297)
      | ~ v3_ordinal1(B_297)
      | ~ v3_ordinal1(k1_ordinal1(B_298)) ) ),
    inference(resolution,[status(thm)],[c_2583,c_16])).

tff(c_2421,plain,(
    ~ r1_ordinal1(k1_ordinal1('#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2411,c_32])).

tff(c_3653,plain,
    ( '#skF_2' = '#skF_3'
    | r2_hidden('#skF_3','#skF_2')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_3640,c_2421])).

tff(c_3664,plain,
    ( '#skF_2' = '#skF_3'
    | r2_hidden('#skF_3','#skF_2')
    | ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_3653])).

tff(c_3665,plain,
    ( '#skF_2' = '#skF_3'
    | ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_2419,c_3664])).

tff(c_3666,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_3665])).

tff(c_3669,plain,(
    ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_3666])).

tff(c_3673,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_3669])).

tff(c_3674,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3665])).

tff(c_26,plain,(
    ! [B_18,A_17] :
      ( ~ r1_tarski(B_18,A_17)
      | ~ r2_hidden(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2418,plain,(
    ~ r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_2411,c_26])).

tff(c_3708,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3674,c_2418])).

tff(c_3713,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2468,c_3708])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:36:39 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.29/1.93  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.29/1.93  
% 5.29/1.93  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.29/1.94  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > #nlpp > k1_ordinal1 > #skF_2 > #skF_3 > #skF_1
% 5.29/1.94  
% 5.29/1.94  %Foreground sorts:
% 5.29/1.94  
% 5.29/1.94  
% 5.29/1.94  %Background operators:
% 5.29/1.94  
% 5.29/1.94  
% 5.29/1.94  %Foreground operators:
% 5.29/1.94  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 5.29/1.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.29/1.94  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.29/1.94  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.29/1.94  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 5.29/1.94  tff('#skF_2', type, '#skF_2': $i).
% 5.29/1.94  tff('#skF_3', type, '#skF_3': $i).
% 5.29/1.94  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 5.29/1.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.29/1.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.29/1.94  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.29/1.94  
% 5.29/1.95  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.29/1.95  tff(f_81, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, B) <=> r1_ordinal1(k1_ordinal1(A), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_ordinal1)).
% 5.29/1.95  tff(f_66, axiom, (![A]: (v3_ordinal1(A) => v3_ordinal1(k1_ordinal1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_ordinal1)).
% 5.29/1.95  tff(f_45, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 5.29/1.95  tff(f_53, axiom, (![A, B]: (r2_hidden(A, k1_ordinal1(B)) <=> (r2_hidden(A, B) | (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_ordinal1)).
% 5.29/1.95  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 5.29/1.95  tff(f_62, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_ordinal1)).
% 5.29/1.95  tff(f_71, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 5.29/1.95  tff(c_2458, plain, (![A_199, B_200]: (r2_hidden('#skF_1'(A_199, B_200), A_199) | r1_tarski(A_199, B_200))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.29/1.95  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.29/1.95  tff(c_2468, plain, (![A_199]: (r1_tarski(A_199, A_199))), inference(resolution, [status(thm)], [c_2458, c_6])).
% 5.29/1.95  tff(c_30, plain, (v3_ordinal1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.29/1.95  tff(c_24, plain, (![A_16]: (v3_ordinal1(k1_ordinal1(A_16)) | ~v3_ordinal1(A_16))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.29/1.95  tff(c_38, plain, (r2_hidden('#skF_2', '#skF_3') | r1_ordinal1(k1_ordinal1('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.29/1.95  tff(c_66, plain, (r1_ordinal1(k1_ordinal1('#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_38])).
% 5.29/1.95  tff(c_32, plain, (~r1_ordinal1(k1_ordinal1('#skF_2'), '#skF_3') | ~r2_hidden('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.29/1.95  tff(c_80, plain, (~r2_hidden('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_32])).
% 5.29/1.95  tff(c_28, plain, (v3_ordinal1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.29/1.95  tff(c_190, plain, (![A_59, B_60]: (r1_tarski(A_59, B_60) | ~r1_ordinal1(A_59, B_60) | ~v3_ordinal1(B_60) | ~v3_ordinal1(A_59))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.29/1.95  tff(c_18, plain, (![B_12]: (r2_hidden(B_12, k1_ordinal1(B_12)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.29/1.95  tff(c_118, plain, (![C_41, B_42, A_43]: (r2_hidden(C_41, B_42) | ~r2_hidden(C_41, A_43) | ~r1_tarski(A_43, B_42))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.29/1.95  tff(c_127, plain, (![B_12, B_42]: (r2_hidden(B_12, B_42) | ~r1_tarski(k1_ordinal1(B_12), B_42))), inference(resolution, [status(thm)], [c_18, c_118])).
% 5.29/1.95  tff(c_2354, plain, (![B_188, B_189]: (r2_hidden(B_188, B_189) | ~r1_ordinal1(k1_ordinal1(B_188), B_189) | ~v3_ordinal1(B_189) | ~v3_ordinal1(k1_ordinal1(B_188)))), inference(resolution, [status(thm)], [c_190, c_127])).
% 5.29/1.95  tff(c_2388, plain, (r2_hidden('#skF_2', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(resolution, [status(thm)], [c_66, c_2354])).
% 5.29/1.95  tff(c_2402, plain, (r2_hidden('#skF_2', '#skF_3') | ~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_2388])).
% 5.29/1.95  tff(c_2403, plain, (~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_80, c_2402])).
% 5.29/1.95  tff(c_2406, plain, (~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_24, c_2403])).
% 5.29/1.95  tff(c_2410, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_2406])).
% 5.29/1.95  tff(c_2411, plain, (r2_hidden('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_38])).
% 5.29/1.95  tff(c_2, plain, (![B_2, A_1]: (~r2_hidden(B_2, A_1) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 5.29/1.95  tff(c_2419, plain, (~r2_hidden('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_2411, c_2])).
% 5.29/1.95  tff(c_2583, plain, (![B_225, A_226]: (r2_hidden(B_225, A_226) | r1_ordinal1(A_226, B_225) | ~v3_ordinal1(B_225) | ~v3_ordinal1(A_226))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.29/1.95  tff(c_16, plain, (![B_12, A_11]: (B_12=A_11 | r2_hidden(A_11, B_12) | ~r2_hidden(A_11, k1_ordinal1(B_12)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.29/1.95  tff(c_3640, plain, (![B_298, B_297]: (B_298=B_297 | r2_hidden(B_297, B_298) | r1_ordinal1(k1_ordinal1(B_298), B_297) | ~v3_ordinal1(B_297) | ~v3_ordinal1(k1_ordinal1(B_298)))), inference(resolution, [status(thm)], [c_2583, c_16])).
% 5.29/1.95  tff(c_2421, plain, (~r1_ordinal1(k1_ordinal1('#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2411, c_32])).
% 5.29/1.95  tff(c_3653, plain, ('#skF_2'='#skF_3' | r2_hidden('#skF_3', '#skF_2') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(resolution, [status(thm)], [c_3640, c_2421])).
% 5.29/1.95  tff(c_3664, plain, ('#skF_2'='#skF_3' | r2_hidden('#skF_3', '#skF_2') | ~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_3653])).
% 5.29/1.95  tff(c_3665, plain, ('#skF_2'='#skF_3' | ~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_2419, c_3664])).
% 5.29/1.95  tff(c_3666, plain, (~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(splitLeft, [status(thm)], [c_3665])).
% 5.29/1.95  tff(c_3669, plain, (~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_24, c_3666])).
% 5.29/1.95  tff(c_3673, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_3669])).
% 5.29/1.95  tff(c_3674, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_3665])).
% 5.29/1.95  tff(c_26, plain, (![B_18, A_17]: (~r1_tarski(B_18, A_17) | ~r2_hidden(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.29/1.95  tff(c_2418, plain, (~r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_2411, c_26])).
% 5.29/1.95  tff(c_3708, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3674, c_2418])).
% 5.29/1.95  tff(c_3713, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2468, c_3708])).
% 5.29/1.95  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.29/1.95  
% 5.29/1.95  Inference rules
% 5.29/1.95  ----------------------
% 5.29/1.95  #Ref     : 0
% 5.29/1.95  #Sup     : 738
% 5.29/1.95  #Fact    : 2
% 5.29/1.95  #Define  : 0
% 5.29/1.95  #Split   : 3
% 5.29/1.95  #Chain   : 0
% 5.29/1.95  #Close   : 0
% 5.29/1.95  
% 5.29/1.95  Ordering : KBO
% 5.29/1.95  
% 5.29/1.95  Simplification rules
% 5.29/1.95  ----------------------
% 5.29/1.95  #Subsume      : 235
% 5.29/1.95  #Demod        : 117
% 5.29/1.95  #Tautology    : 43
% 5.29/1.95  #SimpNegUnit  : 14
% 5.29/1.95  #BackRed      : 34
% 5.29/1.95  
% 5.29/1.95  #Partial instantiations: 0
% 5.29/1.95  #Strategies tried      : 1
% 5.29/1.95  
% 5.29/1.95  Timing (in seconds)
% 5.29/1.95  ----------------------
% 5.29/1.95  Preprocessing        : 0.30
% 5.29/1.95  Parsing              : 0.17
% 5.29/1.95  CNF conversion       : 0.02
% 5.29/1.95  Main loop            : 0.86
% 5.29/1.95  Inferencing          : 0.29
% 5.29/1.95  Reduction            : 0.22
% 5.29/1.95  Demodulation         : 0.15
% 5.29/1.95  BG Simplification    : 0.03
% 5.29/1.95  Subsumption          : 0.26
% 5.29/1.95  Abstraction          : 0.04
% 5.29/1.95  MUC search           : 0.00
% 5.29/1.95  Cooper               : 0.00
% 5.29/1.95  Total                : 1.19
% 5.29/1.95  Index Insertion      : 0.00
% 5.29/1.95  Index Deletion       : 0.00
% 5.29/1.95  Index Matching       : 0.00
% 5.29/1.95  BG Taut test         : 0.00
%------------------------------------------------------------------------------
