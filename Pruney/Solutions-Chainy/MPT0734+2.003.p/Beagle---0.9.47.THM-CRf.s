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
% DateTime   : Thu Dec  3 10:06:03 EST 2020

% Result     : Theorem 2.52s
% Output     : CNFRefutation 2.52s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 259 expanded)
%              Number of leaves         :   22 (  95 expanded)
%              Depth                    :   13
%              Number of atoms          :  106 ( 712 expanded)
%              Number of equality atoms :    9 (  42 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_xboole_0 > r2_xboole_0 > r2_hidden > r1_tarski > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > #nlpp > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_ordinal1,type,(
    v1_ordinal1: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(v2_ordinal1,type,(
    v2_ordinal1: $i > $o )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(r3_xboole_0,type,(
    r3_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_91,negated_conjecture,(
    ~ ! [A] :
        ( v1_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ! [C] :
                ( v3_ordinal1(C)
               => ( ( r1_tarski(A,B)
                    & r2_hidden(B,C) )
                 => r2_hidden(A,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_ordinal1)).

tff(f_60,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( v1_ordinal1(A)
        & v2_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
    <=> ! [B] :
          ( r2_hidden(B,A)
         => r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_ordinal1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r3_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        | r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ~ ( ~ r2_xboole_0(A,B)
          & A != B
          & ~ r2_xboole_0(B,A) )
    <=> r3_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_xboole_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r2_xboole_0(B,C) )
     => r2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_xboole_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_xboole_0(A,B)
           => r2_hidden(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_ordinal1)).

tff(c_32,plain,(
    ~ r2_hidden('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_42,plain,(
    v1_ordinal1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_38,plain,(
    v3_ordinal1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_40,plain,(
    v3_ordinal1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_53,plain,(
    ! [A_24] :
      ( v1_ordinal1(A_24)
      | ~ v3_ordinal1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_61,plain,(
    v1_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_53])).

tff(c_60,plain,(
    v1_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_53])).

tff(c_34,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_76,plain,(
    ! [B_38,A_39] :
      ( r1_tarski(B_38,A_39)
      | ~ r2_hidden(B_38,A_39)
      | ~ v1_ordinal1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_82,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | ~ v1_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_76])).

tff(c_86,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_82])).

tff(c_36,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( ~ r1_tarski(A_3,B_4)
      | r3_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_113,plain,(
    ! [B_52,A_53] :
      ( r2_xboole_0(B_52,A_53)
      | B_52 = A_53
      | r2_xboole_0(A_53,B_52)
      | ~ r3_xboole_0(A_53,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_155,plain,(
    ! [B_54,A_55] :
      ( r2_xboole_0(B_54,A_55)
      | B_54 = A_55
      | r2_xboole_0(A_55,B_54)
      | ~ r1_tarski(A_55,B_54) ) ),
    inference(resolution,[status(thm)],[c_8,c_113])).

tff(c_18,plain,(
    ! [A_7,C_9,B_8] :
      ( r2_xboole_0(A_7,C_9)
      | ~ r2_xboole_0(B_8,C_9)
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_237,plain,(
    ! [A_58,B_59,A_60] :
      ( r2_xboole_0(A_58,B_59)
      | ~ r1_tarski(A_58,A_60)
      | r2_xboole_0(B_59,A_60)
      | B_59 = A_60
      | ~ r1_tarski(A_60,B_59) ) ),
    inference(resolution,[status(thm)],[c_155,c_18])).

tff(c_292,plain,(
    ! [B_65] :
      ( r2_xboole_0('#skF_2',B_65)
      | r2_xboole_0(B_65,'#skF_3')
      | B_65 = '#skF_3'
      | ~ r1_tarski('#skF_3',B_65) ) ),
    inference(resolution,[status(thm)],[c_36,c_237])).

tff(c_397,plain,(
    ! [A_68,B_69] :
      ( r2_xboole_0(A_68,'#skF_3')
      | ~ r1_tarski(A_68,B_69)
      | r2_xboole_0('#skF_2',B_69)
      | B_69 = '#skF_3'
      | ~ r1_tarski('#skF_3',B_69) ) ),
    inference(resolution,[status(thm)],[c_292,c_18])).

tff(c_401,plain,
    ( r2_xboole_0('#skF_3','#skF_3')
    | r2_xboole_0('#skF_2','#skF_4')
    | '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_86,c_397])).

tff(c_407,plain,
    ( r2_xboole_0('#skF_3','#skF_3')
    | r2_xboole_0('#skF_2','#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_401])).

tff(c_412,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_407])).

tff(c_67,plain,(
    ! [B_34,A_35] :
      ( ~ r2_hidden(B_34,A_35)
      | ~ r2_hidden(A_35,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_70,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_67])).

tff(c_419,plain,(
    ~ r2_hidden('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_412,c_70])).

tff(c_422,plain,(
    r2_hidden('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_412,c_34])).

tff(c_433,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_419,c_422])).

tff(c_434,plain,
    ( r2_xboole_0('#skF_2','#skF_4')
    | r2_xboole_0('#skF_3','#skF_3') ),
    inference(splitRight,[status(thm)],[c_407])).

tff(c_436,plain,(
    r2_xboole_0('#skF_3','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_434])).

tff(c_30,plain,(
    ! [A_15,B_17] :
      ( r2_hidden(A_15,B_17)
      | ~ r2_xboole_0(A_15,B_17)
      | ~ v3_ordinal1(B_17)
      | ~ v1_ordinal1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_439,plain,
    ( r2_hidden('#skF_3','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v1_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_436,c_30])).

tff(c_450,plain,(
    r2_hidden('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_40,c_439])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_460,plain,(
    ~ r2_hidden('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_450,c_2])).

tff(c_467,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_450,c_460])).

tff(c_468,plain,(
    r2_xboole_0('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_434])).

tff(c_490,plain,
    ( r2_hidden('#skF_2','#skF_4')
    | ~ v3_ordinal1('#skF_4')
    | ~ v1_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_468,c_30])).

tff(c_501,plain,(
    r2_hidden('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_490])).

tff(c_503,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_501])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:10:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.52/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.52/1.32  
% 2.52/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.52/1.32  %$ r3_xboole_0 > r2_xboole_0 > r2_hidden > r1_tarski > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > #nlpp > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.52/1.32  
% 2.52/1.32  %Foreground sorts:
% 2.52/1.32  
% 2.52/1.32  
% 2.52/1.32  %Background operators:
% 2.52/1.32  
% 2.52/1.32  
% 2.52/1.32  %Foreground operators:
% 2.52/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.52/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.52/1.32  tff(v1_ordinal1, type, v1_ordinal1: $i > $o).
% 2.52/1.32  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.52/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.52/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.52/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.52/1.32  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 2.52/1.32  tff(v2_ordinal1, type, v2_ordinal1: $i > $o).
% 2.52/1.32  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.52/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.52/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.52/1.32  tff(r3_xboole_0, type, r3_xboole_0: ($i * $i) > $o).
% 2.52/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.52/1.32  
% 2.52/1.34  tff(f_91, negated_conjecture, ~(![A]: (v1_ordinal1(A) => (![B]: (v3_ordinal1(B) => (![C]: (v3_ordinal1(C) => ((r1_tarski(A, B) & r2_hidden(B, C)) => r2_hidden(A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_ordinal1)).
% 2.52/1.34  tff(f_60, axiom, (![A]: (v3_ordinal1(A) => (v1_ordinal1(A) & v2_ordinal1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_ordinal1)).
% 2.52/1.34  tff(f_67, axiom, (![A]: (v1_ordinal1(A) <=> (![B]: (r2_hidden(B, A) => r1_tarski(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_ordinal1)).
% 2.52/1.34  tff(f_36, axiom, (![A, B]: (r3_xboole_0(A, B) <=> (r1_tarski(A, B) | r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_xboole_0)).
% 2.52/1.34  tff(f_48, axiom, (![A, B]: (~((~r2_xboole_0(A, B) & ~(A = B)) & ~r2_xboole_0(B, A)) <=> r3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t104_xboole_1)).
% 2.52/1.34  tff(f_54, axiom, (![A, B, C]: ((r1_tarski(A, B) & r2_xboole_0(B, C)) => r2_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_xboole_1)).
% 2.52/1.34  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 2.52/1.34  tff(f_76, axiom, (![A]: (v1_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_xboole_0(A, B) => r2_hidden(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_ordinal1)).
% 2.52/1.34  tff(c_32, plain, (~r2_hidden('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.52/1.34  tff(c_42, plain, (v1_ordinal1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.52/1.34  tff(c_38, plain, (v3_ordinal1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.52/1.34  tff(c_40, plain, (v3_ordinal1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.52/1.34  tff(c_53, plain, (![A_24]: (v1_ordinal1(A_24) | ~v3_ordinal1(A_24))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.52/1.34  tff(c_61, plain, (v1_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_53])).
% 2.52/1.34  tff(c_60, plain, (v1_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_53])).
% 2.52/1.34  tff(c_34, plain, (r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.52/1.34  tff(c_76, plain, (![B_38, A_39]: (r1_tarski(B_38, A_39) | ~r2_hidden(B_38, A_39) | ~v1_ordinal1(A_39))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.52/1.34  tff(c_82, plain, (r1_tarski('#skF_3', '#skF_4') | ~v1_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_76])).
% 2.52/1.34  tff(c_86, plain, (r1_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_82])).
% 2.52/1.34  tff(c_36, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.52/1.34  tff(c_8, plain, (![A_3, B_4]: (~r1_tarski(A_3, B_4) | r3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.52/1.34  tff(c_113, plain, (![B_52, A_53]: (r2_xboole_0(B_52, A_53) | B_52=A_53 | r2_xboole_0(A_53, B_52) | ~r3_xboole_0(A_53, B_52))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.52/1.34  tff(c_155, plain, (![B_54, A_55]: (r2_xboole_0(B_54, A_55) | B_54=A_55 | r2_xboole_0(A_55, B_54) | ~r1_tarski(A_55, B_54))), inference(resolution, [status(thm)], [c_8, c_113])).
% 2.52/1.34  tff(c_18, plain, (![A_7, C_9, B_8]: (r2_xboole_0(A_7, C_9) | ~r2_xboole_0(B_8, C_9) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.52/1.34  tff(c_237, plain, (![A_58, B_59, A_60]: (r2_xboole_0(A_58, B_59) | ~r1_tarski(A_58, A_60) | r2_xboole_0(B_59, A_60) | B_59=A_60 | ~r1_tarski(A_60, B_59))), inference(resolution, [status(thm)], [c_155, c_18])).
% 2.52/1.34  tff(c_292, plain, (![B_65]: (r2_xboole_0('#skF_2', B_65) | r2_xboole_0(B_65, '#skF_3') | B_65='#skF_3' | ~r1_tarski('#skF_3', B_65))), inference(resolution, [status(thm)], [c_36, c_237])).
% 2.52/1.34  tff(c_397, plain, (![A_68, B_69]: (r2_xboole_0(A_68, '#skF_3') | ~r1_tarski(A_68, B_69) | r2_xboole_0('#skF_2', B_69) | B_69='#skF_3' | ~r1_tarski('#skF_3', B_69))), inference(resolution, [status(thm)], [c_292, c_18])).
% 2.52/1.34  tff(c_401, plain, (r2_xboole_0('#skF_3', '#skF_3') | r2_xboole_0('#skF_2', '#skF_4') | '#skF_3'='#skF_4' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_86, c_397])).
% 2.52/1.34  tff(c_407, plain, (r2_xboole_0('#skF_3', '#skF_3') | r2_xboole_0('#skF_2', '#skF_4') | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_401])).
% 2.52/1.34  tff(c_412, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_407])).
% 2.52/1.34  tff(c_67, plain, (![B_34, A_35]: (~r2_hidden(B_34, A_35) | ~r2_hidden(A_35, B_34))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.52/1.34  tff(c_70, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_67])).
% 2.52/1.34  tff(c_419, plain, (~r2_hidden('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_412, c_70])).
% 2.52/1.34  tff(c_422, plain, (r2_hidden('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_412, c_34])).
% 2.52/1.34  tff(c_433, plain, $false, inference(negUnitSimplification, [status(thm)], [c_419, c_422])).
% 2.52/1.34  tff(c_434, plain, (r2_xboole_0('#skF_2', '#skF_4') | r2_xboole_0('#skF_3', '#skF_3')), inference(splitRight, [status(thm)], [c_407])).
% 2.52/1.34  tff(c_436, plain, (r2_xboole_0('#skF_3', '#skF_3')), inference(splitLeft, [status(thm)], [c_434])).
% 2.52/1.34  tff(c_30, plain, (![A_15, B_17]: (r2_hidden(A_15, B_17) | ~r2_xboole_0(A_15, B_17) | ~v3_ordinal1(B_17) | ~v1_ordinal1(A_15))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.52/1.34  tff(c_439, plain, (r2_hidden('#skF_3', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v1_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_436, c_30])).
% 2.52/1.34  tff(c_450, plain, (r2_hidden('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_61, c_40, c_439])).
% 2.52/1.34  tff(c_2, plain, (![B_2, A_1]: (~r2_hidden(B_2, A_1) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.52/1.34  tff(c_460, plain, (~r2_hidden('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_450, c_2])).
% 2.52/1.34  tff(c_467, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_450, c_460])).
% 2.52/1.34  tff(c_468, plain, (r2_xboole_0('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_434])).
% 2.52/1.34  tff(c_490, plain, (r2_hidden('#skF_2', '#skF_4') | ~v3_ordinal1('#skF_4') | ~v1_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_468, c_30])).
% 2.52/1.34  tff(c_501, plain, (r2_hidden('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_490])).
% 2.52/1.34  tff(c_503, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_501])).
% 2.52/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.52/1.34  
% 2.52/1.34  Inference rules
% 2.52/1.34  ----------------------
% 2.52/1.34  #Ref     : 0
% 2.52/1.34  #Sup     : 91
% 2.52/1.34  #Fact    : 4
% 2.52/1.34  #Define  : 0
% 2.52/1.34  #Split   : 2
% 2.52/1.34  #Chain   : 0
% 2.52/1.34  #Close   : 0
% 2.52/1.34  
% 2.52/1.34  Ordering : KBO
% 2.52/1.34  
% 2.52/1.34  Simplification rules
% 2.52/1.34  ----------------------
% 2.52/1.34  #Subsume      : 6
% 2.52/1.34  #Demod        : 47
% 2.52/1.34  #Tautology    : 38
% 2.52/1.34  #SimpNegUnit  : 2
% 2.52/1.34  #BackRed      : 12
% 2.52/1.34  
% 2.52/1.34  #Partial instantiations: 0
% 2.52/1.34  #Strategies tried      : 1
% 2.52/1.34  
% 2.52/1.34  Timing (in seconds)
% 2.52/1.34  ----------------------
% 2.52/1.34  Preprocessing        : 0.28
% 2.52/1.34  Parsing              : 0.15
% 2.52/1.34  CNF conversion       : 0.02
% 2.52/1.34  Main loop            : 0.30
% 2.52/1.34  Inferencing          : 0.11
% 2.52/1.34  Reduction            : 0.07
% 2.52/1.34  Demodulation         : 0.05
% 2.52/1.34  BG Simplification    : 0.02
% 2.52/1.34  Subsumption          : 0.08
% 2.52/1.34  Abstraction          : 0.01
% 2.52/1.34  MUC search           : 0.00
% 2.52/1.34  Cooper               : 0.00
% 2.52/1.34  Total                : 0.60
% 2.52/1.34  Index Insertion      : 0.00
% 2.52/1.34  Index Deletion       : 0.00
% 2.52/1.34  Index Matching       : 0.00
% 2.52/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
