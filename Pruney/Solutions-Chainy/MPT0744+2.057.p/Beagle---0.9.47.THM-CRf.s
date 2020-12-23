%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:22 EST 2020

% Result     : Theorem 1.90s
% Output     : CNFRefutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 117 expanded)
%              Number of leaves         :   18 (  46 expanded)
%              Depth                    :   10
%              Number of atoms          :   96 ( 261 expanded)
%              Number of equality atoms :   10 (  21 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_2 > #skF_1

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

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

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

tff(f_81,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,k1_ordinal1(B))
            <=> r1_ordinal1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
        | r1_ordinal1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r2_hidden(A,k1_ordinal1(B))
    <=> ( r2_hidden(A,B)
        | A = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_66,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ~ ( ~ r2_hidden(A,B)
              & A != B
              & ~ r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).

tff(f_71,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_24,plain,(
    v3_ordinal1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_ordinal1(B_2,A_1)
      | r1_ordinal1(A_1,B_2)
      | ~ v3_ordinal1(B_2)
      | ~ v3_ordinal1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_336,plain,(
    ! [B_57] :
      ( ~ v3_ordinal1(B_57)
      | r1_ordinal1(B_57,B_57) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_2])).

tff(c_14,plain,(
    ! [B_8] : r2_hidden(B_8,k1_ordinal1(B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_22,plain,(
    v3_ordinal1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_26,plain,
    ( ~ r1_ordinal1('#skF_1','#skF_2')
    | ~ r2_hidden('#skF_1',k1_ordinal1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_55,plain,(
    ~ r2_hidden('#skF_1',k1_ordinal1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_32,plain,
    ( r2_hidden('#skF_1',k1_ordinal1('#skF_2'))
    | r1_ordinal1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_60,plain,(
    r1_ordinal1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_32])).

tff(c_8,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,B_5)
      | ~ r1_ordinal1(A_4,B_5)
      | ~ v3_ordinal1(B_5)
      | ~ v3_ordinal1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_131,plain,(
    ! [B_34,A_35] :
      ( r2_hidden(B_34,A_35)
      | B_34 = A_35
      | r2_hidden(A_35,B_34)
      | ~ v3_ordinal1(B_34)
      | ~ v3_ordinal1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_20,plain,(
    ! [B_13,A_12] :
      ( ~ r1_tarski(B_13,A_12)
      | ~ r2_hidden(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_155,plain,(
    ! [A_37,B_38] :
      ( ~ r1_tarski(A_37,B_38)
      | B_38 = A_37
      | r2_hidden(A_37,B_38)
      | ~ v3_ordinal1(B_38)
      | ~ v3_ordinal1(A_37) ) ),
    inference(resolution,[status(thm)],[c_131,c_20])).

tff(c_16,plain,(
    ! [A_7,B_8] :
      ( ~ r2_hidden(A_7,B_8)
      | r2_hidden(A_7,k1_ordinal1(B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_59,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_55])).

tff(c_162,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | '#skF_2' = '#skF_1'
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_155,c_59])).

tff(c_172,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_162])).

tff(c_177,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_172])).

tff(c_180,plain,
    ( ~ r1_ordinal1('#skF_1','#skF_2')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_177])).

tff(c_184,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_60,c_180])).

tff(c_185,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_172])).

tff(c_189,plain,(
    ~ r2_hidden('#skF_1',k1_ordinal1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_55])).

tff(c_193,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_189])).

tff(c_194,plain,(
    ~ r1_ordinal1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_241,plain,(
    ! [A_48,B_49] :
      ( r1_tarski(A_48,B_49)
      | ~ r1_ordinal1(A_48,B_49)
      | ~ v3_ordinal1(B_49)
      | ~ v3_ordinal1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_195,plain,(
    r2_hidden('#skF_1',k1_ordinal1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_203,plain,(
    ! [B_41,A_42] :
      ( B_41 = A_42
      | r2_hidden(A_42,B_41)
      | ~ r2_hidden(A_42,k1_ordinal1(B_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_213,plain,
    ( '#skF_2' = '#skF_1'
    | r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_195,c_203])).

tff(c_217,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_213])).

tff(c_221,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_217,c_20])).

tff(c_244,plain,
    ( ~ r1_ordinal1('#skF_2','#skF_1')
    | ~ v3_ordinal1('#skF_1')
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_241,c_221])).

tff(c_261,plain,(
    ~ r1_ordinal1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_24,c_244])).

tff(c_270,plain,
    ( r1_ordinal1('#skF_1','#skF_2')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_261])).

tff(c_276,plain,(
    r1_ordinal1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_270])).

tff(c_278,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_194,c_276])).

tff(c_279,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_213])).

tff(c_283,plain,(
    ~ r1_ordinal1('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_279,c_194])).

tff(c_339,plain,(
    ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_336,c_283])).

tff(c_343,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_339])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:20:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.90/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.22  
% 1.90/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.22  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_2 > #skF_1
% 1.90/1.22  
% 1.90/1.22  %Foreground sorts:
% 1.90/1.22  
% 1.90/1.22  
% 1.90/1.22  %Background operators:
% 1.90/1.22  
% 1.90/1.22  
% 1.90/1.22  %Foreground operators:
% 1.90/1.22  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 1.90/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.90/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.90/1.22  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.90/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.90/1.22  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 1.90/1.22  tff('#skF_2', type, '#skF_2': $i).
% 1.90/1.22  tff('#skF_1', type, '#skF_1': $i).
% 1.90/1.22  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 1.90/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.90/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.90/1.22  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.90/1.22  
% 2.12/1.23  tff(f_81, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, k1_ordinal1(B)) <=> r1_ordinal1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_ordinal1)).
% 2.12/1.23  tff(f_33, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) | r1_ordinal1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', connectedness_r1_ordinal1)).
% 2.12/1.23  tff(f_51, axiom, (![A, B]: (r2_hidden(A, k1_ordinal1(B)) <=> (r2_hidden(A, B) | (A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_ordinal1)).
% 2.12/1.23  tff(f_43, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 2.12/1.23  tff(f_66, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => ~((~r2_hidden(A, B) & ~(A = B)) & ~r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_ordinal1)).
% 2.12/1.23  tff(f_71, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.12/1.23  tff(c_24, plain, (v3_ordinal1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.12/1.23  tff(c_2, plain, (![B_2, A_1]: (r1_ordinal1(B_2, A_1) | r1_ordinal1(A_1, B_2) | ~v3_ordinal1(B_2) | ~v3_ordinal1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.12/1.23  tff(c_336, plain, (![B_57]: (~v3_ordinal1(B_57) | r1_ordinal1(B_57, B_57))), inference(factorization, [status(thm), theory('equality')], [c_2])).
% 2.12/1.23  tff(c_14, plain, (![B_8]: (r2_hidden(B_8, k1_ordinal1(B_8)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.12/1.23  tff(c_22, plain, (v3_ordinal1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.12/1.23  tff(c_26, plain, (~r1_ordinal1('#skF_1', '#skF_2') | ~r2_hidden('#skF_1', k1_ordinal1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.12/1.23  tff(c_55, plain, (~r2_hidden('#skF_1', k1_ordinal1('#skF_2'))), inference(splitLeft, [status(thm)], [c_26])).
% 2.12/1.23  tff(c_32, plain, (r2_hidden('#skF_1', k1_ordinal1('#skF_2')) | r1_ordinal1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.12/1.23  tff(c_60, plain, (r1_ordinal1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_55, c_32])).
% 2.12/1.23  tff(c_8, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | ~r1_ordinal1(A_4, B_5) | ~v3_ordinal1(B_5) | ~v3_ordinal1(A_4))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.12/1.23  tff(c_131, plain, (![B_34, A_35]: (r2_hidden(B_34, A_35) | B_34=A_35 | r2_hidden(A_35, B_34) | ~v3_ordinal1(B_34) | ~v3_ordinal1(A_35))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.12/1.23  tff(c_20, plain, (![B_13, A_12]: (~r1_tarski(B_13, A_12) | ~r2_hidden(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.12/1.23  tff(c_155, plain, (![A_37, B_38]: (~r1_tarski(A_37, B_38) | B_38=A_37 | r2_hidden(A_37, B_38) | ~v3_ordinal1(B_38) | ~v3_ordinal1(A_37))), inference(resolution, [status(thm)], [c_131, c_20])).
% 2.12/1.23  tff(c_16, plain, (![A_7, B_8]: (~r2_hidden(A_7, B_8) | r2_hidden(A_7, k1_ordinal1(B_8)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.12/1.24  tff(c_59, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_16, c_55])).
% 2.12/1.24  tff(c_162, plain, (~r1_tarski('#skF_1', '#skF_2') | '#skF_2'='#skF_1' | ~v3_ordinal1('#skF_2') | ~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_155, c_59])).
% 2.12/1.24  tff(c_172, plain, (~r1_tarski('#skF_1', '#skF_2') | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_162])).
% 2.12/1.24  tff(c_177, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_172])).
% 2.12/1.24  tff(c_180, plain, (~r1_ordinal1('#skF_1', '#skF_2') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_8, c_177])).
% 2.12/1.24  tff(c_184, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_60, c_180])).
% 2.12/1.24  tff(c_185, plain, ('#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_172])).
% 2.12/1.24  tff(c_189, plain, (~r2_hidden('#skF_1', k1_ordinal1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_185, c_55])).
% 2.12/1.24  tff(c_193, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_189])).
% 2.12/1.24  tff(c_194, plain, (~r1_ordinal1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_26])).
% 2.12/1.24  tff(c_241, plain, (![A_48, B_49]: (r1_tarski(A_48, B_49) | ~r1_ordinal1(A_48, B_49) | ~v3_ordinal1(B_49) | ~v3_ordinal1(A_48))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.12/1.24  tff(c_195, plain, (r2_hidden('#skF_1', k1_ordinal1('#skF_2'))), inference(splitRight, [status(thm)], [c_26])).
% 2.12/1.24  tff(c_203, plain, (![B_41, A_42]: (B_41=A_42 | r2_hidden(A_42, B_41) | ~r2_hidden(A_42, k1_ordinal1(B_41)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.12/1.24  tff(c_213, plain, ('#skF_2'='#skF_1' | r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_195, c_203])).
% 2.12/1.24  tff(c_217, plain, (r2_hidden('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_213])).
% 2.12/1.24  tff(c_221, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_217, c_20])).
% 2.12/1.24  tff(c_244, plain, (~r1_ordinal1('#skF_2', '#skF_1') | ~v3_ordinal1('#skF_1') | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_241, c_221])).
% 2.12/1.24  tff(c_261, plain, (~r1_ordinal1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_24, c_244])).
% 2.12/1.24  tff(c_270, plain, (r1_ordinal1('#skF_1', '#skF_2') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_2, c_261])).
% 2.12/1.24  tff(c_276, plain, (r1_ordinal1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_270])).
% 2.12/1.24  tff(c_278, plain, $false, inference(negUnitSimplification, [status(thm)], [c_194, c_276])).
% 2.12/1.24  tff(c_279, plain, ('#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_213])).
% 2.12/1.24  tff(c_283, plain, (~r1_ordinal1('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_279, c_194])).
% 2.12/1.24  tff(c_339, plain, (~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_336, c_283])).
% 2.12/1.24  tff(c_343, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_339])).
% 2.12/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.24  
% 2.12/1.24  Inference rules
% 2.12/1.24  ----------------------
% 2.12/1.24  #Ref     : 0
% 2.12/1.24  #Sup     : 41
% 2.12/1.24  #Fact    : 8
% 2.12/1.24  #Define  : 0
% 2.12/1.24  #Split   : 3
% 2.12/1.24  #Chain   : 0
% 2.12/1.24  #Close   : 0
% 2.12/1.24  
% 2.12/1.24  Ordering : KBO
% 2.12/1.24  
% 2.12/1.24  Simplification rules
% 2.12/1.24  ----------------------
% 2.12/1.24  #Subsume      : 4
% 2.12/1.24  #Demod        : 26
% 2.12/1.24  #Tautology    : 19
% 2.12/1.24  #SimpNegUnit  : 3
% 2.12/1.24  #BackRed      : 8
% 2.12/1.24  
% 2.12/1.24  #Partial instantiations: 0
% 2.12/1.24  #Strategies tried      : 1
% 2.12/1.24  
% 2.12/1.24  Timing (in seconds)
% 2.12/1.24  ----------------------
% 2.12/1.24  Preprocessing        : 0.27
% 2.12/1.24  Parsing              : 0.15
% 2.12/1.24  CNF conversion       : 0.02
% 2.12/1.24  Main loop            : 0.21
% 2.12/1.24  Inferencing          : 0.09
% 2.12/1.24  Reduction            : 0.05
% 2.12/1.24  Demodulation         : 0.04
% 2.12/1.24  BG Simplification    : 0.01
% 2.12/1.24  Subsumption          : 0.04
% 2.12/1.24  Abstraction          : 0.01
% 2.12/1.24  MUC search           : 0.00
% 2.12/1.24  Cooper               : 0.00
% 2.12/1.24  Total                : 0.50
% 2.12/1.24  Index Insertion      : 0.00
% 2.12/1.24  Index Deletion       : 0.00
% 2.12/1.24  Index Matching       : 0.00
% 2.12/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
