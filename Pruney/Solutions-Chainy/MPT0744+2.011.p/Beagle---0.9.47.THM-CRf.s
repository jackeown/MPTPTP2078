%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:16 EST 2020

% Result     : Theorem 2.62s
% Output     : CNFRefutation 2.62s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 128 expanded)
%              Number of leaves         :   17 (  47 expanded)
%              Depth                    :    9
%              Number of atoms          :   98 ( 286 expanded)
%              Number of equality atoms :   10 (  28 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > #nlpp > k1_ordinal1 > #skF_2 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_54,axiom,(
    ! [A,B] :
      ( r2_hidden(A,k1_ordinal1(B))
    <=> ( r2_hidden(A,B)
        | A = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

tff(f_93,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,k1_ordinal1(B))
            <=> r1_ordinal1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_69,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ~ ( ~ r2_hidden(A,B)
              & A != B
              & ~ r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).

tff(f_83,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_78,axiom,(
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

tff(c_14,plain,(
    ! [B_9] : r2_hidden(B_9,k1_ordinal1(B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_26,plain,(
    v3_ordinal1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_24,plain,(
    v3_ordinal1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_34,plain,
    ( r2_hidden('#skF_1',k1_ordinal1('#skF_2'))
    | r1_ordinal1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_48,plain,(
    r1_ordinal1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | ~ r1_ordinal1(A_5,B_6)
      | ~ v3_ordinal1(B_6)
      | ~ v3_ordinal1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_296,plain,(
    ! [B_58,A_59] :
      ( r2_hidden(B_58,A_59)
      | B_58 = A_59
      | r2_hidden(A_59,B_58)
      | ~ v3_ordinal1(B_58)
      | ~ v3_ordinal1(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_22,plain,(
    ! [B_17,A_16] :
      ( ~ r1_tarski(B_17,A_16)
      | ~ r2_hidden(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_500,plain,(
    ! [A_65,B_66] :
      ( ~ r1_tarski(A_65,B_66)
      | B_66 = A_65
      | r2_hidden(A_65,B_66)
      | ~ v3_ordinal1(B_66)
      | ~ v3_ordinal1(A_65) ) ),
    inference(resolution,[status(thm)],[c_296,c_22])).

tff(c_51,plain,(
    ! [A_26,B_27] :
      ( ~ r2_hidden(A_26,B_27)
      | r2_hidden(A_26,k1_ordinal1(B_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_28,plain,
    ( ~ r1_ordinal1('#skF_1','#skF_2')
    | ~ r2_hidden('#skF_1',k1_ordinal1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_50,plain,(
    ~ r2_hidden('#skF_1',k1_ordinal1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_28])).

tff(c_64,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_51,c_50])).

tff(c_556,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | '#skF_2' = '#skF_1'
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_500,c_64])).

tff(c_585,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_556])).

tff(c_592,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_585])).

tff(c_595,plain,
    ( ~ r1_ordinal1('#skF_1','#skF_2')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_592])).

tff(c_599,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_48,c_595])).

tff(c_600,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_585])).

tff(c_605,plain,(
    ~ r2_hidden('#skF_1',k1_ordinal1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_600,c_50])).

tff(c_610,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_605])).

tff(c_612,plain,(
    ~ r1_ordinal1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_748,plain,(
    ! [B_88,A_89] :
      ( r2_hidden(B_88,A_89)
      | r1_ordinal1(A_89,B_88)
      | ~ v3_ordinal1(B_88)
      | ~ v3_ordinal1(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_611,plain,(
    r2_hidden('#skF_1',k1_ordinal1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_665,plain,(
    ! [B_76,A_77] :
      ( B_76 = A_77
      | r2_hidden(A_77,B_76)
      | ~ r2_hidden(A_77,k1_ordinal1(B_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_676,plain,
    ( '#skF_2' = '#skF_1'
    | r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_611,c_665])).

tff(c_679,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_676])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_685,plain,(
    ~ r2_hidden('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_679,c_2])).

tff(c_766,plain,
    ( r1_ordinal1('#skF_1','#skF_2')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_748,c_685])).

tff(c_805,plain,(
    r1_ordinal1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_766])).

tff(c_807,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_612,c_805])).

tff(c_808,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_676])).

tff(c_813,plain,(
    ~ r1_ordinal1('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_808,c_612])).

tff(c_855,plain,(
    ! [B_98,A_99] :
      ( r2_hidden(B_98,A_99)
      | r1_ordinal1(A_99,B_98)
      | ~ v3_ordinal1(B_98)
      | ~ v3_ordinal1(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_809,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_676])).

tff(c_821,plain,(
    ~ r2_hidden('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_808,c_809])).

tff(c_873,plain,
    ( r1_ordinal1('#skF_1','#skF_1')
    | ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_855,c_821])).

tff(c_909,plain,(
    r1_ordinal1('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_873])).

tff(c_911,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_813,c_909])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:29:11 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.18/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.62/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/1.35  
% 2.62/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/1.35  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > #nlpp > k1_ordinal1 > #skF_2 > #skF_1
% 2.62/1.35  
% 2.62/1.35  %Foreground sorts:
% 2.62/1.35  
% 2.62/1.35  
% 2.62/1.35  %Background operators:
% 2.62/1.35  
% 2.62/1.35  
% 2.62/1.35  %Foreground operators:
% 2.62/1.35  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 2.62/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.62/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.62/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.62/1.35  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 2.62/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.62/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.62/1.35  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 2.62/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.62/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.62/1.35  
% 2.62/1.36  tff(f_54, axiom, (![A, B]: (r2_hidden(A, k1_ordinal1(B)) <=> (r2_hidden(A, B) | (A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_ordinal1)).
% 2.62/1.36  tff(f_93, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, k1_ordinal1(B)) <=> r1_ordinal1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_ordinal1)).
% 2.62/1.36  tff(f_46, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 2.62/1.36  tff(f_69, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => ~((~r2_hidden(A, B) & ~(A = B)) & ~r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_ordinal1)).
% 2.62/1.36  tff(f_83, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.62/1.36  tff(f_78, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_ordinal1)).
% 2.62/1.36  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 2.62/1.36  tff(c_14, plain, (![B_9]: (r2_hidden(B_9, k1_ordinal1(B_9)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.62/1.36  tff(c_26, plain, (v3_ordinal1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.62/1.36  tff(c_24, plain, (v3_ordinal1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.62/1.36  tff(c_34, plain, (r2_hidden('#skF_1', k1_ordinal1('#skF_2')) | r1_ordinal1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.62/1.36  tff(c_48, plain, (r1_ordinal1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_34])).
% 2.62/1.36  tff(c_8, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | ~r1_ordinal1(A_5, B_6) | ~v3_ordinal1(B_6) | ~v3_ordinal1(A_5))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.62/1.36  tff(c_296, plain, (![B_58, A_59]: (r2_hidden(B_58, A_59) | B_58=A_59 | r2_hidden(A_59, B_58) | ~v3_ordinal1(B_58) | ~v3_ordinal1(A_59))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.62/1.36  tff(c_22, plain, (![B_17, A_16]: (~r1_tarski(B_17, A_16) | ~r2_hidden(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.62/1.36  tff(c_500, plain, (![A_65, B_66]: (~r1_tarski(A_65, B_66) | B_66=A_65 | r2_hidden(A_65, B_66) | ~v3_ordinal1(B_66) | ~v3_ordinal1(A_65))), inference(resolution, [status(thm)], [c_296, c_22])).
% 2.62/1.36  tff(c_51, plain, (![A_26, B_27]: (~r2_hidden(A_26, B_27) | r2_hidden(A_26, k1_ordinal1(B_27)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.62/1.36  tff(c_28, plain, (~r1_ordinal1('#skF_1', '#skF_2') | ~r2_hidden('#skF_1', k1_ordinal1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.62/1.36  tff(c_50, plain, (~r2_hidden('#skF_1', k1_ordinal1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_28])).
% 2.62/1.36  tff(c_64, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_51, c_50])).
% 2.62/1.36  tff(c_556, plain, (~r1_tarski('#skF_1', '#skF_2') | '#skF_2'='#skF_1' | ~v3_ordinal1('#skF_2') | ~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_500, c_64])).
% 2.62/1.36  tff(c_585, plain, (~r1_tarski('#skF_1', '#skF_2') | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_556])).
% 2.62/1.36  tff(c_592, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_585])).
% 2.62/1.36  tff(c_595, plain, (~r1_ordinal1('#skF_1', '#skF_2') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_8, c_592])).
% 2.62/1.36  tff(c_599, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_48, c_595])).
% 2.62/1.36  tff(c_600, plain, ('#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_585])).
% 2.62/1.36  tff(c_605, plain, (~r2_hidden('#skF_1', k1_ordinal1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_600, c_50])).
% 2.62/1.36  tff(c_610, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_605])).
% 2.62/1.36  tff(c_612, plain, (~r1_ordinal1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_34])).
% 2.62/1.36  tff(c_748, plain, (![B_88, A_89]: (r2_hidden(B_88, A_89) | r1_ordinal1(A_89, B_88) | ~v3_ordinal1(B_88) | ~v3_ordinal1(A_89))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.62/1.36  tff(c_611, plain, (r2_hidden('#skF_1', k1_ordinal1('#skF_2'))), inference(splitRight, [status(thm)], [c_34])).
% 2.62/1.36  tff(c_665, plain, (![B_76, A_77]: (B_76=A_77 | r2_hidden(A_77, B_76) | ~r2_hidden(A_77, k1_ordinal1(B_76)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.62/1.36  tff(c_676, plain, ('#skF_2'='#skF_1' | r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_611, c_665])).
% 2.62/1.36  tff(c_679, plain, (r2_hidden('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_676])).
% 2.62/1.36  tff(c_2, plain, (![B_2, A_1]: (~r2_hidden(B_2, A_1) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.62/1.36  tff(c_685, plain, (~r2_hidden('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_679, c_2])).
% 2.62/1.36  tff(c_766, plain, (r1_ordinal1('#skF_1', '#skF_2') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_748, c_685])).
% 2.62/1.36  tff(c_805, plain, (r1_ordinal1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_766])).
% 2.62/1.36  tff(c_807, plain, $false, inference(negUnitSimplification, [status(thm)], [c_612, c_805])).
% 2.62/1.36  tff(c_808, plain, ('#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_676])).
% 2.62/1.36  tff(c_813, plain, (~r1_ordinal1('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_808, c_612])).
% 2.62/1.36  tff(c_855, plain, (![B_98, A_99]: (r2_hidden(B_98, A_99) | r1_ordinal1(A_99, B_98) | ~v3_ordinal1(B_98) | ~v3_ordinal1(A_99))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.62/1.36  tff(c_809, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_676])).
% 2.62/1.36  tff(c_821, plain, (~r2_hidden('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_808, c_809])).
% 2.62/1.36  tff(c_873, plain, (r1_ordinal1('#skF_1', '#skF_1') | ~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_855, c_821])).
% 2.62/1.36  tff(c_909, plain, (r1_ordinal1('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_873])).
% 2.62/1.36  tff(c_911, plain, $false, inference(negUnitSimplification, [status(thm)], [c_813, c_909])).
% 2.62/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/1.36  
% 2.62/1.36  Inference rules
% 2.62/1.36  ----------------------
% 2.62/1.36  #Ref     : 0
% 2.62/1.36  #Sup     : 166
% 2.62/1.36  #Fact    : 4
% 2.62/1.36  #Define  : 0
% 2.62/1.36  #Split   : 5
% 2.62/1.36  #Chain   : 0
% 2.62/1.36  #Close   : 0
% 2.62/1.36  
% 2.62/1.36  Ordering : KBO
% 2.62/1.36  
% 2.62/1.36  Simplification rules
% 2.62/1.36  ----------------------
% 2.62/1.36  #Subsume      : 28
% 2.62/1.36  #Demod        : 35
% 2.62/1.36  #Tautology    : 19
% 2.62/1.36  #SimpNegUnit  : 2
% 2.62/1.36  #BackRed      : 11
% 2.62/1.37  
% 2.62/1.37  #Partial instantiations: 0
% 2.62/1.37  #Strategies tried      : 1
% 2.62/1.37  
% 2.62/1.37  Timing (in seconds)
% 2.62/1.37  ----------------------
% 2.62/1.37  Preprocessing        : 0.27
% 2.62/1.37  Parsing              : 0.15
% 2.62/1.37  CNF conversion       : 0.02
% 2.62/1.37  Main loop            : 0.34
% 2.62/1.37  Inferencing          : 0.13
% 2.62/1.37  Reduction            : 0.08
% 2.62/1.37  Demodulation         : 0.05
% 2.62/1.37  BG Simplification    : 0.02
% 2.62/1.37  Subsumption          : 0.08
% 2.62/1.37  Abstraction          : 0.02
% 2.62/1.37  MUC search           : 0.00
% 2.62/1.37  Cooper               : 0.00
% 2.62/1.37  Total                : 0.64
% 2.62/1.37  Index Insertion      : 0.00
% 2.62/1.37  Index Deletion       : 0.00
% 2.62/1.37  Index Matching       : 0.00
% 2.62/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
