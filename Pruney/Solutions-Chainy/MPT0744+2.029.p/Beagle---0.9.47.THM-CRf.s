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
% DateTime   : Thu Dec  3 10:06:18 EST 2020

% Result     : Theorem 2.79s
% Output     : CNFRefutation 2.79s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 110 expanded)
%              Number of leaves         :   19 (  43 expanded)
%              Depth                    :    9
%              Number of atoms          :  100 ( 237 expanded)
%              Number of equality atoms :    9 (  19 expanded)
%              Maximal formula depth    :    9 (   3 average)
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

tff(f_92,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,k1_ordinal1(B))
            <=> r1_ordinal1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

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

tff(f_68,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ~ ( ~ r2_hidden(A,B)
              & A != B
              & ~ r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).

tff(f_82,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_77,axiom,(
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

tff(c_28,plain,(
    v3_ordinal1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_592,plain,(
    ! [A_84,B_85] :
      ( r2_hidden('#skF_1'(A_84,B_85),A_84)
      | r1_tarski(A_84,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_602,plain,(
    ! [A_84] : r1_tarski(A_84,A_84) ),
    inference(resolution,[status(thm)],[c_592,c_6])).

tff(c_850,plain,(
    ! [A_120,B_121] :
      ( r1_ordinal1(A_120,B_121)
      | ~ r1_tarski(A_120,B_121)
      | ~ v3_ordinal1(B_121)
      | ~ v3_ordinal1(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_855,plain,(
    ! [A_122] :
      ( r1_ordinal1(A_122,A_122)
      | ~ v3_ordinal1(A_122) ) ),
    inference(resolution,[status(thm)],[c_602,c_850])).

tff(c_18,plain,(
    ! [B_12] : r2_hidden(B_12,k1_ordinal1(B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_30,plain,(
    v3_ordinal1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_32,plain,
    ( ~ r1_ordinal1('#skF_2','#skF_3')
    | ~ r2_hidden('#skF_2',k1_ordinal1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_52,plain,(
    ~ r2_hidden('#skF_2',k1_ordinal1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_38,plain,
    ( r2_hidden('#skF_2',k1_ordinal1('#skF_3'))
    | r1_ordinal1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_53,plain,(
    r1_ordinal1('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_38])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(A_8,B_9)
      | ~ r1_ordinal1(A_8,B_9)
      | ~ v3_ordinal1(B_9)
      | ~ v3_ordinal1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_341,plain,(
    ! [B_71,A_72] :
      ( r2_hidden(B_71,A_72)
      | B_71 = A_72
      | r2_hidden(A_72,B_71)
      | ~ v3_ordinal1(B_71)
      | ~ v3_ordinal1(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_54,plain,(
    ! [A_29,B_30] :
      ( ~ r2_hidden(A_29,B_30)
      | r2_hidden(A_29,k1_ordinal1(B_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_67,plain,(
    ~ r2_hidden('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_52])).

tff(c_390,plain,
    ( '#skF_2' = '#skF_3'
    | r2_hidden('#skF_3','#skF_2')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_341,c_67])).

tff(c_474,plain,
    ( '#skF_2' = '#skF_3'
    | r2_hidden('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30,c_390])).

tff(c_498,plain,(
    r2_hidden('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_474])).

tff(c_26,plain,(
    ! [B_20,A_19] :
      ( ~ r1_tarski(B_20,A_19)
      | ~ r2_hidden(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_513,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_498,c_26])).

tff(c_517,plain,
    ( ~ r1_ordinal1('#skF_2','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_513])).

tff(c_521,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_53,c_517])).

tff(c_522,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_474])).

tff(c_527,plain,(
    ~ r2_hidden('#skF_3',k1_ordinal1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_522,c_52])).

tff(c_531,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_527])).

tff(c_532,plain,(
    ~ r1_ordinal1('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_723,plain,(
    ! [B_106,A_107] :
      ( r2_hidden(B_106,A_107)
      | r1_ordinal1(A_107,B_106)
      | ~ v3_ordinal1(B_106)
      | ~ v3_ordinal1(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_533,plain,(
    r2_hidden('#skF_2',k1_ordinal1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_612,plain,(
    ! [B_89,A_90] :
      ( B_89 = A_90
      | r2_hidden(A_90,B_89)
      | ~ r2_hidden(A_90,k1_ordinal1(B_89)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_628,plain,
    ( '#skF_2' = '#skF_3'
    | r2_hidden('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_533,c_612])).

tff(c_631,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_628])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_638,plain,(
    ~ r2_hidden('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_631,c_2])).

tff(c_743,plain,
    ( r1_ordinal1('#skF_2','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_723,c_638])).

tff(c_789,plain,(
    r1_ordinal1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_743])).

tff(c_791,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_532,c_789])).

tff(c_792,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_628])).

tff(c_797,plain,(
    ~ r1_ordinal1('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_792,c_532])).

tff(c_858,plain,(
    ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_855,c_797])).

tff(c_862,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_858])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:24:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.79/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.79/1.40  
% 2.79/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.79/1.40  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > #nlpp > k1_ordinal1 > #skF_2 > #skF_3 > #skF_1
% 2.79/1.40  
% 2.79/1.40  %Foreground sorts:
% 2.79/1.40  
% 2.79/1.40  
% 2.79/1.40  %Background operators:
% 2.79/1.40  
% 2.79/1.40  
% 2.79/1.40  %Foreground operators:
% 2.79/1.40  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 2.79/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.79/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.79/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.79/1.40  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 2.79/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.79/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.79/1.40  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 2.79/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.79/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.79/1.40  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.79/1.40  
% 2.79/1.41  tff(f_92, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, k1_ordinal1(B)) <=> r1_ordinal1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_ordinal1)).
% 2.79/1.41  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.79/1.41  tff(f_45, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 2.79/1.41  tff(f_53, axiom, (![A, B]: (r2_hidden(A, k1_ordinal1(B)) <=> (r2_hidden(A, B) | (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_ordinal1)).
% 2.79/1.41  tff(f_68, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => ~((~r2_hidden(A, B) & ~(A = B)) & ~r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_ordinal1)).
% 2.79/1.41  tff(f_82, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.79/1.41  tff(f_77, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_ordinal1)).
% 2.79/1.41  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 2.79/1.41  tff(c_28, plain, (v3_ordinal1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.79/1.41  tff(c_592, plain, (![A_84, B_85]: (r2_hidden('#skF_1'(A_84, B_85), A_84) | r1_tarski(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.79/1.41  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.79/1.41  tff(c_602, plain, (![A_84]: (r1_tarski(A_84, A_84))), inference(resolution, [status(thm)], [c_592, c_6])).
% 2.79/1.41  tff(c_850, plain, (![A_120, B_121]: (r1_ordinal1(A_120, B_121) | ~r1_tarski(A_120, B_121) | ~v3_ordinal1(B_121) | ~v3_ordinal1(A_120))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.79/1.41  tff(c_855, plain, (![A_122]: (r1_ordinal1(A_122, A_122) | ~v3_ordinal1(A_122))), inference(resolution, [status(thm)], [c_602, c_850])).
% 2.79/1.41  tff(c_18, plain, (![B_12]: (r2_hidden(B_12, k1_ordinal1(B_12)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.79/1.41  tff(c_30, plain, (v3_ordinal1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.79/1.41  tff(c_32, plain, (~r1_ordinal1('#skF_2', '#skF_3') | ~r2_hidden('#skF_2', k1_ordinal1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.79/1.41  tff(c_52, plain, (~r2_hidden('#skF_2', k1_ordinal1('#skF_3'))), inference(splitLeft, [status(thm)], [c_32])).
% 2.79/1.41  tff(c_38, plain, (r2_hidden('#skF_2', k1_ordinal1('#skF_3')) | r1_ordinal1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.79/1.41  tff(c_53, plain, (r1_ordinal1('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_52, c_38])).
% 2.79/1.41  tff(c_12, plain, (![A_8, B_9]: (r1_tarski(A_8, B_9) | ~r1_ordinal1(A_8, B_9) | ~v3_ordinal1(B_9) | ~v3_ordinal1(A_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.79/1.41  tff(c_341, plain, (![B_71, A_72]: (r2_hidden(B_71, A_72) | B_71=A_72 | r2_hidden(A_72, B_71) | ~v3_ordinal1(B_71) | ~v3_ordinal1(A_72))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.79/1.41  tff(c_54, plain, (![A_29, B_30]: (~r2_hidden(A_29, B_30) | r2_hidden(A_29, k1_ordinal1(B_30)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.79/1.41  tff(c_67, plain, (~r2_hidden('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_54, c_52])).
% 2.79/1.41  tff(c_390, plain, ('#skF_2'='#skF_3' | r2_hidden('#skF_3', '#skF_2') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_341, c_67])).
% 2.79/1.41  tff(c_474, plain, ('#skF_2'='#skF_3' | r2_hidden('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30, c_390])).
% 2.79/1.41  tff(c_498, plain, (r2_hidden('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_474])).
% 2.79/1.41  tff(c_26, plain, (![B_20, A_19]: (~r1_tarski(B_20, A_19) | ~r2_hidden(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.79/1.41  tff(c_513, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_498, c_26])).
% 2.79/1.41  tff(c_517, plain, (~r1_ordinal1('#skF_2', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_12, c_513])).
% 2.79/1.41  tff(c_521, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_53, c_517])).
% 2.79/1.41  tff(c_522, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_474])).
% 2.79/1.41  tff(c_527, plain, (~r2_hidden('#skF_3', k1_ordinal1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_522, c_52])).
% 2.79/1.41  tff(c_531, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_527])).
% 2.79/1.41  tff(c_532, plain, (~r1_ordinal1('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_32])).
% 2.79/1.41  tff(c_723, plain, (![B_106, A_107]: (r2_hidden(B_106, A_107) | r1_ordinal1(A_107, B_106) | ~v3_ordinal1(B_106) | ~v3_ordinal1(A_107))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.79/1.41  tff(c_533, plain, (r2_hidden('#skF_2', k1_ordinal1('#skF_3'))), inference(splitRight, [status(thm)], [c_32])).
% 2.79/1.41  tff(c_612, plain, (![B_89, A_90]: (B_89=A_90 | r2_hidden(A_90, B_89) | ~r2_hidden(A_90, k1_ordinal1(B_89)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.79/1.41  tff(c_628, plain, ('#skF_2'='#skF_3' | r2_hidden('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_533, c_612])).
% 2.79/1.41  tff(c_631, plain, (r2_hidden('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_628])).
% 2.79/1.41  tff(c_2, plain, (![B_2, A_1]: (~r2_hidden(B_2, A_1) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.79/1.41  tff(c_638, plain, (~r2_hidden('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_631, c_2])).
% 2.79/1.41  tff(c_743, plain, (r1_ordinal1('#skF_2', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_723, c_638])).
% 2.79/1.41  tff(c_789, plain, (r1_ordinal1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_743])).
% 2.79/1.41  tff(c_791, plain, $false, inference(negUnitSimplification, [status(thm)], [c_532, c_789])).
% 2.79/1.41  tff(c_792, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_628])).
% 2.79/1.41  tff(c_797, plain, (~r1_ordinal1('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_792, c_532])).
% 2.79/1.41  tff(c_858, plain, (~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_855, c_797])).
% 2.79/1.41  tff(c_862, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_858])).
% 2.79/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.79/1.41  
% 2.79/1.41  Inference rules
% 2.79/1.41  ----------------------
% 2.79/1.41  #Ref     : 0
% 2.79/1.41  #Sup     : 161
% 2.79/1.41  #Fact    : 2
% 2.79/1.41  #Define  : 0
% 2.79/1.41  #Split   : 4
% 2.79/1.41  #Chain   : 0
% 2.79/1.41  #Close   : 0
% 2.79/1.41  
% 2.79/1.41  Ordering : KBO
% 2.79/1.41  
% 2.79/1.41  Simplification rules
% 2.79/1.41  ----------------------
% 2.79/1.41  #Subsume      : 20
% 2.79/1.41  #Demod        : 39
% 2.79/1.41  #Tautology    : 24
% 2.79/1.41  #SimpNegUnit  : 3
% 2.79/1.41  #BackRed      : 10
% 2.79/1.41  
% 2.79/1.41  #Partial instantiations: 0
% 2.79/1.41  #Strategies tried      : 1
% 2.79/1.41  
% 2.79/1.41  Timing (in seconds)
% 2.79/1.41  ----------------------
% 2.79/1.42  Preprocessing        : 0.28
% 2.79/1.42  Parsing              : 0.16
% 2.79/1.42  CNF conversion       : 0.02
% 2.79/1.42  Main loop            : 0.36
% 2.79/1.42  Inferencing          : 0.14
% 2.79/1.42  Reduction            : 0.09
% 2.79/1.42  Demodulation         : 0.06
% 2.79/1.42  BG Simplification    : 0.02
% 2.79/1.42  Subsumption          : 0.08
% 2.79/1.42  Abstraction          : 0.02
% 2.79/1.42  MUC search           : 0.00
% 2.79/1.42  Cooper               : 0.00
% 2.79/1.42  Total                : 0.68
% 2.79/1.42  Index Insertion      : 0.00
% 2.79/1.42  Index Deletion       : 0.00
% 2.79/1.42  Index Matching       : 0.00
% 2.79/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
