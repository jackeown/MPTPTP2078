%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:19 EST 2020

% Result     : Theorem 2.53s
% Output     : CNFRefutation 2.53s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 134 expanded)
%              Number of leaves         :   25 (  55 expanded)
%              Depth                    :    9
%              Number of atoms          :  110 ( 287 expanded)
%              Number of equality atoms :   10 (  21 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_1 > #skF_3 > #skF_2 > #skF_4

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

tff(v1_ordinal1,type,(
    v1_ordinal1: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_95,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,k1_ordinal1(B))
            <=> r1_ordinal1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
        | r1_ordinal1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( r2_hidden(A,k1_ordinal1(B))
    <=> ( r2_hidden(A,B)
        | A = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

tff(f_47,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( v1_ordinal1(A)
        & v2_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_ordinal1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_xboole_0(A,B)
           => r2_hidden(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_ordinal1)).

tff(f_85,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_48,plain,(
    v3_ordinal1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_30,plain,(
    ! [B_11,A_10] :
      ( r1_ordinal1(B_11,A_10)
      | r1_ordinal1(A_10,B_11)
      | ~ v3_ordinal1(B_11)
      | ~ v3_ordinal1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_557,plain,(
    ! [B_123] :
      ( ~ v3_ordinal1(B_123)
      | r1_ordinal1(B_123,B_123) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_30])).

tff(c_50,plain,(
    v3_ordinal1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_446,plain,(
    ! [A_114,B_115] :
      ( r1_tarski(A_114,B_115)
      | ~ r1_ordinal1(A_114,B_115)
      | ~ v3_ordinal1(B_115)
      | ~ v3_ordinal1(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_40,plain,(
    ! [B_16] : r2_hidden(B_16,k1_ordinal1(B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_58,plain,
    ( r2_hidden('#skF_3',k1_ordinal1('#skF_4'))
    | r1_ordinal1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_79,plain,(
    r1_ordinal1('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_36,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(A_13,B_14)
      | ~ r1_ordinal1(A_13,B_14)
      | ~ v3_ordinal1(B_14)
      | ~ v3_ordinal1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_61,plain,(
    ! [A_25] :
      ( v1_ordinal1(A_25)
      | ~ v3_ordinal1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_69,plain,(
    v1_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_61])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( r2_xboole_0(A_7,B_8)
      | B_8 = A_7
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_156,plain,(
    ! [A_59,B_60] :
      ( r2_hidden(A_59,B_60)
      | ~ r2_xboole_0(A_59,B_60)
      | ~ v3_ordinal1(B_60)
      | ~ v1_ordinal1(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_271,plain,(
    ! [A_79,B_80] :
      ( r2_hidden(A_79,B_80)
      | ~ v3_ordinal1(B_80)
      | ~ v1_ordinal1(A_79)
      | B_80 = A_79
      | ~ r1_tarski(A_79,B_80) ) ),
    inference(resolution,[status(thm)],[c_20,c_156])).

tff(c_42,plain,(
    ! [A_15,B_16] :
      ( ~ r2_hidden(A_15,B_16)
      | r2_hidden(A_15,k1_ordinal1(B_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_52,plain,
    ( ~ r1_ordinal1('#skF_3','#skF_4')
    | ~ r2_hidden('#skF_3',k1_ordinal1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_102,plain,(
    ~ r2_hidden('#skF_3',k1_ordinal1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_52])).

tff(c_106,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_102])).

tff(c_297,plain,
    ( ~ v3_ordinal1('#skF_4')
    | ~ v1_ordinal1('#skF_3')
    | '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_271,c_106])).

tff(c_312,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_48,c_297])).

tff(c_317,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_312])).

tff(c_320,plain,
    ( ~ r1_ordinal1('#skF_3','#skF_4')
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_317])).

tff(c_324,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_79,c_320])).

tff(c_325,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_312])).

tff(c_354,plain,(
    ~ r2_hidden('#skF_4',k1_ordinal1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_325,c_102])).

tff(c_361,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_354])).

tff(c_362,plain,(
    r2_hidden('#skF_3',k1_ordinal1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_427,plain,(
    ! [B_112,A_113] :
      ( B_112 = A_113
      | r2_hidden(A_113,B_112)
      | ~ r2_hidden(A_113,k1_ordinal1(B_112)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_438,plain,
    ( '#skF_3' = '#skF_4'
    | r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_362,c_427])).

tff(c_441,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_438])).

tff(c_46,plain,(
    ! [B_21,A_20] :
      ( ~ r1_tarski(B_21,A_20)
      | ~ r2_hidden(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_445,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_441,c_46])).

tff(c_449,plain,
    ( ~ r1_ordinal1('#skF_4','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_446,c_445])).

tff(c_471,plain,(
    ~ r1_ordinal1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_50,c_449])).

tff(c_495,plain,(
    ! [B_117,A_118] :
      ( r1_ordinal1(B_117,A_118)
      | r1_ordinal1(A_118,B_117)
      | ~ v3_ordinal1(B_117)
      | ~ v3_ordinal1(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_363,plain,(
    ~ r1_ordinal1('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_503,plain,
    ( r1_ordinal1('#skF_4','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_495,c_363])).

tff(c_515,plain,(
    r1_ordinal1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_50,c_503])).

tff(c_517,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_471,c_515])).

tff(c_518,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_438])).

tff(c_527,plain,(
    ~ r1_ordinal1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_518,c_363])).

tff(c_560,plain,(
    ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_557,c_527])).

tff(c_564,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_560])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n003.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 15:32:42 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.53/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.34  
% 2.53/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.34  %$ r2_xboole_0 > r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 2.53/1.34  
% 2.53/1.34  %Foreground sorts:
% 2.53/1.34  
% 2.53/1.34  
% 2.53/1.34  %Background operators:
% 2.53/1.34  
% 2.53/1.34  
% 2.53/1.34  %Foreground operators:
% 2.53/1.34  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.53/1.34  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 2.53/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.53/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.53/1.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.53/1.34  tff(v1_ordinal1, type, v1_ordinal1: $i > $o).
% 2.53/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.53/1.34  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 2.53/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.53/1.34  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.53/1.34  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 2.53/1.34  tff(v2_ordinal1, type, v2_ordinal1: $i > $o).
% 2.53/1.34  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.53/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.53/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.53/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.53/1.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.53/1.34  
% 2.53/1.36  tff(f_95, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, k1_ordinal1(B)) <=> r1_ordinal1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_ordinal1)).
% 2.53/1.36  tff(f_55, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) | r1_ordinal1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', connectedness_r1_ordinal1)).
% 2.53/1.36  tff(f_65, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 2.53/1.36  tff(f_71, axiom, (![A, B]: (r2_hidden(A, k1_ordinal1(B)) <=> (r2_hidden(A, B) | (A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_ordinal1)).
% 2.53/1.36  tff(f_47, axiom, (![A]: (v3_ordinal1(A) => (v1_ordinal1(A) & v2_ordinal1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_ordinal1)).
% 2.53/1.36  tff(f_41, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.53/1.36  tff(f_80, axiom, (![A]: (v1_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_xboole_0(A, B) => r2_hidden(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_ordinal1)).
% 2.53/1.36  tff(f_85, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.53/1.36  tff(c_48, plain, (v3_ordinal1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.53/1.36  tff(c_30, plain, (![B_11, A_10]: (r1_ordinal1(B_11, A_10) | r1_ordinal1(A_10, B_11) | ~v3_ordinal1(B_11) | ~v3_ordinal1(A_10))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.53/1.36  tff(c_557, plain, (![B_123]: (~v3_ordinal1(B_123) | r1_ordinal1(B_123, B_123))), inference(factorization, [status(thm), theory('equality')], [c_30])).
% 2.53/1.36  tff(c_50, plain, (v3_ordinal1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.53/1.36  tff(c_446, plain, (![A_114, B_115]: (r1_tarski(A_114, B_115) | ~r1_ordinal1(A_114, B_115) | ~v3_ordinal1(B_115) | ~v3_ordinal1(A_114))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.53/1.36  tff(c_40, plain, (![B_16]: (r2_hidden(B_16, k1_ordinal1(B_16)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.53/1.36  tff(c_58, plain, (r2_hidden('#skF_3', k1_ordinal1('#skF_4')) | r1_ordinal1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.53/1.36  tff(c_79, plain, (r1_ordinal1('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_58])).
% 2.53/1.36  tff(c_36, plain, (![A_13, B_14]: (r1_tarski(A_13, B_14) | ~r1_ordinal1(A_13, B_14) | ~v3_ordinal1(B_14) | ~v3_ordinal1(A_13))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.53/1.36  tff(c_61, plain, (![A_25]: (v1_ordinal1(A_25) | ~v3_ordinal1(A_25))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.53/1.36  tff(c_69, plain, (v1_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_61])).
% 2.53/1.36  tff(c_20, plain, (![A_7, B_8]: (r2_xboole_0(A_7, B_8) | B_8=A_7 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.53/1.36  tff(c_156, plain, (![A_59, B_60]: (r2_hidden(A_59, B_60) | ~r2_xboole_0(A_59, B_60) | ~v3_ordinal1(B_60) | ~v1_ordinal1(A_59))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.53/1.36  tff(c_271, plain, (![A_79, B_80]: (r2_hidden(A_79, B_80) | ~v3_ordinal1(B_80) | ~v1_ordinal1(A_79) | B_80=A_79 | ~r1_tarski(A_79, B_80))), inference(resolution, [status(thm)], [c_20, c_156])).
% 2.53/1.36  tff(c_42, plain, (![A_15, B_16]: (~r2_hidden(A_15, B_16) | r2_hidden(A_15, k1_ordinal1(B_16)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.53/1.36  tff(c_52, plain, (~r1_ordinal1('#skF_3', '#skF_4') | ~r2_hidden('#skF_3', k1_ordinal1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.53/1.36  tff(c_102, plain, (~r2_hidden('#skF_3', k1_ordinal1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_52])).
% 2.53/1.36  tff(c_106, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_42, c_102])).
% 2.53/1.36  tff(c_297, plain, (~v3_ordinal1('#skF_4') | ~v1_ordinal1('#skF_3') | '#skF_3'='#skF_4' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_271, c_106])).
% 2.53/1.36  tff(c_312, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_69, c_48, c_297])).
% 2.53/1.36  tff(c_317, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_312])).
% 2.53/1.36  tff(c_320, plain, (~r1_ordinal1('#skF_3', '#skF_4') | ~v3_ordinal1('#skF_4') | ~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_317])).
% 2.53/1.36  tff(c_324, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_79, c_320])).
% 2.53/1.36  tff(c_325, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_312])).
% 2.53/1.36  tff(c_354, plain, (~r2_hidden('#skF_4', k1_ordinal1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_325, c_102])).
% 2.53/1.36  tff(c_361, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_354])).
% 2.53/1.36  tff(c_362, plain, (r2_hidden('#skF_3', k1_ordinal1('#skF_4'))), inference(splitRight, [status(thm)], [c_58])).
% 2.53/1.36  tff(c_427, plain, (![B_112, A_113]: (B_112=A_113 | r2_hidden(A_113, B_112) | ~r2_hidden(A_113, k1_ordinal1(B_112)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.53/1.36  tff(c_438, plain, ('#skF_3'='#skF_4' | r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_362, c_427])).
% 2.53/1.36  tff(c_441, plain, (r2_hidden('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_438])).
% 2.53/1.36  tff(c_46, plain, (![B_21, A_20]: (~r1_tarski(B_21, A_20) | ~r2_hidden(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.53/1.36  tff(c_445, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_441, c_46])).
% 2.53/1.36  tff(c_449, plain, (~r1_ordinal1('#skF_4', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_446, c_445])).
% 2.53/1.36  tff(c_471, plain, (~r1_ordinal1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_50, c_449])).
% 2.53/1.36  tff(c_495, plain, (![B_117, A_118]: (r1_ordinal1(B_117, A_118) | r1_ordinal1(A_118, B_117) | ~v3_ordinal1(B_117) | ~v3_ordinal1(A_118))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.53/1.36  tff(c_363, plain, (~r1_ordinal1('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_58])).
% 2.53/1.36  tff(c_503, plain, (r1_ordinal1('#skF_4', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_495, c_363])).
% 2.53/1.36  tff(c_515, plain, (r1_ordinal1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_50, c_503])).
% 2.53/1.36  tff(c_517, plain, $false, inference(negUnitSimplification, [status(thm)], [c_471, c_515])).
% 2.53/1.36  tff(c_518, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_438])).
% 2.53/1.36  tff(c_527, plain, (~r1_ordinal1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_518, c_363])).
% 2.53/1.36  tff(c_560, plain, (~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_557, c_527])).
% 2.53/1.36  tff(c_564, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_560])).
% 2.53/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.36  
% 2.53/1.36  Inference rules
% 2.53/1.36  ----------------------
% 2.53/1.36  #Ref     : 0
% 2.53/1.36  #Sup     : 86
% 2.53/1.36  #Fact    : 6
% 2.53/1.36  #Define  : 0
% 2.53/1.36  #Split   : 4
% 2.53/1.36  #Chain   : 0
% 2.53/1.36  #Close   : 0
% 2.53/1.36  
% 2.53/1.36  Ordering : KBO
% 2.53/1.36  
% 2.53/1.36  Simplification rules
% 2.53/1.36  ----------------------
% 2.53/1.36  #Subsume      : 9
% 2.53/1.36  #Demod        : 31
% 2.53/1.36  #Tautology    : 25
% 2.53/1.36  #SimpNegUnit  : 1
% 2.53/1.36  #BackRed      : 12
% 2.53/1.36  
% 2.53/1.36  #Partial instantiations: 0
% 2.53/1.36  #Strategies tried      : 1
% 2.53/1.36  
% 2.53/1.36  Timing (in seconds)
% 2.53/1.36  ----------------------
% 2.53/1.36  Preprocessing        : 0.30
% 2.53/1.36  Parsing              : 0.17
% 2.53/1.36  CNF conversion       : 0.02
% 2.53/1.36  Main loop            : 0.30
% 2.53/1.36  Inferencing          : 0.12
% 2.53/1.36  Reduction            : 0.07
% 2.53/1.36  Demodulation         : 0.05
% 2.53/1.36  BG Simplification    : 0.02
% 2.53/1.36  Subsumption          : 0.07
% 2.53/1.36  Abstraction          : 0.01
% 2.53/1.36  MUC search           : 0.00
% 2.53/1.36  Cooper               : 0.00
% 2.53/1.36  Total                : 0.63
% 2.53/1.36  Index Insertion      : 0.00
% 2.53/1.36  Index Deletion       : 0.00
% 2.53/1.36  Index Matching       : 0.00
% 2.53/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
