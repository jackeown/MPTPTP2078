%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:17 EST 2020

% Result     : Theorem 22.70s
% Output     : CNFRefutation 22.70s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 118 expanded)
%              Number of leaves         :   24 (  49 expanded)
%              Depth                    :    9
%              Number of atoms          :  102 ( 242 expanded)
%              Number of equality atoms :   10 (  22 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k2_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_102,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,k1_ordinal1(B))
            <=> r1_ordinal1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( r2_hidden(A,k1_ordinal1(B))
    <=> ( r2_hidden(A,B)
        | A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).

tff(f_92,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r1_ordinal1(A,B)
            | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(c_86,plain,
    ( r2_hidden('#skF_5',k1_ordinal1('#skF_6'))
    | r1_ordinal1('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_113,plain,(
    r1_ordinal1('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_70,plain,(
    ! [B_26] : r2_hidden(B_26,k1_ordinal1(B_26)) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_78,plain,(
    v3_ordinal1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_76,plain,(
    v3_ordinal1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_585,plain,(
    ! [B_115,A_116] :
      ( r2_hidden(B_115,A_116)
      | r1_ordinal1(A_116,B_115)
      | ~ v3_ordinal1(B_115)
      | ~ v3_ordinal1(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_123,plain,(
    ! [A_46,B_47] :
      ( ~ r2_hidden(A_46,B_47)
      | r2_hidden(A_46,k1_ordinal1(B_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_80,plain,
    ( ~ r1_ordinal1('#skF_5','#skF_6')
    | ~ r2_hidden('#skF_5',k1_ordinal1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_114,plain,(
    ~ r2_hidden('#skF_5',k1_ordinal1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_133,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_123,c_114])).

tff(c_663,plain,
    ( r1_ordinal1('#skF_6','#skF_5')
    | ~ v3_ordinal1('#skF_5')
    | ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_585,c_133])).

tff(c_694,plain,(
    r1_ordinal1('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_78,c_663])).

tff(c_66,plain,(
    ! [A_23,B_24] :
      ( r1_tarski(A_23,B_24)
      | ~ r1_ordinal1(A_23,B_24)
      | ~ v3_ordinal1(B_24)
      | ~ v3_ordinal1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_828,plain,(
    ! [A_128,B_129] :
      ( r1_tarski(A_128,B_129)
      | ~ r1_ordinal1(A_128,B_129)
      | ~ v3_ordinal1(B_129)
      | ~ v3_ordinal1(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_22,plain,(
    ! [B_10,A_9] :
      ( B_10 = A_9
      | ~ r1_tarski(B_10,A_9)
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4309,plain,(
    ! [B_431,A_432] :
      ( B_431 = A_432
      | ~ r1_tarski(B_431,A_432)
      | ~ r1_ordinal1(A_432,B_431)
      | ~ v3_ordinal1(B_431)
      | ~ v3_ordinal1(A_432) ) ),
    inference(resolution,[status(thm)],[c_828,c_22])).

tff(c_40127,plain,(
    ! [B_3294,A_3295] :
      ( B_3294 = A_3295
      | ~ r1_ordinal1(B_3294,A_3295)
      | ~ r1_ordinal1(A_3295,B_3294)
      | ~ v3_ordinal1(B_3294)
      | ~ v3_ordinal1(A_3295) ) ),
    inference(resolution,[status(thm)],[c_66,c_4309])).

tff(c_40163,plain,
    ( '#skF_5' = '#skF_6'
    | ~ r1_ordinal1('#skF_5','#skF_6')
    | ~ v3_ordinal1('#skF_6')
    | ~ v3_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_694,c_40127])).

tff(c_40187,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_113,c_40163])).

tff(c_40195,plain,(
    ~ r2_hidden('#skF_6',k1_ordinal1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40187,c_114])).

tff(c_40200,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_40195])).

tff(c_40201,plain,(
    ~ r1_ordinal1('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_40204,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_40201])).

tff(c_40206,plain,(
    ~ r1_ordinal1('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_40672,plain,(
    ! [B_3371,A_3372] :
      ( r2_hidden(B_3371,A_3372)
      | r1_ordinal1(A_3372,B_3371)
      | ~ v3_ordinal1(B_3371)
      | ~ v3_ordinal1(A_3372) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_40205,plain,(
    r2_hidden('#skF_5',k1_ordinal1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_40581,plain,(
    ! [B_3359,A_3360] :
      ( B_3359 = A_3360
      | r2_hidden(A_3360,B_3359)
      | ~ r2_hidden(A_3360,k1_ordinal1(B_3359)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_40592,plain,
    ( '#skF_5' = '#skF_6'
    | r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_40205,c_40581])).

tff(c_40608,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_40592])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_40611,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_40608,c_2])).

tff(c_40687,plain,
    ( r1_ordinal1('#skF_5','#skF_6')
    | ~ v3_ordinal1('#skF_6')
    | ~ v3_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40672,c_40611])).

tff(c_40761,plain,(
    r1_ordinal1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_40687])).

tff(c_40763,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40206,c_40761])).

tff(c_40764,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_40592])).

tff(c_40768,plain,(
    ~ r1_ordinal1('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40764,c_40206])).

tff(c_40815,plain,(
    ! [B_3377,A_3378] :
      ( r2_hidden(B_3377,A_3378)
      | r1_ordinal1(A_3378,B_3377)
      | ~ v3_ordinal1(B_3377)
      | ~ v3_ordinal1(A_3378) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_40765,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_40592])).

tff(c_40776,plain,(
    ~ r2_hidden('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40764,c_40765])).

tff(c_40826,plain,
    ( r1_ordinal1('#skF_6','#skF_6')
    | ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_40815,c_40776])).

tff(c_40896,plain,(
    r1_ordinal1('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_40826])).

tff(c_40898,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40768,c_40896])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:25:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 22.70/12.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 22.70/12.33  
% 22.70/12.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 22.70/12.33  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k2_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 22.70/12.33  
% 22.70/12.33  %Foreground sorts:
% 22.70/12.33  
% 22.70/12.33  
% 22.70/12.33  %Background operators:
% 22.70/12.33  
% 22.70/12.33  
% 22.70/12.33  %Foreground operators:
% 22.70/12.33  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 22.70/12.33  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 22.70/12.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 22.70/12.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 22.70/12.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 22.70/12.33  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i) > $i).
% 22.70/12.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 22.70/12.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 22.70/12.33  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 22.70/12.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 22.70/12.33  tff('#skF_5', type, '#skF_5': $i).
% 22.70/12.33  tff('#skF_6', type, '#skF_6': $i).
% 22.70/12.33  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 22.70/12.33  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 22.70/12.33  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i) > $i).
% 22.70/12.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 22.70/12.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 22.70/12.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 22.70/12.33  
% 22.70/12.35  tff(f_102, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, k1_ordinal1(B)) <=> r1_ordinal1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_ordinal1)).
% 22.70/12.35  tff(f_83, axiom, (![A, B]: (r2_hidden(A, k1_ordinal1(B)) <=> (r2_hidden(A, B) | (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_ordinal1)).
% 22.70/12.35  tff(f_92, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_ordinal1)).
% 22.70/12.35  tff(f_77, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 22.70/12.35  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 22.70/12.35  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 22.70/12.35  tff(c_86, plain, (r2_hidden('#skF_5', k1_ordinal1('#skF_6')) | r1_ordinal1('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_102])).
% 22.70/12.35  tff(c_113, plain, (r1_ordinal1('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_86])).
% 22.70/12.35  tff(c_70, plain, (![B_26]: (r2_hidden(B_26, k1_ordinal1(B_26)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 22.70/12.35  tff(c_78, plain, (v3_ordinal1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_102])).
% 22.70/12.35  tff(c_76, plain, (v3_ordinal1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_102])).
% 22.70/12.35  tff(c_585, plain, (![B_115, A_116]: (r2_hidden(B_115, A_116) | r1_ordinal1(A_116, B_115) | ~v3_ordinal1(B_115) | ~v3_ordinal1(A_116))), inference(cnfTransformation, [status(thm)], [f_92])).
% 22.70/12.35  tff(c_123, plain, (![A_46, B_47]: (~r2_hidden(A_46, B_47) | r2_hidden(A_46, k1_ordinal1(B_47)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 22.70/12.35  tff(c_80, plain, (~r1_ordinal1('#skF_5', '#skF_6') | ~r2_hidden('#skF_5', k1_ordinal1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 22.70/12.35  tff(c_114, plain, (~r2_hidden('#skF_5', k1_ordinal1('#skF_6'))), inference(splitLeft, [status(thm)], [c_80])).
% 22.70/12.35  tff(c_133, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_123, c_114])).
% 22.70/12.35  tff(c_663, plain, (r1_ordinal1('#skF_6', '#skF_5') | ~v3_ordinal1('#skF_5') | ~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_585, c_133])).
% 22.70/12.35  tff(c_694, plain, (r1_ordinal1('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_78, c_663])).
% 22.70/12.35  tff(c_66, plain, (![A_23, B_24]: (r1_tarski(A_23, B_24) | ~r1_ordinal1(A_23, B_24) | ~v3_ordinal1(B_24) | ~v3_ordinal1(A_23))), inference(cnfTransformation, [status(thm)], [f_77])).
% 22.70/12.35  tff(c_828, plain, (![A_128, B_129]: (r1_tarski(A_128, B_129) | ~r1_ordinal1(A_128, B_129) | ~v3_ordinal1(B_129) | ~v3_ordinal1(A_128))), inference(cnfTransformation, [status(thm)], [f_77])).
% 22.70/12.35  tff(c_22, plain, (![B_10, A_9]: (B_10=A_9 | ~r1_tarski(B_10, A_9) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 22.70/12.35  tff(c_4309, plain, (![B_431, A_432]: (B_431=A_432 | ~r1_tarski(B_431, A_432) | ~r1_ordinal1(A_432, B_431) | ~v3_ordinal1(B_431) | ~v3_ordinal1(A_432))), inference(resolution, [status(thm)], [c_828, c_22])).
% 22.70/12.35  tff(c_40127, plain, (![B_3294, A_3295]: (B_3294=A_3295 | ~r1_ordinal1(B_3294, A_3295) | ~r1_ordinal1(A_3295, B_3294) | ~v3_ordinal1(B_3294) | ~v3_ordinal1(A_3295))), inference(resolution, [status(thm)], [c_66, c_4309])).
% 22.70/12.35  tff(c_40163, plain, ('#skF_5'='#skF_6' | ~r1_ordinal1('#skF_5', '#skF_6') | ~v3_ordinal1('#skF_6') | ~v3_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_694, c_40127])).
% 22.70/12.35  tff(c_40187, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_113, c_40163])).
% 22.70/12.35  tff(c_40195, plain, (~r2_hidden('#skF_6', k1_ordinal1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_40187, c_114])).
% 22.70/12.35  tff(c_40200, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_40195])).
% 22.70/12.35  tff(c_40201, plain, (~r1_ordinal1('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_80])).
% 22.70/12.35  tff(c_40204, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_113, c_40201])).
% 22.70/12.35  tff(c_40206, plain, (~r1_ordinal1('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_86])).
% 22.70/12.35  tff(c_40672, plain, (![B_3371, A_3372]: (r2_hidden(B_3371, A_3372) | r1_ordinal1(A_3372, B_3371) | ~v3_ordinal1(B_3371) | ~v3_ordinal1(A_3372))), inference(cnfTransformation, [status(thm)], [f_92])).
% 22.70/12.35  tff(c_40205, plain, (r2_hidden('#skF_5', k1_ordinal1('#skF_6'))), inference(splitRight, [status(thm)], [c_86])).
% 22.70/12.35  tff(c_40581, plain, (![B_3359, A_3360]: (B_3359=A_3360 | r2_hidden(A_3360, B_3359) | ~r2_hidden(A_3360, k1_ordinal1(B_3359)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 22.70/12.35  tff(c_40592, plain, ('#skF_5'='#skF_6' | r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_40205, c_40581])).
% 22.70/12.35  tff(c_40608, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_40592])).
% 22.70/12.35  tff(c_2, plain, (![B_2, A_1]: (~r2_hidden(B_2, A_1) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 22.70/12.35  tff(c_40611, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_40608, c_2])).
% 22.70/12.35  tff(c_40687, plain, (r1_ordinal1('#skF_5', '#skF_6') | ~v3_ordinal1('#skF_6') | ~v3_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_40672, c_40611])).
% 22.70/12.35  tff(c_40761, plain, (r1_ordinal1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_40687])).
% 22.70/12.35  tff(c_40763, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40206, c_40761])).
% 22.70/12.35  tff(c_40764, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_40592])).
% 22.70/12.35  tff(c_40768, plain, (~r1_ordinal1('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_40764, c_40206])).
% 22.70/12.35  tff(c_40815, plain, (![B_3377, A_3378]: (r2_hidden(B_3377, A_3378) | r1_ordinal1(A_3378, B_3377) | ~v3_ordinal1(B_3377) | ~v3_ordinal1(A_3378))), inference(cnfTransformation, [status(thm)], [f_92])).
% 22.70/12.35  tff(c_40765, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_40592])).
% 22.70/12.35  tff(c_40776, plain, (~r2_hidden('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_40764, c_40765])).
% 22.70/12.35  tff(c_40826, plain, (r1_ordinal1('#skF_6', '#skF_6') | ~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_40815, c_40776])).
% 22.70/12.35  tff(c_40896, plain, (r1_ordinal1('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_40826])).
% 22.70/12.35  tff(c_40898, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40768, c_40896])).
% 22.70/12.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 22.70/12.35  
% 22.70/12.35  Inference rules
% 22.70/12.35  ----------------------
% 22.70/12.35  #Ref     : 0
% 22.70/12.35  #Sup     : 8729
% 22.70/12.35  #Fact    : 62
% 22.70/12.35  #Define  : 0
% 22.70/12.35  #Split   : 5
% 22.70/12.35  #Chain   : 0
% 22.70/12.35  #Close   : 0
% 22.70/12.35  
% 22.70/12.35  Ordering : KBO
% 22.70/12.35  
% 22.70/12.35  Simplification rules
% 22.70/12.35  ----------------------
% 22.70/12.35  #Subsume      : 3007
% 22.70/12.35  #Demod        : 737
% 22.70/12.35  #Tautology    : 265
% 22.70/12.35  #SimpNegUnit  : 172
% 22.70/12.35  #BackRed      : 11
% 22.70/12.35  
% 22.70/12.35  #Partial instantiations: 0
% 22.70/12.35  #Strategies tried      : 1
% 22.70/12.35  
% 22.70/12.35  Timing (in seconds)
% 22.70/12.35  ----------------------
% 22.70/12.35  Preprocessing        : 0.33
% 22.70/12.35  Parsing              : 0.17
% 22.70/12.35  CNF conversion       : 0.03
% 22.70/12.35  Main loop            : 11.25
% 22.70/12.35  Inferencing          : 1.56
% 22.70/12.35  Reduction            : 3.84
% 22.70/12.35  Demodulation         : 1.22
% 22.70/12.35  BG Simplification    : 0.16
% 22.70/12.35  Subsumption          : 5.01
% 22.70/12.35  Abstraction          : 0.25
% 22.70/12.35  MUC search           : 0.00
% 22.70/12.35  Cooper               : 0.00
% 22.70/12.35  Total                : 11.61
% 22.70/12.35  Index Insertion      : 0.00
% 22.70/12.35  Index Deletion       : 0.00
% 22.70/12.35  Index Matching       : 0.00
% 22.70/12.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
