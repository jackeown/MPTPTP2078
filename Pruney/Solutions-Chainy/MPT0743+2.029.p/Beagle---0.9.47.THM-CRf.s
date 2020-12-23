%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:12 EST 2020

% Result     : Theorem 6.03s
% Output     : CNFRefutation 6.03s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 228 expanded)
%              Number of leaves         :   25 (  83 expanded)
%              Depth                    :   17
%              Number of atoms          :  148 ( 548 expanded)
%              Number of equality atoms :    6 (  12 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(v2_ordinal1,type,(
    v2_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_89,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,B)
            <=> r1_ordinal1(k1_ordinal1(A),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_ordinal1)).

tff(f_74,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v3_ordinal1(k1_ordinal1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( r2_hidden(A,k1_ordinal1(B))
    <=> ( r2_hidden(A,B)
        | A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).

tff(f_79,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_38,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( v1_ordinal1(A)
        & v2_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
    <=> ! [B] :
          ( r2_hidden(B,A)
         => r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_ordinal1)).

tff(f_70,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r1_ordinal1(A,B)
            | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3081,plain,(
    ! [A_238,B_239] :
      ( ~ r2_hidden('#skF_1'(A_238,B_239),B_239)
      | r1_tarski(A_238,B_239) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3090,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_3081])).

tff(c_38,plain,(
    v3_ordinal1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_32,plain,(
    ! [A_19] :
      ( v3_ordinal1(k1_ordinal1(A_19))
      | ~ v3_ordinal1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_40,plain,
    ( ~ r1_ordinal1(k1_ordinal1('#skF_3'),'#skF_4')
    | ~ r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_66,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_36,plain,(
    v3_ordinal1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_46,plain,
    ( r2_hidden('#skF_3','#skF_4')
    | r1_ordinal1(k1_ordinal1('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_99,plain,(
    r1_ordinal1(k1_ordinal1('#skF_3'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_46])).

tff(c_359,plain,(
    ! [A_76,B_77] :
      ( r1_tarski(A_76,B_77)
      | ~ r1_ordinal1(A_76,B_77)
      | ~ v3_ordinal1(B_77)
      | ~ v3_ordinal1(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_26,plain,(
    ! [B_15] : r2_hidden(B_15,k1_ordinal1(B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_203,plain,(
    ! [C_57,B_58,A_59] :
      ( r2_hidden(C_57,B_58)
      | ~ r2_hidden(C_57,A_59)
      | ~ r1_tarski(A_59,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_215,plain,(
    ! [B_15,B_58] :
      ( r2_hidden(B_15,B_58)
      | ~ r1_tarski(k1_ordinal1(B_15),B_58) ) ),
    inference(resolution,[status(thm)],[c_26,c_203])).

tff(c_2958,plain,(
    ! [B_217,B_218] :
      ( r2_hidden(B_217,B_218)
      | ~ r1_ordinal1(k1_ordinal1(B_217),B_218)
      | ~ v3_ordinal1(B_218)
      | ~ v3_ordinal1(k1_ordinal1(B_217)) ) ),
    inference(resolution,[status(thm)],[c_359,c_215])).

tff(c_2980,plain,
    ( r2_hidden('#skF_3','#skF_4')
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1(k1_ordinal1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_99,c_2958])).

tff(c_2991,plain,
    ( r2_hidden('#skF_3','#skF_4')
    | ~ v3_ordinal1(k1_ordinal1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2980])).

tff(c_2992,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_2991])).

tff(c_2995,plain,(
    ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_2992])).

tff(c_2999,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_2995])).

tff(c_3001,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_3026,plain,(
    ! [B_225,A_226] :
      ( ~ r1_tarski(B_225,A_226)
      | ~ r2_hidden(A_226,B_225) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_3037,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_3001,c_3026])).

tff(c_48,plain,(
    ! [A_24] :
      ( v1_ordinal1(A_24)
      | ~ v3_ordinal1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_56,plain,(
    v1_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_48])).

tff(c_55,plain,(
    v1_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_48])).

tff(c_3047,plain,(
    ! [B_233,A_234] :
      ( r1_tarski(B_233,A_234)
      | ~ r2_hidden(B_233,A_234)
      | ~ v1_ordinal1(A_234) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_3056,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | ~ v1_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_3001,c_3047])).

tff(c_3064,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_3056])).

tff(c_3211,plain,(
    ! [B_257,A_258] :
      ( r2_hidden(B_257,A_258)
      | r1_ordinal1(A_258,B_257)
      | ~ v3_ordinal1(B_257)
      | ~ v3_ordinal1(A_258) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4773,plain,(
    ! [B_333,B_334,A_335] :
      ( r2_hidden(B_333,B_334)
      | ~ r1_tarski(A_335,B_334)
      | r1_ordinal1(A_335,B_333)
      | ~ v3_ordinal1(B_333)
      | ~ v3_ordinal1(A_335) ) ),
    inference(resolution,[status(thm)],[c_3211,c_2])).

tff(c_4797,plain,(
    ! [B_333] :
      ( r2_hidden(B_333,'#skF_4')
      | r1_ordinal1('#skF_3',B_333)
      | ~ v3_ordinal1(B_333)
      | ~ v3_ordinal1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_3064,c_4773])).

tff(c_4818,plain,(
    ! [B_336] :
      ( r2_hidden(B_336,'#skF_4')
      | r1_ordinal1('#skF_3',B_336)
      | ~ v3_ordinal1(B_336) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_4797])).

tff(c_14,plain,(
    ! [B_11,A_8] :
      ( r1_tarski(B_11,A_8)
      | ~ r2_hidden(B_11,A_8)
      | ~ v1_ordinal1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4859,plain,(
    ! [B_336] :
      ( r1_tarski(B_336,'#skF_4')
      | ~ v1_ordinal1('#skF_4')
      | r1_ordinal1('#skF_3',B_336)
      | ~ v3_ordinal1(B_336) ) ),
    inference(resolution,[status(thm)],[c_4818,c_14])).

tff(c_4881,plain,(
    ! [B_337] :
      ( r1_tarski(B_337,'#skF_4')
      | r1_ordinal1('#skF_3',B_337)
      | ~ v3_ordinal1(B_337) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_4859])).

tff(c_20,plain,(
    ! [A_12,B_13] :
      ( r1_ordinal1(A_12,B_13)
      | ~ r1_tarski(A_12,B_13)
      | ~ v3_ordinal1(B_13)
      | ~ v3_ordinal1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_4943,plain,(
    ! [B_337] :
      ( r1_ordinal1(B_337,'#skF_4')
      | ~ v3_ordinal1('#skF_4')
      | r1_ordinal1('#skF_3',B_337)
      | ~ v3_ordinal1(B_337) ) ),
    inference(resolution,[status(thm)],[c_4881,c_20])).

tff(c_5005,plain,(
    ! [B_338] :
      ( r1_ordinal1(B_338,'#skF_4')
      | r1_ordinal1('#skF_3',B_338)
      | ~ v3_ordinal1(B_338) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_4943])).

tff(c_3000,plain,(
    ~ r1_ordinal1(k1_ordinal1('#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_5019,plain,
    ( r1_ordinal1('#skF_3',k1_ordinal1('#skF_3'))
    | ~ v3_ordinal1(k1_ordinal1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_5005,c_3000])).

tff(c_5023,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_5019])).

tff(c_5026,plain,(
    ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_5023])).

tff(c_5030,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_5026])).

tff(c_5032,plain,(
    v3_ordinal1(k1_ordinal1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_5019])).

tff(c_24,plain,(
    ! [B_15,A_14] :
      ( B_15 = A_14
      | r2_hidden(A_14,B_15)
      | ~ r2_hidden(A_14,k1_ordinal1(B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_5304,plain,(
    ! [B_355,B_354] :
      ( B_355 = B_354
      | r2_hidden(B_354,B_355)
      | r1_ordinal1(k1_ordinal1(B_355),B_354)
      | ~ v3_ordinal1(B_354)
      | ~ v3_ordinal1(k1_ordinal1(B_355)) ) ),
    inference(resolution,[status(thm)],[c_3211,c_24])).

tff(c_5321,plain,
    ( '#skF_3' = '#skF_4'
    | r2_hidden('#skF_4','#skF_3')
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1(k1_ordinal1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_5304,c_3000])).

tff(c_5335,plain,
    ( '#skF_3' = '#skF_4'
    | r2_hidden('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5032,c_36,c_5321])).

tff(c_5336,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_5335])).

tff(c_5341,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | ~ v1_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_5336,c_14])).

tff(c_5348,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_5341])).

tff(c_5350,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3037,c_5348])).

tff(c_5351,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_5335])).

tff(c_5400,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5351,c_3037])).

tff(c_5417,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3090,c_5400])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:17:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.03/2.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.03/2.19  
% 6.03/2.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.03/2.19  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 6.03/2.19  
% 6.03/2.19  %Foreground sorts:
% 6.03/2.19  
% 6.03/2.19  
% 6.03/2.19  %Background operators:
% 6.03/2.19  
% 6.03/2.19  
% 6.03/2.19  %Foreground operators:
% 6.03/2.19  tff('#skF_2', type, '#skF_2': $i > $i).
% 6.03/2.19  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 6.03/2.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.03/2.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.03/2.19  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.03/2.19  tff(v1_ordinal1, type, v1_ordinal1: $i > $o).
% 6.03/2.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.03/2.19  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 6.03/2.19  tff('#skF_3', type, '#skF_3': $i).
% 6.03/2.19  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 6.03/2.19  tff(v2_ordinal1, type, v2_ordinal1: $i > $o).
% 6.03/2.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.03/2.19  tff('#skF_4', type, '#skF_4': $i).
% 6.03/2.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.03/2.19  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.03/2.19  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.03/2.19  
% 6.03/2.21  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 6.03/2.21  tff(f_89, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, B) <=> r1_ordinal1(k1_ordinal1(A), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_ordinal1)).
% 6.03/2.21  tff(f_74, axiom, (![A]: (v3_ordinal1(A) => v3_ordinal1(k1_ordinal1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_ordinal1)).
% 6.03/2.21  tff(f_55, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 6.03/2.21  tff(f_61, axiom, (![A, B]: (r2_hidden(A, k1_ordinal1(B)) <=> (r2_hidden(A, B) | (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_ordinal1)).
% 6.03/2.21  tff(f_79, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 6.03/2.21  tff(f_38, axiom, (![A]: (v3_ordinal1(A) => (v1_ordinal1(A) & v2_ordinal1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_ordinal1)).
% 6.03/2.21  tff(f_47, axiom, (![A]: (v1_ordinal1(A) <=> (![B]: (r2_hidden(B, A) => r1_tarski(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_ordinal1)).
% 6.03/2.21  tff(f_70, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_ordinal1)).
% 6.03/2.21  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.03/2.21  tff(c_3081, plain, (![A_238, B_239]: (~r2_hidden('#skF_1'(A_238, B_239), B_239) | r1_tarski(A_238, B_239))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.03/2.21  tff(c_3090, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_3081])).
% 6.03/2.21  tff(c_38, plain, (v3_ordinal1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.03/2.21  tff(c_32, plain, (![A_19]: (v3_ordinal1(k1_ordinal1(A_19)) | ~v3_ordinal1(A_19))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.03/2.21  tff(c_40, plain, (~r1_ordinal1(k1_ordinal1('#skF_3'), '#skF_4') | ~r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.03/2.21  tff(c_66, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_40])).
% 6.03/2.21  tff(c_36, plain, (v3_ordinal1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.03/2.21  tff(c_46, plain, (r2_hidden('#skF_3', '#skF_4') | r1_ordinal1(k1_ordinal1('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.03/2.21  tff(c_99, plain, (r1_ordinal1(k1_ordinal1('#skF_3'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_66, c_46])).
% 6.03/2.21  tff(c_359, plain, (![A_76, B_77]: (r1_tarski(A_76, B_77) | ~r1_ordinal1(A_76, B_77) | ~v3_ordinal1(B_77) | ~v3_ordinal1(A_76))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.03/2.21  tff(c_26, plain, (![B_15]: (r2_hidden(B_15, k1_ordinal1(B_15)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.03/2.21  tff(c_203, plain, (![C_57, B_58, A_59]: (r2_hidden(C_57, B_58) | ~r2_hidden(C_57, A_59) | ~r1_tarski(A_59, B_58))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.03/2.21  tff(c_215, plain, (![B_15, B_58]: (r2_hidden(B_15, B_58) | ~r1_tarski(k1_ordinal1(B_15), B_58))), inference(resolution, [status(thm)], [c_26, c_203])).
% 6.03/2.21  tff(c_2958, plain, (![B_217, B_218]: (r2_hidden(B_217, B_218) | ~r1_ordinal1(k1_ordinal1(B_217), B_218) | ~v3_ordinal1(B_218) | ~v3_ordinal1(k1_ordinal1(B_217)))), inference(resolution, [status(thm)], [c_359, c_215])).
% 6.03/2.21  tff(c_2980, plain, (r2_hidden('#skF_3', '#skF_4') | ~v3_ordinal1('#skF_4') | ~v3_ordinal1(k1_ordinal1('#skF_3'))), inference(resolution, [status(thm)], [c_99, c_2958])).
% 6.03/2.21  tff(c_2991, plain, (r2_hidden('#skF_3', '#skF_4') | ~v3_ordinal1(k1_ordinal1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_2980])).
% 6.03/2.21  tff(c_2992, plain, (~v3_ordinal1(k1_ordinal1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_66, c_2991])).
% 6.03/2.21  tff(c_2995, plain, (~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_2992])).
% 6.03/2.21  tff(c_2999, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_2995])).
% 6.03/2.21  tff(c_3001, plain, (r2_hidden('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_40])).
% 6.03/2.21  tff(c_3026, plain, (![B_225, A_226]: (~r1_tarski(B_225, A_226) | ~r2_hidden(A_226, B_225))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.03/2.21  tff(c_3037, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_3001, c_3026])).
% 6.03/2.21  tff(c_48, plain, (![A_24]: (v1_ordinal1(A_24) | ~v3_ordinal1(A_24))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.03/2.21  tff(c_56, plain, (v1_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_48])).
% 6.03/2.21  tff(c_55, plain, (v1_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_48])).
% 6.03/2.21  tff(c_3047, plain, (![B_233, A_234]: (r1_tarski(B_233, A_234) | ~r2_hidden(B_233, A_234) | ~v1_ordinal1(A_234))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.03/2.21  tff(c_3056, plain, (r1_tarski('#skF_3', '#skF_4') | ~v1_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_3001, c_3047])).
% 6.03/2.21  tff(c_3064, plain, (r1_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_55, c_3056])).
% 6.03/2.21  tff(c_3211, plain, (![B_257, A_258]: (r2_hidden(B_257, A_258) | r1_ordinal1(A_258, B_257) | ~v3_ordinal1(B_257) | ~v3_ordinal1(A_258))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.03/2.21  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.03/2.21  tff(c_4773, plain, (![B_333, B_334, A_335]: (r2_hidden(B_333, B_334) | ~r1_tarski(A_335, B_334) | r1_ordinal1(A_335, B_333) | ~v3_ordinal1(B_333) | ~v3_ordinal1(A_335))), inference(resolution, [status(thm)], [c_3211, c_2])).
% 6.03/2.21  tff(c_4797, plain, (![B_333]: (r2_hidden(B_333, '#skF_4') | r1_ordinal1('#skF_3', B_333) | ~v3_ordinal1(B_333) | ~v3_ordinal1('#skF_3'))), inference(resolution, [status(thm)], [c_3064, c_4773])).
% 6.03/2.21  tff(c_4818, plain, (![B_336]: (r2_hidden(B_336, '#skF_4') | r1_ordinal1('#skF_3', B_336) | ~v3_ordinal1(B_336))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_4797])).
% 6.03/2.21  tff(c_14, plain, (![B_11, A_8]: (r1_tarski(B_11, A_8) | ~r2_hidden(B_11, A_8) | ~v1_ordinal1(A_8))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.03/2.21  tff(c_4859, plain, (![B_336]: (r1_tarski(B_336, '#skF_4') | ~v1_ordinal1('#skF_4') | r1_ordinal1('#skF_3', B_336) | ~v3_ordinal1(B_336))), inference(resolution, [status(thm)], [c_4818, c_14])).
% 6.03/2.21  tff(c_4881, plain, (![B_337]: (r1_tarski(B_337, '#skF_4') | r1_ordinal1('#skF_3', B_337) | ~v3_ordinal1(B_337))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_4859])).
% 6.03/2.21  tff(c_20, plain, (![A_12, B_13]: (r1_ordinal1(A_12, B_13) | ~r1_tarski(A_12, B_13) | ~v3_ordinal1(B_13) | ~v3_ordinal1(A_12))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.03/2.21  tff(c_4943, plain, (![B_337]: (r1_ordinal1(B_337, '#skF_4') | ~v3_ordinal1('#skF_4') | r1_ordinal1('#skF_3', B_337) | ~v3_ordinal1(B_337))), inference(resolution, [status(thm)], [c_4881, c_20])).
% 6.03/2.21  tff(c_5005, plain, (![B_338]: (r1_ordinal1(B_338, '#skF_4') | r1_ordinal1('#skF_3', B_338) | ~v3_ordinal1(B_338))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_4943])).
% 6.03/2.21  tff(c_3000, plain, (~r1_ordinal1(k1_ordinal1('#skF_3'), '#skF_4')), inference(splitRight, [status(thm)], [c_40])).
% 6.03/2.21  tff(c_5019, plain, (r1_ordinal1('#skF_3', k1_ordinal1('#skF_3')) | ~v3_ordinal1(k1_ordinal1('#skF_3'))), inference(resolution, [status(thm)], [c_5005, c_3000])).
% 6.03/2.21  tff(c_5023, plain, (~v3_ordinal1(k1_ordinal1('#skF_3'))), inference(splitLeft, [status(thm)], [c_5019])).
% 6.03/2.21  tff(c_5026, plain, (~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_5023])).
% 6.03/2.21  tff(c_5030, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_5026])).
% 6.03/2.21  tff(c_5032, plain, (v3_ordinal1(k1_ordinal1('#skF_3'))), inference(splitRight, [status(thm)], [c_5019])).
% 6.03/2.21  tff(c_24, plain, (![B_15, A_14]: (B_15=A_14 | r2_hidden(A_14, B_15) | ~r2_hidden(A_14, k1_ordinal1(B_15)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.03/2.21  tff(c_5304, plain, (![B_355, B_354]: (B_355=B_354 | r2_hidden(B_354, B_355) | r1_ordinal1(k1_ordinal1(B_355), B_354) | ~v3_ordinal1(B_354) | ~v3_ordinal1(k1_ordinal1(B_355)))), inference(resolution, [status(thm)], [c_3211, c_24])).
% 6.03/2.21  tff(c_5321, plain, ('#skF_3'='#skF_4' | r2_hidden('#skF_4', '#skF_3') | ~v3_ordinal1('#skF_4') | ~v3_ordinal1(k1_ordinal1('#skF_3'))), inference(resolution, [status(thm)], [c_5304, c_3000])).
% 6.03/2.21  tff(c_5335, plain, ('#skF_3'='#skF_4' | r2_hidden('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5032, c_36, c_5321])).
% 6.03/2.21  tff(c_5336, plain, (r2_hidden('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_5335])).
% 6.03/2.21  tff(c_5341, plain, (r1_tarski('#skF_4', '#skF_3') | ~v1_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_5336, c_14])).
% 6.03/2.21  tff(c_5348, plain, (r1_tarski('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_5341])).
% 6.03/2.21  tff(c_5350, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3037, c_5348])).
% 6.03/2.21  tff(c_5351, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_5335])).
% 6.03/2.21  tff(c_5400, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5351, c_3037])).
% 6.03/2.21  tff(c_5417, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3090, c_5400])).
% 6.03/2.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.03/2.21  
% 6.03/2.21  Inference rules
% 6.03/2.21  ----------------------
% 6.03/2.21  #Ref     : 0
% 6.03/2.21  #Sup     : 1083
% 6.03/2.21  #Fact    : 0
% 6.03/2.21  #Define  : 0
% 6.03/2.21  #Split   : 7
% 6.03/2.21  #Chain   : 0
% 6.03/2.21  #Close   : 0
% 6.03/2.21  
% 6.03/2.21  Ordering : KBO
% 6.03/2.21  
% 6.03/2.21  Simplification rules
% 6.03/2.21  ----------------------
% 6.03/2.21  #Subsume      : 249
% 6.03/2.21  #Demod        : 273
% 6.03/2.21  #Tautology    : 120
% 6.03/2.21  #SimpNegUnit  : 17
% 6.03/2.21  #BackRed      : 55
% 6.03/2.21  
% 6.03/2.21  #Partial instantiations: 0
% 6.03/2.21  #Strategies tried      : 1
% 6.03/2.21  
% 6.03/2.21  Timing (in seconds)
% 6.03/2.21  ----------------------
% 6.03/2.21  Preprocessing        : 0.30
% 6.03/2.21  Parsing              : 0.17
% 6.03/2.21  CNF conversion       : 0.02
% 6.03/2.22  Main loop            : 1.09
% 6.03/2.22  Inferencing          : 0.37
% 6.03/2.22  Reduction            : 0.29
% 6.03/2.22  Demodulation         : 0.18
% 6.03/2.22  BG Simplification    : 0.04
% 6.03/2.22  Subsumption          : 0.30
% 6.03/2.22  Abstraction          : 0.05
% 6.03/2.22  MUC search           : 0.00
% 6.03/2.22  Cooper               : 0.00
% 6.03/2.22  Total                : 1.43
% 6.03/2.22  Index Insertion      : 0.00
% 6.03/2.22  Index Deletion       : 0.00
% 6.03/2.22  Index Matching       : 0.00
% 6.03/2.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
