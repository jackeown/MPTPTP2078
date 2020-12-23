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
% DateTime   : Thu Dec  3 10:06:16 EST 2020

% Result     : Theorem 19.72s
% Output     : CNFRefutation 19.72s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 140 expanded)
%              Number of leaves         :   28 (  58 expanded)
%              Depth                    :    9
%              Number of atoms          :  142 ( 292 expanded)
%              Number of equality atoms :   30 (  66 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_93,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,k1_ordinal1(B))
            <=> r1_ordinal1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_62,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_64,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_60,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_66,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_83,axiom,(
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

tff(c_64,plain,(
    v3_ordinal1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_26,plain,(
    ! [B_10] : r1_tarski(B_10,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_27804,plain,(
    ! [A_2467,B_2468] :
      ( r1_ordinal1(A_2467,B_2468)
      | ~ r1_tarski(A_2467,B_2468)
      | ~ v3_ordinal1(B_2468)
      | ~ v3_ordinal1(A_2467) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_27812,plain,(
    ! [B_10] :
      ( r1_ordinal1(B_10,B_10)
      | ~ v3_ordinal1(B_10) ) ),
    inference(resolution,[status(thm)],[c_26,c_27804])).

tff(c_52,plain,(
    ! [A_18] : k2_tarski(A_18,A_18) = k1_tarski(A_18) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_112,plain,(
    ! [A_51,B_52] : k1_enumset1(A_51,A_51,B_52) = k2_tarski(A_51,B_52) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_34,plain,(
    ! [E_17,B_12,C_13] : r2_hidden(E_17,k1_enumset1(E_17,B_12,C_13)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_140,plain,(
    ! [A_53,B_54] : r2_hidden(A_53,k2_tarski(A_53,B_54)) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_34])).

tff(c_145,plain,(
    ! [A_18] : r2_hidden(A_18,k1_tarski(A_18)) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_140])).

tff(c_56,plain,(
    ! [A_21] : k2_xboole_0(A_21,k1_tarski(A_21)) = k1_ordinal1(A_21) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_206,plain,(
    ! [D_66,B_67,A_68] :
      ( ~ r2_hidden(D_66,B_67)
      | r2_hidden(D_66,k2_xboole_0(A_68,B_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1070,plain,(
    ! [D_151,A_152] :
      ( ~ r2_hidden(D_151,k1_tarski(A_152))
      | r2_hidden(D_151,k1_ordinal1(A_152)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_206])).

tff(c_1079,plain,(
    ! [A_18] : r2_hidden(A_18,k1_ordinal1(A_18)) ),
    inference(resolution,[status(thm)],[c_145,c_1070])).

tff(c_66,plain,(
    v3_ordinal1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_519,plain,(
    ! [B_100,A_101] :
      ( r2_hidden(B_100,A_101)
      | r1_ordinal1(A_101,B_100)
      | ~ v3_ordinal1(B_100)
      | ~ v3_ordinal1(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_152,plain,(
    ! [D_57,A_58,B_59] :
      ( ~ r2_hidden(D_57,A_58)
      | r2_hidden(D_57,k2_xboole_0(A_58,B_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_290,plain,(
    ! [D_77,A_78] :
      ( ~ r2_hidden(D_77,A_78)
      | r2_hidden(D_77,k1_ordinal1(A_78)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_152])).

tff(c_68,plain,
    ( ~ r1_ordinal1('#skF_5','#skF_6')
    | ~ r2_hidden('#skF_5',k1_ordinal1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_108,plain,(
    ~ r2_hidden('#skF_5',k1_ordinal1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_341,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_290,c_108])).

tff(c_550,plain,
    ( r1_ordinal1('#skF_6','#skF_5')
    | ~ v3_ordinal1('#skF_5')
    | ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_519,c_341])).

tff(c_604,plain,(
    r1_ordinal1('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_66,c_550])).

tff(c_74,plain,
    ( r2_hidden('#skF_5',k1_ordinal1('#skF_6'))
    | r1_ordinal1('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_139,plain,(
    r1_ordinal1('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_74])).

tff(c_60,plain,(
    ! [A_22,B_23] :
      ( r1_tarski(A_22,B_23)
      | ~ r1_ordinal1(A_22,B_23)
      | ~ v3_ordinal1(B_23)
      | ~ v3_ordinal1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_343,plain,(
    ! [A_79,B_80] :
      ( r1_tarski(A_79,B_80)
      | ~ r1_ordinal1(A_79,B_80)
      | ~ v3_ordinal1(B_80)
      | ~ v3_ordinal1(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_22,plain,(
    ! [B_10,A_9] :
      ( B_10 = A_9
      | ~ r1_tarski(B_10,A_9)
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_3688,plain,(
    ! [B_363,A_364] :
      ( B_363 = A_364
      | ~ r1_tarski(B_363,A_364)
      | ~ r1_ordinal1(A_364,B_363)
      | ~ v3_ordinal1(B_363)
      | ~ v3_ordinal1(A_364) ) ),
    inference(resolution,[status(thm)],[c_343,c_22])).

tff(c_27488,plain,(
    ! [B_2424,A_2425] :
      ( B_2424 = A_2425
      | ~ r1_ordinal1(B_2424,A_2425)
      | ~ r1_ordinal1(A_2425,B_2424)
      | ~ v3_ordinal1(B_2424)
      | ~ v3_ordinal1(A_2425) ) ),
    inference(resolution,[status(thm)],[c_60,c_3688])).

tff(c_27516,plain,
    ( '#skF_5' = '#skF_6'
    | ~ r1_ordinal1('#skF_6','#skF_5')
    | ~ v3_ordinal1('#skF_5')
    | ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_139,c_27488])).

tff(c_27535,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_66,c_604,c_27516])).

tff(c_27539,plain,(
    ~ r2_hidden('#skF_6',k1_ordinal1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27535,c_108])).

tff(c_27543,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1079,c_27539])).

tff(c_27544,plain,(
    ~ r1_ordinal1('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_27545,plain,(
    r2_hidden('#skF_5',k1_ordinal1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_28026,plain,(
    ! [D_2483,B_2484,A_2485] :
      ( r2_hidden(D_2483,B_2484)
      | r2_hidden(D_2483,A_2485)
      | ~ r2_hidden(D_2483,k2_xboole_0(A_2485,B_2484)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_28039,plain,(
    ! [D_2483,A_21] :
      ( r2_hidden(D_2483,k1_tarski(A_21))
      | r2_hidden(D_2483,A_21)
      | ~ r2_hidden(D_2483,k1_ordinal1(A_21)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_28026])).

tff(c_54,plain,(
    ! [A_19,B_20] : k1_enumset1(A_19,A_19,B_20) = k2_tarski(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_28124,plain,(
    ! [E_2495,C_2496,B_2497,A_2498] :
      ( E_2495 = C_2496
      | E_2495 = B_2497
      | E_2495 = A_2498
      | ~ r2_hidden(E_2495,k1_enumset1(A_2498,B_2497,C_2496)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_29953,plain,(
    ! [E_2681,B_2682,A_2683] :
      ( E_2681 = B_2682
      | E_2681 = A_2683
      | E_2681 = A_2683
      | ~ r2_hidden(E_2681,k2_tarski(A_2683,B_2682)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_28124])).

tff(c_36513,plain,(
    ! [E_3254,A_3255] :
      ( E_3254 = A_3255
      | E_3254 = A_3255
      | E_3254 = A_3255
      | ~ r2_hidden(E_3254,k1_tarski(A_3255)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_29953])).

tff(c_36608,plain,(
    ! [D_3256,A_3257] :
      ( D_3256 = A_3257
      | r2_hidden(D_3256,A_3257)
      | ~ r2_hidden(D_3256,k1_ordinal1(A_3257)) ) ),
    inference(resolution,[status(thm)],[c_28039,c_36513])).

tff(c_36706,plain,
    ( '#skF_5' = '#skF_6'
    | r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_27545,c_36608])).

tff(c_36707,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_36706])).

tff(c_27850,plain,(
    ! [B_2473,A_2474] :
      ( r2_hidden(B_2473,A_2474)
      | r1_ordinal1(A_2474,B_2473)
      | ~ v3_ordinal1(B_2473)
      | ~ v3_ordinal1(A_2474) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_27923,plain,(
    ! [A_2474,B_2473] :
      ( ~ r2_hidden(A_2474,B_2473)
      | r1_ordinal1(A_2474,B_2473)
      | ~ v3_ordinal1(B_2473)
      | ~ v3_ordinal1(A_2474) ) ),
    inference(resolution,[status(thm)],[c_27850,c_2])).

tff(c_36710,plain,
    ( r1_ordinal1('#skF_5','#skF_6')
    | ~ v3_ordinal1('#skF_6')
    | ~ v3_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_36707,c_27923])).

tff(c_36715,plain,(
    r1_ordinal1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_36710])).

tff(c_36717,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_27544,c_36715])).

tff(c_36718,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_36706])).

tff(c_36722,plain,(
    ~ r1_ordinal1('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36718,c_27544])).

tff(c_36739,plain,(
    ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_27812,c_36722])).

tff(c_36743,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_36739])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:25:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 19.72/10.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.72/10.27  
% 19.72/10.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.72/10.27  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 19.72/10.27  
% 19.72/10.27  %Foreground sorts:
% 19.72/10.27  
% 19.72/10.27  
% 19.72/10.27  %Background operators:
% 19.72/10.27  
% 19.72/10.27  
% 19.72/10.27  %Foreground operators:
% 19.72/10.27  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 19.72/10.27  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 19.72/10.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 19.72/10.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 19.72/10.27  tff(k1_tarski, type, k1_tarski: $i > $i).
% 19.72/10.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 19.72/10.27  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 19.72/10.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 19.72/10.27  tff('#skF_5', type, '#skF_5': $i).
% 19.72/10.27  tff('#skF_6', type, '#skF_6': $i).
% 19.72/10.27  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 19.72/10.27  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 19.72/10.27  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 19.72/10.27  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 19.72/10.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 19.72/10.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 19.72/10.27  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 19.72/10.27  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 19.72/10.27  
% 19.72/10.28  tff(f_93, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, k1_ordinal1(B)) <=> r1_ordinal1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_ordinal1)).
% 19.72/10.28  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 19.72/10.28  tff(f_74, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 19.72/10.28  tff(f_62, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 19.72/10.28  tff(f_64, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 19.72/10.28  tff(f_60, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 19.72/10.28  tff(f_66, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_ordinal1)).
% 19.72/10.28  tff(f_39, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 19.72/10.28  tff(f_83, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_ordinal1)).
% 19.72/10.28  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 19.72/10.28  tff(c_64, plain, (v3_ordinal1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_93])).
% 19.72/10.28  tff(c_26, plain, (![B_10]: (r1_tarski(B_10, B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 19.72/10.28  tff(c_27804, plain, (![A_2467, B_2468]: (r1_ordinal1(A_2467, B_2468) | ~r1_tarski(A_2467, B_2468) | ~v3_ordinal1(B_2468) | ~v3_ordinal1(A_2467))), inference(cnfTransformation, [status(thm)], [f_74])).
% 19.72/10.28  tff(c_27812, plain, (![B_10]: (r1_ordinal1(B_10, B_10) | ~v3_ordinal1(B_10))), inference(resolution, [status(thm)], [c_26, c_27804])).
% 19.72/10.28  tff(c_52, plain, (![A_18]: (k2_tarski(A_18, A_18)=k1_tarski(A_18))), inference(cnfTransformation, [status(thm)], [f_62])).
% 19.72/10.28  tff(c_112, plain, (![A_51, B_52]: (k1_enumset1(A_51, A_51, B_52)=k2_tarski(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_64])).
% 19.72/10.28  tff(c_34, plain, (![E_17, B_12, C_13]: (r2_hidden(E_17, k1_enumset1(E_17, B_12, C_13)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 19.72/10.28  tff(c_140, plain, (![A_53, B_54]: (r2_hidden(A_53, k2_tarski(A_53, B_54)))), inference(superposition, [status(thm), theory('equality')], [c_112, c_34])).
% 19.72/10.28  tff(c_145, plain, (![A_18]: (r2_hidden(A_18, k1_tarski(A_18)))), inference(superposition, [status(thm), theory('equality')], [c_52, c_140])).
% 19.72/10.28  tff(c_56, plain, (![A_21]: (k2_xboole_0(A_21, k1_tarski(A_21))=k1_ordinal1(A_21))), inference(cnfTransformation, [status(thm)], [f_66])).
% 19.72/10.28  tff(c_206, plain, (![D_66, B_67, A_68]: (~r2_hidden(D_66, B_67) | r2_hidden(D_66, k2_xboole_0(A_68, B_67)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 19.72/10.28  tff(c_1070, plain, (![D_151, A_152]: (~r2_hidden(D_151, k1_tarski(A_152)) | r2_hidden(D_151, k1_ordinal1(A_152)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_206])).
% 19.72/10.28  tff(c_1079, plain, (![A_18]: (r2_hidden(A_18, k1_ordinal1(A_18)))), inference(resolution, [status(thm)], [c_145, c_1070])).
% 19.72/10.28  tff(c_66, plain, (v3_ordinal1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_93])).
% 19.72/10.28  tff(c_519, plain, (![B_100, A_101]: (r2_hidden(B_100, A_101) | r1_ordinal1(A_101, B_100) | ~v3_ordinal1(B_100) | ~v3_ordinal1(A_101))), inference(cnfTransformation, [status(thm)], [f_83])).
% 19.72/10.28  tff(c_152, plain, (![D_57, A_58, B_59]: (~r2_hidden(D_57, A_58) | r2_hidden(D_57, k2_xboole_0(A_58, B_59)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 19.72/10.28  tff(c_290, plain, (![D_77, A_78]: (~r2_hidden(D_77, A_78) | r2_hidden(D_77, k1_ordinal1(A_78)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_152])).
% 19.72/10.28  tff(c_68, plain, (~r1_ordinal1('#skF_5', '#skF_6') | ~r2_hidden('#skF_5', k1_ordinal1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 19.72/10.28  tff(c_108, plain, (~r2_hidden('#skF_5', k1_ordinal1('#skF_6'))), inference(splitLeft, [status(thm)], [c_68])).
% 19.72/10.28  tff(c_341, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_290, c_108])).
% 19.72/10.28  tff(c_550, plain, (r1_ordinal1('#skF_6', '#skF_5') | ~v3_ordinal1('#skF_5') | ~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_519, c_341])).
% 19.72/10.28  tff(c_604, plain, (r1_ordinal1('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_66, c_550])).
% 19.72/10.28  tff(c_74, plain, (r2_hidden('#skF_5', k1_ordinal1('#skF_6')) | r1_ordinal1('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_93])).
% 19.72/10.28  tff(c_139, plain, (r1_ordinal1('#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_108, c_74])).
% 19.72/10.28  tff(c_60, plain, (![A_22, B_23]: (r1_tarski(A_22, B_23) | ~r1_ordinal1(A_22, B_23) | ~v3_ordinal1(B_23) | ~v3_ordinal1(A_22))), inference(cnfTransformation, [status(thm)], [f_74])).
% 19.72/10.28  tff(c_343, plain, (![A_79, B_80]: (r1_tarski(A_79, B_80) | ~r1_ordinal1(A_79, B_80) | ~v3_ordinal1(B_80) | ~v3_ordinal1(A_79))), inference(cnfTransformation, [status(thm)], [f_74])).
% 19.72/10.28  tff(c_22, plain, (![B_10, A_9]: (B_10=A_9 | ~r1_tarski(B_10, A_9) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 19.72/10.28  tff(c_3688, plain, (![B_363, A_364]: (B_363=A_364 | ~r1_tarski(B_363, A_364) | ~r1_ordinal1(A_364, B_363) | ~v3_ordinal1(B_363) | ~v3_ordinal1(A_364))), inference(resolution, [status(thm)], [c_343, c_22])).
% 19.72/10.28  tff(c_27488, plain, (![B_2424, A_2425]: (B_2424=A_2425 | ~r1_ordinal1(B_2424, A_2425) | ~r1_ordinal1(A_2425, B_2424) | ~v3_ordinal1(B_2424) | ~v3_ordinal1(A_2425))), inference(resolution, [status(thm)], [c_60, c_3688])).
% 19.72/10.28  tff(c_27516, plain, ('#skF_5'='#skF_6' | ~r1_ordinal1('#skF_6', '#skF_5') | ~v3_ordinal1('#skF_5') | ~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_139, c_27488])).
% 19.72/10.28  tff(c_27535, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_66, c_604, c_27516])).
% 19.72/10.28  tff(c_27539, plain, (~r2_hidden('#skF_6', k1_ordinal1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_27535, c_108])).
% 19.72/10.28  tff(c_27543, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1079, c_27539])).
% 19.72/10.28  tff(c_27544, plain, (~r1_ordinal1('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_68])).
% 19.72/10.28  tff(c_27545, plain, (r2_hidden('#skF_5', k1_ordinal1('#skF_6'))), inference(splitRight, [status(thm)], [c_68])).
% 19.72/10.28  tff(c_28026, plain, (![D_2483, B_2484, A_2485]: (r2_hidden(D_2483, B_2484) | r2_hidden(D_2483, A_2485) | ~r2_hidden(D_2483, k2_xboole_0(A_2485, B_2484)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 19.72/10.28  tff(c_28039, plain, (![D_2483, A_21]: (r2_hidden(D_2483, k1_tarski(A_21)) | r2_hidden(D_2483, A_21) | ~r2_hidden(D_2483, k1_ordinal1(A_21)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_28026])).
% 19.72/10.28  tff(c_54, plain, (![A_19, B_20]: (k1_enumset1(A_19, A_19, B_20)=k2_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_64])).
% 19.72/10.28  tff(c_28124, plain, (![E_2495, C_2496, B_2497, A_2498]: (E_2495=C_2496 | E_2495=B_2497 | E_2495=A_2498 | ~r2_hidden(E_2495, k1_enumset1(A_2498, B_2497, C_2496)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 19.72/10.28  tff(c_29953, plain, (![E_2681, B_2682, A_2683]: (E_2681=B_2682 | E_2681=A_2683 | E_2681=A_2683 | ~r2_hidden(E_2681, k2_tarski(A_2683, B_2682)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_28124])).
% 19.72/10.28  tff(c_36513, plain, (![E_3254, A_3255]: (E_3254=A_3255 | E_3254=A_3255 | E_3254=A_3255 | ~r2_hidden(E_3254, k1_tarski(A_3255)))), inference(superposition, [status(thm), theory('equality')], [c_52, c_29953])).
% 19.72/10.28  tff(c_36608, plain, (![D_3256, A_3257]: (D_3256=A_3257 | r2_hidden(D_3256, A_3257) | ~r2_hidden(D_3256, k1_ordinal1(A_3257)))), inference(resolution, [status(thm)], [c_28039, c_36513])).
% 19.72/10.28  tff(c_36706, plain, ('#skF_5'='#skF_6' | r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_27545, c_36608])).
% 19.72/10.28  tff(c_36707, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_36706])).
% 19.72/10.28  tff(c_27850, plain, (![B_2473, A_2474]: (r2_hidden(B_2473, A_2474) | r1_ordinal1(A_2474, B_2473) | ~v3_ordinal1(B_2473) | ~v3_ordinal1(A_2474))), inference(cnfTransformation, [status(thm)], [f_83])).
% 19.72/10.28  tff(c_2, plain, (![B_2, A_1]: (~r2_hidden(B_2, A_1) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 19.72/10.28  tff(c_27923, plain, (![A_2474, B_2473]: (~r2_hidden(A_2474, B_2473) | r1_ordinal1(A_2474, B_2473) | ~v3_ordinal1(B_2473) | ~v3_ordinal1(A_2474))), inference(resolution, [status(thm)], [c_27850, c_2])).
% 19.72/10.28  tff(c_36710, plain, (r1_ordinal1('#skF_5', '#skF_6') | ~v3_ordinal1('#skF_6') | ~v3_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_36707, c_27923])).
% 19.72/10.28  tff(c_36715, plain, (r1_ordinal1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_36710])).
% 19.72/10.28  tff(c_36717, plain, $false, inference(negUnitSimplification, [status(thm)], [c_27544, c_36715])).
% 19.72/10.28  tff(c_36718, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_36706])).
% 19.72/10.28  tff(c_36722, plain, (~r1_ordinal1('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_36718, c_27544])).
% 19.72/10.28  tff(c_36739, plain, (~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_27812, c_36722])).
% 19.72/10.28  tff(c_36743, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_36739])).
% 19.72/10.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.72/10.28  
% 19.72/10.28  Inference rules
% 19.72/10.28  ----------------------
% 19.72/10.28  #Ref     : 0
% 19.72/10.28  #Sup     : 7756
% 19.72/10.28  #Fact    : 52
% 19.72/10.28  #Define  : 0
% 19.72/10.29  #Split   : 4
% 19.72/10.29  #Chain   : 0
% 19.72/10.29  #Close   : 0
% 19.72/10.29  
% 19.72/10.29  Ordering : KBO
% 19.72/10.29  
% 19.72/10.29  Simplification rules
% 19.72/10.29  ----------------------
% 19.72/10.29  #Subsume      : 2345
% 19.72/10.29  #Demod        : 487
% 19.72/10.29  #Tautology    : 119
% 19.72/10.29  #SimpNegUnit  : 161
% 19.72/10.29  #BackRed      : 11
% 19.72/10.29  
% 19.72/10.29  #Partial instantiations: 0
% 19.72/10.29  #Strategies tried      : 1
% 19.72/10.29  
% 19.72/10.29  Timing (in seconds)
% 19.72/10.29  ----------------------
% 19.72/10.29  Preprocessing        : 0.48
% 19.72/10.29  Parsing              : 0.24
% 19.72/10.29  CNF conversion       : 0.04
% 19.72/10.29  Main loop            : 8.88
% 19.72/10.29  Inferencing          : 1.56
% 19.72/10.29  Reduction            : 2.60
% 19.72/10.29  Demodulation         : 1.10
% 19.72/10.29  BG Simplification    : 0.17
% 19.72/10.29  Subsumption          : 3.91
% 19.72/10.29  Abstraction          : 0.22
% 19.72/10.29  MUC search           : 0.00
% 19.72/10.29  Cooper               : 0.00
% 19.72/10.29  Total                : 9.40
% 19.72/10.29  Index Insertion      : 0.00
% 19.72/10.29  Index Deletion       : 0.00
% 19.72/10.29  Index Matching       : 0.00
% 19.72/10.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
