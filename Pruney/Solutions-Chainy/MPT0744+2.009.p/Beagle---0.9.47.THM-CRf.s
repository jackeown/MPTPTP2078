%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:16 EST 2020

% Result     : Theorem 13.70s
% Output     : CNFRefutation 13.70s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 145 expanded)
%              Number of leaves         :   24 (  57 expanded)
%              Depth                    :   10
%              Number of atoms          :  122 ( 305 expanded)
%              Number of equality atoms :    9 (  25 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_1 > #skF_3 > #skF_2 > #skF_4

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_59,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_106,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,k1_ordinal1(B))
            <=> r1_ordinal1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_82,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ~ ( ~ r2_hidden(A,B)
              & A != B
              & ~ r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).

tff(f_96,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_91,axiom,(
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
    ! [B_10] : r1_tarski(B_10,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_71,plain,(
    ! [A_33,B_34] :
      ( r2_hidden(A_33,B_34)
      | ~ r1_tarski(k1_tarski(A_33),B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_76,plain,(
    ! [A_33] : r2_hidden(A_33,k1_tarski(A_33)) ),
    inference(resolution,[status(thm)],[c_26,c_71])).

tff(c_34,plain,(
    ! [A_15] : k2_xboole_0(A_15,k1_tarski(A_15)) = k1_ordinal1(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_100,plain,(
    ! [D_41,B_42,A_43] :
      ( ~ r2_hidden(D_41,B_42)
      | r2_hidden(D_41,k2_xboole_0(A_43,B_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1746,plain,(
    ! [D_151,A_152] :
      ( ~ r2_hidden(D_151,k1_tarski(A_152))
      | r2_hidden(D_151,k1_ordinal1(A_152)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_100])).

tff(c_1790,plain,(
    ! [A_33] : r2_hidden(A_33,k1_ordinal1(A_33)) ),
    inference(resolution,[status(thm)],[c_76,c_1746])).

tff(c_48,plain,(
    v3_ordinal1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_46,plain,(
    v3_ordinal1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_56,plain,
    ( r2_hidden('#skF_3',k1_ordinal1('#skF_4'))
    | r1_ordinal1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_70,plain,(
    r1_ordinal1('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_38,plain,(
    ! [A_16,B_17] :
      ( r1_tarski(A_16,B_17)
      | ~ r1_ordinal1(A_16,B_17)
      | ~ v3_ordinal1(B_17)
      | ~ v3_ordinal1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_650,plain,(
    ! [B_94,A_95] :
      ( r2_hidden(B_94,A_95)
      | B_94 = A_95
      | r2_hidden(A_95,B_94)
      | ~ v3_ordinal1(B_94)
      | ~ v3_ordinal1(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_161,plain,(
    ! [D_57,A_58,B_59] :
      ( ~ r2_hidden(D_57,A_58)
      | r2_hidden(D_57,k2_xboole_0(A_58,B_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_330,plain,(
    ! [D_79,A_80] :
      ( ~ r2_hidden(D_79,A_80)
      | r2_hidden(D_79,k1_ordinal1(A_80)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_161])).

tff(c_50,plain,
    ( ~ r1_ordinal1('#skF_3','#skF_4')
    | ~ r2_hidden('#skF_3',k1_ordinal1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_78,plain,(
    ~ r2_hidden('#skF_3',k1_ordinal1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_50])).

tff(c_399,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_330,c_78])).

tff(c_677,plain,
    ( '#skF_3' = '#skF_4'
    | r2_hidden('#skF_4','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_650,c_399])).

tff(c_837,plain,
    ( '#skF_3' = '#skF_4'
    | r2_hidden('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_48,c_677])).

tff(c_881,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_837])).

tff(c_44,plain,(
    ! [B_25,A_24] :
      ( ~ r1_tarski(B_25,A_24)
      | ~ r2_hidden(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_888,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_881,c_44])).

tff(c_891,plain,
    ( ~ r1_ordinal1('#skF_3','#skF_4')
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_888])).

tff(c_895,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_70,c_891])).

tff(c_896,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_837])).

tff(c_900,plain,(
    ~ r2_hidden('#skF_4',k1_ordinal1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_896,c_78])).

tff(c_1868,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1790,c_900])).

tff(c_1870,plain,(
    ~ r1_ordinal1('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_42,plain,(
    ! [B_23,A_21] :
      ( r2_hidden(B_23,A_21)
      | r1_ordinal1(A_21,B_23)
      | ~ v3_ordinal1(B_23)
      | ~ v3_ordinal1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_30,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(k1_tarski(A_11),B_12)
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1869,plain,(
    r2_hidden('#skF_3',k1_ordinal1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_2557,plain,(
    ! [D_225,B_226,A_227] :
      ( r2_hidden(D_225,B_226)
      | r2_hidden(D_225,A_227)
      | ~ r2_hidden(D_225,k2_xboole_0(A_227,B_226)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4772,plain,(
    ! [D_360,A_361] :
      ( r2_hidden(D_360,k1_tarski(A_361))
      | r2_hidden(D_360,A_361)
      | ~ r2_hidden(D_360,k1_ordinal1(A_361)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_2557])).

tff(c_26031,plain,(
    ! [A_1509,D_1510] :
      ( ~ r1_tarski(k1_tarski(A_1509),D_1510)
      | r2_hidden(D_1510,A_1509)
      | ~ r2_hidden(D_1510,k1_ordinal1(A_1509)) ) ),
    inference(resolution,[status(thm)],[c_4772,c_44])).

tff(c_26119,plain,
    ( ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3')
    | r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_1869,c_26031])).

tff(c_26120,plain,(
    ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_26119])).

tff(c_26130,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_26120])).

tff(c_26138,plain,
    ( r1_ordinal1('#skF_3','#skF_4')
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_26130])).

tff(c_26144,plain,(
    r1_ordinal1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_26138])).

tff(c_26146,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1870,c_26144])).

tff(c_26147,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_26119])).

tff(c_2089,plain,(
    ! [B_193,A_194] :
      ( r2_hidden(B_193,A_194)
      | r1_ordinal1(A_194,B_193)
      | ~ v3_ordinal1(B_193)
      | ~ v3_ordinal1(A_194) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_2168,plain,(
    ! [A_194,B_193] :
      ( ~ r2_hidden(A_194,B_193)
      | r1_ordinal1(A_194,B_193)
      | ~ v3_ordinal1(B_193)
      | ~ v3_ordinal1(A_194) ) ),
    inference(resolution,[status(thm)],[c_2089,c_2])).

tff(c_26151,plain,
    ( r1_ordinal1('#skF_3','#skF_4')
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_26147,c_2168])).

tff(c_26159,plain,(
    r1_ordinal1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_26151])).

tff(c_26161,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1870,c_26159])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:32:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.70/6.76  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.70/6.77  
% 13.70/6.77  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.70/6.77  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 13.70/6.77  
% 13.70/6.77  %Foreground sorts:
% 13.70/6.77  
% 13.70/6.77  
% 13.70/6.77  %Background operators:
% 13.70/6.77  
% 13.70/6.77  
% 13.70/6.77  %Foreground operators:
% 13.70/6.77  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 13.70/6.77  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 13.70/6.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.70/6.77  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.70/6.77  tff(k1_tarski, type, k1_tarski: $i > $i).
% 13.70/6.77  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.70/6.77  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 13.70/6.77  tff('#skF_3', type, '#skF_3': $i).
% 13.70/6.77  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 13.70/6.77  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 13.70/6.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.70/6.77  tff('#skF_4', type, '#skF_4': $i).
% 13.70/6.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.70/6.77  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 13.70/6.77  
% 13.70/6.78  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 13.70/6.78  tff(f_49, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 13.70/6.78  tff(f_59, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_ordinal1)).
% 13.70/6.78  tff(f_39, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 13.70/6.78  tff(f_106, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, k1_ordinal1(B)) <=> r1_ordinal1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_ordinal1)).
% 13.70/6.78  tff(f_67, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 13.70/6.78  tff(f_82, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => ~((~r2_hidden(A, B) & ~(A = B)) & ~r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_ordinal1)).
% 13.70/6.78  tff(f_96, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 13.70/6.78  tff(f_91, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_ordinal1)).
% 13.70/6.78  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 13.70/6.78  tff(c_26, plain, (![B_10]: (r1_tarski(B_10, B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 13.70/6.78  tff(c_71, plain, (![A_33, B_34]: (r2_hidden(A_33, B_34) | ~r1_tarski(k1_tarski(A_33), B_34))), inference(cnfTransformation, [status(thm)], [f_49])).
% 13.70/6.78  tff(c_76, plain, (![A_33]: (r2_hidden(A_33, k1_tarski(A_33)))), inference(resolution, [status(thm)], [c_26, c_71])).
% 13.70/6.78  tff(c_34, plain, (![A_15]: (k2_xboole_0(A_15, k1_tarski(A_15))=k1_ordinal1(A_15))), inference(cnfTransformation, [status(thm)], [f_59])).
% 13.70/6.78  tff(c_100, plain, (![D_41, B_42, A_43]: (~r2_hidden(D_41, B_42) | r2_hidden(D_41, k2_xboole_0(A_43, B_42)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.70/6.78  tff(c_1746, plain, (![D_151, A_152]: (~r2_hidden(D_151, k1_tarski(A_152)) | r2_hidden(D_151, k1_ordinal1(A_152)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_100])).
% 13.70/6.78  tff(c_1790, plain, (![A_33]: (r2_hidden(A_33, k1_ordinal1(A_33)))), inference(resolution, [status(thm)], [c_76, c_1746])).
% 13.70/6.78  tff(c_48, plain, (v3_ordinal1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_106])).
% 13.70/6.78  tff(c_46, plain, (v3_ordinal1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_106])).
% 13.70/6.78  tff(c_56, plain, (r2_hidden('#skF_3', k1_ordinal1('#skF_4')) | r1_ordinal1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_106])).
% 13.70/6.79  tff(c_70, plain, (r1_ordinal1('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_56])).
% 13.70/6.79  tff(c_38, plain, (![A_16, B_17]: (r1_tarski(A_16, B_17) | ~r1_ordinal1(A_16, B_17) | ~v3_ordinal1(B_17) | ~v3_ordinal1(A_16))), inference(cnfTransformation, [status(thm)], [f_67])).
% 13.70/6.79  tff(c_650, plain, (![B_94, A_95]: (r2_hidden(B_94, A_95) | B_94=A_95 | r2_hidden(A_95, B_94) | ~v3_ordinal1(B_94) | ~v3_ordinal1(A_95))), inference(cnfTransformation, [status(thm)], [f_82])).
% 13.70/6.79  tff(c_161, plain, (![D_57, A_58, B_59]: (~r2_hidden(D_57, A_58) | r2_hidden(D_57, k2_xboole_0(A_58, B_59)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.70/6.79  tff(c_330, plain, (![D_79, A_80]: (~r2_hidden(D_79, A_80) | r2_hidden(D_79, k1_ordinal1(A_80)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_161])).
% 13.70/6.79  tff(c_50, plain, (~r1_ordinal1('#skF_3', '#skF_4') | ~r2_hidden('#skF_3', k1_ordinal1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_106])).
% 13.70/6.79  tff(c_78, plain, (~r2_hidden('#skF_3', k1_ordinal1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_50])).
% 13.70/6.79  tff(c_399, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_330, c_78])).
% 13.70/6.79  tff(c_677, plain, ('#skF_3'='#skF_4' | r2_hidden('#skF_4', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_650, c_399])).
% 13.70/6.79  tff(c_837, plain, ('#skF_3'='#skF_4' | r2_hidden('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_48, c_677])).
% 13.70/6.79  tff(c_881, plain, (r2_hidden('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_837])).
% 13.70/6.79  tff(c_44, plain, (![B_25, A_24]: (~r1_tarski(B_25, A_24) | ~r2_hidden(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_96])).
% 13.70/6.79  tff(c_888, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_881, c_44])).
% 13.70/6.79  tff(c_891, plain, (~r1_ordinal1('#skF_3', '#skF_4') | ~v3_ordinal1('#skF_4') | ~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_888])).
% 13.70/6.79  tff(c_895, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_70, c_891])).
% 13.70/6.79  tff(c_896, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_837])).
% 13.70/6.79  tff(c_900, plain, (~r2_hidden('#skF_4', k1_ordinal1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_896, c_78])).
% 13.70/6.79  tff(c_1868, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1790, c_900])).
% 13.70/6.79  tff(c_1870, plain, (~r1_ordinal1('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_56])).
% 13.70/6.79  tff(c_42, plain, (![B_23, A_21]: (r2_hidden(B_23, A_21) | r1_ordinal1(A_21, B_23) | ~v3_ordinal1(B_23) | ~v3_ordinal1(A_21))), inference(cnfTransformation, [status(thm)], [f_91])).
% 13.70/6.79  tff(c_30, plain, (![A_11, B_12]: (r1_tarski(k1_tarski(A_11), B_12) | ~r2_hidden(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_49])).
% 13.70/6.79  tff(c_1869, plain, (r2_hidden('#skF_3', k1_ordinal1('#skF_4'))), inference(splitRight, [status(thm)], [c_56])).
% 13.70/6.79  tff(c_2557, plain, (![D_225, B_226, A_227]: (r2_hidden(D_225, B_226) | r2_hidden(D_225, A_227) | ~r2_hidden(D_225, k2_xboole_0(A_227, B_226)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.70/6.79  tff(c_4772, plain, (![D_360, A_361]: (r2_hidden(D_360, k1_tarski(A_361)) | r2_hidden(D_360, A_361) | ~r2_hidden(D_360, k1_ordinal1(A_361)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_2557])).
% 13.70/6.79  tff(c_26031, plain, (![A_1509, D_1510]: (~r1_tarski(k1_tarski(A_1509), D_1510) | r2_hidden(D_1510, A_1509) | ~r2_hidden(D_1510, k1_ordinal1(A_1509)))), inference(resolution, [status(thm)], [c_4772, c_44])).
% 13.70/6.79  tff(c_26119, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_3') | r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_1869, c_26031])).
% 13.70/6.79  tff(c_26120, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_26119])).
% 13.70/6.79  tff(c_26130, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_30, c_26120])).
% 13.70/6.79  tff(c_26138, plain, (r1_ordinal1('#skF_3', '#skF_4') | ~v3_ordinal1('#skF_4') | ~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_26130])).
% 13.70/6.79  tff(c_26144, plain, (r1_ordinal1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_26138])).
% 13.70/6.79  tff(c_26146, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1870, c_26144])).
% 13.70/6.79  tff(c_26147, plain, (r2_hidden('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_26119])).
% 13.70/6.79  tff(c_2089, plain, (![B_193, A_194]: (r2_hidden(B_193, A_194) | r1_ordinal1(A_194, B_193) | ~v3_ordinal1(B_193) | ~v3_ordinal1(A_194))), inference(cnfTransformation, [status(thm)], [f_91])).
% 13.70/6.79  tff(c_2, plain, (![B_2, A_1]: (~r2_hidden(B_2, A_1) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 13.70/6.79  tff(c_2168, plain, (![A_194, B_193]: (~r2_hidden(A_194, B_193) | r1_ordinal1(A_194, B_193) | ~v3_ordinal1(B_193) | ~v3_ordinal1(A_194))), inference(resolution, [status(thm)], [c_2089, c_2])).
% 13.70/6.79  tff(c_26151, plain, (r1_ordinal1('#skF_3', '#skF_4') | ~v3_ordinal1('#skF_4') | ~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_26147, c_2168])).
% 13.70/6.79  tff(c_26159, plain, (r1_ordinal1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_26151])).
% 13.70/6.79  tff(c_26161, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1870, c_26159])).
% 13.70/6.79  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.70/6.79  
% 13.70/6.79  Inference rules
% 13.70/6.79  ----------------------
% 13.70/6.79  #Ref     : 0
% 13.70/6.79  #Sup     : 5523
% 13.70/6.79  #Fact    : 20
% 13.70/6.79  #Define  : 0
% 13.70/6.79  #Split   : 5
% 13.70/6.79  #Chain   : 0
% 13.70/6.79  #Close   : 0
% 13.70/6.79  
% 13.70/6.79  Ordering : KBO
% 13.70/6.79  
% 13.70/6.79  Simplification rules
% 13.70/6.79  ----------------------
% 13.70/6.79  #Subsume      : 1309
% 13.70/6.79  #Demod        : 104
% 13.70/6.79  #Tautology    : 88
% 13.70/6.79  #SimpNegUnit  : 100
% 13.70/6.79  #BackRed      : 8
% 13.70/6.79  
% 13.70/6.79  #Partial instantiations: 0
% 13.70/6.79  #Strategies tried      : 1
% 13.70/6.79  
% 13.70/6.79  Timing (in seconds)
% 13.70/6.79  ----------------------
% 13.70/6.79  Preprocessing        : 0.30
% 13.70/6.79  Parsing              : 0.17
% 13.70/6.79  CNF conversion       : 0.02
% 13.70/6.79  Main loop            : 5.72
% 13.70/6.79  Inferencing          : 0.83
% 13.70/6.79  Reduction            : 1.58
% 13.70/6.79  Demodulation         : 0.55
% 13.70/6.79  BG Simplification    : 0.12
% 13.70/6.79  Subsumption          : 2.80
% 13.70/6.79  Abstraction          : 0.16
% 13.70/6.79  MUC search           : 0.00
% 13.70/6.79  Cooper               : 0.00
% 13.70/6.79  Total                : 6.05
% 13.70/6.79  Index Insertion      : 0.00
% 13.70/6.79  Index Deletion       : 0.00
% 13.70/6.79  Index Matching       : 0.00
% 13.70/6.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
