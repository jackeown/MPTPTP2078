%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:13 EST 2020

% Result     : Theorem 11.95s
% Output     : CNFRefutation 11.95s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 123 expanded)
%              Number of leaves         :   27 (  52 expanded)
%              Depth                    :   11
%              Number of atoms          :  123 ( 262 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_93,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,B)
            <=> r1_ordinal1(k1_ordinal1(A),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_ordinal1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_78,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v3_ordinal1(k1_ordinal1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).

tff(f_74,axiom,(
    ! [A] : r2_hidden(A,k1_ordinal1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_83,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
        | r1_ordinal1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_64,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_38,plain,(
    v3_ordinal1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_40,plain,(
    v3_ordinal1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_4012,plain,(
    ! [A_344,B_345] :
      ( r1_tarski(A_344,B_345)
      | ~ r1_ordinal1(A_344,B_345)
      | ~ v3_ordinal1(B_345)
      | ~ v3_ordinal1(A_344) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_34,plain,(
    ! [A_28] :
      ( v3_ordinal1(k1_ordinal1(A_28))
      | ~ v3_ordinal1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_42,plain,
    ( ~ r1_ordinal1(k1_ordinal1('#skF_2'),'#skF_3')
    | ~ r2_hidden('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_76,plain,(
    ~ r2_hidden('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_48,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | r1_ordinal1(k1_ordinal1('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_77,plain,(
    r1_ordinal1(k1_ordinal1('#skF_2'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_48])).

tff(c_30,plain,(
    ! [A_25,B_26] :
      ( r1_tarski(A_25,B_26)
      | ~ r1_ordinal1(A_25,B_26)
      | ~ v3_ordinal1(B_26)
      | ~ v3_ordinal1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_32,plain,(
    ! [A_27] : r2_hidden(A_27,k1_ordinal1(A_27)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_184,plain,(
    ! [C_62,B_63,A_64] :
      ( r2_hidden(C_62,B_63)
      | ~ r2_hidden(C_62,A_64)
      | ~ r1_tarski(A_64,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_548,plain,(
    ! [A_99,B_100] :
      ( r2_hidden(A_99,B_100)
      | ~ r1_tarski(k1_ordinal1(A_99),B_100) ) ),
    inference(resolution,[status(thm)],[c_32,c_184])).

tff(c_3394,plain,(
    ! [A_275,B_276] :
      ( r2_hidden(A_275,B_276)
      | ~ r1_ordinal1(k1_ordinal1(A_275),B_276)
      | ~ v3_ordinal1(B_276)
      | ~ v3_ordinal1(k1_ordinal1(A_275)) ) ),
    inference(resolution,[status(thm)],[c_30,c_548])).

tff(c_3409,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_77,c_3394])).

tff(c_3416,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_3409])).

tff(c_3417,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_3416])).

tff(c_3420,plain,(
    ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_3417])).

tff(c_3424,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_3420])).

tff(c_3426,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_36,plain,(
    ! [B_30,A_29] :
      ( ~ r1_tarski(B_30,A_29)
      | ~ r2_hidden(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_3430,plain,(
    ~ r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_3426,c_36])).

tff(c_4066,plain,
    ( ~ r1_ordinal1('#skF_3','#skF_2')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4012,c_3430])).

tff(c_4095,plain,(
    ~ r1_ordinal1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_40,c_4066])).

tff(c_24,plain,(
    ! [B_23,A_22] :
      ( r1_ordinal1(B_23,A_22)
      | r1_ordinal1(A_22,B_23)
      | ~ v3_ordinal1(B_23)
      | ~ v3_ordinal1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_3805,plain,(
    ! [B_327,A_328] :
      ( r1_ordinal1(B_327,A_328)
      | r1_ordinal1(A_328,B_327)
      | ~ v3_ordinal1(B_327)
      | ~ v3_ordinal1(A_328) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_3425,plain,(
    ~ r1_ordinal1(k1_ordinal1('#skF_2'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_3811,plain,
    ( r1_ordinal1('#skF_3',k1_ordinal1('#skF_2'))
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_3805,c_3425])).

tff(c_3817,plain,
    ( r1_ordinal1('#skF_3',k1_ordinal1('#skF_2'))
    | ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_3811])).

tff(c_3838,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_3817])).

tff(c_3841,plain,(
    ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_3838])).

tff(c_3845,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_3841])).

tff(c_3847,plain,(
    v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_3817])).

tff(c_20,plain,(
    ! [A_18,B_19] :
      ( r1_tarski(k1_tarski(A_18),B_19)
      | ~ r2_hidden(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_26,plain,(
    ! [A_24] : k2_xboole_0(A_24,k1_tarski(A_24)) = k1_ordinal1(A_24) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_4226,plain,(
    ! [A_357,C_358,B_359] :
      ( r1_tarski(k2_xboole_0(A_357,C_358),B_359)
      | ~ r1_tarski(C_358,B_359)
      | ~ r1_tarski(A_357,B_359) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_4571,plain,(
    ! [A_384,B_385] :
      ( r1_tarski(k1_ordinal1(A_384),B_385)
      | ~ r1_tarski(k1_tarski(A_384),B_385)
      | ~ r1_tarski(A_384,B_385) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_4226])).

tff(c_6519,plain,(
    ! [A_489,B_490] :
      ( r1_tarski(k1_ordinal1(A_489),B_490)
      | ~ r1_tarski(A_489,B_490)
      | ~ r2_hidden(A_489,B_490) ) ),
    inference(resolution,[status(thm)],[c_20,c_4571])).

tff(c_28,plain,(
    ! [A_25,B_26] :
      ( r1_ordinal1(A_25,B_26)
      | ~ r1_tarski(A_25,B_26)
      | ~ v3_ordinal1(B_26)
      | ~ v3_ordinal1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_21240,plain,(
    ! [A_992,B_993] :
      ( r1_ordinal1(k1_ordinal1(A_992),B_993)
      | ~ v3_ordinal1(B_993)
      | ~ v3_ordinal1(k1_ordinal1(A_992))
      | ~ r1_tarski(A_992,B_993)
      | ~ r2_hidden(A_992,B_993) ) ),
    inference(resolution,[status(thm)],[c_6519,c_28])).

tff(c_21267,plain,
    ( ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1(k1_ordinal1('#skF_2'))
    | ~ r1_tarski('#skF_2','#skF_3')
    | ~ r2_hidden('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_21240,c_3425])).

tff(c_21285,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3426,c_3847,c_38,c_21267])).

tff(c_21288,plain,
    ( ~ r1_ordinal1('#skF_2','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_21285])).

tff(c_21291,plain,(
    ~ r1_ordinal1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_21288])).

tff(c_21297,plain,
    ( r1_ordinal1('#skF_3','#skF_2')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_21291])).

tff(c_21306,plain,(
    r1_ordinal1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_40,c_21297])).

tff(c_21308,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4095,c_21306])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:31:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.95/5.04  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.95/5.05  
% 11.95/5.05  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.95/5.05  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_2 > #skF_3 > #skF_1
% 11.95/5.05  
% 11.95/5.05  %Foreground sorts:
% 11.95/5.05  
% 11.95/5.05  
% 11.95/5.05  %Background operators:
% 11.95/5.05  
% 11.95/5.05  
% 11.95/5.05  %Foreground operators:
% 11.95/5.05  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 11.95/5.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.95/5.05  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.95/5.05  tff(k1_tarski, type, k1_tarski: $i > $i).
% 11.95/5.05  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.95/5.05  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 11.95/5.05  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 11.95/5.05  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.95/5.05  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 11.95/5.05  tff('#skF_2', type, '#skF_2': $i).
% 11.95/5.05  tff('#skF_3', type, '#skF_3': $i).
% 11.95/5.05  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 11.95/5.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.95/5.05  tff(k3_tarski, type, k3_tarski: $i > $i).
% 11.95/5.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.95/5.05  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.95/5.05  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 11.95/5.05  
% 11.95/5.06  tff(f_93, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, B) <=> r1_ordinal1(k1_ordinal1(A), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_ordinal1)).
% 11.95/5.06  tff(f_72, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 11.95/5.06  tff(f_78, axiom, (![A]: (v3_ordinal1(A) => v3_ordinal1(k1_ordinal1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_ordinal1)).
% 11.95/5.06  tff(f_74, axiom, (![A]: r2_hidden(A, k1_ordinal1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_ordinal1)).
% 11.95/5.06  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 11.95/5.06  tff(f_83, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 11.95/5.06  tff(f_62, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) | r1_ordinal1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', connectedness_r1_ordinal1)).
% 11.95/5.06  tff(f_52, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 11.95/5.06  tff(f_64, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_ordinal1)).
% 11.95/5.06  tff(f_42, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 11.95/5.06  tff(c_38, plain, (v3_ordinal1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_93])).
% 11.95/5.06  tff(c_40, plain, (v3_ordinal1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_93])).
% 11.95/5.06  tff(c_4012, plain, (![A_344, B_345]: (r1_tarski(A_344, B_345) | ~r1_ordinal1(A_344, B_345) | ~v3_ordinal1(B_345) | ~v3_ordinal1(A_344))), inference(cnfTransformation, [status(thm)], [f_72])).
% 11.95/5.06  tff(c_34, plain, (![A_28]: (v3_ordinal1(k1_ordinal1(A_28)) | ~v3_ordinal1(A_28))), inference(cnfTransformation, [status(thm)], [f_78])).
% 11.95/5.06  tff(c_42, plain, (~r1_ordinal1(k1_ordinal1('#skF_2'), '#skF_3') | ~r2_hidden('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_93])).
% 11.95/5.06  tff(c_76, plain, (~r2_hidden('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_42])).
% 11.95/5.06  tff(c_48, plain, (r2_hidden('#skF_2', '#skF_3') | r1_ordinal1(k1_ordinal1('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_93])).
% 11.95/5.06  tff(c_77, plain, (r1_ordinal1(k1_ordinal1('#skF_2'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_76, c_48])).
% 11.95/5.06  tff(c_30, plain, (![A_25, B_26]: (r1_tarski(A_25, B_26) | ~r1_ordinal1(A_25, B_26) | ~v3_ordinal1(B_26) | ~v3_ordinal1(A_25))), inference(cnfTransformation, [status(thm)], [f_72])).
% 11.95/5.06  tff(c_32, plain, (![A_27]: (r2_hidden(A_27, k1_ordinal1(A_27)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 11.95/5.06  tff(c_184, plain, (![C_62, B_63, A_64]: (r2_hidden(C_62, B_63) | ~r2_hidden(C_62, A_64) | ~r1_tarski(A_64, B_63))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.95/5.06  tff(c_548, plain, (![A_99, B_100]: (r2_hidden(A_99, B_100) | ~r1_tarski(k1_ordinal1(A_99), B_100))), inference(resolution, [status(thm)], [c_32, c_184])).
% 11.95/5.06  tff(c_3394, plain, (![A_275, B_276]: (r2_hidden(A_275, B_276) | ~r1_ordinal1(k1_ordinal1(A_275), B_276) | ~v3_ordinal1(B_276) | ~v3_ordinal1(k1_ordinal1(A_275)))), inference(resolution, [status(thm)], [c_30, c_548])).
% 11.95/5.06  tff(c_3409, plain, (r2_hidden('#skF_2', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(resolution, [status(thm)], [c_77, c_3394])).
% 11.95/5.06  tff(c_3416, plain, (r2_hidden('#skF_2', '#skF_3') | ~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_3409])).
% 11.95/5.06  tff(c_3417, plain, (~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_76, c_3416])).
% 11.95/5.06  tff(c_3420, plain, (~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_34, c_3417])).
% 11.95/5.06  tff(c_3424, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_3420])).
% 11.95/5.06  tff(c_3426, plain, (r2_hidden('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_42])).
% 11.95/5.06  tff(c_36, plain, (![B_30, A_29]: (~r1_tarski(B_30, A_29) | ~r2_hidden(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_83])).
% 11.95/5.06  tff(c_3430, plain, (~r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_3426, c_36])).
% 11.95/5.06  tff(c_4066, plain, (~r1_ordinal1('#skF_3', '#skF_2') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_4012, c_3430])).
% 11.95/5.06  tff(c_4095, plain, (~r1_ordinal1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_40, c_4066])).
% 11.95/5.06  tff(c_24, plain, (![B_23, A_22]: (r1_ordinal1(B_23, A_22) | r1_ordinal1(A_22, B_23) | ~v3_ordinal1(B_23) | ~v3_ordinal1(A_22))), inference(cnfTransformation, [status(thm)], [f_62])).
% 11.95/5.06  tff(c_3805, plain, (![B_327, A_328]: (r1_ordinal1(B_327, A_328) | r1_ordinal1(A_328, B_327) | ~v3_ordinal1(B_327) | ~v3_ordinal1(A_328))), inference(cnfTransformation, [status(thm)], [f_62])).
% 11.95/5.06  tff(c_3425, plain, (~r1_ordinal1(k1_ordinal1('#skF_2'), '#skF_3')), inference(splitRight, [status(thm)], [c_42])).
% 11.95/5.06  tff(c_3811, plain, (r1_ordinal1('#skF_3', k1_ordinal1('#skF_2')) | ~v3_ordinal1('#skF_3') | ~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(resolution, [status(thm)], [c_3805, c_3425])).
% 11.95/5.06  tff(c_3817, plain, (r1_ordinal1('#skF_3', k1_ordinal1('#skF_2')) | ~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_3811])).
% 11.95/5.06  tff(c_3838, plain, (~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(splitLeft, [status(thm)], [c_3817])).
% 11.95/5.06  tff(c_3841, plain, (~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_34, c_3838])).
% 11.95/5.06  tff(c_3845, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_3841])).
% 11.95/5.06  tff(c_3847, plain, (v3_ordinal1(k1_ordinal1('#skF_2'))), inference(splitRight, [status(thm)], [c_3817])).
% 11.95/5.06  tff(c_20, plain, (![A_18, B_19]: (r1_tarski(k1_tarski(A_18), B_19) | ~r2_hidden(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_52])).
% 11.95/5.06  tff(c_26, plain, (![A_24]: (k2_xboole_0(A_24, k1_tarski(A_24))=k1_ordinal1(A_24))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.95/5.06  tff(c_4226, plain, (![A_357, C_358, B_359]: (r1_tarski(k2_xboole_0(A_357, C_358), B_359) | ~r1_tarski(C_358, B_359) | ~r1_tarski(A_357, B_359))), inference(cnfTransformation, [status(thm)], [f_42])).
% 11.95/5.06  tff(c_4571, plain, (![A_384, B_385]: (r1_tarski(k1_ordinal1(A_384), B_385) | ~r1_tarski(k1_tarski(A_384), B_385) | ~r1_tarski(A_384, B_385))), inference(superposition, [status(thm), theory('equality')], [c_26, c_4226])).
% 11.95/5.06  tff(c_6519, plain, (![A_489, B_490]: (r1_tarski(k1_ordinal1(A_489), B_490) | ~r1_tarski(A_489, B_490) | ~r2_hidden(A_489, B_490))), inference(resolution, [status(thm)], [c_20, c_4571])).
% 11.95/5.06  tff(c_28, plain, (![A_25, B_26]: (r1_ordinal1(A_25, B_26) | ~r1_tarski(A_25, B_26) | ~v3_ordinal1(B_26) | ~v3_ordinal1(A_25))), inference(cnfTransformation, [status(thm)], [f_72])).
% 11.95/5.06  tff(c_21240, plain, (![A_992, B_993]: (r1_ordinal1(k1_ordinal1(A_992), B_993) | ~v3_ordinal1(B_993) | ~v3_ordinal1(k1_ordinal1(A_992)) | ~r1_tarski(A_992, B_993) | ~r2_hidden(A_992, B_993))), inference(resolution, [status(thm)], [c_6519, c_28])).
% 11.95/5.06  tff(c_21267, plain, (~v3_ordinal1('#skF_3') | ~v3_ordinal1(k1_ordinal1('#skF_2')) | ~r1_tarski('#skF_2', '#skF_3') | ~r2_hidden('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_21240, c_3425])).
% 11.95/5.06  tff(c_21285, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3426, c_3847, c_38, c_21267])).
% 11.95/5.06  tff(c_21288, plain, (~r1_ordinal1('#skF_2', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_30, c_21285])).
% 11.95/5.06  tff(c_21291, plain, (~r1_ordinal1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_21288])).
% 11.95/5.06  tff(c_21297, plain, (r1_ordinal1('#skF_3', '#skF_2') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_24, c_21291])).
% 11.95/5.06  tff(c_21306, plain, (r1_ordinal1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_40, c_21297])).
% 11.95/5.06  tff(c_21308, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4095, c_21306])).
% 11.95/5.06  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.95/5.06  
% 11.95/5.06  Inference rules
% 11.95/5.06  ----------------------
% 11.95/5.06  #Ref     : 0
% 11.95/5.06  #Sup     : 4482
% 11.95/5.06  #Fact    : 6
% 11.95/5.06  #Define  : 0
% 11.95/5.06  #Split   : 5
% 11.95/5.06  #Chain   : 0
% 11.95/5.06  #Close   : 0
% 11.95/5.06  
% 11.95/5.06  Ordering : KBO
% 11.95/5.06  
% 11.95/5.06  Simplification rules
% 11.95/5.06  ----------------------
% 11.95/5.06  #Subsume      : 684
% 11.95/5.06  #Demod        : 739
% 11.95/5.06  #Tautology    : 471
% 11.95/5.06  #SimpNegUnit  : 3
% 11.95/5.06  #BackRed      : 0
% 11.95/5.06  
% 11.95/5.06  #Partial instantiations: 0
% 11.95/5.06  #Strategies tried      : 1
% 11.95/5.06  
% 11.95/5.06  Timing (in seconds)
% 11.95/5.06  ----------------------
% 11.95/5.06  Preprocessing        : 0.32
% 11.95/5.06  Parsing              : 0.17
% 11.95/5.06  CNF conversion       : 0.02
% 11.95/5.06  Main loop            : 3.99
% 11.95/5.06  Inferencing          : 0.88
% 11.95/5.06  Reduction            : 1.59
% 11.95/5.06  Demodulation         : 1.15
% 11.95/5.06  BG Simplification    : 0.08
% 11.95/5.06  Subsumption          : 1.18
% 11.95/5.06  Abstraction          : 0.09
% 11.95/5.06  MUC search           : 0.00
% 11.95/5.07  Cooper               : 0.00
% 11.95/5.07  Total                : 4.34
% 11.95/5.07  Index Insertion      : 0.00
% 11.95/5.07  Index Deletion       : 0.00
% 11.95/5.07  Index Matching       : 0.00
% 11.95/5.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
