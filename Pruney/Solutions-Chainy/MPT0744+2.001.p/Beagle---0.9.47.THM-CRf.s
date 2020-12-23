%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:15 EST 2020

% Result     : Theorem 5.30s
% Output     : CNFRefutation 5.30s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 127 expanded)
%              Number of leaves         :   26 (  52 expanded)
%              Depth                    :    8
%              Number of atoms          :  108 ( 266 expanded)
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

tff(f_104,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,k1_ordinal1(B))
            <=> r1_ordinal1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
        | r1_ordinal1(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( r2_hidden(A,k1_ordinal1(B))
    <=> ( r2_hidden(A,B)
        | A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_52,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( v1_ordinal1(A)
        & v2_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_85,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_xboole_0(A,B)
           => r2_hidden(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_ordinal1)).

tff(f_94,axiom,(
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

tff(c_50,plain,(
    v3_ordinal1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_32,plain,(
    ! [B_13,A_12] :
      ( r1_ordinal1(B_13,A_12)
      | r1_ordinal1(A_12,B_13)
      | ~ v3_ordinal1(B_13)
      | ~ v3_ordinal1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_3844,plain,(
    ! [B_359] :
      ( ~ v3_ordinal1(B_359)
      | r1_ordinal1(B_359,B_359) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_32])).

tff(c_42,plain,(
    ! [B_18] : r2_hidden(B_18,k1_ordinal1(B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_52,plain,(
    v3_ordinal1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_54,plain,
    ( ~ r1_ordinal1('#skF_3','#skF_4')
    | ~ r2_hidden('#skF_3',k1_ordinal1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_81,plain,(
    ~ r2_hidden('#skF_3',k1_ordinal1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_60,plain,
    ( r2_hidden('#skF_3',k1_ordinal1('#skF_4'))
    | r1_ordinal1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_116,plain,(
    r1_ordinal1('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_60])).

tff(c_38,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(A_15,B_16)
      | ~ r1_ordinal1(A_15,B_16)
      | ~ v3_ordinal1(B_16)
      | ~ v3_ordinal1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_63,plain,(
    ! [A_28] :
      ( v1_ordinal1(A_28)
      | ~ v3_ordinal1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_71,plain,(
    v1_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_63])).

tff(c_22,plain,(
    ! [A_9,B_10] :
      ( r2_xboole_0(A_9,B_10)
      | B_10 = A_9
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_598,plain,(
    ! [A_90,B_91] :
      ( r2_hidden(A_90,B_91)
      | ~ r2_xboole_0(A_90,B_91)
      | ~ v3_ordinal1(B_91)
      | ~ v1_ordinal1(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2695,plain,(
    ! [A_271,B_272] :
      ( r2_hidden(A_271,B_272)
      | ~ v3_ordinal1(B_272)
      | ~ v1_ordinal1(A_271)
      | B_272 = A_271
      | ~ r1_tarski(A_271,B_272) ) ),
    inference(resolution,[status(thm)],[c_22,c_598])).

tff(c_96,plain,(
    ! [A_35,B_36] :
      ( ~ r2_hidden(A_35,B_36)
      | r2_hidden(A_35,k1_ordinal1(B_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_103,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_96,c_81])).

tff(c_3023,plain,
    ( ~ v3_ordinal1('#skF_4')
    | ~ v1_ordinal1('#skF_3')
    | '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_2695,c_103])).

tff(c_3118,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_50,c_3023])).

tff(c_3123,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_3118])).

tff(c_3126,plain,
    ( ~ r1_ordinal1('#skF_3','#skF_4')
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_3123])).

tff(c_3130,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_116,c_3126])).

tff(c_3131,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_3118])).

tff(c_3136,plain,(
    ~ r2_hidden('#skF_4',k1_ordinal1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3131,c_81])).

tff(c_3142,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_3136])).

tff(c_3143,plain,(
    ~ r1_ordinal1('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_3615,plain,(
    ! [B_341,A_342] :
      ( r2_hidden(B_341,A_342)
      | r1_ordinal1(A_342,B_341)
      | ~ v3_ordinal1(B_341)
      | ~ v3_ordinal1(A_342) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_3145,plain,(
    r1_ordinal1('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_3146,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3143,c_3145])).

tff(c_3147,plain,(
    r2_hidden('#skF_3',k1_ordinal1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_3395,plain,(
    ! [B_308,A_309] :
      ( B_308 = A_309
      | r2_hidden(A_309,B_308)
      | ~ r2_hidden(A_309,k1_ordinal1(B_308)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_3406,plain,
    ( '#skF_3' = '#skF_4'
    | r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_3147,c_3395])).

tff(c_3409,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_3406])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_3412,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_3409,c_2])).

tff(c_3652,plain,
    ( r1_ordinal1('#skF_3','#skF_4')
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_3615,c_3412])).

tff(c_3723,plain,(
    r1_ordinal1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_3652])).

tff(c_3725,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3143,c_3723])).

tff(c_3726,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_3406])).

tff(c_3730,plain,(
    ~ r1_ordinal1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3726,c_3143])).

tff(c_3847,plain,(
    ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_3844,c_3730])).

tff(c_3851,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_3847])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:04:05 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.30/2.01  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.30/2.01  
% 5.30/2.01  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.30/2.01  %$ r2_xboole_0 > r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 5.30/2.01  
% 5.30/2.01  %Foreground sorts:
% 5.30/2.01  
% 5.30/2.01  
% 5.30/2.01  %Background operators:
% 5.30/2.01  
% 5.30/2.01  
% 5.30/2.01  %Foreground operators:
% 5.30/2.01  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.30/2.01  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 5.30/2.01  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.30/2.01  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.30/2.01  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.30/2.01  tff(v1_ordinal1, type, v1_ordinal1: $i > $o).
% 5.30/2.01  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.30/2.01  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 5.30/2.01  tff('#skF_3', type, '#skF_3': $i).
% 5.30/2.01  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.30/2.01  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 5.30/2.01  tff(v2_ordinal1, type, v2_ordinal1: $i > $o).
% 5.30/2.01  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 5.30/2.01  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.30/2.01  tff('#skF_4', type, '#skF_4': $i).
% 5.30/2.01  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.30/2.01  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.30/2.01  
% 5.30/2.03  tff(f_104, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, k1_ordinal1(B)) <=> r1_ordinal1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_ordinal1)).
% 5.30/2.03  tff(f_60, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) | r1_ordinal1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', connectedness_r1_ordinal1)).
% 5.30/2.03  tff(f_76, axiom, (![A, B]: (r2_hidden(A, k1_ordinal1(B)) <=> (r2_hidden(A, B) | (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_ordinal1)).
% 5.30/2.03  tff(f_70, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 5.30/2.03  tff(f_52, axiom, (![A]: (v3_ordinal1(A) => (v1_ordinal1(A) & v2_ordinal1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_ordinal1)).
% 5.30/2.03  tff(f_46, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 5.30/2.03  tff(f_85, axiom, (![A]: (v1_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_xboole_0(A, B) => r2_hidden(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_ordinal1)).
% 5.30/2.03  tff(f_94, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_ordinal1)).
% 5.30/2.03  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 5.30/2.03  tff(c_50, plain, (v3_ordinal1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.30/2.03  tff(c_32, plain, (![B_13, A_12]: (r1_ordinal1(B_13, A_12) | r1_ordinal1(A_12, B_13) | ~v3_ordinal1(B_13) | ~v3_ordinal1(A_12))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.30/2.03  tff(c_3844, plain, (![B_359]: (~v3_ordinal1(B_359) | r1_ordinal1(B_359, B_359))), inference(factorization, [status(thm), theory('equality')], [c_32])).
% 5.30/2.03  tff(c_42, plain, (![B_18]: (r2_hidden(B_18, k1_ordinal1(B_18)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.30/2.03  tff(c_52, plain, (v3_ordinal1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.30/2.03  tff(c_54, plain, (~r1_ordinal1('#skF_3', '#skF_4') | ~r2_hidden('#skF_3', k1_ordinal1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.30/2.03  tff(c_81, plain, (~r2_hidden('#skF_3', k1_ordinal1('#skF_4'))), inference(splitLeft, [status(thm)], [c_54])).
% 5.30/2.03  tff(c_60, plain, (r2_hidden('#skF_3', k1_ordinal1('#skF_4')) | r1_ordinal1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.30/2.03  tff(c_116, plain, (r1_ordinal1('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_81, c_60])).
% 5.30/2.03  tff(c_38, plain, (![A_15, B_16]: (r1_tarski(A_15, B_16) | ~r1_ordinal1(A_15, B_16) | ~v3_ordinal1(B_16) | ~v3_ordinal1(A_15))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.30/2.03  tff(c_63, plain, (![A_28]: (v1_ordinal1(A_28) | ~v3_ordinal1(A_28))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.30/2.03  tff(c_71, plain, (v1_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_63])).
% 5.30/2.03  tff(c_22, plain, (![A_9, B_10]: (r2_xboole_0(A_9, B_10) | B_10=A_9 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.30/2.03  tff(c_598, plain, (![A_90, B_91]: (r2_hidden(A_90, B_91) | ~r2_xboole_0(A_90, B_91) | ~v3_ordinal1(B_91) | ~v1_ordinal1(A_90))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.30/2.03  tff(c_2695, plain, (![A_271, B_272]: (r2_hidden(A_271, B_272) | ~v3_ordinal1(B_272) | ~v1_ordinal1(A_271) | B_272=A_271 | ~r1_tarski(A_271, B_272))), inference(resolution, [status(thm)], [c_22, c_598])).
% 5.30/2.03  tff(c_96, plain, (![A_35, B_36]: (~r2_hidden(A_35, B_36) | r2_hidden(A_35, k1_ordinal1(B_36)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.30/2.03  tff(c_103, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_96, c_81])).
% 5.30/2.03  tff(c_3023, plain, (~v3_ordinal1('#skF_4') | ~v1_ordinal1('#skF_3') | '#skF_3'='#skF_4' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_2695, c_103])).
% 5.30/2.03  tff(c_3118, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_71, c_50, c_3023])).
% 5.30/2.03  tff(c_3123, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_3118])).
% 5.30/2.03  tff(c_3126, plain, (~r1_ordinal1('#skF_3', '#skF_4') | ~v3_ordinal1('#skF_4') | ~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_3123])).
% 5.30/2.03  tff(c_3130, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_116, c_3126])).
% 5.30/2.03  tff(c_3131, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_3118])).
% 5.30/2.03  tff(c_3136, plain, (~r2_hidden('#skF_4', k1_ordinal1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3131, c_81])).
% 5.30/2.03  tff(c_3142, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_3136])).
% 5.30/2.03  tff(c_3143, plain, (~r1_ordinal1('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_54])).
% 5.30/2.03  tff(c_3615, plain, (![B_341, A_342]: (r2_hidden(B_341, A_342) | r1_ordinal1(A_342, B_341) | ~v3_ordinal1(B_341) | ~v3_ordinal1(A_342))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.30/2.03  tff(c_3145, plain, (r1_ordinal1('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_60])).
% 5.30/2.03  tff(c_3146, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3143, c_3145])).
% 5.30/2.03  tff(c_3147, plain, (r2_hidden('#skF_3', k1_ordinal1('#skF_4'))), inference(splitRight, [status(thm)], [c_60])).
% 5.30/2.03  tff(c_3395, plain, (![B_308, A_309]: (B_308=A_309 | r2_hidden(A_309, B_308) | ~r2_hidden(A_309, k1_ordinal1(B_308)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.30/2.03  tff(c_3406, plain, ('#skF_3'='#skF_4' | r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_3147, c_3395])).
% 5.30/2.03  tff(c_3409, plain, (r2_hidden('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_3406])).
% 5.30/2.03  tff(c_2, plain, (![B_2, A_1]: (~r2_hidden(B_2, A_1) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 5.30/2.03  tff(c_3412, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_3409, c_2])).
% 5.30/2.03  tff(c_3652, plain, (r1_ordinal1('#skF_3', '#skF_4') | ~v3_ordinal1('#skF_4') | ~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_3615, c_3412])).
% 5.30/2.03  tff(c_3723, plain, (r1_ordinal1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_3652])).
% 5.30/2.03  tff(c_3725, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3143, c_3723])).
% 5.30/2.03  tff(c_3726, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_3406])).
% 5.30/2.03  tff(c_3730, plain, (~r1_ordinal1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3726, c_3143])).
% 5.30/2.03  tff(c_3847, plain, (~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_3844, c_3730])).
% 5.30/2.03  tff(c_3851, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_3847])).
% 5.30/2.03  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.30/2.03  
% 5.30/2.03  Inference rules
% 5.30/2.03  ----------------------
% 5.30/2.03  #Ref     : 0
% 5.30/2.03  #Sup     : 768
% 5.30/2.03  #Fact    : 12
% 5.30/2.03  #Define  : 0
% 5.30/2.03  #Split   : 5
% 5.30/2.03  #Chain   : 0
% 5.30/2.03  #Close   : 0
% 5.30/2.03  
% 5.30/2.03  Ordering : KBO
% 5.30/2.03  
% 5.30/2.03  Simplification rules
% 5.30/2.03  ----------------------
% 5.30/2.03  #Subsume      : 93
% 5.30/2.03  #Demod        : 37
% 5.30/2.03  #Tautology    : 31
% 5.30/2.03  #SimpNegUnit  : 14
% 5.30/2.03  #BackRed      : 13
% 5.30/2.03  
% 5.30/2.03  #Partial instantiations: 0
% 5.30/2.03  #Strategies tried      : 1
% 5.30/2.03  
% 5.30/2.03  Timing (in seconds)
% 5.30/2.03  ----------------------
% 5.30/2.03  Preprocessing        : 0.31
% 5.30/2.03  Parsing              : 0.17
% 5.30/2.03  CNF conversion       : 0.02
% 5.30/2.03  Main loop            : 0.96
% 5.30/2.03  Inferencing          : 0.30
% 5.30/2.03  Reduction            : 0.23
% 5.30/2.03  Demodulation         : 0.14
% 5.30/2.03  BG Simplification    : 0.04
% 5.30/2.03  Subsumption          : 0.30
% 5.30/2.03  Abstraction          : 0.04
% 5.30/2.03  MUC search           : 0.00
% 5.30/2.03  Cooper               : 0.00
% 5.30/2.03  Total                : 1.30
% 5.30/2.03  Index Insertion      : 0.00
% 5.30/2.03  Index Deletion       : 0.00
% 5.30/2.03  Index Matching       : 0.00
% 5.30/2.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------
