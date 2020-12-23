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
% DateTime   : Thu Dec  3 10:06:17 EST 2020

% Result     : Theorem 11.63s
% Output     : CNFRefutation 11.63s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 117 expanded)
%              Number of leaves         :   23 (  48 expanded)
%              Depth                    :    9
%              Number of atoms          :  102 ( 242 expanded)
%              Number of equality atoms :   10 (  22 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_1 > #skF_3 > #skF_2 > #skF_4

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_86,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,k1_ordinal1(B))
            <=> r1_ordinal1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( r2_hidden(A,k1_ordinal1(B))
    <=> ( r2_hidden(A,B)
        | A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).

tff(f_76,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r1_ordinal1(A,B)
            | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

tff(f_61,axiom,(
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

tff(c_58,plain,
    ( r2_hidden('#skF_3',k1_ordinal1('#skF_4'))
    | r1_ordinal1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_85,plain,(
    r1_ordinal1('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_42,plain,(
    ! [B_20] : r2_hidden(B_20,k1_ordinal1(B_20)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_50,plain,(
    v3_ordinal1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_48,plain,(
    v3_ordinal1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_446,plain,(
    ! [B_73,A_74] :
      ( r2_hidden(B_73,A_74)
      | r1_ordinal1(A_74,B_73)
      | ~ v3_ordinal1(B_73)
      | ~ v3_ordinal1(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_96,plain,(
    ! [A_34,B_35] :
      ( ~ r2_hidden(A_34,B_35)
      | r2_hidden(A_34,k1_ordinal1(B_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_52,plain,
    ( ~ r1_ordinal1('#skF_3','#skF_4')
    | ~ r2_hidden('#skF_3',k1_ordinal1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_86,plain,(
    ~ r2_hidden('#skF_3',k1_ordinal1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_106,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_96,c_86])).

tff(c_511,plain,
    ( r1_ordinal1('#skF_4','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_446,c_106])).

tff(c_539,plain,(
    r1_ordinal1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_50,c_511])).

tff(c_38,plain,(
    ! [A_17,B_18] :
      ( r1_tarski(A_17,B_18)
      | ~ r1_ordinal1(A_17,B_18)
      | ~ v3_ordinal1(B_18)
      | ~ v3_ordinal1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_422,plain,(
    ! [A_69,B_70] :
      ( r1_tarski(A_69,B_70)
      | ~ r1_ordinal1(A_69,B_70)
      | ~ v3_ordinal1(B_70)
      | ~ v3_ordinal1(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_22,plain,(
    ! [B_10,A_9] :
      ( B_10 = A_9
      | ~ r1_tarski(B_10,A_9)
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2082,plain,(
    ! [B_162,A_163] :
      ( B_162 = A_163
      | ~ r1_tarski(B_162,A_163)
      | ~ r1_ordinal1(A_163,B_162)
      | ~ v3_ordinal1(B_162)
      | ~ v3_ordinal1(A_163) ) ),
    inference(resolution,[status(thm)],[c_422,c_22])).

tff(c_14991,plain,(
    ! [B_1097,A_1098] :
      ( B_1097 = A_1098
      | ~ r1_ordinal1(B_1097,A_1098)
      | ~ r1_ordinal1(A_1098,B_1097)
      | ~ v3_ordinal1(B_1097)
      | ~ v3_ordinal1(A_1098) ) ),
    inference(resolution,[status(thm)],[c_38,c_2082])).

tff(c_15009,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_ordinal1('#skF_3','#skF_4')
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_539,c_14991])).

tff(c_15023,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_85,c_15009])).

tff(c_15029,plain,(
    ~ r2_hidden('#skF_4',k1_ordinal1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15023,c_86])).

tff(c_15034,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_15029])).

tff(c_15035,plain,(
    ~ r1_ordinal1('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_15038,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_15035])).

tff(c_15040,plain,(
    ~ r1_ordinal1('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_15412,plain,(
    ! [B_1138,A_1139] :
      ( r2_hidden(B_1138,A_1139)
      | r1_ordinal1(A_1139,B_1138)
      | ~ v3_ordinal1(B_1138)
      | ~ v3_ordinal1(A_1139) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_15039,plain,(
    r2_hidden('#skF_3',k1_ordinal1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_15373,plain,(
    ! [B_1133,A_1134] :
      ( B_1133 = A_1134
      | r2_hidden(A_1134,B_1133)
      | ~ r2_hidden(A_1134,k1_ordinal1(B_1133)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_15384,plain,
    ( '#skF_3' = '#skF_4'
    | r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_15039,c_15373])).

tff(c_15387,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_15384])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_15390,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_15387,c_2])).

tff(c_15422,plain,
    ( r1_ordinal1('#skF_3','#skF_4')
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_15412,c_15390])).

tff(c_15491,plain,(
    r1_ordinal1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_15422])).

tff(c_15493,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15040,c_15491])).

tff(c_15494,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_15384])).

tff(c_15498,plain,(
    ~ r1_ordinal1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15494,c_15040])).

tff(c_15507,plain,(
    ! [B_1140,A_1141] :
      ( r2_hidden(B_1140,A_1141)
      | r1_ordinal1(A_1141,B_1140)
      | ~ v3_ordinal1(B_1140)
      | ~ v3_ordinal1(A_1141) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_15495,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_15384])).

tff(c_15506,plain,(
    ~ r2_hidden('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15494,c_15495])).

tff(c_15510,plain,
    ( r1_ordinal1('#skF_4','#skF_4')
    | ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_15507,c_15506])).

tff(c_15574,plain,(
    r1_ordinal1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_15510])).

tff(c_15576,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15498,c_15574])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:56:46 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.63/4.57  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.63/4.58  
% 11.63/4.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.63/4.58  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 11.63/4.58  
% 11.63/4.58  %Foreground sorts:
% 11.63/4.58  
% 11.63/4.58  
% 11.63/4.58  %Background operators:
% 11.63/4.58  
% 11.63/4.58  
% 11.63/4.58  %Foreground operators:
% 11.63/4.58  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 11.63/4.58  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 11.63/4.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.63/4.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.63/4.58  tff(k1_tarski, type, k1_tarski: $i > $i).
% 11.63/4.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.63/4.58  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 11.63/4.58  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.63/4.58  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 11.63/4.58  tff('#skF_3', type, '#skF_3': $i).
% 11.63/4.58  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 11.63/4.58  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 11.63/4.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.63/4.58  tff(k3_tarski, type, k3_tarski: $i > $i).
% 11.63/4.58  tff('#skF_4', type, '#skF_4': $i).
% 11.63/4.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.63/4.58  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.63/4.58  
% 11.63/4.59  tff(f_86, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, k1_ordinal1(B)) <=> r1_ordinal1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_ordinal1)).
% 11.63/4.59  tff(f_67, axiom, (![A, B]: (r2_hidden(A, k1_ordinal1(B)) <=> (r2_hidden(A, B) | (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_ordinal1)).
% 11.63/4.59  tff(f_76, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_ordinal1)).
% 11.63/4.59  tff(f_61, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 11.63/4.59  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 11.63/4.59  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 11.63/4.59  tff(c_58, plain, (r2_hidden('#skF_3', k1_ordinal1('#skF_4')) | r1_ordinal1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_86])).
% 11.63/4.59  tff(c_85, plain, (r1_ordinal1('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_58])).
% 11.63/4.59  tff(c_42, plain, (![B_20]: (r2_hidden(B_20, k1_ordinal1(B_20)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 11.63/4.59  tff(c_50, plain, (v3_ordinal1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 11.63/4.59  tff(c_48, plain, (v3_ordinal1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_86])).
% 11.63/4.59  tff(c_446, plain, (![B_73, A_74]: (r2_hidden(B_73, A_74) | r1_ordinal1(A_74, B_73) | ~v3_ordinal1(B_73) | ~v3_ordinal1(A_74))), inference(cnfTransformation, [status(thm)], [f_76])).
% 11.63/4.59  tff(c_96, plain, (![A_34, B_35]: (~r2_hidden(A_34, B_35) | r2_hidden(A_34, k1_ordinal1(B_35)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 11.63/4.59  tff(c_52, plain, (~r1_ordinal1('#skF_3', '#skF_4') | ~r2_hidden('#skF_3', k1_ordinal1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 11.63/4.59  tff(c_86, plain, (~r2_hidden('#skF_3', k1_ordinal1('#skF_4'))), inference(splitLeft, [status(thm)], [c_52])).
% 11.63/4.59  tff(c_106, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_96, c_86])).
% 11.63/4.59  tff(c_511, plain, (r1_ordinal1('#skF_4', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_446, c_106])).
% 11.63/4.59  tff(c_539, plain, (r1_ordinal1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_50, c_511])).
% 11.63/4.59  tff(c_38, plain, (![A_17, B_18]: (r1_tarski(A_17, B_18) | ~r1_ordinal1(A_17, B_18) | ~v3_ordinal1(B_18) | ~v3_ordinal1(A_17))), inference(cnfTransformation, [status(thm)], [f_61])).
% 11.63/4.59  tff(c_422, plain, (![A_69, B_70]: (r1_tarski(A_69, B_70) | ~r1_ordinal1(A_69, B_70) | ~v3_ordinal1(B_70) | ~v3_ordinal1(A_69))), inference(cnfTransformation, [status(thm)], [f_61])).
% 11.63/4.59  tff(c_22, plain, (![B_10, A_9]: (B_10=A_9 | ~r1_tarski(B_10, A_9) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.63/4.59  tff(c_2082, plain, (![B_162, A_163]: (B_162=A_163 | ~r1_tarski(B_162, A_163) | ~r1_ordinal1(A_163, B_162) | ~v3_ordinal1(B_162) | ~v3_ordinal1(A_163))), inference(resolution, [status(thm)], [c_422, c_22])).
% 11.63/4.59  tff(c_14991, plain, (![B_1097, A_1098]: (B_1097=A_1098 | ~r1_ordinal1(B_1097, A_1098) | ~r1_ordinal1(A_1098, B_1097) | ~v3_ordinal1(B_1097) | ~v3_ordinal1(A_1098))), inference(resolution, [status(thm)], [c_38, c_2082])).
% 11.63/4.59  tff(c_15009, plain, ('#skF_3'='#skF_4' | ~r1_ordinal1('#skF_3', '#skF_4') | ~v3_ordinal1('#skF_4') | ~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_539, c_14991])).
% 11.63/4.59  tff(c_15023, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_85, c_15009])).
% 11.63/4.59  tff(c_15029, plain, (~r2_hidden('#skF_4', k1_ordinal1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_15023, c_86])).
% 11.63/4.59  tff(c_15034, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_15029])).
% 11.63/4.59  tff(c_15035, plain, (~r1_ordinal1('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_52])).
% 11.63/4.59  tff(c_15038, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_85, c_15035])).
% 11.63/4.59  tff(c_15040, plain, (~r1_ordinal1('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_58])).
% 11.63/4.59  tff(c_15412, plain, (![B_1138, A_1139]: (r2_hidden(B_1138, A_1139) | r1_ordinal1(A_1139, B_1138) | ~v3_ordinal1(B_1138) | ~v3_ordinal1(A_1139))), inference(cnfTransformation, [status(thm)], [f_76])).
% 11.63/4.59  tff(c_15039, plain, (r2_hidden('#skF_3', k1_ordinal1('#skF_4'))), inference(splitRight, [status(thm)], [c_58])).
% 11.63/4.59  tff(c_15373, plain, (![B_1133, A_1134]: (B_1133=A_1134 | r2_hidden(A_1134, B_1133) | ~r2_hidden(A_1134, k1_ordinal1(B_1133)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 11.63/4.59  tff(c_15384, plain, ('#skF_3'='#skF_4' | r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_15039, c_15373])).
% 11.63/4.59  tff(c_15387, plain, (r2_hidden('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_15384])).
% 11.63/4.59  tff(c_2, plain, (![B_2, A_1]: (~r2_hidden(B_2, A_1) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 11.63/4.59  tff(c_15390, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_15387, c_2])).
% 11.63/4.59  tff(c_15422, plain, (r1_ordinal1('#skF_3', '#skF_4') | ~v3_ordinal1('#skF_4') | ~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_15412, c_15390])).
% 11.63/4.59  tff(c_15491, plain, (r1_ordinal1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_15422])).
% 11.63/4.59  tff(c_15493, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15040, c_15491])).
% 11.63/4.59  tff(c_15494, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_15384])).
% 11.63/4.59  tff(c_15498, plain, (~r1_ordinal1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_15494, c_15040])).
% 11.63/4.59  tff(c_15507, plain, (![B_1140, A_1141]: (r2_hidden(B_1140, A_1141) | r1_ordinal1(A_1141, B_1140) | ~v3_ordinal1(B_1140) | ~v3_ordinal1(A_1141))), inference(cnfTransformation, [status(thm)], [f_76])).
% 11.63/4.59  tff(c_15495, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_15384])).
% 11.63/4.59  tff(c_15506, plain, (~r2_hidden('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_15494, c_15495])).
% 11.63/4.59  tff(c_15510, plain, (r1_ordinal1('#skF_4', '#skF_4') | ~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_15507, c_15506])).
% 11.63/4.59  tff(c_15574, plain, (r1_ordinal1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_15510])).
% 11.63/4.59  tff(c_15576, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15498, c_15574])).
% 11.63/4.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.63/4.59  
% 11.63/4.59  Inference rules
% 11.63/4.59  ----------------------
% 11.63/4.59  #Ref     : 0
% 11.63/4.59  #Sup     : 3290
% 11.63/4.59  #Fact    : 46
% 11.63/4.59  #Define  : 0
% 11.63/4.59  #Split   : 5
% 11.63/4.59  #Chain   : 0
% 11.63/4.59  #Close   : 0
% 11.63/4.59  
% 11.63/4.59  Ordering : KBO
% 11.63/4.59  
% 11.63/4.59  Simplification rules
% 11.63/4.59  ----------------------
% 11.63/4.59  #Subsume      : 1243
% 11.63/4.59  #Demod        : 568
% 11.63/4.59  #Tautology    : 91
% 11.63/4.59  #SimpNegUnit  : 44
% 11.63/4.59  #BackRed      : 67
% 11.63/4.59  
% 11.63/4.59  #Partial instantiations: 0
% 11.63/4.59  #Strategies tried      : 1
% 11.63/4.59  
% 11.63/4.59  Timing (in seconds)
% 11.63/4.60  ----------------------
% 11.63/4.60  Preprocessing        : 0.38
% 11.63/4.60  Parsing              : 0.21
% 11.63/4.60  CNF conversion       : 0.02
% 11.63/4.60  Main loop            : 3.35
% 11.63/4.60  Inferencing          : 0.71
% 11.63/4.60  Reduction            : 0.95
% 11.63/4.60  Demodulation         : 0.44
% 11.63/4.60  BG Simplification    : 0.08
% 11.63/4.60  Subsumption          : 1.36
% 11.63/4.60  Abstraction          : 0.10
% 11.63/4.60  MUC search           : 0.00
% 11.63/4.60  Cooper               : 0.00
% 11.63/4.60  Total                : 3.76
% 11.63/4.60  Index Insertion      : 0.00
% 11.63/4.60  Index Deletion       : 0.00
% 11.63/4.60  Index Matching       : 0.00
% 11.63/4.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
