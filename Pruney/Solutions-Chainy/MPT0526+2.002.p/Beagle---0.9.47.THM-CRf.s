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
% DateTime   : Thu Dec  3 10:00:10 EST 2020

% Result     : Theorem 11.25s
% Output     : CNFRefutation 11.46s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 106 expanded)
%              Number of leaves         :   19 (  45 expanded)
%              Depth                    :   12
%              Number of atoms          :  113 ( 273 expanded)
%              Number of equality atoms :   25 (  61 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k8_relat_1 > k4_tarski > #nlpp > k2_relat_1 > #skF_4 > #skF_3 > #skF_5 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_56,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k8_relat_1(k2_relat_1(A),A) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k2_relat_1(k8_relat_1(B,C)))
      <=> ( r2_hidden(A,B)
          & r2_hidden(A,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k8_relat_1(A,B)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

tff(c_26,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_82,plain,(
    ! [A_52,B_53] :
      ( r2_hidden(k4_tarski('#skF_2'(A_52,B_53),'#skF_1'(A_52,B_53)),A_52)
      | r2_hidden('#skF_3'(A_52,B_53),B_53)
      | k2_relat_1(A_52) = B_53 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [C_16,A_1,D_19] :
      ( r2_hidden(C_16,k2_relat_1(A_1))
      | ~ r2_hidden(k4_tarski(D_19,C_16),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_97,plain,(
    ! [A_54,B_55] :
      ( r2_hidden('#skF_1'(A_54,B_55),k2_relat_1(A_54))
      | r2_hidden('#skF_3'(A_54,B_55),B_55)
      | k2_relat_1(A_54) = B_55 ) ),
    inference(resolution,[status(thm)],[c_82,c_4])).

tff(c_16,plain,(
    ! [A_20,C_22,B_21] :
      ( r2_hidden(A_20,k2_relat_1(C_22))
      | ~ r2_hidden(A_20,k2_relat_1(k8_relat_1(B_21,C_22)))
      | ~ v1_relat_1(C_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1427,plain,(
    ! [A_155,B_156,C_157] :
      ( r2_hidden('#skF_3'(A_155,k2_relat_1(k8_relat_1(B_156,C_157))),k2_relat_1(C_157))
      | ~ v1_relat_1(C_157)
      | r2_hidden('#skF_1'(A_155,k2_relat_1(k8_relat_1(B_156,C_157))),k2_relat_1(A_155))
      | k2_relat_1(k8_relat_1(B_156,C_157)) = k2_relat_1(A_155) ) ),
    inference(resolution,[status(thm)],[c_97,c_16])).

tff(c_2,plain,(
    ! [A_1,C_16] :
      ( r2_hidden(k4_tarski('#skF_4'(A_1,k2_relat_1(A_1),C_16),C_16),A_1)
      | ~ r2_hidden(C_16,k2_relat_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_119,plain,(
    ! [A_56,B_57,D_58] :
      ( r2_hidden(k4_tarski('#skF_2'(A_56,B_57),'#skF_1'(A_56,B_57)),A_56)
      | ~ r2_hidden(k4_tarski(D_58,'#skF_3'(A_56,B_57)),A_56)
      | k2_relat_1(A_56) = B_57 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_128,plain,(
    ! [A_59,B_60] :
      ( r2_hidden(k4_tarski('#skF_2'(A_59,B_60),'#skF_1'(A_59,B_60)),A_59)
      | k2_relat_1(A_59) = B_60
      | ~ r2_hidden('#skF_3'(A_59,B_60),k2_relat_1(A_59)) ) ),
    inference(resolution,[status(thm)],[c_2,c_119])).

tff(c_142,plain,(
    ! [A_59,B_60] :
      ( r2_hidden('#skF_1'(A_59,B_60),k2_relat_1(A_59))
      | k2_relat_1(A_59) = B_60
      | ~ r2_hidden('#skF_3'(A_59,B_60),k2_relat_1(A_59)) ) ),
    inference(resolution,[status(thm)],[c_128,c_4])).

tff(c_1509,plain,(
    ! [C_157,B_156] :
      ( ~ v1_relat_1(C_157)
      | r2_hidden('#skF_1'(C_157,k2_relat_1(k8_relat_1(B_156,C_157))),k2_relat_1(C_157))
      | k2_relat_1(k8_relat_1(B_156,C_157)) = k2_relat_1(C_157) ) ),
    inference(resolution,[status(thm)],[c_1427,c_142])).

tff(c_18,plain,(
    ! [A_20,B_21,C_22] :
      ( r2_hidden(A_20,B_21)
      | ~ r2_hidden(A_20,k2_relat_1(k8_relat_1(B_21,C_22)))
      | ~ v1_relat_1(C_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_118,plain,(
    ! [A_54,B_21,C_22] :
      ( r2_hidden('#skF_3'(A_54,k2_relat_1(k8_relat_1(B_21,C_22))),B_21)
      | ~ v1_relat_1(C_22)
      | r2_hidden('#skF_1'(A_54,k2_relat_1(k8_relat_1(B_21,C_22))),k2_relat_1(A_54))
      | k2_relat_1(k8_relat_1(B_21,C_22)) = k2_relat_1(A_54) ) ),
    inference(resolution,[status(thm)],[c_97,c_18])).

tff(c_14,plain,(
    ! [A_20,B_21,C_22] :
      ( r2_hidden(A_20,k2_relat_1(k8_relat_1(B_21,C_22)))
      | ~ r2_hidden(A_20,k2_relat_1(C_22))
      | ~ r2_hidden(A_20,B_21)
      | ~ v1_relat_1(C_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_36,plain,(
    ! [A_40,B_41] :
      ( ~ r2_hidden('#skF_1'(A_40,B_41),B_41)
      | r2_hidden('#skF_3'(A_40,B_41),B_41)
      | k2_relat_1(A_40) = B_41 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_418,plain,(
    ! [A_88,B_89,C_90] :
      ( r2_hidden('#skF_3'(A_88,k2_relat_1(k8_relat_1(B_89,C_90))),B_89)
      | ~ v1_relat_1(C_90)
      | ~ r2_hidden('#skF_1'(A_88,k2_relat_1(k8_relat_1(B_89,C_90))),k2_relat_1(k8_relat_1(B_89,C_90)))
      | k2_relat_1(k8_relat_1(B_89,C_90)) = k2_relat_1(A_88) ) ),
    inference(resolution,[status(thm)],[c_36,c_18])).

tff(c_6081,plain,(
    ! [A_316,B_317,C_318] :
      ( r2_hidden('#skF_3'(A_316,k2_relat_1(k8_relat_1(B_317,C_318))),B_317)
      | k2_relat_1(k8_relat_1(B_317,C_318)) = k2_relat_1(A_316)
      | ~ r2_hidden('#skF_1'(A_316,k2_relat_1(k8_relat_1(B_317,C_318))),k2_relat_1(C_318))
      | ~ r2_hidden('#skF_1'(A_316,k2_relat_1(k8_relat_1(B_317,C_318))),B_317)
      | ~ v1_relat_1(C_318) ) ),
    inference(resolution,[status(thm)],[c_14,c_418])).

tff(c_6190,plain,(
    ! [A_54,B_21] :
      ( ~ r2_hidden('#skF_1'(A_54,k2_relat_1(k8_relat_1(B_21,A_54))),B_21)
      | r2_hidden('#skF_3'(A_54,k2_relat_1(k8_relat_1(B_21,A_54))),B_21)
      | ~ v1_relat_1(A_54)
      | k2_relat_1(k8_relat_1(B_21,A_54)) = k2_relat_1(A_54) ) ),
    inference(resolution,[status(thm)],[c_118,c_6081])).

tff(c_64,plain,(
    ! [A_49,B_50,C_51] :
      ( r2_hidden(A_49,k2_relat_1(k8_relat_1(B_50,C_51)))
      | ~ r2_hidden(A_49,k2_relat_1(C_51))
      | ~ r2_hidden(A_49,B_50)
      | ~ v1_relat_1(C_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6,plain,(
    ! [A_1,B_2,D_15] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | ~ r2_hidden(k4_tarski(D_15,'#skF_3'(A_1,B_2)),A_1)
      | k2_relat_1(A_1) = B_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2255,plain,(
    ! [D_198,A_199,B_200,C_201] :
      ( ~ r2_hidden(k4_tarski(D_198,'#skF_3'(A_199,k2_relat_1(k8_relat_1(B_200,C_201)))),A_199)
      | k2_relat_1(k8_relat_1(B_200,C_201)) = k2_relat_1(A_199)
      | ~ r2_hidden('#skF_1'(A_199,k2_relat_1(k8_relat_1(B_200,C_201))),k2_relat_1(C_201))
      | ~ r2_hidden('#skF_1'(A_199,k2_relat_1(k8_relat_1(B_200,C_201))),B_200)
      | ~ v1_relat_1(C_201) ) ),
    inference(resolution,[status(thm)],[c_64,c_6])).

tff(c_9359,plain,(
    ! [B_403,C_404,A_405] :
      ( k2_relat_1(k8_relat_1(B_403,C_404)) = k2_relat_1(A_405)
      | ~ r2_hidden('#skF_1'(A_405,k2_relat_1(k8_relat_1(B_403,C_404))),k2_relat_1(C_404))
      | ~ r2_hidden('#skF_1'(A_405,k2_relat_1(k8_relat_1(B_403,C_404))),B_403)
      | ~ v1_relat_1(C_404)
      | ~ r2_hidden('#skF_3'(A_405,k2_relat_1(k8_relat_1(B_403,C_404))),k2_relat_1(A_405)) ) ),
    inference(resolution,[status(thm)],[c_2,c_2255])).

tff(c_9499,plain,(
    ! [C_406,B_407] :
      ( ~ r2_hidden('#skF_1'(C_406,k2_relat_1(k8_relat_1(B_407,C_406))),B_407)
      | ~ r2_hidden('#skF_3'(C_406,k2_relat_1(k8_relat_1(B_407,C_406))),k2_relat_1(C_406))
      | ~ v1_relat_1(C_406)
      | k2_relat_1(k8_relat_1(B_407,C_406)) = k2_relat_1(C_406) ) ),
    inference(resolution,[status(thm)],[c_1509,c_9359])).

tff(c_9637,plain,(
    ! [C_408] :
      ( ~ r2_hidden('#skF_3'(C_408,k2_relat_1(k8_relat_1(k2_relat_1(C_408),C_408))),k2_relat_1(C_408))
      | ~ v1_relat_1(C_408)
      | k2_relat_1(k8_relat_1(k2_relat_1(C_408),C_408)) = k2_relat_1(C_408) ) ),
    inference(resolution,[status(thm)],[c_1509,c_9499])).

tff(c_9859,plain,(
    ! [A_412] :
      ( ~ r2_hidden('#skF_1'(A_412,k2_relat_1(k8_relat_1(k2_relat_1(A_412),A_412))),k2_relat_1(A_412))
      | ~ v1_relat_1(A_412)
      | k2_relat_1(k8_relat_1(k2_relat_1(A_412),A_412)) = k2_relat_1(A_412) ) ),
    inference(resolution,[status(thm)],[c_6190,c_9637])).

tff(c_10021,plain,(
    ! [C_413] :
      ( ~ v1_relat_1(C_413)
      | k2_relat_1(k8_relat_1(k2_relat_1(C_413),C_413)) = k2_relat_1(C_413) ) ),
    inference(resolution,[status(thm)],[c_1509,c_9859])).

tff(c_20,plain,(
    ! [A_23,B_24] :
      ( r1_tarski(k2_relat_1(k8_relat_1(A_23,B_24)),A_23)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_10542,plain,(
    ! [C_414] :
      ( r1_tarski(k2_relat_1(C_414),k2_relat_1(C_414))
      | ~ v1_relat_1(C_414)
      | ~ v1_relat_1(C_414) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10021,c_20])).

tff(c_22,plain,(
    ! [A_25,B_26] :
      ( k8_relat_1(A_25,B_26) = B_26
      | ~ r1_tarski(k2_relat_1(B_26),A_25)
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_10553,plain,(
    ! [C_415] :
      ( k8_relat_1(k2_relat_1(C_415),C_415) = C_415
      | ~ v1_relat_1(C_415) ) ),
    inference(resolution,[status(thm)],[c_10542,c_22])).

tff(c_24,plain,(
    k8_relat_1(k2_relat_1('#skF_5'),'#skF_5') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_10909,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_10553,c_24])).

tff(c_10921,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_10909])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:41:05 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.25/3.88  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.46/3.89  
% 11.46/3.89  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.46/3.89  %$ r2_hidden > r1_tarski > v1_relat_1 > k8_relat_1 > k4_tarski > #nlpp > k2_relat_1 > #skF_4 > #skF_3 > #skF_5 > #skF_2 > #skF_1
% 11.46/3.89  
% 11.46/3.89  %Foreground sorts:
% 11.46/3.89  
% 11.46/3.89  
% 11.46/3.89  %Background operators:
% 11.46/3.89  
% 11.46/3.89  
% 11.46/3.89  %Foreground operators:
% 11.46/3.89  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 11.46/3.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.46/3.89  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.46/3.89  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 11.46/3.89  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 11.46/3.89  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 11.46/3.89  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.46/3.89  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 11.46/3.89  tff('#skF_5', type, '#skF_5': $i).
% 11.46/3.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.46/3.89  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.46/3.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.46/3.89  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 11.46/3.89  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 11.46/3.89  
% 11.46/3.90  tff(f_56, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k8_relat_1(k2_relat_1(A), A) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t126_relat_1)).
% 11.46/3.90  tff(f_33, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 11.46/3.90  tff(f_41, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k2_relat_1(k8_relat_1(B, C))) <=> (r2_hidden(A, B) & r2_hidden(A, k2_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t115_relat_1)).
% 11.46/3.90  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k8_relat_1(A, B)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_relat_1)).
% 11.46/3.90  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_relat_1)).
% 11.46/3.90  tff(c_26, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_56])).
% 11.46/3.90  tff(c_82, plain, (![A_52, B_53]: (r2_hidden(k4_tarski('#skF_2'(A_52, B_53), '#skF_1'(A_52, B_53)), A_52) | r2_hidden('#skF_3'(A_52, B_53), B_53) | k2_relat_1(A_52)=B_53)), inference(cnfTransformation, [status(thm)], [f_33])).
% 11.46/3.90  tff(c_4, plain, (![C_16, A_1, D_19]: (r2_hidden(C_16, k2_relat_1(A_1)) | ~r2_hidden(k4_tarski(D_19, C_16), A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 11.46/3.90  tff(c_97, plain, (![A_54, B_55]: (r2_hidden('#skF_1'(A_54, B_55), k2_relat_1(A_54)) | r2_hidden('#skF_3'(A_54, B_55), B_55) | k2_relat_1(A_54)=B_55)), inference(resolution, [status(thm)], [c_82, c_4])).
% 11.46/3.90  tff(c_16, plain, (![A_20, C_22, B_21]: (r2_hidden(A_20, k2_relat_1(C_22)) | ~r2_hidden(A_20, k2_relat_1(k8_relat_1(B_21, C_22))) | ~v1_relat_1(C_22))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.46/3.90  tff(c_1427, plain, (![A_155, B_156, C_157]: (r2_hidden('#skF_3'(A_155, k2_relat_1(k8_relat_1(B_156, C_157))), k2_relat_1(C_157)) | ~v1_relat_1(C_157) | r2_hidden('#skF_1'(A_155, k2_relat_1(k8_relat_1(B_156, C_157))), k2_relat_1(A_155)) | k2_relat_1(k8_relat_1(B_156, C_157))=k2_relat_1(A_155))), inference(resolution, [status(thm)], [c_97, c_16])).
% 11.46/3.90  tff(c_2, plain, (![A_1, C_16]: (r2_hidden(k4_tarski('#skF_4'(A_1, k2_relat_1(A_1), C_16), C_16), A_1) | ~r2_hidden(C_16, k2_relat_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 11.46/3.90  tff(c_119, plain, (![A_56, B_57, D_58]: (r2_hidden(k4_tarski('#skF_2'(A_56, B_57), '#skF_1'(A_56, B_57)), A_56) | ~r2_hidden(k4_tarski(D_58, '#skF_3'(A_56, B_57)), A_56) | k2_relat_1(A_56)=B_57)), inference(cnfTransformation, [status(thm)], [f_33])).
% 11.46/3.90  tff(c_128, plain, (![A_59, B_60]: (r2_hidden(k4_tarski('#skF_2'(A_59, B_60), '#skF_1'(A_59, B_60)), A_59) | k2_relat_1(A_59)=B_60 | ~r2_hidden('#skF_3'(A_59, B_60), k2_relat_1(A_59)))), inference(resolution, [status(thm)], [c_2, c_119])).
% 11.46/3.90  tff(c_142, plain, (![A_59, B_60]: (r2_hidden('#skF_1'(A_59, B_60), k2_relat_1(A_59)) | k2_relat_1(A_59)=B_60 | ~r2_hidden('#skF_3'(A_59, B_60), k2_relat_1(A_59)))), inference(resolution, [status(thm)], [c_128, c_4])).
% 11.46/3.90  tff(c_1509, plain, (![C_157, B_156]: (~v1_relat_1(C_157) | r2_hidden('#skF_1'(C_157, k2_relat_1(k8_relat_1(B_156, C_157))), k2_relat_1(C_157)) | k2_relat_1(k8_relat_1(B_156, C_157))=k2_relat_1(C_157))), inference(resolution, [status(thm)], [c_1427, c_142])).
% 11.46/3.90  tff(c_18, plain, (![A_20, B_21, C_22]: (r2_hidden(A_20, B_21) | ~r2_hidden(A_20, k2_relat_1(k8_relat_1(B_21, C_22))) | ~v1_relat_1(C_22))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.46/3.90  tff(c_118, plain, (![A_54, B_21, C_22]: (r2_hidden('#skF_3'(A_54, k2_relat_1(k8_relat_1(B_21, C_22))), B_21) | ~v1_relat_1(C_22) | r2_hidden('#skF_1'(A_54, k2_relat_1(k8_relat_1(B_21, C_22))), k2_relat_1(A_54)) | k2_relat_1(k8_relat_1(B_21, C_22))=k2_relat_1(A_54))), inference(resolution, [status(thm)], [c_97, c_18])).
% 11.46/3.90  tff(c_14, plain, (![A_20, B_21, C_22]: (r2_hidden(A_20, k2_relat_1(k8_relat_1(B_21, C_22))) | ~r2_hidden(A_20, k2_relat_1(C_22)) | ~r2_hidden(A_20, B_21) | ~v1_relat_1(C_22))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.46/3.90  tff(c_36, plain, (![A_40, B_41]: (~r2_hidden('#skF_1'(A_40, B_41), B_41) | r2_hidden('#skF_3'(A_40, B_41), B_41) | k2_relat_1(A_40)=B_41)), inference(cnfTransformation, [status(thm)], [f_33])).
% 11.46/3.90  tff(c_418, plain, (![A_88, B_89, C_90]: (r2_hidden('#skF_3'(A_88, k2_relat_1(k8_relat_1(B_89, C_90))), B_89) | ~v1_relat_1(C_90) | ~r2_hidden('#skF_1'(A_88, k2_relat_1(k8_relat_1(B_89, C_90))), k2_relat_1(k8_relat_1(B_89, C_90))) | k2_relat_1(k8_relat_1(B_89, C_90))=k2_relat_1(A_88))), inference(resolution, [status(thm)], [c_36, c_18])).
% 11.46/3.90  tff(c_6081, plain, (![A_316, B_317, C_318]: (r2_hidden('#skF_3'(A_316, k2_relat_1(k8_relat_1(B_317, C_318))), B_317) | k2_relat_1(k8_relat_1(B_317, C_318))=k2_relat_1(A_316) | ~r2_hidden('#skF_1'(A_316, k2_relat_1(k8_relat_1(B_317, C_318))), k2_relat_1(C_318)) | ~r2_hidden('#skF_1'(A_316, k2_relat_1(k8_relat_1(B_317, C_318))), B_317) | ~v1_relat_1(C_318))), inference(resolution, [status(thm)], [c_14, c_418])).
% 11.46/3.90  tff(c_6190, plain, (![A_54, B_21]: (~r2_hidden('#skF_1'(A_54, k2_relat_1(k8_relat_1(B_21, A_54))), B_21) | r2_hidden('#skF_3'(A_54, k2_relat_1(k8_relat_1(B_21, A_54))), B_21) | ~v1_relat_1(A_54) | k2_relat_1(k8_relat_1(B_21, A_54))=k2_relat_1(A_54))), inference(resolution, [status(thm)], [c_118, c_6081])).
% 11.46/3.90  tff(c_64, plain, (![A_49, B_50, C_51]: (r2_hidden(A_49, k2_relat_1(k8_relat_1(B_50, C_51))) | ~r2_hidden(A_49, k2_relat_1(C_51)) | ~r2_hidden(A_49, B_50) | ~v1_relat_1(C_51))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.46/3.90  tff(c_6, plain, (![A_1, B_2, D_15]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | ~r2_hidden(k4_tarski(D_15, '#skF_3'(A_1, B_2)), A_1) | k2_relat_1(A_1)=B_2)), inference(cnfTransformation, [status(thm)], [f_33])).
% 11.46/3.90  tff(c_2255, plain, (![D_198, A_199, B_200, C_201]: (~r2_hidden(k4_tarski(D_198, '#skF_3'(A_199, k2_relat_1(k8_relat_1(B_200, C_201)))), A_199) | k2_relat_1(k8_relat_1(B_200, C_201))=k2_relat_1(A_199) | ~r2_hidden('#skF_1'(A_199, k2_relat_1(k8_relat_1(B_200, C_201))), k2_relat_1(C_201)) | ~r2_hidden('#skF_1'(A_199, k2_relat_1(k8_relat_1(B_200, C_201))), B_200) | ~v1_relat_1(C_201))), inference(resolution, [status(thm)], [c_64, c_6])).
% 11.46/3.90  tff(c_9359, plain, (![B_403, C_404, A_405]: (k2_relat_1(k8_relat_1(B_403, C_404))=k2_relat_1(A_405) | ~r2_hidden('#skF_1'(A_405, k2_relat_1(k8_relat_1(B_403, C_404))), k2_relat_1(C_404)) | ~r2_hidden('#skF_1'(A_405, k2_relat_1(k8_relat_1(B_403, C_404))), B_403) | ~v1_relat_1(C_404) | ~r2_hidden('#skF_3'(A_405, k2_relat_1(k8_relat_1(B_403, C_404))), k2_relat_1(A_405)))), inference(resolution, [status(thm)], [c_2, c_2255])).
% 11.46/3.90  tff(c_9499, plain, (![C_406, B_407]: (~r2_hidden('#skF_1'(C_406, k2_relat_1(k8_relat_1(B_407, C_406))), B_407) | ~r2_hidden('#skF_3'(C_406, k2_relat_1(k8_relat_1(B_407, C_406))), k2_relat_1(C_406)) | ~v1_relat_1(C_406) | k2_relat_1(k8_relat_1(B_407, C_406))=k2_relat_1(C_406))), inference(resolution, [status(thm)], [c_1509, c_9359])).
% 11.46/3.90  tff(c_9637, plain, (![C_408]: (~r2_hidden('#skF_3'(C_408, k2_relat_1(k8_relat_1(k2_relat_1(C_408), C_408))), k2_relat_1(C_408)) | ~v1_relat_1(C_408) | k2_relat_1(k8_relat_1(k2_relat_1(C_408), C_408))=k2_relat_1(C_408))), inference(resolution, [status(thm)], [c_1509, c_9499])).
% 11.46/3.90  tff(c_9859, plain, (![A_412]: (~r2_hidden('#skF_1'(A_412, k2_relat_1(k8_relat_1(k2_relat_1(A_412), A_412))), k2_relat_1(A_412)) | ~v1_relat_1(A_412) | k2_relat_1(k8_relat_1(k2_relat_1(A_412), A_412))=k2_relat_1(A_412))), inference(resolution, [status(thm)], [c_6190, c_9637])).
% 11.46/3.90  tff(c_10021, plain, (![C_413]: (~v1_relat_1(C_413) | k2_relat_1(k8_relat_1(k2_relat_1(C_413), C_413))=k2_relat_1(C_413))), inference(resolution, [status(thm)], [c_1509, c_9859])).
% 11.46/3.90  tff(c_20, plain, (![A_23, B_24]: (r1_tarski(k2_relat_1(k8_relat_1(A_23, B_24)), A_23) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.46/3.90  tff(c_10542, plain, (![C_414]: (r1_tarski(k2_relat_1(C_414), k2_relat_1(C_414)) | ~v1_relat_1(C_414) | ~v1_relat_1(C_414))), inference(superposition, [status(thm), theory('equality')], [c_10021, c_20])).
% 11.46/3.90  tff(c_22, plain, (![A_25, B_26]: (k8_relat_1(A_25, B_26)=B_26 | ~r1_tarski(k2_relat_1(B_26), A_25) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.46/3.90  tff(c_10553, plain, (![C_415]: (k8_relat_1(k2_relat_1(C_415), C_415)=C_415 | ~v1_relat_1(C_415))), inference(resolution, [status(thm)], [c_10542, c_22])).
% 11.46/3.90  tff(c_24, plain, (k8_relat_1(k2_relat_1('#skF_5'), '#skF_5')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_56])).
% 11.46/3.90  tff(c_10909, plain, (~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_10553, c_24])).
% 11.46/3.90  tff(c_10921, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_10909])).
% 11.46/3.90  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.46/3.90  
% 11.46/3.90  Inference rules
% 11.46/3.90  ----------------------
% 11.46/3.90  #Ref     : 0
% 11.46/3.90  #Sup     : 2687
% 11.46/3.90  #Fact    : 0
% 11.46/3.90  #Define  : 0
% 11.46/3.90  #Split   : 0
% 11.46/3.90  #Chain   : 0
% 11.46/3.90  #Close   : 0
% 11.46/3.90  
% 11.46/3.90  Ordering : KBO
% 11.46/3.90  
% 11.46/3.90  Simplification rules
% 11.46/3.90  ----------------------
% 11.46/3.90  #Subsume      : 304
% 11.46/3.90  #Demod        : 1
% 11.46/3.90  #Tautology    : 72
% 11.46/3.90  #SimpNegUnit  : 0
% 11.46/3.90  #BackRed      : 0
% 11.46/3.90  
% 11.46/3.90  #Partial instantiations: 0
% 11.46/3.90  #Strategies tried      : 1
% 11.46/3.90  
% 11.46/3.90  Timing (in seconds)
% 11.46/3.90  ----------------------
% 11.46/3.91  Preprocessing        : 0.27
% 11.46/3.91  Parsing              : 0.15
% 11.46/3.91  CNF conversion       : 0.02
% 11.46/3.91  Main loop            : 2.87
% 11.46/3.91  Inferencing          : 0.79
% 11.46/3.91  Reduction            : 0.43
% 11.46/3.91  Demodulation         : 0.28
% 11.46/3.91  BG Simplification    : 0.12
% 11.46/3.91  Subsumption          : 1.32
% 11.46/3.91  Abstraction          : 0.26
% 11.46/3.91  MUC search           : 0.00
% 11.46/3.91  Cooper               : 0.00
% 11.46/3.91  Total                : 3.17
% 11.46/3.91  Index Insertion      : 0.00
% 11.46/3.91  Index Deletion       : 0.00
% 11.46/3.91  Index Matching       : 0.00
% 11.46/3.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
