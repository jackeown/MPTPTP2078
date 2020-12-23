%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:56 EST 2020

% Result     : Theorem 3.99s
% Output     : CNFRefutation 4.23s
% Verified   : 
% Statistics : Number of formulae       :   74 (1173 expanded)
%              Number of leaves         :   24 ( 441 expanded)
%              Depth                    :   28
%              Number of atoms          :  148 (3512 expanded)
%              Number of equality atoms :   70 (1248 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > #skF_6 > #skF_3 > #skF_9 > #skF_7 > #skF_8 > #skF_2 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_67,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( k1_relat_1(B) = k1_tarski(A)
         => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( r2_hidden(A,k1_relat_1(B))
          & ! [C] : ~ r2_hidden(C,k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_relat_1)).

tff(f_58,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

tff(c_38,plain,(
    k1_tarski('#skF_8') = k1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_4,plain,(
    ! [C_5] : r2_hidden(C_5,k1_tarski(C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_47,plain,(
    r2_hidden('#skF_8',k1_relat_1('#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_4])).

tff(c_42,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_16,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_3'(A_7,B_8),k2_relat_1(B_8))
      | ~ r2_hidden(A_7,k1_relat_1(B_8))
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_40,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_22,plain,(
    ! [A_10,C_46] :
      ( r2_hidden('#skF_7'(A_10,k2_relat_1(A_10),C_46),k1_relat_1(A_10))
      | ~ r2_hidden(C_46,k2_relat_1(A_10))
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_18,plain,(
    ! [A_10,D_49] :
      ( r2_hidden(k1_funct_1(A_10,D_49),k2_relat_1(A_10))
      | ~ r2_hidden(D_49,k1_relat_1(A_10))
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_161,plain,(
    ! [A_73,C_74] :
      ( r2_hidden('#skF_7'(A_73,k2_relat_1(A_73),C_74),k1_relat_1(A_73))
      | ~ r2_hidden(C_74,k2_relat_1(A_73))
      | ~ v1_funct_1(A_73)
      | ~ v1_relat_1(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_60,plain,(
    ! [C_52,A_53] :
      ( C_52 = A_53
      | ~ r2_hidden(C_52,k1_tarski(A_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_63,plain,(
    ! [C_52] :
      ( C_52 = '#skF_8'
      | ~ r2_hidden(C_52,k1_relat_1('#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_60])).

tff(c_165,plain,(
    ! [C_74] :
      ( '#skF_7'('#skF_9',k2_relat_1('#skF_9'),C_74) = '#skF_8'
      | ~ r2_hidden(C_74,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_161,c_63])).

tff(c_169,plain,(
    ! [C_75] :
      ( '#skF_7'('#skF_9',k2_relat_1('#skF_9'),C_75) = '#skF_8'
      | ~ r2_hidden(C_75,k2_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_165])).

tff(c_173,plain,(
    ! [D_49] :
      ( '#skF_7'('#skF_9',k2_relat_1('#skF_9'),k1_funct_1('#skF_9',D_49)) = '#skF_8'
      | ~ r2_hidden(D_49,k1_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_18,c_169])).

tff(c_194,plain,(
    ! [D_76] :
      ( '#skF_7'('#skF_9',k2_relat_1('#skF_9'),k1_funct_1('#skF_9',D_76)) = '#skF_8'
      | ~ r2_hidden(D_76,k1_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_173])).

tff(c_20,plain,(
    ! [A_10,C_46] :
      ( k1_funct_1(A_10,'#skF_7'(A_10,k2_relat_1(A_10),C_46)) = C_46
      | ~ r2_hidden(C_46,k2_relat_1(A_10))
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_203,plain,(
    ! [D_76] :
      ( k1_funct_1('#skF_9',D_76) = k1_funct_1('#skF_9','#skF_8')
      | ~ r2_hidden(k1_funct_1('#skF_9',D_76),k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9')
      | ~ r2_hidden(D_76,k1_relat_1('#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_20])).

tff(c_263,plain,(
    ! [D_82] :
      ( k1_funct_1('#skF_9',D_82) = k1_funct_1('#skF_9','#skF_8')
      | ~ r2_hidden(k1_funct_1('#skF_9',D_82),k2_relat_1('#skF_9'))
      | ~ r2_hidden(D_82,k1_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_203])).

tff(c_271,plain,(
    ! [D_49] :
      ( k1_funct_1('#skF_9',D_49) = k1_funct_1('#skF_9','#skF_8')
      | ~ r2_hidden(D_49,k1_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_18,c_263])).

tff(c_277,plain,(
    ! [D_83] :
      ( k1_funct_1('#skF_9',D_83) = k1_funct_1('#skF_9','#skF_8')
      | ~ r2_hidden(D_83,k1_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_271])).

tff(c_285,plain,(
    ! [C_46] :
      ( k1_funct_1('#skF_9','#skF_7'('#skF_9',k2_relat_1('#skF_9'),C_46)) = k1_funct_1('#skF_9','#skF_8')
      | ~ r2_hidden(C_46,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_22,c_277])).

tff(c_305,plain,(
    ! [C_84] :
      ( k1_funct_1('#skF_9','#skF_7'('#skF_9',k2_relat_1('#skF_9'),C_84)) = k1_funct_1('#skF_9','#skF_8')
      | ~ r2_hidden(C_84,k2_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_285])).

tff(c_314,plain,(
    ! [C_84] :
      ( k1_funct_1('#skF_9','#skF_8') = C_84
      | ~ r2_hidden(C_84,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9')
      | ~ r2_hidden(C_84,k2_relat_1('#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_305,c_20])).

tff(c_342,plain,(
    ! [C_86] :
      ( k1_funct_1('#skF_9','#skF_8') = C_86
      | ~ r2_hidden(C_86,k2_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_314])).

tff(c_362,plain,(
    ! [A_7] :
      ( k1_funct_1('#skF_9','#skF_8') = '#skF_3'(A_7,'#skF_9')
      | ~ r2_hidden(A_7,k1_relat_1('#skF_9'))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_16,c_342])).

tff(c_372,plain,(
    ! [A_87] :
      ( k1_funct_1('#skF_9','#skF_8') = '#skF_3'(A_87,'#skF_9')
      | ~ r2_hidden(A_87,k1_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_362])).

tff(c_398,plain,(
    k1_funct_1('#skF_9','#skF_8') = '#skF_3'('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_47,c_372])).

tff(c_36,plain,(
    k1_tarski(k1_funct_1('#skF_9','#skF_8')) != k2_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_403,plain,(
    k1_tarski('#skF_3'('#skF_8','#skF_9')) != k2_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_398,c_36])).

tff(c_410,plain,
    ( r2_hidden('#skF_3'('#skF_8','#skF_9'),k2_relat_1('#skF_9'))
    | ~ r2_hidden('#skF_8',k1_relat_1('#skF_9'))
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_398,c_18])).

tff(c_416,plain,(
    r2_hidden('#skF_3'('#skF_8','#skF_9'),k2_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_47,c_410])).

tff(c_12,plain,(
    ! [A_1,B_2] :
      ( '#skF_1'(A_1,B_2) = A_1
      | r2_hidden('#skF_2'(A_1,B_2),B_2)
      | k1_tarski(A_1) = B_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_368,plain,(
    ! [A_1] :
      ( '#skF_2'(A_1,k2_relat_1('#skF_9')) = k1_funct_1('#skF_9','#skF_8')
      | '#skF_1'(A_1,k2_relat_1('#skF_9')) = A_1
      | k2_relat_1('#skF_9') = k1_tarski(A_1) ) ),
    inference(resolution,[status(thm)],[c_12,c_342])).

tff(c_1032,plain,(
    ! [A_114] :
      ( '#skF_2'(A_114,k2_relat_1('#skF_9')) = '#skF_3'('#skF_8','#skF_9')
      | '#skF_1'(A_114,k2_relat_1('#skF_9')) = A_114
      | k2_relat_1('#skF_9') = k1_tarski(A_114) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_398,c_368])).

tff(c_8,plain,(
    ! [A_1,B_2] :
      ( '#skF_1'(A_1,B_2) = A_1
      | '#skF_2'(A_1,B_2) != A_1
      | k1_tarski(A_1) = B_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1043,plain,(
    ! [A_114] :
      ( '#skF_1'(A_114,k2_relat_1('#skF_9')) = A_114
      | A_114 != '#skF_3'('#skF_8','#skF_9')
      | k2_relat_1('#skF_9') = k1_tarski(A_114)
      | '#skF_1'(A_114,k2_relat_1('#skF_9')) = A_114
      | k2_relat_1('#skF_9') = k1_tarski(A_114) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1032,c_8])).

tff(c_2571,plain,(
    ! [A_168] :
      ( A_168 != '#skF_3'('#skF_8','#skF_9')
      | k2_relat_1('#skF_9') = k1_tarski(A_168)
      | '#skF_1'(A_168,k2_relat_1('#skF_9')) = A_168 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_1043])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | '#skF_2'(A_1,B_2) != A_1
      | k1_tarski(A_1) = B_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2614,plain,(
    ! [A_171] :
      ( ~ r2_hidden(A_171,k2_relat_1('#skF_9'))
      | '#skF_2'(A_171,k2_relat_1('#skF_9')) != A_171
      | k2_relat_1('#skF_9') = k1_tarski(A_171)
      | A_171 != '#skF_3'('#skF_8','#skF_9')
      | k2_relat_1('#skF_9') = k1_tarski(A_171) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2571,c_6])).

tff(c_2660,plain,
    ( '#skF_2'('#skF_3'('#skF_8','#skF_9'),k2_relat_1('#skF_9')) != '#skF_3'('#skF_8','#skF_9')
    | k1_tarski('#skF_3'('#skF_8','#skF_9')) = k2_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_416,c_2614])).

tff(c_2705,plain,(
    '#skF_2'('#skF_3'('#skF_8','#skF_9'),k2_relat_1('#skF_9')) != '#skF_3'('#skF_8','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_403,c_403,c_2660])).

tff(c_1030,plain,(
    ! [A_1] :
      ( '#skF_2'(A_1,k2_relat_1('#skF_9')) = '#skF_3'('#skF_8','#skF_9')
      | '#skF_1'(A_1,k2_relat_1('#skF_9')) = A_1
      | k2_relat_1('#skF_9') = k1_tarski(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_398,c_368])).

tff(c_2718,plain,
    ( '#skF_1'('#skF_3'('#skF_8','#skF_9'),k2_relat_1('#skF_9')) = '#skF_3'('#skF_8','#skF_9')
    | k1_tarski('#skF_3'('#skF_8','#skF_9')) = k2_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_1030,c_2705])).

tff(c_2721,plain,(
    '#skF_1'('#skF_3'('#skF_8','#skF_9'),k2_relat_1('#skF_9')) = '#skF_3'('#skF_8','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_403,c_2718])).

tff(c_10,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r2_hidden('#skF_2'(A_1,B_2),B_2)
      | k1_tarski(A_1) = B_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_367,plain,(
    ! [A_1] :
      ( '#skF_2'(A_1,k2_relat_1('#skF_9')) = k1_funct_1('#skF_9','#skF_8')
      | ~ r2_hidden('#skF_1'(A_1,k2_relat_1('#skF_9')),k2_relat_1('#skF_9'))
      | k2_relat_1('#skF_9') = k1_tarski(A_1) ) ),
    inference(resolution,[status(thm)],[c_10,c_342])).

tff(c_1522,plain,(
    ! [A_1] :
      ( '#skF_2'(A_1,k2_relat_1('#skF_9')) = '#skF_3'('#skF_8','#skF_9')
      | ~ r2_hidden('#skF_1'(A_1,k2_relat_1('#skF_9')),k2_relat_1('#skF_9'))
      | k2_relat_1('#skF_9') = k1_tarski(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_398,c_367])).

tff(c_2731,plain,
    ( '#skF_2'('#skF_3'('#skF_8','#skF_9'),k2_relat_1('#skF_9')) = '#skF_3'('#skF_8','#skF_9')
    | ~ r2_hidden('#skF_3'('#skF_8','#skF_9'),k2_relat_1('#skF_9'))
    | k1_tarski('#skF_3'('#skF_8','#skF_9')) = k2_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_2721,c_1522])).

tff(c_2748,plain,
    ( '#skF_2'('#skF_3'('#skF_8','#skF_9'),k2_relat_1('#skF_9')) = '#skF_3'('#skF_8','#skF_9')
    | k1_tarski('#skF_3'('#skF_8','#skF_9')) = k2_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_416,c_2731])).

tff(c_2750,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_403,c_2705,c_2748])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:57:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.99/1.71  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.13/1.72  
% 4.13/1.72  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.13/1.72  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > #skF_6 > #skF_3 > #skF_9 > #skF_7 > #skF_8 > #skF_2 > #skF_1 > #skF_5 > #skF_4
% 4.13/1.72  
% 4.13/1.72  %Foreground sorts:
% 4.13/1.72  
% 4.13/1.72  
% 4.13/1.72  %Background operators:
% 4.13/1.72  
% 4.13/1.72  
% 4.13/1.72  %Foreground operators:
% 4.13/1.72  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 4.13/1.72  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.13/1.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.13/1.72  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.13/1.72  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.13/1.72  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.13/1.72  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.13/1.72  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.13/1.72  tff('#skF_9', type, '#skF_9': $i).
% 4.13/1.72  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 4.13/1.72  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.13/1.72  tff('#skF_8', type, '#skF_8': $i).
% 4.13/1.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.13/1.72  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.13/1.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.13/1.72  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.13/1.72  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.13/1.72  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 4.13/1.72  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.13/1.72  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.13/1.72  
% 4.23/1.73  tff(f_67, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 4.23/1.73  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 4.23/1.73  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => ~(r2_hidden(A, k1_relat_1(B)) & (![C]: ~r2_hidden(C, k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_relat_1)).
% 4.23/1.73  tff(f_58, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 4.23/1.73  tff(c_38, plain, (k1_tarski('#skF_8')=k1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.23/1.73  tff(c_4, plain, (![C_5]: (r2_hidden(C_5, k1_tarski(C_5)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.23/1.73  tff(c_47, plain, (r2_hidden('#skF_8', k1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_38, c_4])).
% 4.23/1.73  tff(c_42, plain, (v1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.23/1.73  tff(c_16, plain, (![A_7, B_8]: (r2_hidden('#skF_3'(A_7, B_8), k2_relat_1(B_8)) | ~r2_hidden(A_7, k1_relat_1(B_8)) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.23/1.73  tff(c_40, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.23/1.73  tff(c_22, plain, (![A_10, C_46]: (r2_hidden('#skF_7'(A_10, k2_relat_1(A_10), C_46), k1_relat_1(A_10)) | ~r2_hidden(C_46, k2_relat_1(A_10)) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.23/1.73  tff(c_18, plain, (![A_10, D_49]: (r2_hidden(k1_funct_1(A_10, D_49), k2_relat_1(A_10)) | ~r2_hidden(D_49, k1_relat_1(A_10)) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.23/1.73  tff(c_161, plain, (![A_73, C_74]: (r2_hidden('#skF_7'(A_73, k2_relat_1(A_73), C_74), k1_relat_1(A_73)) | ~r2_hidden(C_74, k2_relat_1(A_73)) | ~v1_funct_1(A_73) | ~v1_relat_1(A_73))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.23/1.73  tff(c_60, plain, (![C_52, A_53]: (C_52=A_53 | ~r2_hidden(C_52, k1_tarski(A_53)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.23/1.73  tff(c_63, plain, (![C_52]: (C_52='#skF_8' | ~r2_hidden(C_52, k1_relat_1('#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_38, c_60])).
% 4.23/1.73  tff(c_165, plain, (![C_74]: ('#skF_7'('#skF_9', k2_relat_1('#skF_9'), C_74)='#skF_8' | ~r2_hidden(C_74, k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_161, c_63])).
% 4.23/1.73  tff(c_169, plain, (![C_75]: ('#skF_7'('#skF_9', k2_relat_1('#skF_9'), C_75)='#skF_8' | ~r2_hidden(C_75, k2_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_165])).
% 4.23/1.73  tff(c_173, plain, (![D_49]: ('#skF_7'('#skF_9', k2_relat_1('#skF_9'), k1_funct_1('#skF_9', D_49))='#skF_8' | ~r2_hidden(D_49, k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_18, c_169])).
% 4.23/1.73  tff(c_194, plain, (![D_76]: ('#skF_7'('#skF_9', k2_relat_1('#skF_9'), k1_funct_1('#skF_9', D_76))='#skF_8' | ~r2_hidden(D_76, k1_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_173])).
% 4.23/1.73  tff(c_20, plain, (![A_10, C_46]: (k1_funct_1(A_10, '#skF_7'(A_10, k2_relat_1(A_10), C_46))=C_46 | ~r2_hidden(C_46, k2_relat_1(A_10)) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.23/1.73  tff(c_203, plain, (![D_76]: (k1_funct_1('#skF_9', D_76)=k1_funct_1('#skF_9', '#skF_8') | ~r2_hidden(k1_funct_1('#skF_9', D_76), k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | ~r2_hidden(D_76, k1_relat_1('#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_194, c_20])).
% 4.23/1.73  tff(c_263, plain, (![D_82]: (k1_funct_1('#skF_9', D_82)=k1_funct_1('#skF_9', '#skF_8') | ~r2_hidden(k1_funct_1('#skF_9', D_82), k2_relat_1('#skF_9')) | ~r2_hidden(D_82, k1_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_203])).
% 4.23/1.73  tff(c_271, plain, (![D_49]: (k1_funct_1('#skF_9', D_49)=k1_funct_1('#skF_9', '#skF_8') | ~r2_hidden(D_49, k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_18, c_263])).
% 4.23/1.73  tff(c_277, plain, (![D_83]: (k1_funct_1('#skF_9', D_83)=k1_funct_1('#skF_9', '#skF_8') | ~r2_hidden(D_83, k1_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_271])).
% 4.23/1.73  tff(c_285, plain, (![C_46]: (k1_funct_1('#skF_9', '#skF_7'('#skF_9', k2_relat_1('#skF_9'), C_46))=k1_funct_1('#skF_9', '#skF_8') | ~r2_hidden(C_46, k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_22, c_277])).
% 4.23/1.73  tff(c_305, plain, (![C_84]: (k1_funct_1('#skF_9', '#skF_7'('#skF_9', k2_relat_1('#skF_9'), C_84))=k1_funct_1('#skF_9', '#skF_8') | ~r2_hidden(C_84, k2_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_285])).
% 4.23/1.73  tff(c_314, plain, (![C_84]: (k1_funct_1('#skF_9', '#skF_8')=C_84 | ~r2_hidden(C_84, k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | ~r2_hidden(C_84, k2_relat_1('#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_305, c_20])).
% 4.23/1.73  tff(c_342, plain, (![C_86]: (k1_funct_1('#skF_9', '#skF_8')=C_86 | ~r2_hidden(C_86, k2_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_314])).
% 4.23/1.73  tff(c_362, plain, (![A_7]: (k1_funct_1('#skF_9', '#skF_8')='#skF_3'(A_7, '#skF_9') | ~r2_hidden(A_7, k1_relat_1('#skF_9')) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_16, c_342])).
% 4.23/1.73  tff(c_372, plain, (![A_87]: (k1_funct_1('#skF_9', '#skF_8')='#skF_3'(A_87, '#skF_9') | ~r2_hidden(A_87, k1_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_362])).
% 4.23/1.73  tff(c_398, plain, (k1_funct_1('#skF_9', '#skF_8')='#skF_3'('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_47, c_372])).
% 4.23/1.73  tff(c_36, plain, (k1_tarski(k1_funct_1('#skF_9', '#skF_8'))!=k2_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.23/1.73  tff(c_403, plain, (k1_tarski('#skF_3'('#skF_8', '#skF_9'))!=k2_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_398, c_36])).
% 4.23/1.73  tff(c_410, plain, (r2_hidden('#skF_3'('#skF_8', '#skF_9'), k2_relat_1('#skF_9')) | ~r2_hidden('#skF_8', k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_398, c_18])).
% 4.23/1.73  tff(c_416, plain, (r2_hidden('#skF_3'('#skF_8', '#skF_9'), k2_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_47, c_410])).
% 4.23/1.73  tff(c_12, plain, (![A_1, B_2]: ('#skF_1'(A_1, B_2)=A_1 | r2_hidden('#skF_2'(A_1, B_2), B_2) | k1_tarski(A_1)=B_2)), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.23/1.73  tff(c_368, plain, (![A_1]: ('#skF_2'(A_1, k2_relat_1('#skF_9'))=k1_funct_1('#skF_9', '#skF_8') | '#skF_1'(A_1, k2_relat_1('#skF_9'))=A_1 | k2_relat_1('#skF_9')=k1_tarski(A_1))), inference(resolution, [status(thm)], [c_12, c_342])).
% 4.23/1.73  tff(c_1032, plain, (![A_114]: ('#skF_2'(A_114, k2_relat_1('#skF_9'))='#skF_3'('#skF_8', '#skF_9') | '#skF_1'(A_114, k2_relat_1('#skF_9'))=A_114 | k2_relat_1('#skF_9')=k1_tarski(A_114))), inference(demodulation, [status(thm), theory('equality')], [c_398, c_368])).
% 4.23/1.73  tff(c_8, plain, (![A_1, B_2]: ('#skF_1'(A_1, B_2)=A_1 | '#skF_2'(A_1, B_2)!=A_1 | k1_tarski(A_1)=B_2)), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.23/1.73  tff(c_1043, plain, (![A_114]: ('#skF_1'(A_114, k2_relat_1('#skF_9'))=A_114 | A_114!='#skF_3'('#skF_8', '#skF_9') | k2_relat_1('#skF_9')=k1_tarski(A_114) | '#skF_1'(A_114, k2_relat_1('#skF_9'))=A_114 | k2_relat_1('#skF_9')=k1_tarski(A_114))), inference(superposition, [status(thm), theory('equality')], [c_1032, c_8])).
% 4.23/1.73  tff(c_2571, plain, (![A_168]: (A_168!='#skF_3'('#skF_8', '#skF_9') | k2_relat_1('#skF_9')=k1_tarski(A_168) | '#skF_1'(A_168, k2_relat_1('#skF_9'))=A_168)), inference(factorization, [status(thm), theory('equality')], [c_1043])).
% 4.23/1.73  tff(c_6, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | '#skF_2'(A_1, B_2)!=A_1 | k1_tarski(A_1)=B_2)), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.23/1.73  tff(c_2614, plain, (![A_171]: (~r2_hidden(A_171, k2_relat_1('#skF_9')) | '#skF_2'(A_171, k2_relat_1('#skF_9'))!=A_171 | k2_relat_1('#skF_9')=k1_tarski(A_171) | A_171!='#skF_3'('#skF_8', '#skF_9') | k2_relat_1('#skF_9')=k1_tarski(A_171))), inference(superposition, [status(thm), theory('equality')], [c_2571, c_6])).
% 4.23/1.73  tff(c_2660, plain, ('#skF_2'('#skF_3'('#skF_8', '#skF_9'), k2_relat_1('#skF_9'))!='#skF_3'('#skF_8', '#skF_9') | k1_tarski('#skF_3'('#skF_8', '#skF_9'))=k2_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_416, c_2614])).
% 4.23/1.73  tff(c_2705, plain, ('#skF_2'('#skF_3'('#skF_8', '#skF_9'), k2_relat_1('#skF_9'))!='#skF_3'('#skF_8', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_403, c_403, c_2660])).
% 4.23/1.73  tff(c_1030, plain, (![A_1]: ('#skF_2'(A_1, k2_relat_1('#skF_9'))='#skF_3'('#skF_8', '#skF_9') | '#skF_1'(A_1, k2_relat_1('#skF_9'))=A_1 | k2_relat_1('#skF_9')=k1_tarski(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_398, c_368])).
% 4.23/1.73  tff(c_2718, plain, ('#skF_1'('#skF_3'('#skF_8', '#skF_9'), k2_relat_1('#skF_9'))='#skF_3'('#skF_8', '#skF_9') | k1_tarski('#skF_3'('#skF_8', '#skF_9'))=k2_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_1030, c_2705])).
% 4.23/1.73  tff(c_2721, plain, ('#skF_1'('#skF_3'('#skF_8', '#skF_9'), k2_relat_1('#skF_9'))='#skF_3'('#skF_8', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_403, c_2718])).
% 4.23/1.73  tff(c_10, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r2_hidden('#skF_2'(A_1, B_2), B_2) | k1_tarski(A_1)=B_2)), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.23/1.73  tff(c_367, plain, (![A_1]: ('#skF_2'(A_1, k2_relat_1('#skF_9'))=k1_funct_1('#skF_9', '#skF_8') | ~r2_hidden('#skF_1'(A_1, k2_relat_1('#skF_9')), k2_relat_1('#skF_9')) | k2_relat_1('#skF_9')=k1_tarski(A_1))), inference(resolution, [status(thm)], [c_10, c_342])).
% 4.23/1.73  tff(c_1522, plain, (![A_1]: ('#skF_2'(A_1, k2_relat_1('#skF_9'))='#skF_3'('#skF_8', '#skF_9') | ~r2_hidden('#skF_1'(A_1, k2_relat_1('#skF_9')), k2_relat_1('#skF_9')) | k2_relat_1('#skF_9')=k1_tarski(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_398, c_367])).
% 4.23/1.73  tff(c_2731, plain, ('#skF_2'('#skF_3'('#skF_8', '#skF_9'), k2_relat_1('#skF_9'))='#skF_3'('#skF_8', '#skF_9') | ~r2_hidden('#skF_3'('#skF_8', '#skF_9'), k2_relat_1('#skF_9')) | k1_tarski('#skF_3'('#skF_8', '#skF_9'))=k2_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_2721, c_1522])).
% 4.23/1.73  tff(c_2748, plain, ('#skF_2'('#skF_3'('#skF_8', '#skF_9'), k2_relat_1('#skF_9'))='#skF_3'('#skF_8', '#skF_9') | k1_tarski('#skF_3'('#skF_8', '#skF_9'))=k2_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_416, c_2731])).
% 4.23/1.73  tff(c_2750, plain, $false, inference(negUnitSimplification, [status(thm)], [c_403, c_2705, c_2748])).
% 4.23/1.73  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.23/1.73  
% 4.23/1.73  Inference rules
% 4.23/1.73  ----------------------
% 4.23/1.73  #Ref     : 2
% 4.23/1.73  #Sup     : 499
% 4.23/1.73  #Fact    : 6
% 4.23/1.73  #Define  : 0
% 4.23/1.73  #Split   : 4
% 4.23/1.73  #Chain   : 0
% 4.23/1.73  #Close   : 0
% 4.23/1.73  
% 4.23/1.73  Ordering : KBO
% 4.23/1.73  
% 4.23/1.73  Simplification rules
% 4.23/1.73  ----------------------
% 4.23/1.73  #Subsume      : 77
% 4.23/1.73  #Demod        : 575
% 4.23/1.73  #Tautology    : 256
% 4.23/1.73  #SimpNegUnit  : 83
% 4.23/1.73  #BackRed      : 18
% 4.23/1.73  
% 4.23/1.73  #Partial instantiations: 0
% 4.23/1.73  #Strategies tried      : 1
% 4.23/1.73  
% 4.23/1.73  Timing (in seconds)
% 4.23/1.73  ----------------------
% 4.23/1.74  Preprocessing        : 0.29
% 4.23/1.74  Parsing              : 0.15
% 4.23/1.74  CNF conversion       : 0.03
% 4.23/1.74  Main loop            : 0.68
% 4.23/1.74  Inferencing          : 0.25
% 4.23/1.74  Reduction            : 0.22
% 4.23/1.74  Demodulation         : 0.15
% 4.23/1.74  BG Simplification    : 0.04
% 4.23/1.74  Subsumption          : 0.13
% 4.23/1.74  Abstraction          : 0.04
% 4.23/1.74  MUC search           : 0.00
% 4.23/1.74  Cooper               : 0.00
% 4.23/1.74  Total                : 1.01
% 4.23/1.74  Index Insertion      : 0.00
% 4.23/1.74  Index Deletion       : 0.00
% 4.23/1.74  Index Matching       : 0.00
% 4.23/1.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
