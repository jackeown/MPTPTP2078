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
% DateTime   : Thu Dec  3 10:02:54 EST 2020

% Result     : Theorem 3.16s
% Output     : CNFRefutation 3.36s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 250 expanded)
%              Number of leaves         :   26 ( 103 expanded)
%              Depth                    :   17
%              Number of atoms          :  114 ( 606 expanded)
%              Number of equality atoms :   56 ( 263 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k4_tarski > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_72,negated_conjecture,(
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
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

tff(c_34,plain,(
    k1_tarski(k1_funct_1('#skF_4','#skF_3')) != k2_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_40,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_38,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_36,plain,(
    k1_tarski('#skF_3') = k1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_4,plain,(
    ! [C_5] : r2_hidden(C_5,k1_tarski(C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_45,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_4])).

tff(c_91,plain,(
    ! [A_30,B_31] :
      ( k9_relat_1(A_30,k1_tarski(B_31)) = k11_relat_1(A_30,B_31)
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_112,plain,(
    ! [A_35] :
      ( k9_relat_1(A_35,k1_relat_1('#skF_4')) = k11_relat_1(A_35,'#skF_3')
      | ~ v1_relat_1(A_35) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_91])).

tff(c_22,plain,(
    ! [A_15] :
      ( k9_relat_1(A_15,k1_relat_1(A_15)) = k2_relat_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_119,plain,
    ( k11_relat_1('#skF_4','#skF_3') = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_22])).

tff(c_129,plain,(
    k11_relat_1('#skF_4','#skF_3') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_40,c_119])).

tff(c_223,plain,(
    ! [A_57,C_58] :
      ( r2_hidden(k4_tarski(A_57,k1_funct_1(C_58,A_57)),C_58)
      | ~ r2_hidden(A_57,k1_relat_1(C_58))
      | ~ v1_funct_1(C_58)
      | ~ v1_relat_1(C_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_26,plain,(
    ! [B_17,C_18,A_16] :
      ( r2_hidden(B_17,k11_relat_1(C_18,A_16))
      | ~ r2_hidden(k4_tarski(A_16,B_17),C_18)
      | ~ v1_relat_1(C_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_396,plain,(
    ! [C_73,A_74] :
      ( r2_hidden(k1_funct_1(C_73,A_74),k11_relat_1(C_73,A_74))
      | ~ r2_hidden(A_74,k1_relat_1(C_73))
      | ~ v1_funct_1(C_73)
      | ~ v1_relat_1(C_73) ) ),
    inference(resolution,[status(thm)],[c_223,c_26])).

tff(c_408,plain,
    ( r2_hidden(k1_funct_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | ~ r2_hidden('#skF_3',k1_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_396])).

tff(c_414,plain,(
    r2_hidden(k1_funct_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_45,c_408])).

tff(c_12,plain,(
    ! [A_1,B_2] :
      ( '#skF_1'(A_1,B_2) = A_1
      | r2_hidden('#skF_2'(A_1,B_2),B_2)
      | k1_tarski(A_1) = B_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_24,plain,(
    ! [A_16,B_17,C_18] :
      ( r2_hidden(k4_tarski(A_16,B_17),C_18)
      | ~ r2_hidden(B_17,k11_relat_1(C_18,A_16))
      | ~ v1_relat_1(C_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_198,plain,(
    ! [C_52,A_53,B_54] :
      ( k1_funct_1(C_52,A_53) = B_54
      | ~ r2_hidden(k4_tarski(A_53,B_54),C_52)
      | ~ v1_funct_1(C_52)
      | ~ v1_relat_1(C_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_263,plain,(
    ! [C_61,A_62,B_63] :
      ( k1_funct_1(C_61,A_62) = B_63
      | ~ v1_funct_1(C_61)
      | ~ r2_hidden(B_63,k11_relat_1(C_61,A_62))
      | ~ v1_relat_1(C_61) ) ),
    inference(resolution,[status(thm)],[c_24,c_198])).

tff(c_285,plain,(
    ! [B_63] :
      ( k1_funct_1('#skF_4','#skF_3') = B_63
      | ~ v1_funct_1('#skF_4')
      | ~ r2_hidden(B_63,k2_relat_1('#skF_4'))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_263])).

tff(c_293,plain,(
    ! [B_64] :
      ( k1_funct_1('#skF_4','#skF_3') = B_64
      | ~ r2_hidden(B_64,k2_relat_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_285])).

tff(c_432,plain,(
    ! [A_78] :
      ( '#skF_2'(A_78,k2_relat_1('#skF_4')) = k1_funct_1('#skF_4','#skF_3')
      | '#skF_1'(A_78,k2_relat_1('#skF_4')) = A_78
      | k2_relat_1('#skF_4') = k1_tarski(A_78) ) ),
    inference(resolution,[status(thm)],[c_12,c_293])).

tff(c_8,plain,(
    ! [A_1,B_2] :
      ( '#skF_1'(A_1,B_2) = A_1
      | '#skF_2'(A_1,B_2) != A_1
      | k1_tarski(A_1) = B_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_443,plain,(
    ! [A_78] :
      ( '#skF_1'(A_78,k2_relat_1('#skF_4')) = A_78
      | k1_funct_1('#skF_4','#skF_3') != A_78
      | k2_relat_1('#skF_4') = k1_tarski(A_78)
      | '#skF_1'(A_78,k2_relat_1('#skF_4')) = A_78
      | k2_relat_1('#skF_4') = k1_tarski(A_78) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_432,c_8])).

tff(c_943,plain,(
    ! [A_118] :
      ( k1_funct_1('#skF_4','#skF_3') != A_118
      | k2_relat_1('#skF_4') = k1_tarski(A_118)
      | '#skF_1'(A_118,k2_relat_1('#skF_4')) = A_118 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_443])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | '#skF_2'(A_1,B_2) != A_1
      | k1_tarski(A_1) = B_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1001,plain,(
    ! [A_121] :
      ( ~ r2_hidden(A_121,k2_relat_1('#skF_4'))
      | '#skF_2'(A_121,k2_relat_1('#skF_4')) != A_121
      | k2_relat_1('#skF_4') = k1_tarski(A_121)
      | k1_funct_1('#skF_4','#skF_3') != A_121
      | k2_relat_1('#skF_4') = k1_tarski(A_121) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_943,c_6])).

tff(c_1004,plain,
    ( '#skF_2'(k1_funct_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) != k1_funct_1('#skF_4','#skF_3')
    | k1_tarski(k1_funct_1('#skF_4','#skF_3')) = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_414,c_1001])).

tff(c_1023,plain,(
    '#skF_2'(k1_funct_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) != k1_funct_1('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_34,c_1004])).

tff(c_313,plain,(
    ! [A_1] :
      ( '#skF_2'(A_1,k2_relat_1('#skF_4')) = k1_funct_1('#skF_4','#skF_3')
      | '#skF_1'(A_1,k2_relat_1('#skF_4')) = A_1
      | k2_relat_1('#skF_4') = k1_tarski(A_1) ) ),
    inference(resolution,[status(thm)],[c_12,c_293])).

tff(c_1030,plain,
    ( '#skF_1'(k1_funct_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) = k1_funct_1('#skF_4','#skF_3')
    | k1_tarski(k1_funct_1('#skF_4','#skF_3')) = k2_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_313,c_1023])).

tff(c_1033,plain,(
    '#skF_1'(k1_funct_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) = k1_funct_1('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_1030])).

tff(c_10,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r2_hidden('#skF_2'(A_1,B_2),B_2)
      | k1_tarski(A_1) = B_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_311,plain,(
    ! [A_1] :
      ( '#skF_2'(A_1,k2_relat_1('#skF_4')) = k1_funct_1('#skF_4','#skF_3')
      | ~ r2_hidden('#skF_1'(A_1,k2_relat_1('#skF_4')),k2_relat_1('#skF_4'))
      | k2_relat_1('#skF_4') = k1_tarski(A_1) ) ),
    inference(resolution,[status(thm)],[c_10,c_293])).

tff(c_1040,plain,
    ( '#skF_2'(k1_funct_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) = k1_funct_1('#skF_4','#skF_3')
    | ~ r2_hidden(k1_funct_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski(k1_funct_1('#skF_4','#skF_3')) = k2_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1033,c_311])).

tff(c_1054,plain,
    ( '#skF_2'(k1_funct_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) = k1_funct_1('#skF_4','#skF_3')
    | k1_tarski(k1_funct_1('#skF_4','#skF_3')) = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_414,c_1040])).

tff(c_1056,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_1023,c_1054])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 15:37:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.16/1.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.57  
% 3.16/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.57  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k4_tarski > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.16/1.57  
% 3.16/1.57  %Foreground sorts:
% 3.16/1.57  
% 3.16/1.57  
% 3.16/1.57  %Background operators:
% 3.16/1.57  
% 3.16/1.57  
% 3.16/1.57  %Foreground operators:
% 3.16/1.57  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.16/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.16/1.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.16/1.57  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.16/1.57  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.16/1.57  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.16/1.57  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.16/1.57  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.16/1.57  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 3.16/1.57  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.16/1.57  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.16/1.57  tff('#skF_3', type, '#skF_3': $i).
% 3.16/1.57  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.16/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.16/1.57  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.16/1.57  tff('#skF_4', type, '#skF_4': $i).
% 3.16/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.16/1.57  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.16/1.57  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.16/1.57  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.16/1.57  
% 3.36/1.58  tff(f_72, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 3.36/1.58  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 3.36/1.58  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_relat_1)).
% 3.36/1.58  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 3.36/1.58  tff(f_63, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 3.36/1.58  tff(f_53, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t204_relat_1)).
% 3.36/1.58  tff(c_34, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_3'))!=k2_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.36/1.58  tff(c_40, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.36/1.58  tff(c_38, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.36/1.58  tff(c_36, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.36/1.58  tff(c_4, plain, (![C_5]: (r2_hidden(C_5, k1_tarski(C_5)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.36/1.58  tff(c_45, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_36, c_4])).
% 3.36/1.58  tff(c_91, plain, (![A_30, B_31]: (k9_relat_1(A_30, k1_tarski(B_31))=k11_relat_1(A_30, B_31) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.36/1.58  tff(c_112, plain, (![A_35]: (k9_relat_1(A_35, k1_relat_1('#skF_4'))=k11_relat_1(A_35, '#skF_3') | ~v1_relat_1(A_35))), inference(superposition, [status(thm), theory('equality')], [c_36, c_91])).
% 3.36/1.58  tff(c_22, plain, (![A_15]: (k9_relat_1(A_15, k1_relat_1(A_15))=k2_relat_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.36/1.58  tff(c_119, plain, (k11_relat_1('#skF_4', '#skF_3')=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_112, c_22])).
% 3.36/1.58  tff(c_129, plain, (k11_relat_1('#skF_4', '#skF_3')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_40, c_119])).
% 3.36/1.58  tff(c_223, plain, (![A_57, C_58]: (r2_hidden(k4_tarski(A_57, k1_funct_1(C_58, A_57)), C_58) | ~r2_hidden(A_57, k1_relat_1(C_58)) | ~v1_funct_1(C_58) | ~v1_relat_1(C_58))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.36/1.58  tff(c_26, plain, (![B_17, C_18, A_16]: (r2_hidden(B_17, k11_relat_1(C_18, A_16)) | ~r2_hidden(k4_tarski(A_16, B_17), C_18) | ~v1_relat_1(C_18))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.36/1.58  tff(c_396, plain, (![C_73, A_74]: (r2_hidden(k1_funct_1(C_73, A_74), k11_relat_1(C_73, A_74)) | ~r2_hidden(A_74, k1_relat_1(C_73)) | ~v1_funct_1(C_73) | ~v1_relat_1(C_73))), inference(resolution, [status(thm)], [c_223, c_26])).
% 3.36/1.58  tff(c_408, plain, (r2_hidden(k1_funct_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | ~r2_hidden('#skF_3', k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_129, c_396])).
% 3.36/1.58  tff(c_414, plain, (r2_hidden(k1_funct_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_45, c_408])).
% 3.36/1.58  tff(c_12, plain, (![A_1, B_2]: ('#skF_1'(A_1, B_2)=A_1 | r2_hidden('#skF_2'(A_1, B_2), B_2) | k1_tarski(A_1)=B_2)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.36/1.58  tff(c_24, plain, (![A_16, B_17, C_18]: (r2_hidden(k4_tarski(A_16, B_17), C_18) | ~r2_hidden(B_17, k11_relat_1(C_18, A_16)) | ~v1_relat_1(C_18))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.36/1.58  tff(c_198, plain, (![C_52, A_53, B_54]: (k1_funct_1(C_52, A_53)=B_54 | ~r2_hidden(k4_tarski(A_53, B_54), C_52) | ~v1_funct_1(C_52) | ~v1_relat_1(C_52))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.36/1.58  tff(c_263, plain, (![C_61, A_62, B_63]: (k1_funct_1(C_61, A_62)=B_63 | ~v1_funct_1(C_61) | ~r2_hidden(B_63, k11_relat_1(C_61, A_62)) | ~v1_relat_1(C_61))), inference(resolution, [status(thm)], [c_24, c_198])).
% 3.36/1.58  tff(c_285, plain, (![B_63]: (k1_funct_1('#skF_4', '#skF_3')=B_63 | ~v1_funct_1('#skF_4') | ~r2_hidden(B_63, k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_129, c_263])).
% 3.36/1.58  tff(c_293, plain, (![B_64]: (k1_funct_1('#skF_4', '#skF_3')=B_64 | ~r2_hidden(B_64, k2_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_285])).
% 3.36/1.58  tff(c_432, plain, (![A_78]: ('#skF_2'(A_78, k2_relat_1('#skF_4'))=k1_funct_1('#skF_4', '#skF_3') | '#skF_1'(A_78, k2_relat_1('#skF_4'))=A_78 | k2_relat_1('#skF_4')=k1_tarski(A_78))), inference(resolution, [status(thm)], [c_12, c_293])).
% 3.36/1.58  tff(c_8, plain, (![A_1, B_2]: ('#skF_1'(A_1, B_2)=A_1 | '#skF_2'(A_1, B_2)!=A_1 | k1_tarski(A_1)=B_2)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.36/1.58  tff(c_443, plain, (![A_78]: ('#skF_1'(A_78, k2_relat_1('#skF_4'))=A_78 | k1_funct_1('#skF_4', '#skF_3')!=A_78 | k2_relat_1('#skF_4')=k1_tarski(A_78) | '#skF_1'(A_78, k2_relat_1('#skF_4'))=A_78 | k2_relat_1('#skF_4')=k1_tarski(A_78))), inference(superposition, [status(thm), theory('equality')], [c_432, c_8])).
% 3.36/1.58  tff(c_943, plain, (![A_118]: (k1_funct_1('#skF_4', '#skF_3')!=A_118 | k2_relat_1('#skF_4')=k1_tarski(A_118) | '#skF_1'(A_118, k2_relat_1('#skF_4'))=A_118)), inference(factorization, [status(thm), theory('equality')], [c_443])).
% 3.36/1.58  tff(c_6, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | '#skF_2'(A_1, B_2)!=A_1 | k1_tarski(A_1)=B_2)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.36/1.58  tff(c_1001, plain, (![A_121]: (~r2_hidden(A_121, k2_relat_1('#skF_4')) | '#skF_2'(A_121, k2_relat_1('#skF_4'))!=A_121 | k2_relat_1('#skF_4')=k1_tarski(A_121) | k1_funct_1('#skF_4', '#skF_3')!=A_121 | k2_relat_1('#skF_4')=k1_tarski(A_121))), inference(superposition, [status(thm), theory('equality')], [c_943, c_6])).
% 3.36/1.58  tff(c_1004, plain, ('#skF_2'(k1_funct_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))!=k1_funct_1('#skF_4', '#skF_3') | k1_tarski(k1_funct_1('#skF_4', '#skF_3'))=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_414, c_1001])).
% 3.36/1.58  tff(c_1023, plain, ('#skF_2'(k1_funct_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))!=k1_funct_1('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_34, c_34, c_1004])).
% 3.36/1.58  tff(c_313, plain, (![A_1]: ('#skF_2'(A_1, k2_relat_1('#skF_4'))=k1_funct_1('#skF_4', '#skF_3') | '#skF_1'(A_1, k2_relat_1('#skF_4'))=A_1 | k2_relat_1('#skF_4')=k1_tarski(A_1))), inference(resolution, [status(thm)], [c_12, c_293])).
% 3.36/1.58  tff(c_1030, plain, ('#skF_1'(k1_funct_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))=k1_funct_1('#skF_4', '#skF_3') | k1_tarski(k1_funct_1('#skF_4', '#skF_3'))=k2_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_313, c_1023])).
% 3.36/1.58  tff(c_1033, plain, ('#skF_1'(k1_funct_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))=k1_funct_1('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_34, c_1030])).
% 3.36/1.58  tff(c_10, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r2_hidden('#skF_2'(A_1, B_2), B_2) | k1_tarski(A_1)=B_2)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.36/1.58  tff(c_311, plain, (![A_1]: ('#skF_2'(A_1, k2_relat_1('#skF_4'))=k1_funct_1('#skF_4', '#skF_3') | ~r2_hidden('#skF_1'(A_1, k2_relat_1('#skF_4')), k2_relat_1('#skF_4')) | k2_relat_1('#skF_4')=k1_tarski(A_1))), inference(resolution, [status(thm)], [c_10, c_293])).
% 3.36/1.58  tff(c_1040, plain, ('#skF_2'(k1_funct_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))=k1_funct_1('#skF_4', '#skF_3') | ~r2_hidden(k1_funct_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski(k1_funct_1('#skF_4', '#skF_3'))=k2_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1033, c_311])).
% 3.36/1.58  tff(c_1054, plain, ('#skF_2'(k1_funct_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))=k1_funct_1('#skF_4', '#skF_3') | k1_tarski(k1_funct_1('#skF_4', '#skF_3'))=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_414, c_1040])).
% 3.36/1.58  tff(c_1056, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_1023, c_1054])).
% 3.36/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.36/1.58  
% 3.36/1.58  Inference rules
% 3.36/1.58  ----------------------
% 3.36/1.58  #Ref     : 0
% 3.36/1.58  #Sup     : 202
% 3.36/1.58  #Fact    : 4
% 3.36/1.58  #Define  : 0
% 3.36/1.58  #Split   : 2
% 3.36/1.58  #Chain   : 0
% 3.36/1.58  #Close   : 0
% 3.36/1.58  
% 3.36/1.58  Ordering : KBO
% 3.36/1.58  
% 3.36/1.58  Simplification rules
% 3.36/1.58  ----------------------
% 3.36/1.58  #Subsume      : 34
% 3.36/1.58  #Demod        : 79
% 3.36/1.58  #Tautology    : 70
% 3.36/1.58  #SimpNegUnit  : 4
% 3.36/1.58  #BackRed      : 0
% 3.36/1.58  
% 3.36/1.58  #Partial instantiations: 0
% 3.36/1.58  #Strategies tried      : 1
% 3.36/1.58  
% 3.36/1.58  Timing (in seconds)
% 3.36/1.58  ----------------------
% 3.36/1.58  Preprocessing        : 0.32
% 3.36/1.58  Parsing              : 0.17
% 3.36/1.58  CNF conversion       : 0.02
% 3.36/1.58  Main loop            : 0.43
% 3.36/1.58  Inferencing          : 0.18
% 3.36/1.58  Reduction            : 0.11
% 3.36/1.58  Demodulation         : 0.08
% 3.36/1.58  BG Simplification    : 0.03
% 3.36/1.59  Subsumption          : 0.09
% 3.36/1.59  Abstraction          : 0.03
% 3.36/1.59  MUC search           : 0.00
% 3.36/1.59  Cooper               : 0.00
% 3.36/1.59  Total                : 0.78
% 3.36/1.59  Index Insertion      : 0.00
% 3.36/1.59  Index Deletion       : 0.00
% 3.36/1.59  Index Matching       : 0.00
% 3.36/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
