%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:13 EST 2020

% Result     : Theorem 5.36s
% Output     : CNFRefutation 5.36s
% Verified   : 
% Statistics : Number of formulae       :   62 (  96 expanded)
%              Number of leaves         :   28 (  46 expanded)
%              Depth                    :   11
%              Number of atoms          :   90 ( 169 expanded)
%              Number of equality atoms :   16 (  24 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k4_tarski > k2_tarski > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > #skF_4 > #skF_7 > #skF_2 > #skF_6 > #skF_5 > #skF_8 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_86,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r2_hidden(k4_tarski(A,B),C)
        <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_51,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

tff(c_64,plain,(
    v1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_66,plain,
    ( ~ r2_hidden('#skF_7',k11_relat_1('#skF_8','#skF_6'))
    | ~ r2_hidden(k4_tarski('#skF_6','#skF_7'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_95,plain,(
    ~ r2_hidden(k4_tarski('#skF_6','#skF_7'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_72,plain,
    ( r2_hidden(k4_tarski('#skF_6','#skF_7'),'#skF_8')
    | r2_hidden('#skF_7',k11_relat_1('#skF_8','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_155,plain,(
    r2_hidden('#skF_7',k11_relat_1('#skF_8','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_72])).

tff(c_50,plain,(
    ! [A_20,B_22] :
      ( k9_relat_1(A_20,k1_tarski(B_22)) = k11_relat_1(A_20,B_22)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_259,plain,(
    ! [A_73,B_74,C_75] :
      ( r2_hidden('#skF_5'(A_73,B_74,C_75),B_74)
      | ~ r2_hidden(A_73,k9_relat_1(C_75,B_74))
      | ~ v1_relat_1(C_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_44,plain,(
    ! [A_14] : k2_tarski(A_14,A_14) = k1_tarski(A_14) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_126,plain,(
    ! [D_52,B_53,A_54] :
      ( D_52 = B_53
      | D_52 = A_54
      | ~ r2_hidden(D_52,k2_tarski(A_54,B_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_129,plain,(
    ! [D_52,A_14] :
      ( D_52 = A_14
      | D_52 = A_14
      | ~ r2_hidden(D_52,k1_tarski(A_14)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_126])).

tff(c_396,plain,(
    ! [A_103,A_104,C_105] :
      ( '#skF_5'(A_103,k1_tarski(A_104),C_105) = A_104
      | ~ r2_hidden(A_103,k9_relat_1(C_105,k1_tarski(A_104)))
      | ~ v1_relat_1(C_105) ) ),
    inference(resolution,[status(thm)],[c_259,c_129])).

tff(c_442,plain,(
    ! [A_112,B_113,A_114] :
      ( '#skF_5'(A_112,k1_tarski(B_113),A_114) = B_113
      | ~ r2_hidden(A_112,k11_relat_1(A_114,B_113))
      | ~ v1_relat_1(A_114)
      | ~ v1_relat_1(A_114) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_396])).

tff(c_457,plain,
    ( '#skF_5'('#skF_7',k1_tarski('#skF_6'),'#skF_8') = '#skF_6'
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_155,c_442])).

tff(c_463,plain,(
    '#skF_5'('#skF_7',k1_tarski('#skF_6'),'#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_457])).

tff(c_56,plain,(
    ! [A_23,B_24,C_25] :
      ( r2_hidden(k4_tarski('#skF_5'(A_23,B_24,C_25),A_23),C_25)
      | ~ r2_hidden(A_23,k9_relat_1(C_25,B_24))
      | ~ v1_relat_1(C_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_467,plain,
    ( r2_hidden(k4_tarski('#skF_6','#skF_7'),'#skF_8')
    | ~ r2_hidden('#skF_7',k9_relat_1('#skF_8',k1_tarski('#skF_6')))
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_463,c_56])).

tff(c_477,plain,
    ( r2_hidden(k4_tarski('#skF_6','#skF_7'),'#skF_8')
    | ~ r2_hidden('#skF_7',k9_relat_1('#skF_8',k1_tarski('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_467])).

tff(c_478,plain,(
    ~ r2_hidden('#skF_7',k9_relat_1('#skF_8',k1_tarski('#skF_6'))) ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_477])).

tff(c_486,plain,
    ( ~ r2_hidden('#skF_7',k11_relat_1('#skF_8','#skF_6'))
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_478])).

tff(c_489,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_155,c_486])).

tff(c_490,plain,(
    ~ r2_hidden('#skF_7',k11_relat_1('#skF_8','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_491,plain,(
    r2_hidden(k4_tarski('#skF_6','#skF_7'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_593,plain,(
    ! [A_130,C_131,B_132] :
      ( r2_hidden(A_130,k1_relat_1(C_131))
      | ~ r2_hidden(k4_tarski(A_130,B_132),C_131)
      | ~ v1_relat_1(C_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_596,plain,
    ( r2_hidden('#skF_6',k1_relat_1('#skF_8'))
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_491,c_593])).

tff(c_623,plain,(
    r2_hidden('#skF_6',k1_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_596])).

tff(c_75,plain,(
    ! [A_36] : k2_tarski(A_36,A_36) = k1_tarski(A_36) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_28,plain,(
    ! [D_13,A_8] : r2_hidden(D_13,k2_tarski(A_8,D_13)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_81,plain,(
    ! [A_36] : r2_hidden(A_36,k1_tarski(A_36)) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_28])).

tff(c_1021,plain,(
    ! [A_232,C_233,B_234,D_235] :
      ( r2_hidden(A_232,k9_relat_1(C_233,B_234))
      | ~ r2_hidden(D_235,B_234)
      | ~ r2_hidden(k4_tarski(D_235,A_232),C_233)
      | ~ r2_hidden(D_235,k1_relat_1(C_233))
      | ~ v1_relat_1(C_233) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1295,plain,(
    ! [A_242,C_243,A_244] :
      ( r2_hidden(A_242,k9_relat_1(C_243,k1_tarski(A_244)))
      | ~ r2_hidden(k4_tarski(A_244,A_242),C_243)
      | ~ r2_hidden(A_244,k1_relat_1(C_243))
      | ~ v1_relat_1(C_243) ) ),
    inference(resolution,[status(thm)],[c_81,c_1021])).

tff(c_1652,plain,(
    ! [A_259,A_260,B_261] :
      ( r2_hidden(A_259,k11_relat_1(A_260,B_261))
      | ~ r2_hidden(k4_tarski(B_261,A_259),A_260)
      | ~ r2_hidden(B_261,k1_relat_1(A_260))
      | ~ v1_relat_1(A_260)
      | ~ v1_relat_1(A_260) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_1295])).

tff(c_1726,plain,
    ( r2_hidden('#skF_7',k11_relat_1('#skF_8','#skF_6'))
    | ~ r2_hidden('#skF_6',k1_relat_1('#skF_8'))
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_491,c_1652])).

tff(c_1771,plain,(
    r2_hidden('#skF_7',k11_relat_1('#skF_8','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_623,c_1726])).

tff(c_1773,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_490,c_1771])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:52:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.36/2.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.36/2.45  
% 5.36/2.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.36/2.45  %$ r2_hidden > v1_relat_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k4_tarski > k2_tarski > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > #skF_4 > #skF_7 > #skF_2 > #skF_6 > #skF_5 > #skF_8 > #skF_3 > #skF_1
% 5.36/2.45  
% 5.36/2.45  %Foreground sorts:
% 5.36/2.45  
% 5.36/2.45  
% 5.36/2.45  %Background operators:
% 5.36/2.45  
% 5.36/2.45  
% 5.36/2.45  %Foreground operators:
% 5.36/2.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.36/2.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.36/2.45  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.36/2.45  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.36/2.45  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 5.36/2.45  tff('#skF_7', type, '#skF_7': $i).
% 5.36/2.45  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.36/2.45  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.36/2.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.36/2.45  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 5.36/2.45  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 5.36/2.45  tff('#skF_6', type, '#skF_6': $i).
% 5.36/2.45  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 5.36/2.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.36/2.45  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.36/2.45  tff('#skF_8', type, '#skF_8': $i).
% 5.36/2.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.36/2.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.36/2.45  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 5.36/2.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.36/2.45  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 5.36/2.45  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.36/2.45  
% 5.36/2.47  tff(f_86, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t204_relat_1)).
% 5.36/2.47  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 5.36/2.47  tff(f_71, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 5.36/2.47  tff(f_51, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 5.36/2.47  tff(f_49, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 5.36/2.47  tff(f_79, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_relat_1)).
% 5.36/2.47  tff(c_64, plain, (v1_relat_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.36/2.47  tff(c_66, plain, (~r2_hidden('#skF_7', k11_relat_1('#skF_8', '#skF_6')) | ~r2_hidden(k4_tarski('#skF_6', '#skF_7'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.36/2.47  tff(c_95, plain, (~r2_hidden(k4_tarski('#skF_6', '#skF_7'), '#skF_8')), inference(splitLeft, [status(thm)], [c_66])).
% 5.36/2.47  tff(c_72, plain, (r2_hidden(k4_tarski('#skF_6', '#skF_7'), '#skF_8') | r2_hidden('#skF_7', k11_relat_1('#skF_8', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.36/2.47  tff(c_155, plain, (r2_hidden('#skF_7', k11_relat_1('#skF_8', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_95, c_72])).
% 5.36/2.47  tff(c_50, plain, (![A_20, B_22]: (k9_relat_1(A_20, k1_tarski(B_22))=k11_relat_1(A_20, B_22) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.36/2.47  tff(c_259, plain, (![A_73, B_74, C_75]: (r2_hidden('#skF_5'(A_73, B_74, C_75), B_74) | ~r2_hidden(A_73, k9_relat_1(C_75, B_74)) | ~v1_relat_1(C_75))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.36/2.47  tff(c_44, plain, (![A_14]: (k2_tarski(A_14, A_14)=k1_tarski(A_14))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.36/2.47  tff(c_126, plain, (![D_52, B_53, A_54]: (D_52=B_53 | D_52=A_54 | ~r2_hidden(D_52, k2_tarski(A_54, B_53)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.36/2.47  tff(c_129, plain, (![D_52, A_14]: (D_52=A_14 | D_52=A_14 | ~r2_hidden(D_52, k1_tarski(A_14)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_126])).
% 5.36/2.47  tff(c_396, plain, (![A_103, A_104, C_105]: ('#skF_5'(A_103, k1_tarski(A_104), C_105)=A_104 | ~r2_hidden(A_103, k9_relat_1(C_105, k1_tarski(A_104))) | ~v1_relat_1(C_105))), inference(resolution, [status(thm)], [c_259, c_129])).
% 5.36/2.47  tff(c_442, plain, (![A_112, B_113, A_114]: ('#skF_5'(A_112, k1_tarski(B_113), A_114)=B_113 | ~r2_hidden(A_112, k11_relat_1(A_114, B_113)) | ~v1_relat_1(A_114) | ~v1_relat_1(A_114))), inference(superposition, [status(thm), theory('equality')], [c_50, c_396])).
% 5.36/2.47  tff(c_457, plain, ('#skF_5'('#skF_7', k1_tarski('#skF_6'), '#skF_8')='#skF_6' | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_155, c_442])).
% 5.36/2.47  tff(c_463, plain, ('#skF_5'('#skF_7', k1_tarski('#skF_6'), '#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_457])).
% 5.36/2.47  tff(c_56, plain, (![A_23, B_24, C_25]: (r2_hidden(k4_tarski('#skF_5'(A_23, B_24, C_25), A_23), C_25) | ~r2_hidden(A_23, k9_relat_1(C_25, B_24)) | ~v1_relat_1(C_25))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.36/2.47  tff(c_467, plain, (r2_hidden(k4_tarski('#skF_6', '#skF_7'), '#skF_8') | ~r2_hidden('#skF_7', k9_relat_1('#skF_8', k1_tarski('#skF_6'))) | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_463, c_56])).
% 5.36/2.47  tff(c_477, plain, (r2_hidden(k4_tarski('#skF_6', '#skF_7'), '#skF_8') | ~r2_hidden('#skF_7', k9_relat_1('#skF_8', k1_tarski('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_467])).
% 5.36/2.47  tff(c_478, plain, (~r2_hidden('#skF_7', k9_relat_1('#skF_8', k1_tarski('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_95, c_477])).
% 5.36/2.47  tff(c_486, plain, (~r2_hidden('#skF_7', k11_relat_1('#skF_8', '#skF_6')) | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_50, c_478])).
% 5.36/2.47  tff(c_489, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_155, c_486])).
% 5.36/2.47  tff(c_490, plain, (~r2_hidden('#skF_7', k11_relat_1('#skF_8', '#skF_6'))), inference(splitRight, [status(thm)], [c_66])).
% 5.36/2.47  tff(c_491, plain, (r2_hidden(k4_tarski('#skF_6', '#skF_7'), '#skF_8')), inference(splitRight, [status(thm)], [c_66])).
% 5.36/2.47  tff(c_593, plain, (![A_130, C_131, B_132]: (r2_hidden(A_130, k1_relat_1(C_131)) | ~r2_hidden(k4_tarski(A_130, B_132), C_131) | ~v1_relat_1(C_131))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.36/2.47  tff(c_596, plain, (r2_hidden('#skF_6', k1_relat_1('#skF_8')) | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_491, c_593])).
% 5.36/2.47  tff(c_623, plain, (r2_hidden('#skF_6', k1_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_596])).
% 5.36/2.47  tff(c_75, plain, (![A_36]: (k2_tarski(A_36, A_36)=k1_tarski(A_36))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.36/2.47  tff(c_28, plain, (![D_13, A_8]: (r2_hidden(D_13, k2_tarski(A_8, D_13)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.36/2.47  tff(c_81, plain, (![A_36]: (r2_hidden(A_36, k1_tarski(A_36)))), inference(superposition, [status(thm), theory('equality')], [c_75, c_28])).
% 5.36/2.47  tff(c_1021, plain, (![A_232, C_233, B_234, D_235]: (r2_hidden(A_232, k9_relat_1(C_233, B_234)) | ~r2_hidden(D_235, B_234) | ~r2_hidden(k4_tarski(D_235, A_232), C_233) | ~r2_hidden(D_235, k1_relat_1(C_233)) | ~v1_relat_1(C_233))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.36/2.47  tff(c_1295, plain, (![A_242, C_243, A_244]: (r2_hidden(A_242, k9_relat_1(C_243, k1_tarski(A_244))) | ~r2_hidden(k4_tarski(A_244, A_242), C_243) | ~r2_hidden(A_244, k1_relat_1(C_243)) | ~v1_relat_1(C_243))), inference(resolution, [status(thm)], [c_81, c_1021])).
% 5.36/2.47  tff(c_1652, plain, (![A_259, A_260, B_261]: (r2_hidden(A_259, k11_relat_1(A_260, B_261)) | ~r2_hidden(k4_tarski(B_261, A_259), A_260) | ~r2_hidden(B_261, k1_relat_1(A_260)) | ~v1_relat_1(A_260) | ~v1_relat_1(A_260))), inference(superposition, [status(thm), theory('equality')], [c_50, c_1295])).
% 5.36/2.47  tff(c_1726, plain, (r2_hidden('#skF_7', k11_relat_1('#skF_8', '#skF_6')) | ~r2_hidden('#skF_6', k1_relat_1('#skF_8')) | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_491, c_1652])).
% 5.36/2.47  tff(c_1771, plain, (r2_hidden('#skF_7', k11_relat_1('#skF_8', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_623, c_1726])).
% 5.36/2.47  tff(c_1773, plain, $false, inference(negUnitSimplification, [status(thm)], [c_490, c_1771])).
% 5.36/2.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.36/2.47  
% 5.36/2.47  Inference rules
% 5.36/2.47  ----------------------
% 5.36/2.47  #Ref     : 0
% 5.36/2.47  #Sup     : 351
% 5.36/2.47  #Fact    : 0
% 5.36/2.47  #Define  : 0
% 5.36/2.47  #Split   : 2
% 5.36/2.47  #Chain   : 0
% 5.36/2.47  #Close   : 0
% 5.36/2.47  
% 5.36/2.47  Ordering : KBO
% 5.36/2.47  
% 5.36/2.47  Simplification rules
% 5.36/2.47  ----------------------
% 5.36/2.47  #Subsume      : 26
% 5.36/2.47  #Demod        : 42
% 5.36/2.47  #Tautology    : 44
% 5.36/2.47  #SimpNegUnit  : 4
% 5.36/2.47  #BackRed      : 0
% 5.36/2.47  
% 5.36/2.47  #Partial instantiations: 0
% 5.36/2.47  #Strategies tried      : 1
% 5.36/2.47  
% 5.36/2.47  Timing (in seconds)
% 5.36/2.47  ----------------------
% 5.36/2.48  Preprocessing        : 0.52
% 5.36/2.48  Parsing              : 0.25
% 5.36/2.48  CNF conversion       : 0.04
% 5.36/2.48  Main loop            : 0.99
% 5.36/2.48  Inferencing          : 0.37
% 5.36/2.48  Reduction            : 0.29
% 5.36/2.48  Demodulation         : 0.21
% 5.36/2.48  BG Simplification    : 0.06
% 5.36/2.48  Subsumption          : 0.19
% 5.36/2.48  Abstraction          : 0.07
% 5.36/2.48  MUC search           : 0.00
% 5.36/2.48  Cooper               : 0.00
% 5.36/2.48  Total                : 1.56
% 5.36/2.48  Index Insertion      : 0.00
% 5.36/2.48  Index Deletion       : 0.00
% 5.36/2.48  Index Matching       : 0.00
% 5.36/2.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
