%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:33 EST 2020

% Result     : Theorem 9.98s
% Output     : CNFRefutation 9.98s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 113 expanded)
%              Number of leaves         :   19 (  48 expanded)
%              Depth                    :   12
%              Number of atoms          :  109 ( 299 expanded)
%              Number of equality atoms :   19 (  48 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k9_relat_1 > k4_tarski > #nlpp > k2_relat_1 > k1_relat_1 > #skF_4 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_57,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

tff(c_28,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_75,plain,(
    ! [A_56,B_57] :
      ( r2_hidden(k4_tarski('#skF_2'(A_56,B_57),'#skF_1'(A_56,B_57)),A_56)
      | r2_hidden('#skF_3'(A_56,B_57),B_57)
      | k2_relat_1(A_56) = B_57 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [C_16,A_1,D_19] :
      ( r2_hidden(C_16,k2_relat_1(A_1))
      | ~ r2_hidden(k4_tarski(D_19,C_16),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_89,plain,(
    ! [A_58,B_59] :
      ( r2_hidden('#skF_1'(A_58,B_59),k2_relat_1(A_58))
      | r2_hidden('#skF_3'(A_58,B_59),B_59)
      | k2_relat_1(A_58) = B_59 ) ),
    inference(resolution,[status(thm)],[c_75,c_4])).

tff(c_44,plain,(
    ! [A_47,B_48,C_49] :
      ( r2_hidden(k4_tarski('#skF_5'(A_47,B_48,C_49),A_47),C_49)
      | ~ r2_hidden(A_47,k9_relat_1(C_49,B_48))
      | ~ v1_relat_1(C_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_52,plain,(
    ! [A_47,C_49,B_48] :
      ( r2_hidden(A_47,k2_relat_1(C_49))
      | ~ r2_hidden(A_47,k9_relat_1(C_49,B_48))
      | ~ v1_relat_1(C_49) ) ),
    inference(resolution,[status(thm)],[c_44,c_4])).

tff(c_289,plain,(
    ! [A_88,C_89,B_90] :
      ( r2_hidden('#skF_3'(A_88,k9_relat_1(C_89,B_90)),k2_relat_1(C_89))
      | ~ v1_relat_1(C_89)
      | r2_hidden('#skF_1'(A_88,k9_relat_1(C_89,B_90)),k2_relat_1(A_88))
      | k9_relat_1(C_89,B_90) = k2_relat_1(A_88) ) ),
    inference(resolution,[status(thm)],[c_89,c_52])).

tff(c_2,plain,(
    ! [A_1,C_16] :
      ( r2_hidden(k4_tarski('#skF_4'(A_1,k2_relat_1(A_1),C_16),C_16),A_1)
      | ~ r2_hidden(C_16,k2_relat_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_102,plain,(
    ! [A_62,B_63,D_64] :
      ( r2_hidden(k4_tarski('#skF_2'(A_62,B_63),'#skF_1'(A_62,B_63)),A_62)
      | ~ r2_hidden(k4_tarski(D_64,'#skF_3'(A_62,B_63)),A_62)
      | k2_relat_1(A_62) = B_63 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_111,plain,(
    ! [A_65,B_66] :
      ( r2_hidden(k4_tarski('#skF_2'(A_65,B_66),'#skF_1'(A_65,B_66)),A_65)
      | k2_relat_1(A_65) = B_66
      | ~ r2_hidden('#skF_3'(A_65,B_66),k2_relat_1(A_65)) ) ),
    inference(resolution,[status(thm)],[c_2,c_102])).

tff(c_124,plain,(
    ! [A_65,B_66] :
      ( r2_hidden('#skF_1'(A_65,B_66),k2_relat_1(A_65))
      | k2_relat_1(A_65) = B_66
      | ~ r2_hidden('#skF_3'(A_65,B_66),k2_relat_1(A_65)) ) ),
    inference(resolution,[status(thm)],[c_111,c_4])).

tff(c_313,plain,(
    ! [C_89,B_90] :
      ( ~ v1_relat_1(C_89)
      | r2_hidden('#skF_1'(C_89,k9_relat_1(C_89,B_90)),k2_relat_1(C_89))
      | k9_relat_1(C_89,B_90) = k2_relat_1(C_89) ) ),
    inference(resolution,[status(thm)],[c_289,c_124])).

tff(c_31,plain,(
    ! [A_35,C_36] :
      ( r2_hidden(k4_tarski('#skF_4'(A_35,k2_relat_1(A_35),C_36),C_36),A_35)
      | ~ r2_hidden(C_36,k2_relat_1(A_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_24,plain,(
    ! [A_26,C_28,B_27] :
      ( r2_hidden(A_26,k1_relat_1(C_28))
      | ~ r2_hidden(k4_tarski(A_26,B_27),C_28)
      | ~ v1_relat_1(C_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_38,plain,(
    ! [A_35,C_36] :
      ( r2_hidden('#skF_4'(A_35,k2_relat_1(A_35),C_36),k1_relat_1(A_35))
      | ~ v1_relat_1(A_35)
      | ~ r2_hidden(C_36,k2_relat_1(A_35)) ) ),
    inference(resolution,[status(thm)],[c_31,c_24])).

tff(c_163,plain,(
    ! [A_71,C_72,B_73,D_74] :
      ( r2_hidden(A_71,k9_relat_1(C_72,B_73))
      | ~ r2_hidden(D_74,B_73)
      | ~ r2_hidden(k4_tarski(D_74,A_71),C_72)
      | ~ r2_hidden(D_74,k1_relat_1(C_72))
      | ~ v1_relat_1(C_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2487,plain,(
    ! [A_327,C_328,A_329,C_330] :
      ( r2_hidden(A_327,k9_relat_1(C_328,k1_relat_1(A_329)))
      | ~ r2_hidden(k4_tarski('#skF_4'(A_329,k2_relat_1(A_329),C_330),A_327),C_328)
      | ~ r2_hidden('#skF_4'(A_329,k2_relat_1(A_329),C_330),k1_relat_1(C_328))
      | ~ v1_relat_1(C_328)
      | ~ v1_relat_1(A_329)
      | ~ r2_hidden(C_330,k2_relat_1(A_329)) ) ),
    inference(resolution,[status(thm)],[c_38,c_163])).

tff(c_2512,plain,(
    ! [C_331,A_332] :
      ( r2_hidden(C_331,k9_relat_1(A_332,k1_relat_1(A_332)))
      | ~ r2_hidden('#skF_4'(A_332,k2_relat_1(A_332),C_331),k1_relat_1(A_332))
      | ~ v1_relat_1(A_332)
      | ~ r2_hidden(C_331,k2_relat_1(A_332)) ) ),
    inference(resolution,[status(thm)],[c_2,c_2487])).

tff(c_2522,plain,(
    ! [C_333,A_334] :
      ( r2_hidden(C_333,k9_relat_1(A_334,k1_relat_1(A_334)))
      | ~ v1_relat_1(A_334)
      | ~ r2_hidden(C_333,k2_relat_1(A_334)) ) ),
    inference(resolution,[status(thm)],[c_38,c_2512])).

tff(c_10,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r2_hidden('#skF_3'(A_1,B_2),B_2)
      | k2_relat_1(A_1) = B_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_53,plain,(
    ! [A_50,C_51,B_52] :
      ( r2_hidden(A_50,k2_relat_1(C_51))
      | ~ r2_hidden(A_50,k9_relat_1(C_51,B_52))
      | ~ v1_relat_1(C_51) ) ),
    inference(resolution,[status(thm)],[c_44,c_4])).

tff(c_72,plain,(
    ! [A_1,C_51,B_52] :
      ( r2_hidden('#skF_3'(A_1,k9_relat_1(C_51,B_52)),k2_relat_1(C_51))
      | ~ v1_relat_1(C_51)
      | ~ r2_hidden('#skF_1'(A_1,k9_relat_1(C_51,B_52)),k9_relat_1(C_51,B_52))
      | k9_relat_1(C_51,B_52) = k2_relat_1(A_1) ) ),
    inference(resolution,[status(thm)],[c_10,c_53])).

tff(c_2622,plain,(
    ! [A_1,A_334] :
      ( r2_hidden('#skF_3'(A_1,k9_relat_1(A_334,k1_relat_1(A_334))),k2_relat_1(A_334))
      | k9_relat_1(A_334,k1_relat_1(A_334)) = k2_relat_1(A_1)
      | ~ v1_relat_1(A_334)
      | ~ r2_hidden('#skF_1'(A_1,k9_relat_1(A_334,k1_relat_1(A_334))),k2_relat_1(A_334)) ) ),
    inference(resolution,[status(thm)],[c_2522,c_72])).

tff(c_6,plain,(
    ! [A_1,B_2,D_15] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | ~ r2_hidden(k4_tarski(D_15,'#skF_3'(A_1,B_2)),A_1)
      | k2_relat_1(A_1) = B_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6874,plain,(
    ! [D_461,A_462,A_463] :
      ( ~ r2_hidden(k4_tarski(D_461,'#skF_3'(A_462,k9_relat_1(A_463,k1_relat_1(A_463)))),A_462)
      | k9_relat_1(A_463,k1_relat_1(A_463)) = k2_relat_1(A_462)
      | ~ v1_relat_1(A_463)
      | ~ r2_hidden('#skF_1'(A_462,k9_relat_1(A_463,k1_relat_1(A_463))),k2_relat_1(A_463)) ) ),
    inference(resolution,[status(thm)],[c_2522,c_6])).

tff(c_6951,plain,(
    ! [A_464,A_465] :
      ( k9_relat_1(A_464,k1_relat_1(A_464)) = k2_relat_1(A_465)
      | ~ v1_relat_1(A_464)
      | ~ r2_hidden('#skF_1'(A_465,k9_relat_1(A_464,k1_relat_1(A_464))),k2_relat_1(A_464))
      | ~ r2_hidden('#skF_3'(A_465,k9_relat_1(A_464,k1_relat_1(A_464))),k2_relat_1(A_465)) ) ),
    inference(resolution,[status(thm)],[c_2,c_6874])).

tff(c_6997,plain,(
    ! [C_466] :
      ( ~ r2_hidden('#skF_3'(C_466,k9_relat_1(C_466,k1_relat_1(C_466))),k2_relat_1(C_466))
      | ~ v1_relat_1(C_466)
      | k9_relat_1(C_466,k1_relat_1(C_466)) = k2_relat_1(C_466) ) ),
    inference(resolution,[status(thm)],[c_313,c_6951])).

tff(c_7109,plain,(
    ! [A_473] :
      ( k9_relat_1(A_473,k1_relat_1(A_473)) = k2_relat_1(A_473)
      | ~ v1_relat_1(A_473)
      | ~ r2_hidden('#skF_1'(A_473,k9_relat_1(A_473,k1_relat_1(A_473))),k2_relat_1(A_473)) ) ),
    inference(resolution,[status(thm)],[c_2622,c_6997])).

tff(c_7160,plain,(
    ! [C_474] :
      ( ~ v1_relat_1(C_474)
      | k9_relat_1(C_474,k1_relat_1(C_474)) = k2_relat_1(C_474) ) ),
    inference(resolution,[status(thm)],[c_313,c_7109])).

tff(c_26,plain,(
    k9_relat_1('#skF_6',k1_relat_1('#skF_6')) != k2_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_7639,plain,(
    ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_7160,c_26])).

tff(c_7649,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_7639])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:55:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.98/3.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.98/3.27  
% 9.98/3.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.98/3.27  %$ r2_hidden > v1_relat_1 > k9_relat_1 > k4_tarski > #nlpp > k2_relat_1 > k1_relat_1 > #skF_4 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_1
% 9.98/3.27  
% 9.98/3.27  %Foreground sorts:
% 9.98/3.27  
% 9.98/3.27  
% 9.98/3.27  %Background operators:
% 9.98/3.27  
% 9.98/3.27  
% 9.98/3.27  %Foreground operators:
% 9.98/3.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.98/3.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.98/3.27  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 9.98/3.27  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 9.98/3.27  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 9.98/3.27  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.98/3.27  tff('#skF_6', type, '#skF_6': $i).
% 9.98/3.27  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 9.98/3.27  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 9.98/3.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.98/3.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.98/3.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.98/3.27  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 9.98/3.27  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.98/3.27  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.98/3.27  
% 9.98/3.29  tff(f_57, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 9.98/3.29  tff(f_33, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 9.98/3.29  tff(f_44, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 9.98/3.29  tff(f_52, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_relat_1)).
% 9.98/3.29  tff(c_28, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.98/3.29  tff(c_75, plain, (![A_56, B_57]: (r2_hidden(k4_tarski('#skF_2'(A_56, B_57), '#skF_1'(A_56, B_57)), A_56) | r2_hidden('#skF_3'(A_56, B_57), B_57) | k2_relat_1(A_56)=B_57)), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.98/3.29  tff(c_4, plain, (![C_16, A_1, D_19]: (r2_hidden(C_16, k2_relat_1(A_1)) | ~r2_hidden(k4_tarski(D_19, C_16), A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.98/3.29  tff(c_89, plain, (![A_58, B_59]: (r2_hidden('#skF_1'(A_58, B_59), k2_relat_1(A_58)) | r2_hidden('#skF_3'(A_58, B_59), B_59) | k2_relat_1(A_58)=B_59)), inference(resolution, [status(thm)], [c_75, c_4])).
% 9.98/3.29  tff(c_44, plain, (![A_47, B_48, C_49]: (r2_hidden(k4_tarski('#skF_5'(A_47, B_48, C_49), A_47), C_49) | ~r2_hidden(A_47, k9_relat_1(C_49, B_48)) | ~v1_relat_1(C_49))), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.98/3.29  tff(c_52, plain, (![A_47, C_49, B_48]: (r2_hidden(A_47, k2_relat_1(C_49)) | ~r2_hidden(A_47, k9_relat_1(C_49, B_48)) | ~v1_relat_1(C_49))), inference(resolution, [status(thm)], [c_44, c_4])).
% 9.98/3.29  tff(c_289, plain, (![A_88, C_89, B_90]: (r2_hidden('#skF_3'(A_88, k9_relat_1(C_89, B_90)), k2_relat_1(C_89)) | ~v1_relat_1(C_89) | r2_hidden('#skF_1'(A_88, k9_relat_1(C_89, B_90)), k2_relat_1(A_88)) | k9_relat_1(C_89, B_90)=k2_relat_1(A_88))), inference(resolution, [status(thm)], [c_89, c_52])).
% 9.98/3.29  tff(c_2, plain, (![A_1, C_16]: (r2_hidden(k4_tarski('#skF_4'(A_1, k2_relat_1(A_1), C_16), C_16), A_1) | ~r2_hidden(C_16, k2_relat_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.98/3.29  tff(c_102, plain, (![A_62, B_63, D_64]: (r2_hidden(k4_tarski('#skF_2'(A_62, B_63), '#skF_1'(A_62, B_63)), A_62) | ~r2_hidden(k4_tarski(D_64, '#skF_3'(A_62, B_63)), A_62) | k2_relat_1(A_62)=B_63)), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.98/3.29  tff(c_111, plain, (![A_65, B_66]: (r2_hidden(k4_tarski('#skF_2'(A_65, B_66), '#skF_1'(A_65, B_66)), A_65) | k2_relat_1(A_65)=B_66 | ~r2_hidden('#skF_3'(A_65, B_66), k2_relat_1(A_65)))), inference(resolution, [status(thm)], [c_2, c_102])).
% 9.98/3.29  tff(c_124, plain, (![A_65, B_66]: (r2_hidden('#skF_1'(A_65, B_66), k2_relat_1(A_65)) | k2_relat_1(A_65)=B_66 | ~r2_hidden('#skF_3'(A_65, B_66), k2_relat_1(A_65)))), inference(resolution, [status(thm)], [c_111, c_4])).
% 9.98/3.29  tff(c_313, plain, (![C_89, B_90]: (~v1_relat_1(C_89) | r2_hidden('#skF_1'(C_89, k9_relat_1(C_89, B_90)), k2_relat_1(C_89)) | k9_relat_1(C_89, B_90)=k2_relat_1(C_89))), inference(resolution, [status(thm)], [c_289, c_124])).
% 9.98/3.29  tff(c_31, plain, (![A_35, C_36]: (r2_hidden(k4_tarski('#skF_4'(A_35, k2_relat_1(A_35), C_36), C_36), A_35) | ~r2_hidden(C_36, k2_relat_1(A_35)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.98/3.29  tff(c_24, plain, (![A_26, C_28, B_27]: (r2_hidden(A_26, k1_relat_1(C_28)) | ~r2_hidden(k4_tarski(A_26, B_27), C_28) | ~v1_relat_1(C_28))), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.98/3.29  tff(c_38, plain, (![A_35, C_36]: (r2_hidden('#skF_4'(A_35, k2_relat_1(A_35), C_36), k1_relat_1(A_35)) | ~v1_relat_1(A_35) | ~r2_hidden(C_36, k2_relat_1(A_35)))), inference(resolution, [status(thm)], [c_31, c_24])).
% 9.98/3.29  tff(c_163, plain, (![A_71, C_72, B_73, D_74]: (r2_hidden(A_71, k9_relat_1(C_72, B_73)) | ~r2_hidden(D_74, B_73) | ~r2_hidden(k4_tarski(D_74, A_71), C_72) | ~r2_hidden(D_74, k1_relat_1(C_72)) | ~v1_relat_1(C_72))), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.98/3.29  tff(c_2487, plain, (![A_327, C_328, A_329, C_330]: (r2_hidden(A_327, k9_relat_1(C_328, k1_relat_1(A_329))) | ~r2_hidden(k4_tarski('#skF_4'(A_329, k2_relat_1(A_329), C_330), A_327), C_328) | ~r2_hidden('#skF_4'(A_329, k2_relat_1(A_329), C_330), k1_relat_1(C_328)) | ~v1_relat_1(C_328) | ~v1_relat_1(A_329) | ~r2_hidden(C_330, k2_relat_1(A_329)))), inference(resolution, [status(thm)], [c_38, c_163])).
% 9.98/3.29  tff(c_2512, plain, (![C_331, A_332]: (r2_hidden(C_331, k9_relat_1(A_332, k1_relat_1(A_332))) | ~r2_hidden('#skF_4'(A_332, k2_relat_1(A_332), C_331), k1_relat_1(A_332)) | ~v1_relat_1(A_332) | ~r2_hidden(C_331, k2_relat_1(A_332)))), inference(resolution, [status(thm)], [c_2, c_2487])).
% 9.98/3.29  tff(c_2522, plain, (![C_333, A_334]: (r2_hidden(C_333, k9_relat_1(A_334, k1_relat_1(A_334))) | ~v1_relat_1(A_334) | ~r2_hidden(C_333, k2_relat_1(A_334)))), inference(resolution, [status(thm)], [c_38, c_2512])).
% 9.98/3.29  tff(c_10, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r2_hidden('#skF_3'(A_1, B_2), B_2) | k2_relat_1(A_1)=B_2)), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.98/3.29  tff(c_53, plain, (![A_50, C_51, B_52]: (r2_hidden(A_50, k2_relat_1(C_51)) | ~r2_hidden(A_50, k9_relat_1(C_51, B_52)) | ~v1_relat_1(C_51))), inference(resolution, [status(thm)], [c_44, c_4])).
% 9.98/3.29  tff(c_72, plain, (![A_1, C_51, B_52]: (r2_hidden('#skF_3'(A_1, k9_relat_1(C_51, B_52)), k2_relat_1(C_51)) | ~v1_relat_1(C_51) | ~r2_hidden('#skF_1'(A_1, k9_relat_1(C_51, B_52)), k9_relat_1(C_51, B_52)) | k9_relat_1(C_51, B_52)=k2_relat_1(A_1))), inference(resolution, [status(thm)], [c_10, c_53])).
% 9.98/3.29  tff(c_2622, plain, (![A_1, A_334]: (r2_hidden('#skF_3'(A_1, k9_relat_1(A_334, k1_relat_1(A_334))), k2_relat_1(A_334)) | k9_relat_1(A_334, k1_relat_1(A_334))=k2_relat_1(A_1) | ~v1_relat_1(A_334) | ~r2_hidden('#skF_1'(A_1, k9_relat_1(A_334, k1_relat_1(A_334))), k2_relat_1(A_334)))), inference(resolution, [status(thm)], [c_2522, c_72])).
% 9.98/3.29  tff(c_6, plain, (![A_1, B_2, D_15]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | ~r2_hidden(k4_tarski(D_15, '#skF_3'(A_1, B_2)), A_1) | k2_relat_1(A_1)=B_2)), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.98/3.29  tff(c_6874, plain, (![D_461, A_462, A_463]: (~r2_hidden(k4_tarski(D_461, '#skF_3'(A_462, k9_relat_1(A_463, k1_relat_1(A_463)))), A_462) | k9_relat_1(A_463, k1_relat_1(A_463))=k2_relat_1(A_462) | ~v1_relat_1(A_463) | ~r2_hidden('#skF_1'(A_462, k9_relat_1(A_463, k1_relat_1(A_463))), k2_relat_1(A_463)))), inference(resolution, [status(thm)], [c_2522, c_6])).
% 9.98/3.29  tff(c_6951, plain, (![A_464, A_465]: (k9_relat_1(A_464, k1_relat_1(A_464))=k2_relat_1(A_465) | ~v1_relat_1(A_464) | ~r2_hidden('#skF_1'(A_465, k9_relat_1(A_464, k1_relat_1(A_464))), k2_relat_1(A_464)) | ~r2_hidden('#skF_3'(A_465, k9_relat_1(A_464, k1_relat_1(A_464))), k2_relat_1(A_465)))), inference(resolution, [status(thm)], [c_2, c_6874])).
% 9.98/3.29  tff(c_6997, plain, (![C_466]: (~r2_hidden('#skF_3'(C_466, k9_relat_1(C_466, k1_relat_1(C_466))), k2_relat_1(C_466)) | ~v1_relat_1(C_466) | k9_relat_1(C_466, k1_relat_1(C_466))=k2_relat_1(C_466))), inference(resolution, [status(thm)], [c_313, c_6951])).
% 9.98/3.29  tff(c_7109, plain, (![A_473]: (k9_relat_1(A_473, k1_relat_1(A_473))=k2_relat_1(A_473) | ~v1_relat_1(A_473) | ~r2_hidden('#skF_1'(A_473, k9_relat_1(A_473, k1_relat_1(A_473))), k2_relat_1(A_473)))), inference(resolution, [status(thm)], [c_2622, c_6997])).
% 9.98/3.29  tff(c_7160, plain, (![C_474]: (~v1_relat_1(C_474) | k9_relat_1(C_474, k1_relat_1(C_474))=k2_relat_1(C_474))), inference(resolution, [status(thm)], [c_313, c_7109])).
% 9.98/3.29  tff(c_26, plain, (k9_relat_1('#skF_6', k1_relat_1('#skF_6'))!=k2_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.98/3.29  tff(c_7639, plain, (~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_7160, c_26])).
% 9.98/3.29  tff(c_7649, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_7639])).
% 9.98/3.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.98/3.29  
% 9.98/3.29  Inference rules
% 9.98/3.29  ----------------------
% 9.98/3.29  #Ref     : 0
% 9.98/3.29  #Sup     : 1839
% 9.98/3.29  #Fact    : 0
% 9.98/3.29  #Define  : 0
% 9.98/3.29  #Split   : 0
% 9.98/3.29  #Chain   : 0
% 9.98/3.29  #Close   : 0
% 9.98/3.29  
% 9.98/3.29  Ordering : KBO
% 9.98/3.29  
% 9.98/3.29  Simplification rules
% 9.98/3.29  ----------------------
% 9.98/3.29  #Subsume      : 175
% 9.98/3.29  #Demod        : 1
% 9.98/3.29  #Tautology    : 60
% 9.98/3.29  #SimpNegUnit  : 0
% 9.98/3.29  #BackRed      : 0
% 9.98/3.29  
% 9.98/3.29  #Partial instantiations: 0
% 9.98/3.29  #Strategies tried      : 1
% 9.98/3.29  
% 9.98/3.29  Timing (in seconds)
% 9.98/3.29  ----------------------
% 9.98/3.29  Preprocessing        : 0.31
% 9.98/3.29  Parsing              : 0.16
% 9.98/3.29  CNF conversion       : 0.03
% 9.98/3.29  Main loop            : 2.15
% 9.98/3.29  Inferencing          : 0.71
% 9.98/3.29  Reduction            : 0.37
% 9.98/3.29  Demodulation         : 0.23
% 9.98/3.29  BG Simplification    : 0.09
% 9.98/3.29  Subsumption          : 0.80
% 9.98/3.29  Abstraction          : 0.14
% 9.98/3.29  MUC search           : 0.00
% 9.98/3.29  Cooper               : 0.00
% 9.98/3.29  Total                : 2.49
% 9.98/3.29  Index Insertion      : 0.00
% 9.98/3.29  Index Deletion       : 0.00
% 9.98/3.29  Index Matching       : 0.00
% 9.98/3.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
