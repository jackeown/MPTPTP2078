%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:07 EST 2020

% Result     : Theorem 5.64s
% Output     : CNFRefutation 5.89s
% Verified   : 
% Statistics : Number of formulae       :   48 (  63 expanded)
%              Number of leaves         :   19 (  32 expanded)
%              Depth                    :   12
%              Number of atoms          :  103 ( 161 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k9_relat_1 > k4_tarski > #nlpp > k1_relat_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ! [D] :
            ( v1_relat_1(D)
           => ( ( r1_tarski(C,D)
                & r1_tarski(A,B) )
             => r1_tarski(k9_relat_1(C,A),k9_relat_1(D,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( r1_tarski(B,C)
           => r1_tarski(k9_relat_1(B,A),k9_relat_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(c_26,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_24,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_22,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_16,plain,(
    ! [B_13,A_12,C_15] :
      ( r1_tarski(k9_relat_1(B_13,A_12),k9_relat_1(C_15,A_12))
      | ~ r1_tarski(B_13,C_15)
      | ~ v1_relat_1(C_15)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_35,plain,(
    ! [C_22,B_23,A_24] :
      ( r2_hidden(C_22,B_23)
      | ~ r2_hidden(C_22,A_24)
      | ~ r1_tarski(A_24,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_38,plain,(
    ! [A_1,B_2,B_23] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_23)
      | ~ r1_tarski(A_1,B_23)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_35])).

tff(c_20,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_28,plain,(
    ! [A_19,B_20] :
      ( ~ r2_hidden('#skF_1'(A_19,B_20),B_20)
      | r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_33,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_28])).

tff(c_53,plain,(
    ! [A_34,B_35,C_36] :
      ( r2_hidden('#skF_2'(A_34,B_35,C_36),k1_relat_1(C_36))
      | ~ r2_hidden(A_34,k9_relat_1(C_36,B_35))
      | ~ v1_relat_1(C_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_56,plain,(
    ! [A_34,B_35,C_36,B_2] :
      ( r2_hidden('#skF_2'(A_34,B_35,C_36),B_2)
      | ~ r1_tarski(k1_relat_1(C_36),B_2)
      | ~ r2_hidden(A_34,k9_relat_1(C_36,B_35))
      | ~ v1_relat_1(C_36) ) ),
    inference(resolution,[status(thm)],[c_53,c_2])).

tff(c_12,plain,(
    ! [A_6,B_7,C_8] :
      ( r2_hidden(k4_tarski('#skF_2'(A_6,B_7,C_8),A_6),C_8)
      | ~ r2_hidden(A_6,k9_relat_1(C_8,B_7))
      | ~ v1_relat_1(C_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_39,plain,(
    ! [A_25,B_26,C_27] :
      ( r2_hidden('#skF_2'(A_25,B_26,C_27),B_26)
      | ~ r2_hidden(A_25,k9_relat_1(C_27,B_26))
      | ~ v1_relat_1(C_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_42,plain,(
    ! [A_25,B_26,C_27,B_2] :
      ( r2_hidden('#skF_2'(A_25,B_26,C_27),B_2)
      | ~ r1_tarski(B_26,B_2)
      | ~ r2_hidden(A_25,k9_relat_1(C_27,B_26))
      | ~ v1_relat_1(C_27) ) ),
    inference(resolution,[status(thm)],[c_39,c_2])).

tff(c_142,plain,(
    ! [A_68,C_69,B_70,D_71] :
      ( r2_hidden(A_68,k9_relat_1(C_69,B_70))
      | ~ r2_hidden(D_71,B_70)
      | ~ r2_hidden(k4_tarski(D_71,A_68),C_69)
      | ~ r2_hidden(D_71,k1_relat_1(C_69))
      | ~ v1_relat_1(C_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1518,plain,(
    ! [A_266,A_261,B_264,C_265,B_263,C_262] :
      ( r2_hidden(A_266,k9_relat_1(C_265,B_264))
      | ~ r2_hidden(k4_tarski('#skF_2'(A_261,B_263,C_262),A_266),C_265)
      | ~ r2_hidden('#skF_2'(A_261,B_263,C_262),k1_relat_1(C_265))
      | ~ v1_relat_1(C_265)
      | ~ r1_tarski(B_263,B_264)
      | ~ r2_hidden(A_261,k9_relat_1(C_262,B_263))
      | ~ v1_relat_1(C_262) ) ),
    inference(resolution,[status(thm)],[c_42,c_142])).

tff(c_1894,plain,(
    ! [A_315,C_316,B_317,B_318] :
      ( r2_hidden(A_315,k9_relat_1(C_316,B_317))
      | ~ r2_hidden('#skF_2'(A_315,B_318,C_316),k1_relat_1(C_316))
      | ~ r1_tarski(B_318,B_317)
      | ~ r2_hidden(A_315,k9_relat_1(C_316,B_318))
      | ~ v1_relat_1(C_316) ) ),
    inference(resolution,[status(thm)],[c_12,c_1518])).

tff(c_1909,plain,(
    ! [A_34,C_36,B_317,B_35] :
      ( r2_hidden(A_34,k9_relat_1(C_36,B_317))
      | ~ r1_tarski(B_35,B_317)
      | ~ r1_tarski(k1_relat_1(C_36),k1_relat_1(C_36))
      | ~ r2_hidden(A_34,k9_relat_1(C_36,B_35))
      | ~ v1_relat_1(C_36) ) ),
    inference(resolution,[status(thm)],[c_56,c_1894])).

tff(c_1928,plain,(
    ! [A_319,C_320,B_321,B_322] :
      ( r2_hidden(A_319,k9_relat_1(C_320,B_321))
      | ~ r1_tarski(B_322,B_321)
      | ~ r2_hidden(A_319,k9_relat_1(C_320,B_322))
      | ~ v1_relat_1(C_320) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_1909])).

tff(c_2080,plain,(
    ! [A_329,C_330] :
      ( r2_hidden(A_329,k9_relat_1(C_330,'#skF_4'))
      | ~ r2_hidden(A_329,k9_relat_1(C_330,'#skF_3'))
      | ~ v1_relat_1(C_330) ) ),
    inference(resolution,[status(thm)],[c_20,c_1928])).

tff(c_2364,plain,(
    ! [A_346,B_347,C_348] :
      ( r2_hidden('#skF_1'(A_346,B_347),k9_relat_1(C_348,'#skF_4'))
      | ~ v1_relat_1(C_348)
      | ~ r1_tarski(A_346,k9_relat_1(C_348,'#skF_3'))
      | r1_tarski(A_346,B_347) ) ),
    inference(resolution,[status(thm)],[c_38,c_2080])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2389,plain,(
    ! [C_349,A_350] :
      ( ~ v1_relat_1(C_349)
      | ~ r1_tarski(A_350,k9_relat_1(C_349,'#skF_3'))
      | r1_tarski(A_350,k9_relat_1(C_349,'#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_2364,c_4])).

tff(c_2449,plain,(
    ! [B_353,C_354] :
      ( r1_tarski(k9_relat_1(B_353,'#skF_3'),k9_relat_1(C_354,'#skF_4'))
      | ~ r1_tarski(B_353,C_354)
      | ~ v1_relat_1(C_354)
      | ~ v1_relat_1(B_353) ) ),
    inference(resolution,[status(thm)],[c_16,c_2389])).

tff(c_18,plain,(
    ~ r1_tarski(k9_relat_1('#skF_5','#skF_3'),k9_relat_1('#skF_6','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2472,plain,
    ( ~ r1_tarski('#skF_5','#skF_6')
    | ~ v1_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_2449,c_18])).

tff(c_2486,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_22,c_2472])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n021.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 17:19:34 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.64/2.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.89/2.12  
% 5.89/2.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.89/2.12  %$ r2_hidden > r1_tarski > v1_relat_1 > k9_relat_1 > k4_tarski > #nlpp > k1_relat_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4 > #skF_1
% 5.89/2.12  
% 5.89/2.12  %Foreground sorts:
% 5.89/2.12  
% 5.89/2.12  
% 5.89/2.12  %Background operators:
% 5.89/2.12  
% 5.89/2.12  
% 5.89/2.12  %Foreground operators:
% 5.89/2.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.89/2.12  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.89/2.12  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.89/2.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.89/2.12  tff('#skF_5', type, '#skF_5': $i).
% 5.89/2.12  tff('#skF_6', type, '#skF_6': $i).
% 5.89/2.12  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.89/2.12  tff('#skF_3', type, '#skF_3': $i).
% 5.89/2.12  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.89/2.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.89/2.12  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.89/2.12  tff('#skF_4', type, '#skF_4': $i).
% 5.89/2.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.89/2.12  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.89/2.12  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.89/2.12  
% 5.89/2.13  tff(f_64, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(C, D) & r1_tarski(A, B)) => r1_tarski(k9_relat_1(C, A), k9_relat_1(D, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t158_relat_1)).
% 5.89/2.13  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(B, C) => r1_tarski(k9_relat_1(B, A), k9_relat_1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t157_relat_1)).
% 5.89/2.13  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.89/2.13  tff(f_43, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 5.89/2.13  tff(c_26, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.89/2.13  tff(c_24, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.89/2.13  tff(c_22, plain, (r1_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.89/2.13  tff(c_16, plain, (![B_13, A_12, C_15]: (r1_tarski(k9_relat_1(B_13, A_12), k9_relat_1(C_15, A_12)) | ~r1_tarski(B_13, C_15) | ~v1_relat_1(C_15) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.89/2.13  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.89/2.13  tff(c_35, plain, (![C_22, B_23, A_24]: (r2_hidden(C_22, B_23) | ~r2_hidden(C_22, A_24) | ~r1_tarski(A_24, B_23))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.89/2.13  tff(c_38, plain, (![A_1, B_2, B_23]: (r2_hidden('#skF_1'(A_1, B_2), B_23) | ~r1_tarski(A_1, B_23) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_35])).
% 5.89/2.13  tff(c_20, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.89/2.13  tff(c_28, plain, (![A_19, B_20]: (~r2_hidden('#skF_1'(A_19, B_20), B_20) | r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.89/2.13  tff(c_33, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_28])).
% 5.89/2.13  tff(c_53, plain, (![A_34, B_35, C_36]: (r2_hidden('#skF_2'(A_34, B_35, C_36), k1_relat_1(C_36)) | ~r2_hidden(A_34, k9_relat_1(C_36, B_35)) | ~v1_relat_1(C_36))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.89/2.13  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.89/2.13  tff(c_56, plain, (![A_34, B_35, C_36, B_2]: (r2_hidden('#skF_2'(A_34, B_35, C_36), B_2) | ~r1_tarski(k1_relat_1(C_36), B_2) | ~r2_hidden(A_34, k9_relat_1(C_36, B_35)) | ~v1_relat_1(C_36))), inference(resolution, [status(thm)], [c_53, c_2])).
% 5.89/2.13  tff(c_12, plain, (![A_6, B_7, C_8]: (r2_hidden(k4_tarski('#skF_2'(A_6, B_7, C_8), A_6), C_8) | ~r2_hidden(A_6, k9_relat_1(C_8, B_7)) | ~v1_relat_1(C_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.89/2.13  tff(c_39, plain, (![A_25, B_26, C_27]: (r2_hidden('#skF_2'(A_25, B_26, C_27), B_26) | ~r2_hidden(A_25, k9_relat_1(C_27, B_26)) | ~v1_relat_1(C_27))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.89/2.13  tff(c_42, plain, (![A_25, B_26, C_27, B_2]: (r2_hidden('#skF_2'(A_25, B_26, C_27), B_2) | ~r1_tarski(B_26, B_2) | ~r2_hidden(A_25, k9_relat_1(C_27, B_26)) | ~v1_relat_1(C_27))), inference(resolution, [status(thm)], [c_39, c_2])).
% 5.89/2.13  tff(c_142, plain, (![A_68, C_69, B_70, D_71]: (r2_hidden(A_68, k9_relat_1(C_69, B_70)) | ~r2_hidden(D_71, B_70) | ~r2_hidden(k4_tarski(D_71, A_68), C_69) | ~r2_hidden(D_71, k1_relat_1(C_69)) | ~v1_relat_1(C_69))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.89/2.13  tff(c_1518, plain, (![A_266, A_261, B_264, C_265, B_263, C_262]: (r2_hidden(A_266, k9_relat_1(C_265, B_264)) | ~r2_hidden(k4_tarski('#skF_2'(A_261, B_263, C_262), A_266), C_265) | ~r2_hidden('#skF_2'(A_261, B_263, C_262), k1_relat_1(C_265)) | ~v1_relat_1(C_265) | ~r1_tarski(B_263, B_264) | ~r2_hidden(A_261, k9_relat_1(C_262, B_263)) | ~v1_relat_1(C_262))), inference(resolution, [status(thm)], [c_42, c_142])).
% 5.89/2.13  tff(c_1894, plain, (![A_315, C_316, B_317, B_318]: (r2_hidden(A_315, k9_relat_1(C_316, B_317)) | ~r2_hidden('#skF_2'(A_315, B_318, C_316), k1_relat_1(C_316)) | ~r1_tarski(B_318, B_317) | ~r2_hidden(A_315, k9_relat_1(C_316, B_318)) | ~v1_relat_1(C_316))), inference(resolution, [status(thm)], [c_12, c_1518])).
% 5.89/2.13  tff(c_1909, plain, (![A_34, C_36, B_317, B_35]: (r2_hidden(A_34, k9_relat_1(C_36, B_317)) | ~r1_tarski(B_35, B_317) | ~r1_tarski(k1_relat_1(C_36), k1_relat_1(C_36)) | ~r2_hidden(A_34, k9_relat_1(C_36, B_35)) | ~v1_relat_1(C_36))), inference(resolution, [status(thm)], [c_56, c_1894])).
% 5.89/2.13  tff(c_1928, plain, (![A_319, C_320, B_321, B_322]: (r2_hidden(A_319, k9_relat_1(C_320, B_321)) | ~r1_tarski(B_322, B_321) | ~r2_hidden(A_319, k9_relat_1(C_320, B_322)) | ~v1_relat_1(C_320))), inference(demodulation, [status(thm), theory('equality')], [c_33, c_1909])).
% 5.89/2.13  tff(c_2080, plain, (![A_329, C_330]: (r2_hidden(A_329, k9_relat_1(C_330, '#skF_4')) | ~r2_hidden(A_329, k9_relat_1(C_330, '#skF_3')) | ~v1_relat_1(C_330))), inference(resolution, [status(thm)], [c_20, c_1928])).
% 5.89/2.13  tff(c_2364, plain, (![A_346, B_347, C_348]: (r2_hidden('#skF_1'(A_346, B_347), k9_relat_1(C_348, '#skF_4')) | ~v1_relat_1(C_348) | ~r1_tarski(A_346, k9_relat_1(C_348, '#skF_3')) | r1_tarski(A_346, B_347))), inference(resolution, [status(thm)], [c_38, c_2080])).
% 5.89/2.13  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.89/2.13  tff(c_2389, plain, (![C_349, A_350]: (~v1_relat_1(C_349) | ~r1_tarski(A_350, k9_relat_1(C_349, '#skF_3')) | r1_tarski(A_350, k9_relat_1(C_349, '#skF_4')))), inference(resolution, [status(thm)], [c_2364, c_4])).
% 5.89/2.13  tff(c_2449, plain, (![B_353, C_354]: (r1_tarski(k9_relat_1(B_353, '#skF_3'), k9_relat_1(C_354, '#skF_4')) | ~r1_tarski(B_353, C_354) | ~v1_relat_1(C_354) | ~v1_relat_1(B_353))), inference(resolution, [status(thm)], [c_16, c_2389])).
% 5.89/2.13  tff(c_18, plain, (~r1_tarski(k9_relat_1('#skF_5', '#skF_3'), k9_relat_1('#skF_6', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.89/2.13  tff(c_2472, plain, (~r1_tarski('#skF_5', '#skF_6') | ~v1_relat_1('#skF_6') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_2449, c_18])).
% 5.89/2.13  tff(c_2486, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_22, c_2472])).
% 5.89/2.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.89/2.13  
% 5.89/2.13  Inference rules
% 5.89/2.13  ----------------------
% 5.89/2.13  #Ref     : 0
% 5.89/2.13  #Sup     : 582
% 5.89/2.13  #Fact    : 0
% 5.89/2.13  #Define  : 0
% 5.89/2.13  #Split   : 11
% 5.89/2.13  #Chain   : 0
% 5.89/2.13  #Close   : 0
% 5.89/2.13  
% 5.89/2.13  Ordering : KBO
% 5.89/2.13  
% 5.89/2.13  Simplification rules
% 5.89/2.13  ----------------------
% 5.89/2.13  #Subsume      : 98
% 5.89/2.13  #Demod        : 94
% 5.89/2.14  #Tautology    : 12
% 5.89/2.14  #SimpNegUnit  : 1
% 5.89/2.14  #BackRed      : 0
% 5.89/2.14  
% 5.89/2.14  #Partial instantiations: 0
% 5.89/2.14  #Strategies tried      : 1
% 5.89/2.14  
% 5.89/2.14  Timing (in seconds)
% 5.89/2.14  ----------------------
% 5.89/2.14  Preprocessing        : 0.28
% 5.89/2.14  Parsing              : 0.16
% 5.89/2.14  CNF conversion       : 0.02
% 5.89/2.14  Main loop            : 1.02
% 5.89/2.14  Inferencing          : 0.32
% 5.89/2.14  Reduction            : 0.22
% 5.89/2.14  Demodulation         : 0.14
% 5.89/2.14  BG Simplification    : 0.03
% 5.89/2.14  Subsumption          : 0.38
% 5.89/2.14  Abstraction          : 0.04
% 5.89/2.14  MUC search           : 0.00
% 5.89/2.14  Cooper               : 0.00
% 5.89/2.14  Total                : 1.33
% 5.89/2.14  Index Insertion      : 0.00
% 5.89/2.14  Index Deletion       : 0.00
% 5.89/2.14  Index Matching       : 0.00
% 5.89/2.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
