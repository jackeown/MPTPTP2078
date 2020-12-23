%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:31 EST 2020

% Result     : Theorem 3.65s
% Output     : CNFRefutation 3.65s
% Verified   : 
% Statistics : Number of formulae       :   41 (  59 expanded)
%              Number of leaves         :   19 (  29 expanded)
%              Depth                    :    7
%              Number of atoms          :   66 ( 112 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k5_relat_1 > k4_tarski > #nlpp > k6_relat_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_43,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_66,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(k5_relat_1(B,k6_relat_1(A)),B)
          & r1_tarski(k5_relat_1(k6_relat_1(A),B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_tarski(A,B)
        <=> ! [C,D] :
              ( r2_hidden(k4_tarski(C,D),A)
             => r2_hidden(k4_tarski(C,D),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).

tff(f_51,axiom,(
    ! [A,B,C,D] :
      ( v1_relat_1(D)
     => ( r2_hidden(k4_tarski(A,B),k5_relat_1(k6_relat_1(C),D))
      <=> ( r2_hidden(A,C)
          & r2_hidden(k4_tarski(A,B),D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_relat_1)).

tff(f_59,axiom,(
    ! [A,B,C,D] :
      ( v1_relat_1(D)
     => ( r2_hidden(k4_tarski(A,B),k5_relat_1(D,k6_relat_1(C)))
      <=> ( r2_hidden(B,C)
          & r2_hidden(k4_tarski(A,B),D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_relat_1)).

tff(c_10,plain,(
    ! [A_20] : v1_relat_1(k6_relat_1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_26,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_8,plain,(
    ! [A_18,B_19] :
      ( v1_relat_1(k5_relat_1(A_18,B_19))
      | ~ v1_relat_1(B_19)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6,plain,(
    ! [A_1,B_11] :
      ( r2_hidden(k4_tarski('#skF_1'(A_1,B_11),'#skF_2'(A_1,B_11)),A_1)
      | r1_tarski(A_1,B_11)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_458,plain,(
    ! [A_186,B_187,D_188,C_189] :
      ( r2_hidden(k4_tarski(A_186,B_187),D_188)
      | ~ r2_hidden(k4_tarski(A_186,B_187),k5_relat_1(k6_relat_1(C_189),D_188))
      | ~ v1_relat_1(D_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_812,plain,(
    ! [C_309,D_310,B_311] :
      ( r2_hidden(k4_tarski('#skF_1'(k5_relat_1(k6_relat_1(C_309),D_310),B_311),'#skF_2'(k5_relat_1(k6_relat_1(C_309),D_310),B_311)),D_310)
      | ~ v1_relat_1(D_310)
      | r1_tarski(k5_relat_1(k6_relat_1(C_309),D_310),B_311)
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(C_309),D_310)) ) ),
    inference(resolution,[status(thm)],[c_6,c_458])).

tff(c_4,plain,(
    ! [A_1,B_11] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_1,B_11),'#skF_2'(A_1,B_11)),B_11)
      | r1_tarski(A_1,B_11)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_865,plain,(
    ! [D_312,C_313] :
      ( ~ v1_relat_1(D_312)
      | r1_tarski(k5_relat_1(k6_relat_1(C_313),D_312),D_312)
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(C_313),D_312)) ) ),
    inference(resolution,[status(thm)],[c_812,c_4])).

tff(c_56,plain,(
    ! [A_49,B_50,D_51,C_52] :
      ( r2_hidden(k4_tarski(A_49,B_50),D_51)
      | ~ r2_hidden(k4_tarski(A_49,B_50),k5_relat_1(D_51,k6_relat_1(C_52)))
      | ~ v1_relat_1(D_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_329,plain,(
    ! [D_168,C_169,B_170] :
      ( r2_hidden(k4_tarski('#skF_1'(k5_relat_1(D_168,k6_relat_1(C_169)),B_170),'#skF_2'(k5_relat_1(D_168,k6_relat_1(C_169)),B_170)),D_168)
      | ~ v1_relat_1(D_168)
      | r1_tarski(k5_relat_1(D_168,k6_relat_1(C_169)),B_170)
      | ~ v1_relat_1(k5_relat_1(D_168,k6_relat_1(C_169))) ) ),
    inference(resolution,[status(thm)],[c_6,c_56])).

tff(c_382,plain,(
    ! [D_171,C_172] :
      ( ~ v1_relat_1(D_171)
      | r1_tarski(k5_relat_1(D_171,k6_relat_1(C_172)),D_171)
      | ~ v1_relat_1(k5_relat_1(D_171,k6_relat_1(C_172))) ) ),
    inference(resolution,[status(thm)],[c_329,c_4])).

tff(c_24,plain,
    ( ~ r1_tarski(k5_relat_1(k6_relat_1('#skF_3'),'#skF_4'),'#skF_4')
    | ~ r1_tarski(k5_relat_1('#skF_4',k6_relat_1('#skF_3')),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_29,plain,(
    ~ r1_tarski(k5_relat_1('#skF_4',k6_relat_1('#skF_3')),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_410,plain,
    ( ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1(k5_relat_1('#skF_4',k6_relat_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_382,c_29])).

tff(c_428,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_4',k6_relat_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_410])).

tff(c_431,plain,
    ( ~ v1_relat_1(k6_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_8,c_428])).

tff(c_435,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_10,c_431])).

tff(c_436,plain,(
    ~ r1_tarski(k5_relat_1(k6_relat_1('#skF_3'),'#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_897,plain,
    ( ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1(k5_relat_1(k6_relat_1('#skF_3'),'#skF_4')) ),
    inference(resolution,[status(thm)],[c_865,c_436])).

tff(c_918,plain,(
    ~ v1_relat_1(k5_relat_1(k6_relat_1('#skF_3'),'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_897])).

tff(c_921,plain,
    ( ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1(k6_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_8,c_918])).

tff(c_925,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_26,c_921])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:59:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.65/1.57  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.65/1.57  
% 3.65/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.65/1.57  %$ r2_hidden > r1_tarski > v1_relat_1 > k5_relat_1 > k4_tarski > #nlpp > k6_relat_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.65/1.57  
% 3.65/1.57  %Foreground sorts:
% 3.65/1.57  
% 3.65/1.57  
% 3.65/1.57  %Background operators:
% 3.65/1.57  
% 3.65/1.57  
% 3.65/1.57  %Foreground operators:
% 3.65/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.65/1.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.65/1.57  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.65/1.57  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.65/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.65/1.57  tff('#skF_3', type, '#skF_3': $i).
% 3.65/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.65/1.57  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.65/1.57  tff('#skF_4', type, '#skF_4': $i).
% 3.65/1.57  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.65/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.65/1.57  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.65/1.57  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.65/1.57  
% 3.65/1.59  tff(f_43, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 3.65/1.59  tff(f_66, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(k5_relat_1(B, k6_relat_1(A)), B) & r1_tarski(k5_relat_1(k6_relat_1(A), B), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_relat_1)).
% 3.65/1.59  tff(f_41, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 3.65/1.59  tff(f_35, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_tarski(A, B) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), A) => r2_hidden(k4_tarski(C, D), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_relat_1)).
% 3.65/1.59  tff(f_51, axiom, (![A, B, C, D]: (v1_relat_1(D) => (r2_hidden(k4_tarski(A, B), k5_relat_1(k6_relat_1(C), D)) <=> (r2_hidden(A, C) & r2_hidden(k4_tarski(A, B), D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_relat_1)).
% 3.65/1.59  tff(f_59, axiom, (![A, B, C, D]: (v1_relat_1(D) => (r2_hidden(k4_tarski(A, B), k5_relat_1(D, k6_relat_1(C))) <=> (r2_hidden(B, C) & r2_hidden(k4_tarski(A, B), D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_relat_1)).
% 3.65/1.59  tff(c_10, plain, (![A_20]: (v1_relat_1(k6_relat_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.65/1.59  tff(c_26, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.65/1.59  tff(c_8, plain, (![A_18, B_19]: (v1_relat_1(k5_relat_1(A_18, B_19)) | ~v1_relat_1(B_19) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.65/1.59  tff(c_6, plain, (![A_1, B_11]: (r2_hidden(k4_tarski('#skF_1'(A_1, B_11), '#skF_2'(A_1, B_11)), A_1) | r1_tarski(A_1, B_11) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.65/1.59  tff(c_458, plain, (![A_186, B_187, D_188, C_189]: (r2_hidden(k4_tarski(A_186, B_187), D_188) | ~r2_hidden(k4_tarski(A_186, B_187), k5_relat_1(k6_relat_1(C_189), D_188)) | ~v1_relat_1(D_188))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.65/1.59  tff(c_812, plain, (![C_309, D_310, B_311]: (r2_hidden(k4_tarski('#skF_1'(k5_relat_1(k6_relat_1(C_309), D_310), B_311), '#skF_2'(k5_relat_1(k6_relat_1(C_309), D_310), B_311)), D_310) | ~v1_relat_1(D_310) | r1_tarski(k5_relat_1(k6_relat_1(C_309), D_310), B_311) | ~v1_relat_1(k5_relat_1(k6_relat_1(C_309), D_310)))), inference(resolution, [status(thm)], [c_6, c_458])).
% 3.65/1.59  tff(c_4, plain, (![A_1, B_11]: (~r2_hidden(k4_tarski('#skF_1'(A_1, B_11), '#skF_2'(A_1, B_11)), B_11) | r1_tarski(A_1, B_11) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.65/1.59  tff(c_865, plain, (![D_312, C_313]: (~v1_relat_1(D_312) | r1_tarski(k5_relat_1(k6_relat_1(C_313), D_312), D_312) | ~v1_relat_1(k5_relat_1(k6_relat_1(C_313), D_312)))), inference(resolution, [status(thm)], [c_812, c_4])).
% 3.65/1.59  tff(c_56, plain, (![A_49, B_50, D_51, C_52]: (r2_hidden(k4_tarski(A_49, B_50), D_51) | ~r2_hidden(k4_tarski(A_49, B_50), k5_relat_1(D_51, k6_relat_1(C_52))) | ~v1_relat_1(D_51))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.65/1.59  tff(c_329, plain, (![D_168, C_169, B_170]: (r2_hidden(k4_tarski('#skF_1'(k5_relat_1(D_168, k6_relat_1(C_169)), B_170), '#skF_2'(k5_relat_1(D_168, k6_relat_1(C_169)), B_170)), D_168) | ~v1_relat_1(D_168) | r1_tarski(k5_relat_1(D_168, k6_relat_1(C_169)), B_170) | ~v1_relat_1(k5_relat_1(D_168, k6_relat_1(C_169))))), inference(resolution, [status(thm)], [c_6, c_56])).
% 3.65/1.59  tff(c_382, plain, (![D_171, C_172]: (~v1_relat_1(D_171) | r1_tarski(k5_relat_1(D_171, k6_relat_1(C_172)), D_171) | ~v1_relat_1(k5_relat_1(D_171, k6_relat_1(C_172))))), inference(resolution, [status(thm)], [c_329, c_4])).
% 3.65/1.59  tff(c_24, plain, (~r1_tarski(k5_relat_1(k6_relat_1('#skF_3'), '#skF_4'), '#skF_4') | ~r1_tarski(k5_relat_1('#skF_4', k6_relat_1('#skF_3')), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.65/1.59  tff(c_29, plain, (~r1_tarski(k5_relat_1('#skF_4', k6_relat_1('#skF_3')), '#skF_4')), inference(splitLeft, [status(thm)], [c_24])).
% 3.65/1.59  tff(c_410, plain, (~v1_relat_1('#skF_4') | ~v1_relat_1(k5_relat_1('#skF_4', k6_relat_1('#skF_3')))), inference(resolution, [status(thm)], [c_382, c_29])).
% 3.65/1.59  tff(c_428, plain, (~v1_relat_1(k5_relat_1('#skF_4', k6_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_410])).
% 3.65/1.59  tff(c_431, plain, (~v1_relat_1(k6_relat_1('#skF_3')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_8, c_428])).
% 3.65/1.59  tff(c_435, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_10, c_431])).
% 3.65/1.59  tff(c_436, plain, (~r1_tarski(k5_relat_1(k6_relat_1('#skF_3'), '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_24])).
% 3.65/1.59  tff(c_897, plain, (~v1_relat_1('#skF_4') | ~v1_relat_1(k5_relat_1(k6_relat_1('#skF_3'), '#skF_4'))), inference(resolution, [status(thm)], [c_865, c_436])).
% 3.65/1.59  tff(c_918, plain, (~v1_relat_1(k5_relat_1(k6_relat_1('#skF_3'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_897])).
% 3.65/1.59  tff(c_921, plain, (~v1_relat_1('#skF_4') | ~v1_relat_1(k6_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_8, c_918])).
% 3.65/1.59  tff(c_925, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_26, c_921])).
% 3.65/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.65/1.59  
% 3.65/1.59  Inference rules
% 3.65/1.59  ----------------------
% 3.65/1.59  #Ref     : 0
% 3.65/1.59  #Sup     : 172
% 3.65/1.59  #Fact    : 0
% 3.65/1.59  #Define  : 0
% 3.65/1.59  #Split   : 2
% 3.65/1.59  #Chain   : 0
% 3.65/1.59  #Close   : 0
% 3.65/1.59  
% 3.65/1.59  Ordering : KBO
% 3.65/1.59  
% 3.65/1.59  Simplification rules
% 3.65/1.59  ----------------------
% 3.65/1.59  #Subsume      : 27
% 3.65/1.59  #Demod        : 69
% 3.65/1.59  #Tautology    : 18
% 3.65/1.59  #SimpNegUnit  : 0
% 3.65/1.59  #BackRed      : 0
% 3.65/1.59  
% 3.65/1.59  #Partial instantiations: 0
% 3.65/1.59  #Strategies tried      : 1
% 3.65/1.59  
% 3.65/1.59  Timing (in seconds)
% 3.65/1.59  ----------------------
% 3.65/1.59  Preprocessing        : 0.29
% 3.65/1.59  Parsing              : 0.15
% 3.65/1.59  CNF conversion       : 0.02
% 3.65/1.59  Main loop            : 0.54
% 3.65/1.59  Inferencing          : 0.22
% 3.65/1.59  Reduction            : 0.12
% 3.65/1.59  Demodulation         : 0.09
% 3.65/1.59  BG Simplification    : 0.02
% 3.65/1.59  Subsumption          : 0.14
% 3.65/1.59  Abstraction          : 0.02
% 3.65/1.59  MUC search           : 0.00
% 3.65/1.59  Cooper               : 0.00
% 3.65/1.59  Total                : 0.86
% 3.65/1.59  Index Insertion      : 0.00
% 3.65/1.59  Index Deletion       : 0.00
% 3.65/1.59  Index Matching       : 0.00
% 3.65/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
