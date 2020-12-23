%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:05 EST 2020

% Result     : Theorem 3.43s
% Output     : CNFRefutation 3.43s
% Verified   : 
% Statistics : Number of formulae       :   41 (  60 expanded)
%              Number of leaves         :   17 (  30 expanded)
%              Depth                    :   12
%              Number of atoms          :   86 ( 144 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k9_relat_1 > k4_tarski > #nlpp > k1_relat_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_1

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

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_relat_1)).

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

tff(c_20,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_22,plain,(
    ! [A_14,B_15] :
      ( ~ r2_hidden('#skF_1'(A_14,B_15),B_15)
      | r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_27,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_22])).

tff(c_46,plain,(
    ! [A_26,B_27,C_28] :
      ( r2_hidden('#skF_2'(A_26,B_27,C_28),k1_relat_1(C_28))
      | ~ r2_hidden(A_26,k9_relat_1(C_28,B_27))
      | ~ v1_relat_1(C_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_49,plain,(
    ! [A_26,B_27,C_28,B_2] :
      ( r2_hidden('#skF_2'(A_26,B_27,C_28),B_2)
      | ~ r1_tarski(k1_relat_1(C_28),B_2)
      | ~ r2_hidden(A_26,k9_relat_1(C_28,B_27))
      | ~ v1_relat_1(C_28) ) ),
    inference(resolution,[status(thm)],[c_46,c_2])).

tff(c_12,plain,(
    ! [A_6,B_7,C_8] :
      ( r2_hidden(k4_tarski('#skF_2'(A_6,B_7,C_8),A_6),C_8)
      | ~ r2_hidden(A_6,k9_relat_1(C_8,B_7))
      | ~ v1_relat_1(C_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_18,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_42,plain,(
    ! [A_23,B_24,C_25] :
      ( r2_hidden('#skF_2'(A_23,B_24,C_25),B_24)
      | ~ r2_hidden(A_23,k9_relat_1(C_25,B_24))
      | ~ v1_relat_1(C_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_91,plain,(
    ! [A_44,B_45,C_46,B_47] :
      ( r2_hidden('#skF_2'(A_44,B_45,C_46),B_47)
      | ~ r1_tarski(B_45,B_47)
      | ~ r2_hidden(A_44,k9_relat_1(C_46,B_45))
      | ~ v1_relat_1(C_46) ) ),
    inference(resolution,[status(thm)],[c_42,c_2])).

tff(c_141,plain,(
    ! [B_66,B_67,B_64,C_65,A_68] :
      ( r2_hidden('#skF_2'(A_68,B_66,C_65),B_67)
      | ~ r1_tarski(B_64,B_67)
      | ~ r1_tarski(B_66,B_64)
      | ~ r2_hidden(A_68,k9_relat_1(C_65,B_66))
      | ~ v1_relat_1(C_65) ) ),
    inference(resolution,[status(thm)],[c_91,c_2])).

tff(c_148,plain,(
    ! [A_69,B_70,C_71] :
      ( r2_hidden('#skF_2'(A_69,B_70,C_71),'#skF_4')
      | ~ r1_tarski(B_70,'#skF_3')
      | ~ r2_hidden(A_69,k9_relat_1(C_71,B_70))
      | ~ v1_relat_1(C_71) ) ),
    inference(resolution,[status(thm)],[c_18,c_141])).

tff(c_8,plain,(
    ! [A_6,C_8,B_7,D_11] :
      ( r2_hidden(A_6,k9_relat_1(C_8,B_7))
      | ~ r2_hidden(D_11,B_7)
      | ~ r2_hidden(k4_tarski(D_11,A_6),C_8)
      | ~ r2_hidden(D_11,k1_relat_1(C_8))
      | ~ v1_relat_1(C_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_733,plain,(
    ! [A_213,B_210,C_212,C_214,A_211] :
      ( r2_hidden(A_213,k9_relat_1(C_212,'#skF_4'))
      | ~ r2_hidden(k4_tarski('#skF_2'(A_211,B_210,C_214),A_213),C_212)
      | ~ r2_hidden('#skF_2'(A_211,B_210,C_214),k1_relat_1(C_212))
      | ~ v1_relat_1(C_212)
      | ~ r1_tarski(B_210,'#skF_3')
      | ~ r2_hidden(A_211,k9_relat_1(C_214,B_210))
      | ~ v1_relat_1(C_214) ) ),
    inference(resolution,[status(thm)],[c_148,c_8])).

tff(c_750,plain,(
    ! [A_215,C_216,B_217] :
      ( r2_hidden(A_215,k9_relat_1(C_216,'#skF_4'))
      | ~ r2_hidden('#skF_2'(A_215,B_217,C_216),k1_relat_1(C_216))
      | ~ r1_tarski(B_217,'#skF_3')
      | ~ r2_hidden(A_215,k9_relat_1(C_216,B_217))
      | ~ v1_relat_1(C_216) ) ),
    inference(resolution,[status(thm)],[c_12,c_733])).

tff(c_762,plain,(
    ! [A_26,C_28,B_27] :
      ( r2_hidden(A_26,k9_relat_1(C_28,'#skF_4'))
      | ~ r1_tarski(B_27,'#skF_3')
      | ~ r1_tarski(k1_relat_1(C_28),k1_relat_1(C_28))
      | ~ r2_hidden(A_26,k9_relat_1(C_28,B_27))
      | ~ v1_relat_1(C_28) ) ),
    inference(resolution,[status(thm)],[c_49,c_750])).

tff(c_782,plain,(
    ! [A_218,C_219,B_220] :
      ( r2_hidden(A_218,k9_relat_1(C_219,'#skF_4'))
      | ~ r1_tarski(B_220,'#skF_3')
      | ~ r2_hidden(A_218,k9_relat_1(C_219,B_220))
      | ~ v1_relat_1(C_219) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27,c_762])).

tff(c_849,plain,(
    ! [C_227,B_228,B_229] :
      ( r2_hidden('#skF_1'(k9_relat_1(C_227,B_228),B_229),k9_relat_1(C_227,'#skF_4'))
      | ~ r1_tarski(B_228,'#skF_3')
      | ~ v1_relat_1(C_227)
      | r1_tarski(k9_relat_1(C_227,B_228),B_229) ) ),
    inference(resolution,[status(thm)],[c_6,c_782])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_870,plain,(
    ! [B_230,C_231] :
      ( ~ r1_tarski(B_230,'#skF_3')
      | ~ v1_relat_1(C_231)
      | r1_tarski(k9_relat_1(C_231,B_230),k9_relat_1(C_231,'#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_849,c_4])).

tff(c_16,plain,(
    ~ r1_tarski(k9_relat_1('#skF_5','#skF_3'),k9_relat_1('#skF_5','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_898,plain,
    ( ~ r1_tarski('#skF_3','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_870,c_16])).

tff(c_914,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_27,c_898])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:46:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.43/1.58  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.43/1.59  
% 3.43/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.43/1.59  %$ r2_hidden > r1_tarski > v1_relat_1 > k9_relat_1 > k4_tarski > #nlpp > k1_relat_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_1
% 3.43/1.59  
% 3.43/1.59  %Foreground sorts:
% 3.43/1.59  
% 3.43/1.59  
% 3.43/1.59  %Background operators:
% 3.43/1.59  
% 3.43/1.59  
% 3.43/1.59  %Foreground operators:
% 3.43/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.43/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.43/1.59  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.43/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.43/1.59  tff('#skF_5', type, '#skF_5': $i).
% 3.43/1.59  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.43/1.59  tff('#skF_3', type, '#skF_3': $i).
% 3.43/1.59  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.43/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.43/1.59  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.43/1.59  tff('#skF_4', type, '#skF_4': $i).
% 3.43/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.43/1.59  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.43/1.59  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.43/1.59  
% 3.43/1.60  tff(f_50, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t156_relat_1)).
% 3.43/1.60  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.43/1.60  tff(f_43, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 3.43/1.60  tff(c_20, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.43/1.60  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.43/1.60  tff(c_22, plain, (![A_14, B_15]: (~r2_hidden('#skF_1'(A_14, B_15), B_15) | r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.43/1.60  tff(c_27, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_22])).
% 3.43/1.60  tff(c_46, plain, (![A_26, B_27, C_28]: (r2_hidden('#skF_2'(A_26, B_27, C_28), k1_relat_1(C_28)) | ~r2_hidden(A_26, k9_relat_1(C_28, B_27)) | ~v1_relat_1(C_28))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.43/1.60  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.43/1.60  tff(c_49, plain, (![A_26, B_27, C_28, B_2]: (r2_hidden('#skF_2'(A_26, B_27, C_28), B_2) | ~r1_tarski(k1_relat_1(C_28), B_2) | ~r2_hidden(A_26, k9_relat_1(C_28, B_27)) | ~v1_relat_1(C_28))), inference(resolution, [status(thm)], [c_46, c_2])).
% 3.43/1.60  tff(c_12, plain, (![A_6, B_7, C_8]: (r2_hidden(k4_tarski('#skF_2'(A_6, B_7, C_8), A_6), C_8) | ~r2_hidden(A_6, k9_relat_1(C_8, B_7)) | ~v1_relat_1(C_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.43/1.60  tff(c_18, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.43/1.60  tff(c_42, plain, (![A_23, B_24, C_25]: (r2_hidden('#skF_2'(A_23, B_24, C_25), B_24) | ~r2_hidden(A_23, k9_relat_1(C_25, B_24)) | ~v1_relat_1(C_25))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.43/1.60  tff(c_91, plain, (![A_44, B_45, C_46, B_47]: (r2_hidden('#skF_2'(A_44, B_45, C_46), B_47) | ~r1_tarski(B_45, B_47) | ~r2_hidden(A_44, k9_relat_1(C_46, B_45)) | ~v1_relat_1(C_46))), inference(resolution, [status(thm)], [c_42, c_2])).
% 3.43/1.60  tff(c_141, plain, (![B_66, B_67, B_64, C_65, A_68]: (r2_hidden('#skF_2'(A_68, B_66, C_65), B_67) | ~r1_tarski(B_64, B_67) | ~r1_tarski(B_66, B_64) | ~r2_hidden(A_68, k9_relat_1(C_65, B_66)) | ~v1_relat_1(C_65))), inference(resolution, [status(thm)], [c_91, c_2])).
% 3.43/1.60  tff(c_148, plain, (![A_69, B_70, C_71]: (r2_hidden('#skF_2'(A_69, B_70, C_71), '#skF_4') | ~r1_tarski(B_70, '#skF_3') | ~r2_hidden(A_69, k9_relat_1(C_71, B_70)) | ~v1_relat_1(C_71))), inference(resolution, [status(thm)], [c_18, c_141])).
% 3.43/1.60  tff(c_8, plain, (![A_6, C_8, B_7, D_11]: (r2_hidden(A_6, k9_relat_1(C_8, B_7)) | ~r2_hidden(D_11, B_7) | ~r2_hidden(k4_tarski(D_11, A_6), C_8) | ~r2_hidden(D_11, k1_relat_1(C_8)) | ~v1_relat_1(C_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.43/1.60  tff(c_733, plain, (![A_213, B_210, C_212, C_214, A_211]: (r2_hidden(A_213, k9_relat_1(C_212, '#skF_4')) | ~r2_hidden(k4_tarski('#skF_2'(A_211, B_210, C_214), A_213), C_212) | ~r2_hidden('#skF_2'(A_211, B_210, C_214), k1_relat_1(C_212)) | ~v1_relat_1(C_212) | ~r1_tarski(B_210, '#skF_3') | ~r2_hidden(A_211, k9_relat_1(C_214, B_210)) | ~v1_relat_1(C_214))), inference(resolution, [status(thm)], [c_148, c_8])).
% 3.43/1.60  tff(c_750, plain, (![A_215, C_216, B_217]: (r2_hidden(A_215, k9_relat_1(C_216, '#skF_4')) | ~r2_hidden('#skF_2'(A_215, B_217, C_216), k1_relat_1(C_216)) | ~r1_tarski(B_217, '#skF_3') | ~r2_hidden(A_215, k9_relat_1(C_216, B_217)) | ~v1_relat_1(C_216))), inference(resolution, [status(thm)], [c_12, c_733])).
% 3.43/1.60  tff(c_762, plain, (![A_26, C_28, B_27]: (r2_hidden(A_26, k9_relat_1(C_28, '#skF_4')) | ~r1_tarski(B_27, '#skF_3') | ~r1_tarski(k1_relat_1(C_28), k1_relat_1(C_28)) | ~r2_hidden(A_26, k9_relat_1(C_28, B_27)) | ~v1_relat_1(C_28))), inference(resolution, [status(thm)], [c_49, c_750])).
% 3.43/1.60  tff(c_782, plain, (![A_218, C_219, B_220]: (r2_hidden(A_218, k9_relat_1(C_219, '#skF_4')) | ~r1_tarski(B_220, '#skF_3') | ~r2_hidden(A_218, k9_relat_1(C_219, B_220)) | ~v1_relat_1(C_219))), inference(demodulation, [status(thm), theory('equality')], [c_27, c_762])).
% 3.43/1.60  tff(c_849, plain, (![C_227, B_228, B_229]: (r2_hidden('#skF_1'(k9_relat_1(C_227, B_228), B_229), k9_relat_1(C_227, '#skF_4')) | ~r1_tarski(B_228, '#skF_3') | ~v1_relat_1(C_227) | r1_tarski(k9_relat_1(C_227, B_228), B_229))), inference(resolution, [status(thm)], [c_6, c_782])).
% 3.43/1.60  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.43/1.60  tff(c_870, plain, (![B_230, C_231]: (~r1_tarski(B_230, '#skF_3') | ~v1_relat_1(C_231) | r1_tarski(k9_relat_1(C_231, B_230), k9_relat_1(C_231, '#skF_4')))), inference(resolution, [status(thm)], [c_849, c_4])).
% 3.43/1.60  tff(c_16, plain, (~r1_tarski(k9_relat_1('#skF_5', '#skF_3'), k9_relat_1('#skF_5', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.43/1.60  tff(c_898, plain, (~r1_tarski('#skF_3', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_870, c_16])).
% 3.43/1.60  tff(c_914, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_27, c_898])).
% 3.43/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.43/1.60  
% 3.43/1.60  Inference rules
% 3.43/1.60  ----------------------
% 3.43/1.60  #Ref     : 0
% 3.43/1.60  #Sup     : 222
% 3.43/1.60  #Fact    : 0
% 3.43/1.60  #Define  : 0
% 3.43/1.60  #Split   : 2
% 3.43/1.60  #Chain   : 0
% 3.43/1.60  #Close   : 0
% 3.43/1.60  
% 3.43/1.60  Ordering : KBO
% 3.43/1.60  
% 3.43/1.60  Simplification rules
% 3.43/1.60  ----------------------
% 3.43/1.60  #Subsume      : 51
% 3.43/1.60  #Demod        : 15
% 3.43/1.60  #Tautology    : 7
% 3.43/1.60  #SimpNegUnit  : 0
% 3.43/1.60  #BackRed      : 0
% 3.43/1.60  
% 3.43/1.60  #Partial instantiations: 0
% 3.43/1.60  #Strategies tried      : 1
% 3.43/1.60  
% 3.43/1.60  Timing (in seconds)
% 3.43/1.60  ----------------------
% 3.43/1.60  Preprocessing        : 0.24
% 3.43/1.60  Parsing              : 0.13
% 3.43/1.60  CNF conversion       : 0.02
% 3.43/1.60  Main loop            : 0.55
% 3.43/1.60  Inferencing          : 0.19
% 3.43/1.60  Reduction            : 0.11
% 3.43/1.60  Demodulation         : 0.07
% 3.43/1.60  BG Simplification    : 0.02
% 3.43/1.60  Subsumption          : 0.21
% 3.43/1.60  Abstraction          : 0.02
% 3.43/1.60  MUC search           : 0.00
% 3.43/1.60  Cooper               : 0.00
% 3.43/1.61  Total                : 0.82
% 3.43/1.61  Index Insertion      : 0.00
% 3.43/1.61  Index Deletion       : 0.00
% 3.43/1.61  Index Matching       : 0.00
% 3.43/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
