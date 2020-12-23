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
% DateTime   : Thu Dec  3 10:00:15 EST 2020

% Result     : Theorem 5.64s
% Output     : CNFRefutation 5.64s
% Verified   : 
% Statistics : Number of formulae       :   55 (  76 expanded)
%              Number of leaves         :   27 (  39 expanded)
%              Depth                    :    9
%              Number of atoms          :  119 ( 161 expanded)
%              Number of equality atoms :    5 (   9 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k8_relat_1 > k5_relat_1 > k4_tarski > #nlpp > k6_relat_1 > #skF_6 > #skF_7 > #skF_3 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_51,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_88,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => r1_tarski(k8_relat_1(A,C),k8_relat_1(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t131_relat_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( ! [C] :
            ( r2_hidden(C,A)
           => r2_hidden(k4_tarski(C,C),B) )
       => r1_tarski(k6_relat_1(A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( B = k6_relat_1(A)
      <=> ! [C,D] :
            ( r2_hidden(k4_tarski(C,D),B)
          <=> ( r2_hidden(C,A)
              & C = D ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ! [D] :
                  ( v1_relat_1(D)
                 => ( ( r1_tarski(A,B)
                      & r1_tarski(C,D) )
                   => r1_tarski(k5_relat_1(A,C),k5_relat_1(B,D)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_relat_1)).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_32,plain,(
    ! [A_16] : v1_relat_1(k6_relat_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_44,plain,(
    r1_tarski('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_103,plain,(
    ! [A_58,B_59] :
      ( r2_hidden('#skF_6'(A_58,B_59),A_58)
      | r1_tarski(k6_relat_1(A_58),B_59)
      | ~ v1_relat_1(B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_121,plain,(
    ! [A_66,B_67,B_68] :
      ( r2_hidden('#skF_6'(A_66,B_67),B_68)
      | ~ r1_tarski(A_66,B_68)
      | r1_tarski(k6_relat_1(A_66),B_67)
      | ~ v1_relat_1(B_67) ) ),
    inference(resolution,[status(thm)],[c_103,c_2])).

tff(c_402,plain,(
    ! [A_121,B_122,B_123,B_124] :
      ( r2_hidden('#skF_6'(A_121,B_122),B_123)
      | ~ r1_tarski(B_124,B_123)
      | ~ r1_tarski(A_121,B_124)
      | r1_tarski(k6_relat_1(A_121),B_122)
      | ~ v1_relat_1(B_122) ) ),
    inference(resolution,[status(thm)],[c_121,c_2])).

tff(c_412,plain,(
    ! [A_125,B_126] :
      ( r2_hidden('#skF_6'(A_125,B_126),'#skF_8')
      | ~ r1_tarski(A_125,'#skF_7')
      | r1_tarski(k6_relat_1(A_125),B_126)
      | ~ v1_relat_1(B_126) ) ),
    inference(resolution,[status(thm)],[c_44,c_402])).

tff(c_701,plain,(
    ! [A_135,B_136,B_137] :
      ( r2_hidden('#skF_6'(A_135,B_136),B_137)
      | ~ r1_tarski('#skF_8',B_137)
      | ~ r1_tarski(A_135,'#skF_7')
      | r1_tarski(k6_relat_1(A_135),B_136)
      | ~ v1_relat_1(B_136) ) ),
    inference(resolution,[status(thm)],[c_412,c_2])).

tff(c_26,plain,(
    ! [D_15,A_8] :
      ( r2_hidden(k4_tarski(D_15,D_15),k6_relat_1(A_8))
      | ~ r2_hidden(D_15,A_8)
      | ~ v1_relat_1(k6_relat_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_52,plain,(
    ! [D_15,A_8] :
      ( r2_hidden(k4_tarski(D_15,D_15),k6_relat_1(A_8))
      | ~ r2_hidden(D_15,A_8) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_26])).

tff(c_125,plain,(
    ! [A_69,B_70] :
      ( ~ r2_hidden(k4_tarski('#skF_6'(A_69,B_70),'#skF_6'(A_69,B_70)),B_70)
      | r1_tarski(k6_relat_1(A_69),B_70)
      | ~ v1_relat_1(B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_129,plain,(
    ! [A_69,A_8] :
      ( r1_tarski(k6_relat_1(A_69),k6_relat_1(A_8))
      | ~ v1_relat_1(k6_relat_1(A_8))
      | ~ r2_hidden('#skF_6'(A_69,k6_relat_1(A_8)),A_8) ) ),
    inference(resolution,[status(thm)],[c_52,c_125])).

tff(c_132,plain,(
    ! [A_69,A_8] :
      ( r1_tarski(k6_relat_1(A_69),k6_relat_1(A_8))
      | ~ r2_hidden('#skF_6'(A_69,k6_relat_1(A_8)),A_8) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_129])).

tff(c_709,plain,(
    ! [B_137,A_135] :
      ( ~ r1_tarski('#skF_8',B_137)
      | ~ r1_tarski(A_135,'#skF_7')
      | r1_tarski(k6_relat_1(A_135),k6_relat_1(B_137))
      | ~ v1_relat_1(k6_relat_1(B_137)) ) ),
    inference(resolution,[status(thm)],[c_701,c_132])).

tff(c_716,plain,(
    ! [B_137,A_135] :
      ( ~ r1_tarski('#skF_8',B_137)
      | ~ r1_tarski(A_135,'#skF_7')
      | r1_tarski(k6_relat_1(A_135),k6_relat_1(B_137)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_709])).

tff(c_46,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_34,plain,(
    ! [B_18,A_17] :
      ( k5_relat_1(B_18,k6_relat_1(A_17)) = k8_relat_1(A_17,B_18)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1053,plain,(
    ! [A_146,C_147,B_148,D_149] :
      ( r1_tarski(k5_relat_1(A_146,C_147),k5_relat_1(B_148,D_149))
      | ~ r1_tarski(C_147,D_149)
      | ~ r1_tarski(A_146,B_148)
      | ~ v1_relat_1(D_149)
      | ~ v1_relat_1(C_147)
      | ~ v1_relat_1(B_148)
      | ~ v1_relat_1(A_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1072,plain,(
    ! [A_17,B_18,B_148,D_149] :
      ( r1_tarski(k8_relat_1(A_17,B_18),k5_relat_1(B_148,D_149))
      | ~ r1_tarski(k6_relat_1(A_17),D_149)
      | ~ r1_tarski(B_18,B_148)
      | ~ v1_relat_1(D_149)
      | ~ v1_relat_1(k6_relat_1(A_17))
      | ~ v1_relat_1(B_148)
      | ~ v1_relat_1(B_18)
      | ~ v1_relat_1(B_18) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_1053])).

tff(c_2702,plain,(
    ! [A_261,B_262,B_263,D_264] :
      ( r1_tarski(k8_relat_1(A_261,B_262),k5_relat_1(B_263,D_264))
      | ~ r1_tarski(k6_relat_1(A_261),D_264)
      | ~ r1_tarski(B_262,B_263)
      | ~ v1_relat_1(D_264)
      | ~ v1_relat_1(B_263)
      | ~ v1_relat_1(B_262) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1072])).

tff(c_2731,plain,(
    ! [A_261,B_262,A_17,B_18] :
      ( r1_tarski(k8_relat_1(A_261,B_262),k8_relat_1(A_17,B_18))
      | ~ r1_tarski(k6_relat_1(A_261),k6_relat_1(A_17))
      | ~ r1_tarski(B_262,B_18)
      | ~ v1_relat_1(k6_relat_1(A_17))
      | ~ v1_relat_1(B_18)
      | ~ v1_relat_1(B_262)
      | ~ v1_relat_1(B_18) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_2702])).

tff(c_2908,plain,(
    ! [A_275,B_276,A_277,B_278] :
      ( r1_tarski(k8_relat_1(A_275,B_276),k8_relat_1(A_277,B_278))
      | ~ r1_tarski(k6_relat_1(A_275),k6_relat_1(A_277))
      | ~ r1_tarski(B_276,B_278)
      | ~ v1_relat_1(B_276)
      | ~ v1_relat_1(B_278) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_2731])).

tff(c_42,plain,(
    ~ r1_tarski(k8_relat_1('#skF_7','#skF_9'),k8_relat_1('#skF_8','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2939,plain,
    ( ~ r1_tarski(k6_relat_1('#skF_7'),k6_relat_1('#skF_8'))
    | ~ r1_tarski('#skF_9','#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_2908,c_42])).

tff(c_2956,plain,(
    ~ r1_tarski(k6_relat_1('#skF_7'),k6_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_12,c_2939])).

tff(c_2959,plain,
    ( ~ r1_tarski('#skF_8','#skF_8')
    | ~ r1_tarski('#skF_7','#skF_7') ),
    inference(resolution,[status(thm)],[c_716,c_2956])).

tff(c_2969,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_12,c_2959])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:21:00 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.64/2.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.64/2.15  
% 5.64/2.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.64/2.16  %$ r2_hidden > r1_tarski > v1_relat_1 > k8_relat_1 > k5_relat_1 > k4_tarski > #nlpp > k6_relat_1 > #skF_6 > #skF_7 > #skF_3 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_5 > #skF_4
% 5.64/2.16  
% 5.64/2.16  %Foreground sorts:
% 5.64/2.16  
% 5.64/2.16  
% 5.64/2.16  %Background operators:
% 5.64/2.16  
% 5.64/2.16  
% 5.64/2.16  %Foreground operators:
% 5.64/2.16  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 5.64/2.16  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 5.64/2.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.64/2.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.64/2.16  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.64/2.16  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.64/2.16  tff('#skF_7', type, '#skF_7': $i).
% 5.64/2.16  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.64/2.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.64/2.16  tff('#skF_9', type, '#skF_9': $i).
% 5.64/2.16  tff('#skF_8', type, '#skF_8': $i).
% 5.64/2.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.64/2.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.64/2.16  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.64/2.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.64/2.16  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.64/2.16  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.64/2.16  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 5.64/2.16  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 5.64/2.16  
% 5.64/2.17  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.64/2.17  tff(f_51, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 5.64/2.17  tff(f_88, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k8_relat_1(A, C), k8_relat_1(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t131_relat_1)).
% 5.64/2.17  tff(f_81, axiom, (![A, B]: (v1_relat_1(B) => ((![C]: (r2_hidden(C, A) => r2_hidden(k4_tarski(C, C), B))) => r1_tarski(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_relat_1)).
% 5.64/2.17  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.64/2.17  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => ((B = k6_relat_1(A)) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), B) <=> (r2_hidden(C, A) & (C = D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_relat_1)).
% 5.64/2.17  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 5.64/2.17  tff(f_72, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k5_relat_1(A, C), k5_relat_1(B, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_relat_1)).
% 5.64/2.17  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.64/2.17  tff(c_32, plain, (![A_16]: (v1_relat_1(k6_relat_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.64/2.17  tff(c_44, plain, (r1_tarski('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.64/2.17  tff(c_103, plain, (![A_58, B_59]: (r2_hidden('#skF_6'(A_58, B_59), A_58) | r1_tarski(k6_relat_1(A_58), B_59) | ~v1_relat_1(B_59))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.64/2.17  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.64/2.17  tff(c_121, plain, (![A_66, B_67, B_68]: (r2_hidden('#skF_6'(A_66, B_67), B_68) | ~r1_tarski(A_66, B_68) | r1_tarski(k6_relat_1(A_66), B_67) | ~v1_relat_1(B_67))), inference(resolution, [status(thm)], [c_103, c_2])).
% 5.64/2.17  tff(c_402, plain, (![A_121, B_122, B_123, B_124]: (r2_hidden('#skF_6'(A_121, B_122), B_123) | ~r1_tarski(B_124, B_123) | ~r1_tarski(A_121, B_124) | r1_tarski(k6_relat_1(A_121), B_122) | ~v1_relat_1(B_122))), inference(resolution, [status(thm)], [c_121, c_2])).
% 5.64/2.17  tff(c_412, plain, (![A_125, B_126]: (r2_hidden('#skF_6'(A_125, B_126), '#skF_8') | ~r1_tarski(A_125, '#skF_7') | r1_tarski(k6_relat_1(A_125), B_126) | ~v1_relat_1(B_126))), inference(resolution, [status(thm)], [c_44, c_402])).
% 5.64/2.17  tff(c_701, plain, (![A_135, B_136, B_137]: (r2_hidden('#skF_6'(A_135, B_136), B_137) | ~r1_tarski('#skF_8', B_137) | ~r1_tarski(A_135, '#skF_7') | r1_tarski(k6_relat_1(A_135), B_136) | ~v1_relat_1(B_136))), inference(resolution, [status(thm)], [c_412, c_2])).
% 5.64/2.17  tff(c_26, plain, (![D_15, A_8]: (r2_hidden(k4_tarski(D_15, D_15), k6_relat_1(A_8)) | ~r2_hidden(D_15, A_8) | ~v1_relat_1(k6_relat_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.64/2.17  tff(c_52, plain, (![D_15, A_8]: (r2_hidden(k4_tarski(D_15, D_15), k6_relat_1(A_8)) | ~r2_hidden(D_15, A_8))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_26])).
% 5.64/2.17  tff(c_125, plain, (![A_69, B_70]: (~r2_hidden(k4_tarski('#skF_6'(A_69, B_70), '#skF_6'(A_69, B_70)), B_70) | r1_tarski(k6_relat_1(A_69), B_70) | ~v1_relat_1(B_70))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.64/2.17  tff(c_129, plain, (![A_69, A_8]: (r1_tarski(k6_relat_1(A_69), k6_relat_1(A_8)) | ~v1_relat_1(k6_relat_1(A_8)) | ~r2_hidden('#skF_6'(A_69, k6_relat_1(A_8)), A_8))), inference(resolution, [status(thm)], [c_52, c_125])).
% 5.64/2.17  tff(c_132, plain, (![A_69, A_8]: (r1_tarski(k6_relat_1(A_69), k6_relat_1(A_8)) | ~r2_hidden('#skF_6'(A_69, k6_relat_1(A_8)), A_8))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_129])).
% 5.64/2.17  tff(c_709, plain, (![B_137, A_135]: (~r1_tarski('#skF_8', B_137) | ~r1_tarski(A_135, '#skF_7') | r1_tarski(k6_relat_1(A_135), k6_relat_1(B_137)) | ~v1_relat_1(k6_relat_1(B_137)))), inference(resolution, [status(thm)], [c_701, c_132])).
% 5.64/2.17  tff(c_716, plain, (![B_137, A_135]: (~r1_tarski('#skF_8', B_137) | ~r1_tarski(A_135, '#skF_7') | r1_tarski(k6_relat_1(A_135), k6_relat_1(B_137)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_709])).
% 5.64/2.17  tff(c_46, plain, (v1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.64/2.17  tff(c_34, plain, (![B_18, A_17]: (k5_relat_1(B_18, k6_relat_1(A_17))=k8_relat_1(A_17, B_18) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.64/2.17  tff(c_1053, plain, (![A_146, C_147, B_148, D_149]: (r1_tarski(k5_relat_1(A_146, C_147), k5_relat_1(B_148, D_149)) | ~r1_tarski(C_147, D_149) | ~r1_tarski(A_146, B_148) | ~v1_relat_1(D_149) | ~v1_relat_1(C_147) | ~v1_relat_1(B_148) | ~v1_relat_1(A_146))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.64/2.17  tff(c_1072, plain, (![A_17, B_18, B_148, D_149]: (r1_tarski(k8_relat_1(A_17, B_18), k5_relat_1(B_148, D_149)) | ~r1_tarski(k6_relat_1(A_17), D_149) | ~r1_tarski(B_18, B_148) | ~v1_relat_1(D_149) | ~v1_relat_1(k6_relat_1(A_17)) | ~v1_relat_1(B_148) | ~v1_relat_1(B_18) | ~v1_relat_1(B_18))), inference(superposition, [status(thm), theory('equality')], [c_34, c_1053])).
% 5.64/2.17  tff(c_2702, plain, (![A_261, B_262, B_263, D_264]: (r1_tarski(k8_relat_1(A_261, B_262), k5_relat_1(B_263, D_264)) | ~r1_tarski(k6_relat_1(A_261), D_264) | ~r1_tarski(B_262, B_263) | ~v1_relat_1(D_264) | ~v1_relat_1(B_263) | ~v1_relat_1(B_262))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1072])).
% 5.64/2.17  tff(c_2731, plain, (![A_261, B_262, A_17, B_18]: (r1_tarski(k8_relat_1(A_261, B_262), k8_relat_1(A_17, B_18)) | ~r1_tarski(k6_relat_1(A_261), k6_relat_1(A_17)) | ~r1_tarski(B_262, B_18) | ~v1_relat_1(k6_relat_1(A_17)) | ~v1_relat_1(B_18) | ~v1_relat_1(B_262) | ~v1_relat_1(B_18))), inference(superposition, [status(thm), theory('equality')], [c_34, c_2702])).
% 5.64/2.17  tff(c_2908, plain, (![A_275, B_276, A_277, B_278]: (r1_tarski(k8_relat_1(A_275, B_276), k8_relat_1(A_277, B_278)) | ~r1_tarski(k6_relat_1(A_275), k6_relat_1(A_277)) | ~r1_tarski(B_276, B_278) | ~v1_relat_1(B_276) | ~v1_relat_1(B_278))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_2731])).
% 5.64/2.17  tff(c_42, plain, (~r1_tarski(k8_relat_1('#skF_7', '#skF_9'), k8_relat_1('#skF_8', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.64/2.17  tff(c_2939, plain, (~r1_tarski(k6_relat_1('#skF_7'), k6_relat_1('#skF_8')) | ~r1_tarski('#skF_9', '#skF_9') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_2908, c_42])).
% 5.64/2.17  tff(c_2956, plain, (~r1_tarski(k6_relat_1('#skF_7'), k6_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_12, c_2939])).
% 5.64/2.17  tff(c_2959, plain, (~r1_tarski('#skF_8', '#skF_8') | ~r1_tarski('#skF_7', '#skF_7')), inference(resolution, [status(thm)], [c_716, c_2956])).
% 5.64/2.17  tff(c_2969, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_12, c_2959])).
% 5.64/2.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.64/2.17  
% 5.64/2.17  Inference rules
% 5.64/2.17  ----------------------
% 5.64/2.17  #Ref     : 0
% 5.64/2.17  #Sup     : 871
% 5.64/2.17  #Fact    : 0
% 5.64/2.17  #Define  : 0
% 5.64/2.17  #Split   : 4
% 5.64/2.17  #Chain   : 0
% 5.64/2.17  #Close   : 0
% 5.64/2.17  
% 5.64/2.17  Ordering : KBO
% 5.64/2.17  
% 5.64/2.17  Simplification rules
% 5.64/2.17  ----------------------
% 5.64/2.17  #Subsume      : 180
% 5.64/2.17  #Demod        : 52
% 5.64/2.17  #Tautology    : 46
% 5.64/2.17  #SimpNegUnit  : 0
% 5.64/2.17  #BackRed      : 0
% 5.64/2.17  
% 5.64/2.17  #Partial instantiations: 0
% 5.64/2.17  #Strategies tried      : 1
% 5.64/2.17  
% 5.64/2.17  Timing (in seconds)
% 5.64/2.17  ----------------------
% 5.64/2.17  Preprocessing        : 0.33
% 5.64/2.17  Parsing              : 0.17
% 5.64/2.17  CNF conversion       : 0.02
% 5.64/2.17  Main loop            : 0.98
% 5.64/2.17  Inferencing          : 0.25
% 5.64/2.17  Reduction            : 0.21
% 5.64/2.17  Demodulation         : 0.13
% 5.64/2.17  BG Simplification    : 0.04
% 5.64/2.17  Subsumption          : 0.43
% 5.64/2.17  Abstraction          : 0.05
% 5.64/2.17  MUC search           : 0.00
% 5.64/2.17  Cooper               : 0.00
% 5.64/2.17  Total                : 1.34
% 5.64/2.17  Index Insertion      : 0.00
% 5.64/2.17  Index Deletion       : 0.00
% 5.64/2.17  Index Matching       : 0.00
% 5.64/2.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
