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
% DateTime   : Thu Dec  3 10:00:16 EST 2020

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :   50 (  63 expanded)
%              Number of leaves         :   26 (  34 expanded)
%              Depth                    :    9
%              Number of atoms          :   85 ( 107 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :   10 (   5 average)
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

tff(f_77,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => r1_tarski(k8_relat_1(A,C),k8_relat_1(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t131_relat_1)).

tff(f_45,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_70,axiom,(
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

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( B = k6_relat_1(A)
      <=> ! [C,D] :
            ( r2_hidden(k4_tarski(C,D),B)
          <=> ( r2_hidden(C,A)
              & C = D ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( r1_tarski(A,B)
               => r1_tarski(k5_relat_1(C,A),k5_relat_1(C,B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_relat_1)).

tff(c_38,plain,(
    r1_tarski('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_26,plain,(
    ! [A_14] : v1_relat_1(k6_relat_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_84,plain,(
    ! [A_46,B_47] :
      ( r2_hidden('#skF_6'(A_46,B_47),A_46)
      | r1_tarski(k6_relat_1(A_46),B_47)
      | ~ v1_relat_1(B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_118,plain,(
    ! [A_58,B_59,B_60] :
      ( r2_hidden('#skF_6'(A_58,B_59),B_60)
      | ~ r1_tarski(A_58,B_60)
      | r1_tarski(k6_relat_1(A_58),B_59)
      | ~ v1_relat_1(B_59) ) ),
    inference(resolution,[status(thm)],[c_84,c_2])).

tff(c_20,plain,(
    ! [D_13,A_6] :
      ( r2_hidden(k4_tarski(D_13,D_13),k6_relat_1(A_6))
      | ~ r2_hidden(D_13,A_6)
      | ~ v1_relat_1(k6_relat_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_46,plain,(
    ! [D_13,A_6] :
      ( r2_hidden(k4_tarski(D_13,D_13),k6_relat_1(A_6))
      | ~ r2_hidden(D_13,A_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_20])).

tff(c_102,plain,(
    ! [A_54,B_55] :
      ( ~ r2_hidden(k4_tarski('#skF_6'(A_54,B_55),'#skF_6'(A_54,B_55)),B_55)
      | r1_tarski(k6_relat_1(A_54),B_55)
      | ~ v1_relat_1(B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_106,plain,(
    ! [A_54,A_6] :
      ( r1_tarski(k6_relat_1(A_54),k6_relat_1(A_6))
      | ~ v1_relat_1(k6_relat_1(A_6))
      | ~ r2_hidden('#skF_6'(A_54,k6_relat_1(A_6)),A_6) ) ),
    inference(resolution,[status(thm)],[c_46,c_102])).

tff(c_109,plain,(
    ! [A_54,A_6] :
      ( r1_tarski(k6_relat_1(A_54),k6_relat_1(A_6))
      | ~ r2_hidden('#skF_6'(A_54,k6_relat_1(A_6)),A_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_106])).

tff(c_122,plain,(
    ! [A_58,B_60] :
      ( ~ r1_tarski(A_58,B_60)
      | r1_tarski(k6_relat_1(A_58),k6_relat_1(B_60))
      | ~ v1_relat_1(k6_relat_1(B_60)) ) ),
    inference(resolution,[status(thm)],[c_118,c_109])).

tff(c_127,plain,(
    ! [A_58,B_60] :
      ( ~ r1_tarski(A_58,B_60)
      | r1_tarski(k6_relat_1(A_58),k6_relat_1(B_60)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_122])).

tff(c_40,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_28,plain,(
    ! [B_16,A_15] :
      ( k5_relat_1(B_16,k6_relat_1(A_15)) = k8_relat_1(A_15,B_16)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_133,plain,(
    ! [C_63,A_64,B_65] :
      ( r1_tarski(k5_relat_1(C_63,A_64),k5_relat_1(C_63,B_65))
      | ~ r1_tarski(A_64,B_65)
      | ~ v1_relat_1(C_63)
      | ~ v1_relat_1(B_65)
      | ~ v1_relat_1(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_139,plain,(
    ! [B_16,A_64,A_15] :
      ( r1_tarski(k5_relat_1(B_16,A_64),k8_relat_1(A_15,B_16))
      | ~ r1_tarski(A_64,k6_relat_1(A_15))
      | ~ v1_relat_1(B_16)
      | ~ v1_relat_1(k6_relat_1(A_15))
      | ~ v1_relat_1(A_64)
      | ~ v1_relat_1(B_16) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_133])).

tff(c_230,plain,(
    ! [B_83,A_84,A_85] :
      ( r1_tarski(k5_relat_1(B_83,A_84),k8_relat_1(A_85,B_83))
      | ~ r1_tarski(A_84,k6_relat_1(A_85))
      | ~ v1_relat_1(A_84)
      | ~ v1_relat_1(B_83) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_139])).

tff(c_235,plain,(
    ! [A_15,B_16,A_85] :
      ( r1_tarski(k8_relat_1(A_15,B_16),k8_relat_1(A_85,B_16))
      | ~ r1_tarski(k6_relat_1(A_15),k6_relat_1(A_85))
      | ~ v1_relat_1(k6_relat_1(A_15))
      | ~ v1_relat_1(B_16)
      | ~ v1_relat_1(B_16) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_230])).

tff(c_239,plain,(
    ! [A_86,B_87,A_88] :
      ( r1_tarski(k8_relat_1(A_86,B_87),k8_relat_1(A_88,B_87))
      | ~ r1_tarski(k6_relat_1(A_86),k6_relat_1(A_88))
      | ~ v1_relat_1(B_87) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_235])).

tff(c_36,plain,(
    ~ r1_tarski(k8_relat_1('#skF_7','#skF_9'),k8_relat_1('#skF_8','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_244,plain,
    ( ~ r1_tarski(k6_relat_1('#skF_7'),k6_relat_1('#skF_8'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_239,c_36])).

tff(c_248,plain,(
    ~ r1_tarski(k6_relat_1('#skF_7'),k6_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_244])).

tff(c_251,plain,(
    ~ r1_tarski('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_127,c_248])).

tff(c_255,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_251])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:18:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.15/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.25  
% 2.15/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.25  %$ r2_hidden > r1_tarski > v1_relat_1 > k8_relat_1 > k5_relat_1 > k4_tarski > #nlpp > k6_relat_1 > #skF_6 > #skF_7 > #skF_3 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_5 > #skF_4
% 2.15/1.25  
% 2.15/1.25  %Foreground sorts:
% 2.15/1.25  
% 2.15/1.25  
% 2.15/1.25  %Background operators:
% 2.15/1.25  
% 2.15/1.25  
% 2.15/1.25  %Foreground operators:
% 2.15/1.25  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.15/1.25  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.15/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.15/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.15/1.25  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.15/1.25  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.15/1.25  tff('#skF_7', type, '#skF_7': $i).
% 2.15/1.25  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.15/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.15/1.25  tff('#skF_9', type, '#skF_9': $i).
% 2.15/1.25  tff('#skF_8', type, '#skF_8': $i).
% 2.15/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.15/1.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.15/1.25  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.15/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.15/1.25  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.15/1.25  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.15/1.25  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.15/1.25  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.15/1.25  
% 2.15/1.26  tff(f_77, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k8_relat_1(A, C), k8_relat_1(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t131_relat_1)).
% 2.15/1.26  tff(f_45, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.15/1.26  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => ((![C]: (r2_hidden(C, A) => r2_hidden(k4_tarski(C, C), B))) => r1_tarski(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_relat_1)).
% 2.15/1.26  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.15/1.26  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => ((B = k6_relat_1(A)) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), B) <=> (r2_hidden(C, A) & (C = D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_relat_1)).
% 2.15/1.26  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 2.15/1.26  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k5_relat_1(C, A), k5_relat_1(C, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_relat_1)).
% 2.15/1.26  tff(c_38, plain, (r1_tarski('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.15/1.26  tff(c_26, plain, (![A_14]: (v1_relat_1(k6_relat_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.15/1.26  tff(c_84, plain, (![A_46, B_47]: (r2_hidden('#skF_6'(A_46, B_47), A_46) | r1_tarski(k6_relat_1(A_46), B_47) | ~v1_relat_1(B_47))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.15/1.26  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.15/1.26  tff(c_118, plain, (![A_58, B_59, B_60]: (r2_hidden('#skF_6'(A_58, B_59), B_60) | ~r1_tarski(A_58, B_60) | r1_tarski(k6_relat_1(A_58), B_59) | ~v1_relat_1(B_59))), inference(resolution, [status(thm)], [c_84, c_2])).
% 2.15/1.26  tff(c_20, plain, (![D_13, A_6]: (r2_hidden(k4_tarski(D_13, D_13), k6_relat_1(A_6)) | ~r2_hidden(D_13, A_6) | ~v1_relat_1(k6_relat_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.15/1.26  tff(c_46, plain, (![D_13, A_6]: (r2_hidden(k4_tarski(D_13, D_13), k6_relat_1(A_6)) | ~r2_hidden(D_13, A_6))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_20])).
% 2.15/1.26  tff(c_102, plain, (![A_54, B_55]: (~r2_hidden(k4_tarski('#skF_6'(A_54, B_55), '#skF_6'(A_54, B_55)), B_55) | r1_tarski(k6_relat_1(A_54), B_55) | ~v1_relat_1(B_55))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.15/1.26  tff(c_106, plain, (![A_54, A_6]: (r1_tarski(k6_relat_1(A_54), k6_relat_1(A_6)) | ~v1_relat_1(k6_relat_1(A_6)) | ~r2_hidden('#skF_6'(A_54, k6_relat_1(A_6)), A_6))), inference(resolution, [status(thm)], [c_46, c_102])).
% 2.15/1.26  tff(c_109, plain, (![A_54, A_6]: (r1_tarski(k6_relat_1(A_54), k6_relat_1(A_6)) | ~r2_hidden('#skF_6'(A_54, k6_relat_1(A_6)), A_6))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_106])).
% 2.15/1.26  tff(c_122, plain, (![A_58, B_60]: (~r1_tarski(A_58, B_60) | r1_tarski(k6_relat_1(A_58), k6_relat_1(B_60)) | ~v1_relat_1(k6_relat_1(B_60)))), inference(resolution, [status(thm)], [c_118, c_109])).
% 2.15/1.26  tff(c_127, plain, (![A_58, B_60]: (~r1_tarski(A_58, B_60) | r1_tarski(k6_relat_1(A_58), k6_relat_1(B_60)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_122])).
% 2.15/1.26  tff(c_40, plain, (v1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.15/1.26  tff(c_28, plain, (![B_16, A_15]: (k5_relat_1(B_16, k6_relat_1(A_15))=k8_relat_1(A_15, B_16) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.15/1.26  tff(c_133, plain, (![C_63, A_64, B_65]: (r1_tarski(k5_relat_1(C_63, A_64), k5_relat_1(C_63, B_65)) | ~r1_tarski(A_64, B_65) | ~v1_relat_1(C_63) | ~v1_relat_1(B_65) | ~v1_relat_1(A_64))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.15/1.26  tff(c_139, plain, (![B_16, A_64, A_15]: (r1_tarski(k5_relat_1(B_16, A_64), k8_relat_1(A_15, B_16)) | ~r1_tarski(A_64, k6_relat_1(A_15)) | ~v1_relat_1(B_16) | ~v1_relat_1(k6_relat_1(A_15)) | ~v1_relat_1(A_64) | ~v1_relat_1(B_16))), inference(superposition, [status(thm), theory('equality')], [c_28, c_133])).
% 2.15/1.26  tff(c_230, plain, (![B_83, A_84, A_85]: (r1_tarski(k5_relat_1(B_83, A_84), k8_relat_1(A_85, B_83)) | ~r1_tarski(A_84, k6_relat_1(A_85)) | ~v1_relat_1(A_84) | ~v1_relat_1(B_83))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_139])).
% 2.15/1.26  tff(c_235, plain, (![A_15, B_16, A_85]: (r1_tarski(k8_relat_1(A_15, B_16), k8_relat_1(A_85, B_16)) | ~r1_tarski(k6_relat_1(A_15), k6_relat_1(A_85)) | ~v1_relat_1(k6_relat_1(A_15)) | ~v1_relat_1(B_16) | ~v1_relat_1(B_16))), inference(superposition, [status(thm), theory('equality')], [c_28, c_230])).
% 2.15/1.26  tff(c_239, plain, (![A_86, B_87, A_88]: (r1_tarski(k8_relat_1(A_86, B_87), k8_relat_1(A_88, B_87)) | ~r1_tarski(k6_relat_1(A_86), k6_relat_1(A_88)) | ~v1_relat_1(B_87))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_235])).
% 2.15/1.26  tff(c_36, plain, (~r1_tarski(k8_relat_1('#skF_7', '#skF_9'), k8_relat_1('#skF_8', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.15/1.26  tff(c_244, plain, (~r1_tarski(k6_relat_1('#skF_7'), k6_relat_1('#skF_8')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_239, c_36])).
% 2.15/1.26  tff(c_248, plain, (~r1_tarski(k6_relat_1('#skF_7'), k6_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_244])).
% 2.15/1.26  tff(c_251, plain, (~r1_tarski('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_127, c_248])).
% 2.15/1.26  tff(c_255, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_251])).
% 2.15/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.26  
% 2.15/1.26  Inference rules
% 2.15/1.26  ----------------------
% 2.15/1.26  #Ref     : 0
% 2.15/1.26  #Sup     : 44
% 2.15/1.26  #Fact    : 0
% 2.15/1.26  #Define  : 0
% 2.15/1.26  #Split   : 0
% 2.15/1.26  #Chain   : 0
% 2.15/1.26  #Close   : 0
% 2.15/1.26  
% 2.15/1.26  Ordering : KBO
% 2.15/1.26  
% 2.15/1.26  Simplification rules
% 2.15/1.26  ----------------------
% 2.15/1.26  #Subsume      : 3
% 2.15/1.26  #Demod        : 15
% 2.15/1.26  #Tautology    : 7
% 2.15/1.26  #SimpNegUnit  : 0
% 2.15/1.26  #BackRed      : 0
% 2.15/1.26  
% 2.15/1.26  #Partial instantiations: 0
% 2.15/1.26  #Strategies tried      : 1
% 2.15/1.26  
% 2.15/1.26  Timing (in seconds)
% 2.15/1.26  ----------------------
% 2.15/1.26  Preprocessing        : 0.31
% 2.15/1.26  Parsing              : 0.16
% 2.15/1.26  CNF conversion       : 0.02
% 2.15/1.27  Main loop            : 0.20
% 2.15/1.27  Inferencing          : 0.08
% 2.15/1.27  Reduction            : 0.05
% 2.15/1.27  Demodulation         : 0.04
% 2.15/1.27  BG Simplification    : 0.02
% 2.15/1.27  Subsumption          : 0.05
% 2.15/1.27  Abstraction          : 0.01
% 2.15/1.27  MUC search           : 0.00
% 2.15/1.27  Cooper               : 0.00
% 2.15/1.27  Total                : 0.54
% 2.15/1.27  Index Insertion      : 0.00
% 2.15/1.27  Index Deletion       : 0.00
% 2.15/1.27  Index Matching       : 0.00
% 2.15/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
