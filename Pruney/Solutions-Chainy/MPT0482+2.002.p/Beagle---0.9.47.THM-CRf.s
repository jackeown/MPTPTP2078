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
% DateTime   : Thu Dec  3 09:59:31 EST 2020

% Result     : Theorem 6.48s
% Output     : CNFRefutation 6.48s
% Verified   : 
% Statistics : Number of formulae       :   52 (  63 expanded)
%              Number of leaves         :   26 (  34 expanded)
%              Depth                    :   12
%              Number of atoms          :   89 ( 120 expanded)
%              Number of equality atoms :    8 (  13 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k5_relat_1 > k4_tarski > #nlpp > k6_relat_1 > k1_relat_1 > #skF_6 > #skF_3 > #skF_9 > #skF_7 > #skF_8 > #skF_2 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_77,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(k1_relat_1(B),A)
         => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_tarski(A,B)
        <=> ! [C,D] :
              ( r2_hidden(k4_tarski(C,D),A)
             => r2_hidden(k4_tarski(C,D),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_64,axiom,(
    ! [A,B,C,D] :
      ( v1_relat_1(D)
     => ( r2_hidden(k4_tarski(A,B),k5_relat_1(k6_relat_1(C),D))
      <=> ( r2_hidden(A,C)
          & r2_hidden(k4_tarski(A,B),D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_relat_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k5_relat_1(B,k6_relat_1(A)),B)
        & r1_tarski(k5_relat_1(k6_relat_1(A),B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_relat_1)).

tff(c_42,plain,(
    k5_relat_1(k6_relat_1('#skF_8'),'#skF_9') != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_46,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_44,plain,(
    r1_tarski(k1_relat_1('#skF_9'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_130,plain,(
    ! [A_83,B_84] :
      ( r2_hidden(k4_tarski('#skF_2'(A_83,B_84),'#skF_3'(A_83,B_84)),A_83)
      | r1_tarski(A_83,B_84)
      | ~ v1_relat_1(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_22,plain,(
    ! [C_40,A_25,D_43] :
      ( r2_hidden(C_40,k1_relat_1(A_25))
      | ~ r2_hidden(k4_tarski(C_40,D_43),A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_148,plain,(
    ! [A_85,B_86] :
      ( r2_hidden('#skF_2'(A_85,B_86),k1_relat_1(A_85))
      | r1_tarski(A_85,B_86)
      | ~ v1_relat_1(A_85) ) ),
    inference(resolution,[status(thm)],[c_130,c_22])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_165,plain,(
    ! [A_91,B_92,B_93] :
      ( r2_hidden('#skF_2'(A_91,B_92),B_93)
      | ~ r1_tarski(k1_relat_1(A_91),B_93)
      | r1_tarski(A_91,B_92)
      | ~ v1_relat_1(A_91) ) ),
    inference(resolution,[status(thm)],[c_148,c_2])).

tff(c_1880,plain,(
    ! [A_233,B_234,B_235,B_236] :
      ( r2_hidden('#skF_2'(A_233,B_234),B_235)
      | ~ r1_tarski(B_236,B_235)
      | ~ r1_tarski(k1_relat_1(A_233),B_236)
      | r1_tarski(A_233,B_234)
      | ~ v1_relat_1(A_233) ) ),
    inference(resolution,[status(thm)],[c_165,c_2])).

tff(c_1914,plain,(
    ! [A_242,B_243] :
      ( r2_hidden('#skF_2'(A_242,B_243),'#skF_8')
      | ~ r1_tarski(k1_relat_1(A_242),k1_relat_1('#skF_9'))
      | r1_tarski(A_242,B_243)
      | ~ v1_relat_1(A_242) ) ),
    inference(resolution,[status(thm)],[c_44,c_1880])).

tff(c_1920,plain,(
    ! [B_243] :
      ( r2_hidden('#skF_2'('#skF_9',B_243),'#skF_8')
      | r1_tarski('#skF_9',B_243)
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_12,c_1914])).

tff(c_1924,plain,(
    ! [B_243] :
      ( r2_hidden('#skF_2'('#skF_9',B_243),'#skF_8')
      | r1_tarski('#skF_9',B_243) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1920])).

tff(c_18,plain,(
    ! [A_8,B_18] :
      ( r2_hidden(k4_tarski('#skF_2'(A_8,B_18),'#skF_3'(A_8,B_18)),A_8)
      | r1_tarski(A_8,B_18)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_527,plain,(
    ! [A_130,B_131,C_132,D_133] :
      ( r2_hidden(k4_tarski(A_130,B_131),k5_relat_1(k6_relat_1(C_132),D_133))
      | ~ r2_hidden(k4_tarski(A_130,B_131),D_133)
      | ~ r2_hidden(A_130,C_132)
      | ~ v1_relat_1(D_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_16,plain,(
    ! [A_8,B_18] :
      ( ~ r2_hidden(k4_tarski('#skF_2'(A_8,B_18),'#skF_3'(A_8,B_18)),B_18)
      | r1_tarski(A_8,B_18)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_4045,plain,(
    ! [A_356,C_357,D_358] :
      ( r1_tarski(A_356,k5_relat_1(k6_relat_1(C_357),D_358))
      | ~ v1_relat_1(A_356)
      | ~ r2_hidden(k4_tarski('#skF_2'(A_356,k5_relat_1(k6_relat_1(C_357),D_358)),'#skF_3'(A_356,k5_relat_1(k6_relat_1(C_357),D_358))),D_358)
      | ~ r2_hidden('#skF_2'(A_356,k5_relat_1(k6_relat_1(C_357),D_358)),C_357)
      | ~ v1_relat_1(D_358) ) ),
    inference(resolution,[status(thm)],[c_527,c_16])).

tff(c_4076,plain,(
    ! [A_359,C_360] :
      ( ~ r2_hidden('#skF_2'(A_359,k5_relat_1(k6_relat_1(C_360),A_359)),C_360)
      | r1_tarski(A_359,k5_relat_1(k6_relat_1(C_360),A_359))
      | ~ v1_relat_1(A_359) ) ),
    inference(resolution,[status(thm)],[c_18,c_4045])).

tff(c_4096,plain,
    ( ~ v1_relat_1('#skF_9')
    | r1_tarski('#skF_9',k5_relat_1(k6_relat_1('#skF_8'),'#skF_9')) ),
    inference(resolution,[status(thm)],[c_1924,c_4076])).

tff(c_4133,plain,(
    r1_tarski('#skF_9',k5_relat_1(k6_relat_1('#skF_8'),'#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_4096])).

tff(c_38,plain,(
    ! [A_48,B_49] :
      ( r1_tarski(k5_relat_1(k6_relat_1(A_48),B_49),B_49)
      | ~ v1_relat_1(B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_59,plain,(
    ! [B_59,A_60] :
      ( B_59 = A_60
      | ~ r1_tarski(B_59,A_60)
      | ~ r1_tarski(A_60,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_68,plain,(
    ! [A_48,B_49] :
      ( k5_relat_1(k6_relat_1(A_48),B_49) = B_49
      | ~ r1_tarski(B_49,k5_relat_1(k6_relat_1(A_48),B_49))
      | ~ v1_relat_1(B_49) ) ),
    inference(resolution,[status(thm)],[c_38,c_59])).

tff(c_4161,plain,
    ( k5_relat_1(k6_relat_1('#skF_8'),'#skF_9') = '#skF_9'
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_4133,c_68])).

tff(c_4181,plain,(
    k5_relat_1(k6_relat_1('#skF_8'),'#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_4161])).

tff(c_4183,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_4181])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:49:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.48/2.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.48/2.38  
% 6.48/2.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.48/2.39  %$ r2_hidden > r1_tarski > v1_relat_1 > k5_relat_1 > k4_tarski > #nlpp > k6_relat_1 > k1_relat_1 > #skF_6 > #skF_3 > #skF_9 > #skF_7 > #skF_8 > #skF_2 > #skF_1 > #skF_5 > #skF_4
% 6.48/2.39  
% 6.48/2.39  %Foreground sorts:
% 6.48/2.39  
% 6.48/2.39  
% 6.48/2.39  %Background operators:
% 6.48/2.39  
% 6.48/2.39  
% 6.48/2.39  %Foreground operators:
% 6.48/2.39  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 6.48/2.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.48/2.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.48/2.39  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 6.48/2.39  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 6.48/2.39  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 6.48/2.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.48/2.39  tff('#skF_9', type, '#skF_9': $i).
% 6.48/2.39  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 6.48/2.39  tff('#skF_8', type, '#skF_8': $i).
% 6.48/2.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.48/2.39  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.48/2.39  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.48/2.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.48/2.39  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.48/2.39  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.48/2.39  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 6.48/2.39  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.48/2.39  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 6.48/2.39  
% 6.48/2.40  tff(f_77, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_relat_1)).
% 6.48/2.40  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.48/2.40  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_tarski(A, B) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), A) => r2_hidden(k4_tarski(C, D), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_relat_1)).
% 6.48/2.40  tff(f_56, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 6.48/2.40  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 6.48/2.40  tff(f_64, axiom, (![A, B, C, D]: (v1_relat_1(D) => (r2_hidden(k4_tarski(A, B), k5_relat_1(k6_relat_1(C), D)) <=> (r2_hidden(A, C) & r2_hidden(k4_tarski(A, B), D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_relat_1)).
% 6.48/2.40  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k5_relat_1(B, k6_relat_1(A)), B) & r1_tarski(k5_relat_1(k6_relat_1(A), B), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_relat_1)).
% 6.48/2.40  tff(c_42, plain, (k5_relat_1(k6_relat_1('#skF_8'), '#skF_9')!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.48/2.40  tff(c_46, plain, (v1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.48/2.40  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.48/2.40  tff(c_44, plain, (r1_tarski(k1_relat_1('#skF_9'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.48/2.40  tff(c_130, plain, (![A_83, B_84]: (r2_hidden(k4_tarski('#skF_2'(A_83, B_84), '#skF_3'(A_83, B_84)), A_83) | r1_tarski(A_83, B_84) | ~v1_relat_1(A_83))), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.48/2.40  tff(c_22, plain, (![C_40, A_25, D_43]: (r2_hidden(C_40, k1_relat_1(A_25)) | ~r2_hidden(k4_tarski(C_40, D_43), A_25))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.48/2.40  tff(c_148, plain, (![A_85, B_86]: (r2_hidden('#skF_2'(A_85, B_86), k1_relat_1(A_85)) | r1_tarski(A_85, B_86) | ~v1_relat_1(A_85))), inference(resolution, [status(thm)], [c_130, c_22])).
% 6.48/2.40  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.48/2.40  tff(c_165, plain, (![A_91, B_92, B_93]: (r2_hidden('#skF_2'(A_91, B_92), B_93) | ~r1_tarski(k1_relat_1(A_91), B_93) | r1_tarski(A_91, B_92) | ~v1_relat_1(A_91))), inference(resolution, [status(thm)], [c_148, c_2])).
% 6.48/2.40  tff(c_1880, plain, (![A_233, B_234, B_235, B_236]: (r2_hidden('#skF_2'(A_233, B_234), B_235) | ~r1_tarski(B_236, B_235) | ~r1_tarski(k1_relat_1(A_233), B_236) | r1_tarski(A_233, B_234) | ~v1_relat_1(A_233))), inference(resolution, [status(thm)], [c_165, c_2])).
% 6.48/2.40  tff(c_1914, plain, (![A_242, B_243]: (r2_hidden('#skF_2'(A_242, B_243), '#skF_8') | ~r1_tarski(k1_relat_1(A_242), k1_relat_1('#skF_9')) | r1_tarski(A_242, B_243) | ~v1_relat_1(A_242))), inference(resolution, [status(thm)], [c_44, c_1880])).
% 6.48/2.40  tff(c_1920, plain, (![B_243]: (r2_hidden('#skF_2'('#skF_9', B_243), '#skF_8') | r1_tarski('#skF_9', B_243) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_12, c_1914])).
% 6.48/2.40  tff(c_1924, plain, (![B_243]: (r2_hidden('#skF_2'('#skF_9', B_243), '#skF_8') | r1_tarski('#skF_9', B_243))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1920])).
% 6.48/2.40  tff(c_18, plain, (![A_8, B_18]: (r2_hidden(k4_tarski('#skF_2'(A_8, B_18), '#skF_3'(A_8, B_18)), A_8) | r1_tarski(A_8, B_18) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.48/2.40  tff(c_527, plain, (![A_130, B_131, C_132, D_133]: (r2_hidden(k4_tarski(A_130, B_131), k5_relat_1(k6_relat_1(C_132), D_133)) | ~r2_hidden(k4_tarski(A_130, B_131), D_133) | ~r2_hidden(A_130, C_132) | ~v1_relat_1(D_133))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.48/2.40  tff(c_16, plain, (![A_8, B_18]: (~r2_hidden(k4_tarski('#skF_2'(A_8, B_18), '#skF_3'(A_8, B_18)), B_18) | r1_tarski(A_8, B_18) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.48/2.40  tff(c_4045, plain, (![A_356, C_357, D_358]: (r1_tarski(A_356, k5_relat_1(k6_relat_1(C_357), D_358)) | ~v1_relat_1(A_356) | ~r2_hidden(k4_tarski('#skF_2'(A_356, k5_relat_1(k6_relat_1(C_357), D_358)), '#skF_3'(A_356, k5_relat_1(k6_relat_1(C_357), D_358))), D_358) | ~r2_hidden('#skF_2'(A_356, k5_relat_1(k6_relat_1(C_357), D_358)), C_357) | ~v1_relat_1(D_358))), inference(resolution, [status(thm)], [c_527, c_16])).
% 6.48/2.40  tff(c_4076, plain, (![A_359, C_360]: (~r2_hidden('#skF_2'(A_359, k5_relat_1(k6_relat_1(C_360), A_359)), C_360) | r1_tarski(A_359, k5_relat_1(k6_relat_1(C_360), A_359)) | ~v1_relat_1(A_359))), inference(resolution, [status(thm)], [c_18, c_4045])).
% 6.48/2.40  tff(c_4096, plain, (~v1_relat_1('#skF_9') | r1_tarski('#skF_9', k5_relat_1(k6_relat_1('#skF_8'), '#skF_9'))), inference(resolution, [status(thm)], [c_1924, c_4076])).
% 6.48/2.40  tff(c_4133, plain, (r1_tarski('#skF_9', k5_relat_1(k6_relat_1('#skF_8'), '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_4096])).
% 6.48/2.40  tff(c_38, plain, (![A_48, B_49]: (r1_tarski(k5_relat_1(k6_relat_1(A_48), B_49), B_49) | ~v1_relat_1(B_49))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.48/2.40  tff(c_59, plain, (![B_59, A_60]: (B_59=A_60 | ~r1_tarski(B_59, A_60) | ~r1_tarski(A_60, B_59))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.48/2.40  tff(c_68, plain, (![A_48, B_49]: (k5_relat_1(k6_relat_1(A_48), B_49)=B_49 | ~r1_tarski(B_49, k5_relat_1(k6_relat_1(A_48), B_49)) | ~v1_relat_1(B_49))), inference(resolution, [status(thm)], [c_38, c_59])).
% 6.48/2.40  tff(c_4161, plain, (k5_relat_1(k6_relat_1('#skF_8'), '#skF_9')='#skF_9' | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_4133, c_68])).
% 6.48/2.40  tff(c_4181, plain, (k5_relat_1(k6_relat_1('#skF_8'), '#skF_9')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_4161])).
% 6.48/2.40  tff(c_4183, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_4181])).
% 6.48/2.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.48/2.40  
% 6.48/2.40  Inference rules
% 6.48/2.40  ----------------------
% 6.48/2.40  #Ref     : 0
% 6.48/2.40  #Sup     : 890
% 6.48/2.40  #Fact    : 0
% 6.48/2.40  #Define  : 0
% 6.48/2.40  #Split   : 11
% 6.48/2.40  #Chain   : 0
% 6.48/2.40  #Close   : 0
% 6.48/2.40  
% 6.48/2.40  Ordering : KBO
% 6.48/2.40  
% 6.48/2.40  Simplification rules
% 6.48/2.40  ----------------------
% 6.48/2.40  #Subsume      : 134
% 6.48/2.40  #Demod        : 55
% 6.48/2.40  #Tautology    : 36
% 6.48/2.40  #SimpNegUnit  : 5
% 6.48/2.40  #BackRed      : 26
% 6.48/2.40  
% 6.48/2.40  #Partial instantiations: 0
% 6.48/2.40  #Strategies tried      : 1
% 6.48/2.40  
% 6.48/2.40  Timing (in seconds)
% 6.48/2.40  ----------------------
% 6.89/2.40  Preprocessing        : 0.31
% 6.89/2.40  Parsing              : 0.17
% 6.89/2.40  CNF conversion       : 0.03
% 6.89/2.40  Main loop            : 1.27
% 6.89/2.40  Inferencing          : 0.38
% 6.89/2.40  Reduction            : 0.29
% 6.89/2.40  Demodulation         : 0.18
% 6.89/2.40  BG Simplification    : 0.05
% 6.89/2.40  Subsumption          : 0.46
% 6.89/2.40  Abstraction          : 0.05
% 6.89/2.40  MUC search           : 0.00
% 6.89/2.40  Cooper               : 0.00
% 6.89/2.40  Total                : 1.61
% 6.89/2.40  Index Insertion      : 0.00
% 6.89/2.40  Index Deletion       : 0.00
% 6.89/2.40  Index Matching       : 0.00
% 6.89/2.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
