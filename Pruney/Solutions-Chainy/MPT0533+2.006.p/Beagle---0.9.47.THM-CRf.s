%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:18 EST 2020

% Result     : Theorem 4.85s
% Output     : CNFRefutation 5.17s
% Verified   : 
% Statistics : Number of formulae       :   59 (  85 expanded)
%              Number of leaves         :   27 (  43 expanded)
%              Depth                    :    9
%              Number of atoms          :  125 ( 190 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k8_relat_1 > k5_relat_1 > k4_tarski > #nlpp > k6_relat_1 > #skF_6 > #skF_7 > #skF_3 > #skF_10 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_5 > #skF_4

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

tff('#skF_10',type,(
    '#skF_10': $i )).

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

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_45,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_87,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ! [D] :
            ( v1_relat_1(D)
           => ( ( r1_tarski(C,D)
                & r1_tarski(A,B) )
             => r1_tarski(k8_relat_1(A,C),k8_relat_1(B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t133_relat_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( ! [C] :
            ( r2_hidden(C,A)
           => r2_hidden(k4_tarski(C,C),B) )
       => r1_tarski(k6_relat_1(A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( B = k6_relat_1(A)
      <=> ! [C,D] :
            ( r2_hidden(k4_tarski(C,D),B)
          <=> ( r2_hidden(C,A)
              & C = D ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_66,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_relat_1)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_54,plain,(
    ! [A_42,B_43] :
      ( ~ r2_hidden('#skF_1'(A_42,B_43),B_43)
      | r1_tarski(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_59,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_54])).

tff(c_26,plain,(
    ! [A_14] : v1_relat_1(k6_relat_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_38,plain,(
    r1_tarski('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_88,plain,(
    ! [A_55,B_56] :
      ( r2_hidden('#skF_6'(A_55,B_56),A_55)
      | r1_tarski(k6_relat_1(A_55),B_56)
      | ~ v1_relat_1(B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_140,plain,(
    ! [A_69,B_70,B_71] :
      ( r2_hidden('#skF_6'(A_69,B_70),B_71)
      | ~ r1_tarski(A_69,B_71)
      | r1_tarski(k6_relat_1(A_69),B_70)
      | ~ v1_relat_1(B_70) ) ),
    inference(resolution,[status(thm)],[c_88,c_2])).

tff(c_439,plain,(
    ! [A_124,B_125,B_126,B_127] :
      ( r2_hidden('#skF_6'(A_124,B_125),B_126)
      | ~ r1_tarski(B_127,B_126)
      | ~ r1_tarski(A_124,B_127)
      | r1_tarski(k6_relat_1(A_124),B_125)
      | ~ v1_relat_1(B_125) ) ),
    inference(resolution,[status(thm)],[c_140,c_2])).

tff(c_491,plain,(
    ! [A_131,B_132] :
      ( r2_hidden('#skF_6'(A_131,B_132),'#skF_8')
      | ~ r1_tarski(A_131,'#skF_7')
      | r1_tarski(k6_relat_1(A_131),B_132)
      | ~ v1_relat_1(B_132) ) ),
    inference(resolution,[status(thm)],[c_38,c_439])).

tff(c_738,plain,(
    ! [A_152,B_153,B_154] :
      ( r2_hidden('#skF_6'(A_152,B_153),B_154)
      | ~ r1_tarski('#skF_8',B_154)
      | ~ r1_tarski(A_152,'#skF_7')
      | r1_tarski(k6_relat_1(A_152),B_153)
      | ~ v1_relat_1(B_153) ) ),
    inference(resolution,[status(thm)],[c_491,c_2])).

tff(c_20,plain,(
    ! [D_13,A_6] :
      ( r2_hidden(k4_tarski(D_13,D_13),k6_relat_1(A_6))
      | ~ r2_hidden(D_13,A_6)
      | ~ v1_relat_1(k6_relat_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_50,plain,(
    ! [D_13,A_6] :
      ( r2_hidden(k4_tarski(D_13,D_13),k6_relat_1(A_6))
      | ~ r2_hidden(D_13,A_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_20])).

tff(c_92,plain,(
    ! [A_57,B_58] :
      ( ~ r2_hidden(k4_tarski('#skF_6'(A_57,B_58),'#skF_6'(A_57,B_58)),B_58)
      | r1_tarski(k6_relat_1(A_57),B_58)
      | ~ v1_relat_1(B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_96,plain,(
    ! [A_57,A_6] :
      ( r1_tarski(k6_relat_1(A_57),k6_relat_1(A_6))
      | ~ v1_relat_1(k6_relat_1(A_6))
      | ~ r2_hidden('#skF_6'(A_57,k6_relat_1(A_6)),A_6) ) ),
    inference(resolution,[status(thm)],[c_50,c_92])).

tff(c_99,plain,(
    ! [A_57,A_6] :
      ( r1_tarski(k6_relat_1(A_57),k6_relat_1(A_6))
      | ~ r2_hidden('#skF_6'(A_57,k6_relat_1(A_6)),A_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_96])).

tff(c_750,plain,(
    ! [B_154,A_152] :
      ( ~ r1_tarski('#skF_8',B_154)
      | ~ r1_tarski(A_152,'#skF_7')
      | r1_tarski(k6_relat_1(A_152),k6_relat_1(B_154))
      | ~ v1_relat_1(k6_relat_1(B_154)) ) ),
    inference(resolution,[status(thm)],[c_738,c_99])).

tff(c_759,plain,(
    ! [B_154,A_152] :
      ( ~ r1_tarski('#skF_8',B_154)
      | ~ r1_tarski(A_152,'#skF_7')
      | r1_tarski(k6_relat_1(A_152),k6_relat_1(B_154)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_750])).

tff(c_44,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_42,plain,(
    v1_relat_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_40,plain,(
    r1_tarski('#skF_9','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_28,plain,(
    ! [B_16,A_15] :
      ( k5_relat_1(B_16,k6_relat_1(A_15)) = k8_relat_1(A_15,B_16)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_324,plain,(
    ! [A_101,C_102,B_103,D_104] :
      ( r1_tarski(k5_relat_1(A_101,C_102),k5_relat_1(B_103,D_104))
      | ~ r1_tarski(C_102,D_104)
      | ~ r1_tarski(A_101,B_103)
      | ~ v1_relat_1(D_104)
      | ~ v1_relat_1(C_102)
      | ~ v1_relat_1(B_103)
      | ~ v1_relat_1(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_332,plain,(
    ! [A_101,C_102,A_15,B_16] :
      ( r1_tarski(k5_relat_1(A_101,C_102),k8_relat_1(A_15,B_16))
      | ~ r1_tarski(C_102,k6_relat_1(A_15))
      | ~ r1_tarski(A_101,B_16)
      | ~ v1_relat_1(k6_relat_1(A_15))
      | ~ v1_relat_1(C_102)
      | ~ v1_relat_1(B_16)
      | ~ v1_relat_1(A_101)
      | ~ v1_relat_1(B_16) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_324])).

tff(c_1964,plain,(
    ! [A_247,C_248,A_249,B_250] :
      ( r1_tarski(k5_relat_1(A_247,C_248),k8_relat_1(A_249,B_250))
      | ~ r1_tarski(C_248,k6_relat_1(A_249))
      | ~ r1_tarski(A_247,B_250)
      | ~ v1_relat_1(C_248)
      | ~ v1_relat_1(A_247)
      | ~ v1_relat_1(B_250) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_332])).

tff(c_1985,plain,(
    ! [A_15,B_16,A_249,B_250] :
      ( r1_tarski(k8_relat_1(A_15,B_16),k8_relat_1(A_249,B_250))
      | ~ r1_tarski(k6_relat_1(A_15),k6_relat_1(A_249))
      | ~ r1_tarski(B_16,B_250)
      | ~ v1_relat_1(k6_relat_1(A_15))
      | ~ v1_relat_1(B_16)
      | ~ v1_relat_1(B_250)
      | ~ v1_relat_1(B_16) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1964])).

tff(c_2209,plain,(
    ! [A_262,B_263,A_264,B_265] :
      ( r1_tarski(k8_relat_1(A_262,B_263),k8_relat_1(A_264,B_265))
      | ~ r1_tarski(k6_relat_1(A_262),k6_relat_1(A_264))
      | ~ r1_tarski(B_263,B_265)
      | ~ v1_relat_1(B_265)
      | ~ v1_relat_1(B_263) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1985])).

tff(c_36,plain,(
    ~ r1_tarski(k8_relat_1('#skF_7','#skF_9'),k8_relat_1('#skF_8','#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_2230,plain,
    ( ~ r1_tarski(k6_relat_1('#skF_7'),k6_relat_1('#skF_8'))
    | ~ r1_tarski('#skF_9','#skF_10')
    | ~ v1_relat_1('#skF_10')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_2209,c_36])).

tff(c_2242,plain,(
    ~ r1_tarski(k6_relat_1('#skF_7'),k6_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_2230])).

tff(c_2248,plain,
    ( ~ r1_tarski('#skF_8','#skF_8')
    | ~ r1_tarski('#skF_7','#skF_7') ),
    inference(resolution,[status(thm)],[c_759,c_2242])).

tff(c_2259,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_59,c_2248])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:14:35 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.85/1.91  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.85/1.92  
% 4.85/1.92  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.85/1.92  %$ r2_hidden > r1_tarski > v1_relat_1 > k8_relat_1 > k5_relat_1 > k4_tarski > #nlpp > k6_relat_1 > #skF_6 > #skF_7 > #skF_3 > #skF_10 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_5 > #skF_4
% 4.85/1.92  
% 4.85/1.92  %Foreground sorts:
% 4.85/1.92  
% 4.85/1.92  
% 4.85/1.92  %Background operators:
% 4.85/1.92  
% 4.85/1.92  
% 4.85/1.92  %Foreground operators:
% 4.85/1.92  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 4.85/1.92  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 4.85/1.92  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.85/1.92  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.85/1.92  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.85/1.92  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.85/1.92  tff('#skF_7', type, '#skF_7': $i).
% 4.85/1.92  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.85/1.92  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.85/1.92  tff('#skF_10', type, '#skF_10': $i).
% 4.85/1.92  tff('#skF_9', type, '#skF_9': $i).
% 4.85/1.92  tff('#skF_8', type, '#skF_8': $i).
% 4.85/1.92  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.85/1.92  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.85/1.92  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.85/1.92  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.85/1.92  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.85/1.92  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.85/1.92  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 4.85/1.92  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.85/1.92  
% 5.17/1.93  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.17/1.93  tff(f_45, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 5.17/1.93  tff(f_87, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(C, D) & r1_tarski(A, B)) => r1_tarski(k8_relat_1(A, C), k8_relat_1(B, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t133_relat_1)).
% 5.17/1.93  tff(f_75, axiom, (![A, B]: (v1_relat_1(B) => ((![C]: (r2_hidden(C, A) => r2_hidden(k4_tarski(C, C), B))) => r1_tarski(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_relat_1)).
% 5.17/1.93  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => ((B = k6_relat_1(A)) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), B) <=> (r2_hidden(C, A) & (C = D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_relat_1)).
% 5.17/1.93  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_relat_1)).
% 5.17/1.93  tff(f_66, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k5_relat_1(A, C), k5_relat_1(B, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_relat_1)).
% 5.17/1.93  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.17/1.93  tff(c_54, plain, (![A_42, B_43]: (~r2_hidden('#skF_1'(A_42, B_43), B_43) | r1_tarski(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.17/1.93  tff(c_59, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_54])).
% 5.17/1.93  tff(c_26, plain, (![A_14]: (v1_relat_1(k6_relat_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.17/1.93  tff(c_38, plain, (r1_tarski('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.17/1.93  tff(c_88, plain, (![A_55, B_56]: (r2_hidden('#skF_6'(A_55, B_56), A_55) | r1_tarski(k6_relat_1(A_55), B_56) | ~v1_relat_1(B_56))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.17/1.93  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.17/1.93  tff(c_140, plain, (![A_69, B_70, B_71]: (r2_hidden('#skF_6'(A_69, B_70), B_71) | ~r1_tarski(A_69, B_71) | r1_tarski(k6_relat_1(A_69), B_70) | ~v1_relat_1(B_70))), inference(resolution, [status(thm)], [c_88, c_2])).
% 5.17/1.93  tff(c_439, plain, (![A_124, B_125, B_126, B_127]: (r2_hidden('#skF_6'(A_124, B_125), B_126) | ~r1_tarski(B_127, B_126) | ~r1_tarski(A_124, B_127) | r1_tarski(k6_relat_1(A_124), B_125) | ~v1_relat_1(B_125))), inference(resolution, [status(thm)], [c_140, c_2])).
% 5.17/1.93  tff(c_491, plain, (![A_131, B_132]: (r2_hidden('#skF_6'(A_131, B_132), '#skF_8') | ~r1_tarski(A_131, '#skF_7') | r1_tarski(k6_relat_1(A_131), B_132) | ~v1_relat_1(B_132))), inference(resolution, [status(thm)], [c_38, c_439])).
% 5.17/1.93  tff(c_738, plain, (![A_152, B_153, B_154]: (r2_hidden('#skF_6'(A_152, B_153), B_154) | ~r1_tarski('#skF_8', B_154) | ~r1_tarski(A_152, '#skF_7') | r1_tarski(k6_relat_1(A_152), B_153) | ~v1_relat_1(B_153))), inference(resolution, [status(thm)], [c_491, c_2])).
% 5.17/1.93  tff(c_20, plain, (![D_13, A_6]: (r2_hidden(k4_tarski(D_13, D_13), k6_relat_1(A_6)) | ~r2_hidden(D_13, A_6) | ~v1_relat_1(k6_relat_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.17/1.93  tff(c_50, plain, (![D_13, A_6]: (r2_hidden(k4_tarski(D_13, D_13), k6_relat_1(A_6)) | ~r2_hidden(D_13, A_6))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_20])).
% 5.17/1.93  tff(c_92, plain, (![A_57, B_58]: (~r2_hidden(k4_tarski('#skF_6'(A_57, B_58), '#skF_6'(A_57, B_58)), B_58) | r1_tarski(k6_relat_1(A_57), B_58) | ~v1_relat_1(B_58))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.17/1.93  tff(c_96, plain, (![A_57, A_6]: (r1_tarski(k6_relat_1(A_57), k6_relat_1(A_6)) | ~v1_relat_1(k6_relat_1(A_6)) | ~r2_hidden('#skF_6'(A_57, k6_relat_1(A_6)), A_6))), inference(resolution, [status(thm)], [c_50, c_92])).
% 5.17/1.93  tff(c_99, plain, (![A_57, A_6]: (r1_tarski(k6_relat_1(A_57), k6_relat_1(A_6)) | ~r2_hidden('#skF_6'(A_57, k6_relat_1(A_6)), A_6))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_96])).
% 5.17/1.93  tff(c_750, plain, (![B_154, A_152]: (~r1_tarski('#skF_8', B_154) | ~r1_tarski(A_152, '#skF_7') | r1_tarski(k6_relat_1(A_152), k6_relat_1(B_154)) | ~v1_relat_1(k6_relat_1(B_154)))), inference(resolution, [status(thm)], [c_738, c_99])).
% 5.17/1.93  tff(c_759, plain, (![B_154, A_152]: (~r1_tarski('#skF_8', B_154) | ~r1_tarski(A_152, '#skF_7') | r1_tarski(k6_relat_1(A_152), k6_relat_1(B_154)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_750])).
% 5.17/1.93  tff(c_44, plain, (v1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.17/1.93  tff(c_42, plain, (v1_relat_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.17/1.93  tff(c_40, plain, (r1_tarski('#skF_9', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.17/1.93  tff(c_28, plain, (![B_16, A_15]: (k5_relat_1(B_16, k6_relat_1(A_15))=k8_relat_1(A_15, B_16) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.17/1.93  tff(c_324, plain, (![A_101, C_102, B_103, D_104]: (r1_tarski(k5_relat_1(A_101, C_102), k5_relat_1(B_103, D_104)) | ~r1_tarski(C_102, D_104) | ~r1_tarski(A_101, B_103) | ~v1_relat_1(D_104) | ~v1_relat_1(C_102) | ~v1_relat_1(B_103) | ~v1_relat_1(A_101))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.17/1.93  tff(c_332, plain, (![A_101, C_102, A_15, B_16]: (r1_tarski(k5_relat_1(A_101, C_102), k8_relat_1(A_15, B_16)) | ~r1_tarski(C_102, k6_relat_1(A_15)) | ~r1_tarski(A_101, B_16) | ~v1_relat_1(k6_relat_1(A_15)) | ~v1_relat_1(C_102) | ~v1_relat_1(B_16) | ~v1_relat_1(A_101) | ~v1_relat_1(B_16))), inference(superposition, [status(thm), theory('equality')], [c_28, c_324])).
% 5.17/1.93  tff(c_1964, plain, (![A_247, C_248, A_249, B_250]: (r1_tarski(k5_relat_1(A_247, C_248), k8_relat_1(A_249, B_250)) | ~r1_tarski(C_248, k6_relat_1(A_249)) | ~r1_tarski(A_247, B_250) | ~v1_relat_1(C_248) | ~v1_relat_1(A_247) | ~v1_relat_1(B_250))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_332])).
% 5.17/1.93  tff(c_1985, plain, (![A_15, B_16, A_249, B_250]: (r1_tarski(k8_relat_1(A_15, B_16), k8_relat_1(A_249, B_250)) | ~r1_tarski(k6_relat_1(A_15), k6_relat_1(A_249)) | ~r1_tarski(B_16, B_250) | ~v1_relat_1(k6_relat_1(A_15)) | ~v1_relat_1(B_16) | ~v1_relat_1(B_250) | ~v1_relat_1(B_16))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1964])).
% 5.17/1.93  tff(c_2209, plain, (![A_262, B_263, A_264, B_265]: (r1_tarski(k8_relat_1(A_262, B_263), k8_relat_1(A_264, B_265)) | ~r1_tarski(k6_relat_1(A_262), k6_relat_1(A_264)) | ~r1_tarski(B_263, B_265) | ~v1_relat_1(B_265) | ~v1_relat_1(B_263))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1985])).
% 5.17/1.93  tff(c_36, plain, (~r1_tarski(k8_relat_1('#skF_7', '#skF_9'), k8_relat_1('#skF_8', '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.17/1.93  tff(c_2230, plain, (~r1_tarski(k6_relat_1('#skF_7'), k6_relat_1('#skF_8')) | ~r1_tarski('#skF_9', '#skF_10') | ~v1_relat_1('#skF_10') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_2209, c_36])).
% 5.17/1.93  tff(c_2242, plain, (~r1_tarski(k6_relat_1('#skF_7'), k6_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_2230])).
% 5.17/1.93  tff(c_2248, plain, (~r1_tarski('#skF_8', '#skF_8') | ~r1_tarski('#skF_7', '#skF_7')), inference(resolution, [status(thm)], [c_759, c_2242])).
% 5.17/1.93  tff(c_2259, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_59, c_59, c_2248])).
% 5.17/1.93  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.17/1.93  
% 5.17/1.93  Inference rules
% 5.17/1.93  ----------------------
% 5.17/1.93  #Ref     : 0
% 5.17/1.93  #Sup     : 648
% 5.17/1.93  #Fact    : 0
% 5.17/1.93  #Define  : 0
% 5.17/1.93  #Split   : 6
% 5.17/1.93  #Chain   : 0
% 5.17/1.93  #Close   : 0
% 5.17/1.93  
% 5.17/1.93  Ordering : KBO
% 5.17/1.93  
% 5.17/1.93  Simplification rules
% 5.17/1.93  ----------------------
% 5.17/1.93  #Subsume      : 94
% 5.17/1.93  #Demod        : 28
% 5.17/1.93  #Tautology    : 18
% 5.17/1.93  #SimpNegUnit  : 0
% 5.17/1.93  #BackRed      : 0
% 5.17/1.93  
% 5.17/1.93  #Partial instantiations: 0
% 5.17/1.93  #Strategies tried      : 1
% 5.17/1.93  
% 5.17/1.93  Timing (in seconds)
% 5.17/1.93  ----------------------
% 5.17/1.94  Preprocessing        : 0.32
% 5.17/1.94  Parsing              : 0.16
% 5.17/1.94  CNF conversion       : 0.03
% 5.17/1.94  Main loop            : 0.86
% 5.17/1.94  Inferencing          : 0.23
% 5.17/1.94  Reduction            : 0.20
% 5.17/1.94  Demodulation         : 0.13
% 5.17/1.94  BG Simplification    : 0.04
% 5.17/1.94  Subsumption          : 0.31
% 5.17/1.94  Abstraction          : 0.05
% 5.17/1.94  MUC search           : 0.00
% 5.17/1.94  Cooper               : 0.00
% 5.17/1.94  Total                : 1.21
% 5.17/1.94  Index Insertion      : 0.00
% 5.17/1.94  Index Deletion       : 0.00
% 5.17/1.94  Index Matching       : 0.00
% 5.17/1.94  BG Taut test         : 0.00
%------------------------------------------------------------------------------
