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
% DateTime   : Thu Dec  3 10:17:30 EST 2020

% Result     : Theorem 4.02s
% Output     : CNFRefutation 4.34s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 120 expanded)
%              Number of leaves         :   34 (  59 expanded)
%              Depth                    :   14
%              Number of atoms          :   87 ( 178 expanded)
%              Number of equality atoms :   29 (  71 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_111,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_tarski(k10_relat_1(A,C),B)
           => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_67,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r1_tarski(A,k1_relat_1(C))
          & r1_tarski(k9_relat_1(C,A),B) )
       => r1_tarski(A,k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_funct_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => k9_relat_1(B,k10_relat_1(B,A)) = k3_xboole_0(A,k9_relat_1(B,k1_relat_1(B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_funct_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

tff(c_48,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') != k10_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_54,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_50,plain,(
    r1_tarski(k10_relat_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_36,plain,(
    ! [A_42] : v1_relat_1(k6_relat_1(A_42)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_32,plain,(
    ! [A_40] : k2_relat_1(k6_relat_1(A_40)) = A_40 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_30,plain,(
    ! [A_40] : k1_relat_1(k6_relat_1(A_40)) = A_40 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_77,plain,(
    ! [A_60] :
      ( k7_relat_1(A_60,k1_relat_1(A_60)) = A_60
      | ~ v1_relat_1(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_86,plain,(
    ! [A_40] :
      ( k7_relat_1(k6_relat_1(A_40),A_40) = k6_relat_1(A_40)
      | ~ v1_relat_1(k6_relat_1(A_40)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_77])).

tff(c_90,plain,(
    ! [A_40] : k7_relat_1(k6_relat_1(A_40),A_40) = k6_relat_1(A_40) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_86])).

tff(c_193,plain,(
    ! [B_77,A_78] :
      ( k2_relat_1(k7_relat_1(B_77,A_78)) = k9_relat_1(B_77,A_78)
      | ~ v1_relat_1(B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_205,plain,(
    ! [A_40] :
      ( k9_relat_1(k6_relat_1(A_40),A_40) = k2_relat_1(k6_relat_1(A_40))
      | ~ v1_relat_1(k6_relat_1(A_40)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_193])).

tff(c_212,plain,(
    ! [A_40] : k9_relat_1(k6_relat_1(A_40),A_40) = A_40 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_205])).

tff(c_38,plain,(
    ! [A_42] : v1_funct_1(k6_relat_1(A_42)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2261,plain,(
    ! [A_221,C_222,B_223] :
      ( r1_tarski(A_221,k10_relat_1(C_222,B_223))
      | ~ r1_tarski(k9_relat_1(C_222,A_221),B_223)
      | ~ r1_tarski(A_221,k1_relat_1(C_222))
      | ~ v1_funct_1(C_222)
      | ~ v1_relat_1(C_222) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2282,plain,(
    ! [A_40,B_223] :
      ( r1_tarski(A_40,k10_relat_1(k6_relat_1(A_40),B_223))
      | ~ r1_tarski(A_40,B_223)
      | ~ r1_tarski(A_40,k1_relat_1(k6_relat_1(A_40)))
      | ~ v1_funct_1(k6_relat_1(A_40))
      | ~ v1_relat_1(k6_relat_1(A_40)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_212,c_2261])).

tff(c_2301,plain,(
    ! [A_224,B_225] :
      ( r1_tarski(A_224,k10_relat_1(k6_relat_1(A_224),B_225))
      | ~ r1_tarski(A_224,B_225) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_38,c_6,c_30,c_2282])).

tff(c_118,plain,(
    ! [B_66,A_67] :
      ( r1_tarski(k10_relat_1(B_66,A_67),k1_relat_1(B_66))
      | ~ v1_relat_1(B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_121,plain,(
    ! [A_40,A_67] :
      ( r1_tarski(k10_relat_1(k6_relat_1(A_40),A_67),A_40)
      | ~ v1_relat_1(k6_relat_1(A_40)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_118])).

tff(c_123,plain,(
    ! [A_40,A_67] : r1_tarski(k10_relat_1(k6_relat_1(A_40),A_67),A_40) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_121])).

tff(c_167,plain,(
    ! [B_72,A_73] :
      ( B_72 = A_73
      | ~ r1_tarski(B_72,A_73)
      | ~ r1_tarski(A_73,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_176,plain,(
    ! [A_40,A_67] :
      ( k10_relat_1(k6_relat_1(A_40),A_67) = A_40
      | ~ r1_tarski(A_40,k10_relat_1(k6_relat_1(A_40),A_67)) ) ),
    inference(resolution,[status(thm)],[c_123,c_167])).

tff(c_2364,plain,(
    ! [A_226,B_227] :
      ( k10_relat_1(k6_relat_1(A_226),B_227) = A_226
      | ~ r1_tarski(A_226,B_227) ) ),
    inference(resolution,[status(thm)],[c_2301,c_176])).

tff(c_1414,plain,(
    ! [A_175,B_176] :
      ( k3_xboole_0(A_175,k9_relat_1(B_176,k1_relat_1(B_176))) = k9_relat_1(B_176,k10_relat_1(B_176,A_175))
      | ~ v1_funct_1(B_176)
      | ~ v1_relat_1(B_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1437,plain,(
    ! [A_40,A_175] :
      ( k9_relat_1(k6_relat_1(A_40),k10_relat_1(k6_relat_1(A_40),A_175)) = k3_xboole_0(A_175,k9_relat_1(k6_relat_1(A_40),A_40))
      | ~ v1_funct_1(k6_relat_1(A_40))
      | ~ v1_relat_1(k6_relat_1(A_40)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1414])).

tff(c_1441,plain,(
    ! [A_40,A_175] : k9_relat_1(k6_relat_1(A_40),k10_relat_1(k6_relat_1(A_40),A_175)) = k3_xboole_0(A_175,A_40) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_38,c_212,c_1437])).

tff(c_2391,plain,(
    ! [A_226,B_227] :
      ( k9_relat_1(k6_relat_1(A_226),A_226) = k3_xboole_0(B_227,A_226)
      | ~ r1_tarski(A_226,B_227) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2364,c_1441])).

tff(c_2618,plain,(
    ! [B_228,A_229] :
      ( k3_xboole_0(B_228,A_229) = A_229
      | ~ r1_tarski(A_229,B_228) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_2391])).

tff(c_2741,plain,(
    k3_xboole_0('#skF_2',k10_relat_1('#skF_1','#skF_3')) = k10_relat_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_2618])).

tff(c_40,plain,(
    ! [A_43,C_45,B_44] :
      ( k3_xboole_0(A_43,k10_relat_1(C_45,B_44)) = k10_relat_1(k7_relat_1(C_45,A_43),B_44)
      | ~ v1_relat_1(C_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2771,plain,
    ( k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2741,c_40])).

tff(c_2784,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2771])).

tff(c_2786,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_2784])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n006.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 09:57:52 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.02/1.71  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.02/1.72  
% 4.02/1.72  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.02/1.72  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 4.02/1.72  
% 4.02/1.72  %Foreground sorts:
% 4.02/1.72  
% 4.02/1.72  
% 4.02/1.72  %Background operators:
% 4.02/1.72  
% 4.02/1.72  
% 4.02/1.72  %Foreground operators:
% 4.02/1.72  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.02/1.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.02/1.72  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.02/1.72  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.02/1.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.02/1.72  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.02/1.72  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.02/1.72  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.02/1.72  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.02/1.72  tff('#skF_2', type, '#skF_2': $i).
% 4.02/1.72  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.02/1.72  tff('#skF_3', type, '#skF_3': $i).
% 4.02/1.72  tff('#skF_1', type, '#skF_1': $i).
% 4.02/1.72  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.02/1.72  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.02/1.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.02/1.72  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.02/1.72  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.02/1.72  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.02/1.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.02/1.72  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.02/1.72  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.02/1.72  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.02/1.72  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.02/1.72  
% 4.34/1.75  tff(f_111, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_funct_2)).
% 4.34/1.75  tff(f_75, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 4.34/1.75  tff(f_67, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 4.34/1.75  tff(f_71, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 4.34/1.75  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 4.34/1.75  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.34/1.75  tff(f_101, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(A, k1_relat_1(C)) & r1_tarski(k9_relat_1(C, A), B)) => r1_tarski(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t163_funct_1)).
% 4.34/1.75  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 4.34/1.75  tff(f_91, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = k3_xboole_0(A, k9_relat_1(B, k1_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_funct_1)).
% 4.34/1.75  tff(f_79, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 4.34/1.75  tff(c_48, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')!=k10_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.34/1.75  tff(c_54, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.34/1.75  tff(c_50, plain, (r1_tarski(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.34/1.75  tff(c_36, plain, (![A_42]: (v1_relat_1(k6_relat_1(A_42)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.34/1.75  tff(c_32, plain, (![A_40]: (k2_relat_1(k6_relat_1(A_40))=A_40)), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.34/1.75  tff(c_30, plain, (![A_40]: (k1_relat_1(k6_relat_1(A_40))=A_40)), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.34/1.75  tff(c_77, plain, (![A_60]: (k7_relat_1(A_60, k1_relat_1(A_60))=A_60 | ~v1_relat_1(A_60))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.34/1.75  tff(c_86, plain, (![A_40]: (k7_relat_1(k6_relat_1(A_40), A_40)=k6_relat_1(A_40) | ~v1_relat_1(k6_relat_1(A_40)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_77])).
% 4.34/1.75  tff(c_90, plain, (![A_40]: (k7_relat_1(k6_relat_1(A_40), A_40)=k6_relat_1(A_40))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_86])).
% 4.34/1.75  tff(c_193, plain, (![B_77, A_78]: (k2_relat_1(k7_relat_1(B_77, A_78))=k9_relat_1(B_77, A_78) | ~v1_relat_1(B_77))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.34/1.75  tff(c_205, plain, (![A_40]: (k9_relat_1(k6_relat_1(A_40), A_40)=k2_relat_1(k6_relat_1(A_40)) | ~v1_relat_1(k6_relat_1(A_40)))), inference(superposition, [status(thm), theory('equality')], [c_90, c_193])).
% 4.34/1.75  tff(c_212, plain, (![A_40]: (k9_relat_1(k6_relat_1(A_40), A_40)=A_40)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_205])).
% 4.34/1.75  tff(c_38, plain, (![A_42]: (v1_funct_1(k6_relat_1(A_42)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.34/1.75  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.34/1.75  tff(c_2261, plain, (![A_221, C_222, B_223]: (r1_tarski(A_221, k10_relat_1(C_222, B_223)) | ~r1_tarski(k9_relat_1(C_222, A_221), B_223) | ~r1_tarski(A_221, k1_relat_1(C_222)) | ~v1_funct_1(C_222) | ~v1_relat_1(C_222))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.34/1.75  tff(c_2282, plain, (![A_40, B_223]: (r1_tarski(A_40, k10_relat_1(k6_relat_1(A_40), B_223)) | ~r1_tarski(A_40, B_223) | ~r1_tarski(A_40, k1_relat_1(k6_relat_1(A_40))) | ~v1_funct_1(k6_relat_1(A_40)) | ~v1_relat_1(k6_relat_1(A_40)))), inference(superposition, [status(thm), theory('equality')], [c_212, c_2261])).
% 4.34/1.75  tff(c_2301, plain, (![A_224, B_225]: (r1_tarski(A_224, k10_relat_1(k6_relat_1(A_224), B_225)) | ~r1_tarski(A_224, B_225))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_38, c_6, c_30, c_2282])).
% 4.34/1.75  tff(c_118, plain, (![B_66, A_67]: (r1_tarski(k10_relat_1(B_66, A_67), k1_relat_1(B_66)) | ~v1_relat_1(B_66))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.34/1.75  tff(c_121, plain, (![A_40, A_67]: (r1_tarski(k10_relat_1(k6_relat_1(A_40), A_67), A_40) | ~v1_relat_1(k6_relat_1(A_40)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_118])).
% 4.34/1.75  tff(c_123, plain, (![A_40, A_67]: (r1_tarski(k10_relat_1(k6_relat_1(A_40), A_67), A_40))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_121])).
% 4.34/1.75  tff(c_167, plain, (![B_72, A_73]: (B_72=A_73 | ~r1_tarski(B_72, A_73) | ~r1_tarski(A_73, B_72))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.34/1.75  tff(c_176, plain, (![A_40, A_67]: (k10_relat_1(k6_relat_1(A_40), A_67)=A_40 | ~r1_tarski(A_40, k10_relat_1(k6_relat_1(A_40), A_67)))), inference(resolution, [status(thm)], [c_123, c_167])).
% 4.34/1.75  tff(c_2364, plain, (![A_226, B_227]: (k10_relat_1(k6_relat_1(A_226), B_227)=A_226 | ~r1_tarski(A_226, B_227))), inference(resolution, [status(thm)], [c_2301, c_176])).
% 4.34/1.75  tff(c_1414, plain, (![A_175, B_176]: (k3_xboole_0(A_175, k9_relat_1(B_176, k1_relat_1(B_176)))=k9_relat_1(B_176, k10_relat_1(B_176, A_175)) | ~v1_funct_1(B_176) | ~v1_relat_1(B_176))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.34/1.75  tff(c_1437, plain, (![A_40, A_175]: (k9_relat_1(k6_relat_1(A_40), k10_relat_1(k6_relat_1(A_40), A_175))=k3_xboole_0(A_175, k9_relat_1(k6_relat_1(A_40), A_40)) | ~v1_funct_1(k6_relat_1(A_40)) | ~v1_relat_1(k6_relat_1(A_40)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_1414])).
% 4.34/1.75  tff(c_1441, plain, (![A_40, A_175]: (k9_relat_1(k6_relat_1(A_40), k10_relat_1(k6_relat_1(A_40), A_175))=k3_xboole_0(A_175, A_40))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_38, c_212, c_1437])).
% 4.34/1.75  tff(c_2391, plain, (![A_226, B_227]: (k9_relat_1(k6_relat_1(A_226), A_226)=k3_xboole_0(B_227, A_226) | ~r1_tarski(A_226, B_227))), inference(superposition, [status(thm), theory('equality')], [c_2364, c_1441])).
% 4.34/1.75  tff(c_2618, plain, (![B_228, A_229]: (k3_xboole_0(B_228, A_229)=A_229 | ~r1_tarski(A_229, B_228))), inference(demodulation, [status(thm), theory('equality')], [c_212, c_2391])).
% 4.34/1.75  tff(c_2741, plain, (k3_xboole_0('#skF_2', k10_relat_1('#skF_1', '#skF_3'))=k10_relat_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_50, c_2618])).
% 4.34/1.75  tff(c_40, plain, (![A_43, C_45, B_44]: (k3_xboole_0(A_43, k10_relat_1(C_45, B_44))=k10_relat_1(k7_relat_1(C_45, A_43), B_44) | ~v1_relat_1(C_45))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.34/1.75  tff(c_2771, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2741, c_40])).
% 4.34/1.75  tff(c_2784, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2771])).
% 4.34/1.75  tff(c_2786, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_2784])).
% 4.34/1.75  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.34/1.75  
% 4.34/1.75  Inference rules
% 4.34/1.75  ----------------------
% 4.34/1.75  #Ref     : 0
% 4.34/1.75  #Sup     : 608
% 4.34/1.75  #Fact    : 0
% 4.34/1.75  #Define  : 0
% 4.34/1.75  #Split   : 1
% 4.34/1.75  #Chain   : 0
% 4.34/1.75  #Close   : 0
% 4.34/1.75  
% 4.34/1.75  Ordering : KBO
% 4.34/1.75  
% 4.34/1.75  Simplification rules
% 4.34/1.75  ----------------------
% 4.34/1.75  #Subsume      : 70
% 4.34/1.75  #Demod        : 415
% 4.34/1.75  #Tautology    : 207
% 4.34/1.75  #SimpNegUnit  : 1
% 4.34/1.75  #BackRed      : 0
% 4.34/1.75  
% 4.34/1.75  #Partial instantiations: 0
% 4.34/1.75  #Strategies tried      : 1
% 4.34/1.75  
% 4.34/1.75  Timing (in seconds)
% 4.34/1.75  ----------------------
% 4.34/1.75  Preprocessing        : 0.34
% 4.34/1.75  Parsing              : 0.18
% 4.34/1.75  CNF conversion       : 0.02
% 4.34/1.75  Main loop            : 0.62
% 4.34/1.75  Inferencing          : 0.21
% 4.34/1.75  Reduction            : 0.22
% 4.34/1.75  Demodulation         : 0.17
% 4.34/1.75  BG Simplification    : 0.03
% 4.34/1.75  Subsumption          : 0.12
% 4.34/1.75  Abstraction          : 0.03
% 4.34/1.75  MUC search           : 0.00
% 4.34/1.75  Cooper               : 0.00
% 4.34/1.75  Total                : 1.00
% 4.34/1.75  Index Insertion      : 0.00
% 4.34/1.75  Index Deletion       : 0.00
% 4.34/1.75  Index Matching       : 0.00
% 4.34/1.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
