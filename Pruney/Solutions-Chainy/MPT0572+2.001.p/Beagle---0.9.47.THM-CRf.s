%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:48 EST 2020

% Result     : Theorem 10.01s
% Output     : CNFRefutation 10.01s
% Verified   : 
% Statistics : Number of formulae       :   58 (  76 expanded)
%              Number of leaves         :   30 (  40 expanded)
%              Depth                    :    6
%              Number of atoms          :   68 ( 101 expanded)
%              Number of equality atoms :   13 (  18 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_51,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_65,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_74,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => r1_tarski(k10_relat_1(C,k3_xboole_0(A,B)),k3_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_18,plain,(
    ! [B_16,A_15] : k2_tarski(B_16,A_15) = k2_tarski(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_75,plain,(
    ! [A_54,B_55] : k1_setfam_1(k2_tarski(A_54,B_55)) = k3_xboole_0(A_54,B_55) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_99,plain,(
    ! [A_58,B_59] : k1_setfam_1(k2_tarski(A_58,B_59)) = k3_xboole_0(B_59,A_58) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_75])).

tff(c_32,plain,(
    ! [A_44,B_45] : k1_setfam_1(k2_tarski(A_44,B_45)) = k3_xboole_0(A_44,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_122,plain,(
    ! [B_60,A_61] : k3_xboole_0(B_60,A_61) = k3_xboole_0(A_61,B_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_32])).

tff(c_12,plain,(
    ! [A_8,B_9] : r1_tarski(k3_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_137,plain,(
    ! [B_60,A_61] : r1_tarski(k3_xboole_0(B_60,A_61),A_61) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_12])).

tff(c_38,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( k2_xboole_0(A_13,k4_xboole_0(B_14,A_13)) = B_14
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_10319,plain,(
    ! [C_389,A_390,B_391] :
      ( k2_xboole_0(k10_relat_1(C_389,A_390),k10_relat_1(C_389,B_391)) = k10_relat_1(C_389,k2_xboole_0(A_390,B_391))
      | ~ v1_relat_1(C_389) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_10,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(A_5,C_7)
      | ~ r1_tarski(k2_xboole_0(A_5,B_6),C_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_11754,plain,(
    ! [C_434,A_435,C_436,B_437] :
      ( r1_tarski(k10_relat_1(C_434,A_435),C_436)
      | ~ r1_tarski(k10_relat_1(C_434,k2_xboole_0(A_435,B_437)),C_436)
      | ~ v1_relat_1(C_434) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10319,c_10])).

tff(c_17246,plain,(
    ! [C_546,A_547,C_548,B_549] :
      ( r1_tarski(k10_relat_1(C_546,A_547),C_548)
      | ~ r1_tarski(k10_relat_1(C_546,B_549),C_548)
      | ~ v1_relat_1(C_546)
      | ~ r1_tarski(A_547,B_549) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_11754])).

tff(c_20455,plain,(
    ! [C_627,A_628,B_629] :
      ( r1_tarski(k10_relat_1(C_627,A_628),k10_relat_1(C_627,B_629))
      | ~ v1_relat_1(C_627)
      | ~ r1_tarski(A_628,B_629) ) ),
    inference(resolution,[status(thm)],[c_6,c_17246])).

tff(c_727,plain,(
    ! [C_127,A_128,B_129] :
      ( k2_xboole_0(k10_relat_1(C_127,A_128),k10_relat_1(C_127,B_129)) = k10_relat_1(C_127,k2_xboole_0(A_128,B_129))
      | ~ v1_relat_1(C_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1425,plain,(
    ! [C_162,A_163,C_164,B_165] :
      ( r1_tarski(k10_relat_1(C_162,A_163),C_164)
      | ~ r1_tarski(k10_relat_1(C_162,k2_xboole_0(A_163,B_165)),C_164)
      | ~ v1_relat_1(C_162) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_727,c_10])).

tff(c_7034,plain,(
    ! [C_286,A_287,C_288,B_289] :
      ( r1_tarski(k10_relat_1(C_286,A_287),C_288)
      | ~ r1_tarski(k10_relat_1(C_286,B_289),C_288)
      | ~ v1_relat_1(C_286)
      | ~ r1_tarski(A_287,B_289) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1425])).

tff(c_10143,plain,(
    ! [C_377,A_378,B_379] :
      ( r1_tarski(k10_relat_1(C_377,A_378),k10_relat_1(C_377,B_379))
      | ~ v1_relat_1(C_377)
      | ~ r1_tarski(A_378,B_379) ) ),
    inference(resolution,[status(thm)],[c_6,c_7034])).

tff(c_407,plain,(
    ! [A_104,B_105,C_106] :
      ( r1_tarski(A_104,k3_xboole_0(B_105,C_106))
      | ~ r1_tarski(A_104,C_106)
      | ~ r1_tarski(A_104,B_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_36,plain,(
    ~ r1_tarski(k10_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k3_xboole_0(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_439,plain,
    ( ~ r1_tarski(k10_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k10_relat_1('#skF_3','#skF_2'))
    | ~ r1_tarski(k10_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k10_relat_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_407,c_36])).

tff(c_649,plain,(
    ~ r1_tarski(k10_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k10_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_439])).

tff(c_10175,plain,
    ( ~ v1_relat_1('#skF_3')
    | ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_10143,c_649])).

tff(c_10197,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_38,c_10175])).

tff(c_10198,plain,(
    ~ r1_tarski(k10_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k10_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_439])).

tff(c_20493,plain,
    ( ~ v1_relat_1('#skF_3')
    | ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_20455,c_10198])).

tff(c_20522,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_38,c_20493])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n014.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 11:19:52 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.01/3.76  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.01/3.76  
% 10.01/3.76  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.01/3.76  %$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 10.01/3.76  
% 10.01/3.76  %Foreground sorts:
% 10.01/3.76  
% 10.01/3.76  
% 10.01/3.76  %Background operators:
% 10.01/3.76  
% 10.01/3.76  
% 10.01/3.76  %Foreground operators:
% 10.01/3.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.01/3.76  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.01/3.76  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 10.01/3.76  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 10.01/3.76  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.01/3.76  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 10.01/3.76  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.01/3.76  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 10.01/3.76  tff('#skF_2', type, '#skF_2': $i).
% 10.01/3.76  tff('#skF_3', type, '#skF_3': $i).
% 10.01/3.76  tff('#skF_1', type, '#skF_1': $i).
% 10.01/3.76  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 10.01/3.76  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 10.01/3.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.01/3.76  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 10.01/3.76  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.01/3.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.01/3.76  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.01/3.76  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.01/3.76  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 10.01/3.76  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 10.01/3.76  
% 10.01/3.77  tff(f_51, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 10.01/3.77  tff(f_65, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 10.01/3.77  tff(f_39, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 10.01/3.77  tff(f_74, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => r1_tarski(k10_relat_1(C, k3_xboole_0(A, B)), k3_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t176_relat_1)).
% 10.01/3.77  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.01/3.77  tff(f_49, axiom, (![A, B]: (r1_tarski(A, B) => (B = k2_xboole_0(A, k4_xboole_0(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_xboole_1)).
% 10.01/3.77  tff(f_69, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_relat_1)).
% 10.01/3.77  tff(f_37, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 10.01/3.77  tff(f_45, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 10.01/3.77  tff(c_18, plain, (![B_16, A_15]: (k2_tarski(B_16, A_15)=k2_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.01/3.77  tff(c_75, plain, (![A_54, B_55]: (k1_setfam_1(k2_tarski(A_54, B_55))=k3_xboole_0(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_65])).
% 10.01/3.77  tff(c_99, plain, (![A_58, B_59]: (k1_setfam_1(k2_tarski(A_58, B_59))=k3_xboole_0(B_59, A_58))), inference(superposition, [status(thm), theory('equality')], [c_18, c_75])).
% 10.01/3.77  tff(c_32, plain, (![A_44, B_45]: (k1_setfam_1(k2_tarski(A_44, B_45))=k3_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_65])).
% 10.01/3.77  tff(c_122, plain, (![B_60, A_61]: (k3_xboole_0(B_60, A_61)=k3_xboole_0(A_61, B_60))), inference(superposition, [status(thm), theory('equality')], [c_99, c_32])).
% 10.01/3.77  tff(c_12, plain, (![A_8, B_9]: (r1_tarski(k3_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.01/3.77  tff(c_137, plain, (![B_60, A_61]: (r1_tarski(k3_xboole_0(B_60, A_61), A_61))), inference(superposition, [status(thm), theory('equality')], [c_122, c_12])).
% 10.01/3.77  tff(c_38, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_74])).
% 10.01/3.77  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.01/3.77  tff(c_16, plain, (![A_13, B_14]: (k2_xboole_0(A_13, k4_xboole_0(B_14, A_13))=B_14 | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 10.01/3.77  tff(c_10319, plain, (![C_389, A_390, B_391]: (k2_xboole_0(k10_relat_1(C_389, A_390), k10_relat_1(C_389, B_391))=k10_relat_1(C_389, k2_xboole_0(A_390, B_391)) | ~v1_relat_1(C_389))), inference(cnfTransformation, [status(thm)], [f_69])).
% 10.01/3.77  tff(c_10, plain, (![A_5, C_7, B_6]: (r1_tarski(A_5, C_7) | ~r1_tarski(k2_xboole_0(A_5, B_6), C_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.01/3.77  tff(c_11754, plain, (![C_434, A_435, C_436, B_437]: (r1_tarski(k10_relat_1(C_434, A_435), C_436) | ~r1_tarski(k10_relat_1(C_434, k2_xboole_0(A_435, B_437)), C_436) | ~v1_relat_1(C_434))), inference(superposition, [status(thm), theory('equality')], [c_10319, c_10])).
% 10.01/3.77  tff(c_17246, plain, (![C_546, A_547, C_548, B_549]: (r1_tarski(k10_relat_1(C_546, A_547), C_548) | ~r1_tarski(k10_relat_1(C_546, B_549), C_548) | ~v1_relat_1(C_546) | ~r1_tarski(A_547, B_549))), inference(superposition, [status(thm), theory('equality')], [c_16, c_11754])).
% 10.01/3.77  tff(c_20455, plain, (![C_627, A_628, B_629]: (r1_tarski(k10_relat_1(C_627, A_628), k10_relat_1(C_627, B_629)) | ~v1_relat_1(C_627) | ~r1_tarski(A_628, B_629))), inference(resolution, [status(thm)], [c_6, c_17246])).
% 10.01/3.77  tff(c_727, plain, (![C_127, A_128, B_129]: (k2_xboole_0(k10_relat_1(C_127, A_128), k10_relat_1(C_127, B_129))=k10_relat_1(C_127, k2_xboole_0(A_128, B_129)) | ~v1_relat_1(C_127))), inference(cnfTransformation, [status(thm)], [f_69])).
% 10.01/3.77  tff(c_1425, plain, (![C_162, A_163, C_164, B_165]: (r1_tarski(k10_relat_1(C_162, A_163), C_164) | ~r1_tarski(k10_relat_1(C_162, k2_xboole_0(A_163, B_165)), C_164) | ~v1_relat_1(C_162))), inference(superposition, [status(thm), theory('equality')], [c_727, c_10])).
% 10.01/3.77  tff(c_7034, plain, (![C_286, A_287, C_288, B_289]: (r1_tarski(k10_relat_1(C_286, A_287), C_288) | ~r1_tarski(k10_relat_1(C_286, B_289), C_288) | ~v1_relat_1(C_286) | ~r1_tarski(A_287, B_289))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1425])).
% 10.01/3.77  tff(c_10143, plain, (![C_377, A_378, B_379]: (r1_tarski(k10_relat_1(C_377, A_378), k10_relat_1(C_377, B_379)) | ~v1_relat_1(C_377) | ~r1_tarski(A_378, B_379))), inference(resolution, [status(thm)], [c_6, c_7034])).
% 10.01/3.77  tff(c_407, plain, (![A_104, B_105, C_106]: (r1_tarski(A_104, k3_xboole_0(B_105, C_106)) | ~r1_tarski(A_104, C_106) | ~r1_tarski(A_104, B_105))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.01/3.77  tff(c_36, plain, (~r1_tarski(k10_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k3_xboole_0(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_74])).
% 10.01/3.77  tff(c_439, plain, (~r1_tarski(k10_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k10_relat_1('#skF_3', '#skF_2')) | ~r1_tarski(k10_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k10_relat_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_407, c_36])).
% 10.01/3.77  tff(c_649, plain, (~r1_tarski(k10_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k10_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_439])).
% 10.01/3.77  tff(c_10175, plain, (~v1_relat_1('#skF_3') | ~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_10143, c_649])).
% 10.01/3.77  tff(c_10197, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_38, c_10175])).
% 10.01/3.77  tff(c_10198, plain, (~r1_tarski(k10_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k10_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_439])).
% 10.01/3.77  tff(c_20493, plain, (~v1_relat_1('#skF_3') | ~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_20455, c_10198])).
% 10.01/3.77  tff(c_20522, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_137, c_38, c_20493])).
% 10.01/3.77  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.01/3.77  
% 10.01/3.77  Inference rules
% 10.01/3.77  ----------------------
% 10.01/3.77  #Ref     : 0
% 10.01/3.77  #Sup     : 5117
% 10.01/3.77  #Fact    : 0
% 10.01/3.77  #Define  : 0
% 10.01/3.77  #Split   : 2
% 10.01/3.77  #Chain   : 0
% 10.01/3.77  #Close   : 0
% 10.01/3.77  
% 10.01/3.77  Ordering : KBO
% 10.01/3.77  
% 10.01/3.77  Simplification rules
% 10.01/3.77  ----------------------
% 10.01/3.77  #Subsume      : 499
% 10.01/3.77  #Demod        : 3509
% 10.01/3.77  #Tautology    : 2483
% 10.01/3.77  #SimpNegUnit  : 2
% 10.01/3.77  #BackRed      : 0
% 10.01/3.77  
% 10.01/3.77  #Partial instantiations: 0
% 10.01/3.77  #Strategies tried      : 1
% 10.01/3.77  
% 10.01/3.77  Timing (in seconds)
% 10.01/3.77  ----------------------
% 10.01/3.78  Preprocessing        : 0.31
% 10.01/3.78  Parsing              : 0.16
% 10.01/3.78  CNF conversion       : 0.02
% 10.01/3.78  Main loop            : 2.69
% 10.01/3.78  Inferencing          : 0.58
% 10.01/3.78  Reduction            : 1.28
% 10.01/3.78  Demodulation         : 1.11
% 10.01/3.78  BG Simplification    : 0.08
% 10.01/3.78  Subsumption          : 0.59
% 10.01/3.78  Abstraction          : 0.12
% 10.01/3.78  MUC search           : 0.00
% 10.15/3.78  Cooper               : 0.00
% 10.15/3.78  Total                : 3.03
% 10.15/3.78  Index Insertion      : 0.00
% 10.15/3.78  Index Deletion       : 0.00
% 10.15/3.78  Index Matching       : 0.00
% 10.15/3.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
