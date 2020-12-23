%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:55 EST 2020

% Result     : Theorem 3.16s
% Output     : CNFRefutation 3.16s
% Verified   : 
% Statistics : Number of formulae       :   56 (  86 expanded)
%              Number of leaves         :   30 (  44 expanded)
%              Depth                    :    8
%              Number of atoms          :   54 ( 104 expanded)
%              Number of equality atoms :   15 (  24 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_tarski > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_3 > #skF_2 > #skF_1 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_70,negated_conjecture,(
    ~ ( k1_relat_1(k1_xboole_0) = k1_xboole_0
      & k2_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_28,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( r2_hidden(A,k1_relat_1(B))
          & ! [C] : ~ r2_hidden(C,k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_relat_1)).

tff(c_36,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_43,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_851,plain,(
    ! [A_145,B_146] :
      ( r2_hidden(k4_tarski('#skF_2'(A_145,B_146),'#skF_1'(A_145,B_146)),A_145)
      | r2_hidden('#skF_3'(A_145,B_146),B_146)
      | k2_relat_1(A_145) = B_146 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_4,plain,(
    ! [A_1] : r1_xboole_0(A_1,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_53,plain,(
    ! [A_59,C_60,B_61] :
      ( ~ r2_hidden(A_59,C_60)
      | ~ r1_xboole_0(k2_tarski(A_59,B_61),C_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_58,plain,(
    ! [A_59] : ~ r2_hidden(A_59,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_53])).

tff(c_936,plain,(
    ! [B_147] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_147),B_147)
      | k2_relat_1(k1_xboole_0) = B_147 ) ),
    inference(resolution,[status(thm)],[c_851,c_58])).

tff(c_1017,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_936,c_58])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_38,plain,(
    ! [A_56] :
      ( v1_relat_1(A_56)
      | ~ v1_xboole_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_42,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_38])).

tff(c_34,plain,(
    ! [A_52,B_53] :
      ( r2_hidden('#skF_5'(A_52,B_53),k2_relat_1(B_53))
      | ~ r2_hidden(A_52,k1_relat_1(B_53))
      | ~ v1_relat_1(B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_80,plain,(
    ! [A_75,C_76] :
      ( r2_hidden(k4_tarski('#skF_4'(A_75,k2_relat_1(A_75),C_76),C_76),A_75)
      | ~ r2_hidden(C_76,k2_relat_1(A_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_90,plain,(
    ! [C_77] : ~ r2_hidden(C_77,k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_80,c_58])).

tff(c_98,plain,(
    ! [A_52] :
      ( ~ r2_hidden(A_52,k1_relat_1(k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_34,c_90])).

tff(c_102,plain,(
    ! [A_52] : ~ r2_hidden(A_52,k1_relat_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_98])).

tff(c_1014,plain,(
    k2_relat_1(k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_936,c_102])).

tff(c_1046,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1017,c_1014])).

tff(c_1047,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_43,c_1046])).

tff(c_1048,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_1333,plain,(
    ! [A_203,B_204] :
      ( r2_hidden(k4_tarski('#skF_2'(A_203,B_204),'#skF_1'(A_203,B_204)),A_203)
      | r2_hidden('#skF_3'(A_203,B_204),B_204)
      | k2_relat_1(A_203) = B_204 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1063,plain,(
    ! [A_150,C_151,B_152] :
      ( ~ r2_hidden(A_150,C_151)
      | ~ r1_xboole_0(k2_tarski(A_150,B_152),C_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1068,plain,(
    ! [A_150] : ~ r2_hidden(A_150,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_1063])).

tff(c_1403,plain,(
    ! [B_205] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_205),B_205)
      | k2_relat_1(k1_xboole_0) = B_205 ) ),
    inference(resolution,[status(thm)],[c_1333,c_1068])).

tff(c_1455,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1403,c_1068])).

tff(c_1472,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1048,c_1455])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:24:01 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.16/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.47  
% 3.16/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.47  %$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_tarski > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_3 > #skF_2 > #skF_1 > #skF_5
% 3.16/1.47  
% 3.16/1.47  %Foreground sorts:
% 3.16/1.47  
% 3.16/1.47  
% 3.16/1.47  %Background operators:
% 3.16/1.47  
% 3.16/1.47  
% 3.16/1.47  %Foreground operators:
% 3.16/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.16/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.16/1.47  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.16/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.16/1.47  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.16/1.47  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.16/1.47  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.16/1.47  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.16/1.47  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.16/1.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.16/1.47  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.16/1.47  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.16/1.47  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.16/1.47  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.16/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.16/1.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.16/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.16/1.47  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.16/1.47  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.16/1.47  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.16/1.47  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.16/1.47  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.16/1.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.16/1.47  
% 3.16/1.48  tff(f_70, negated_conjecture, ~((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.16/1.48  tff(f_57, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 3.16/1.48  tff(f_28, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.16/1.48  tff(f_45, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 3.16/1.48  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.16/1.48  tff(f_49, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 3.16/1.48  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => ~(r2_hidden(A, k1_relat_1(B)) & (![C]: ~r2_hidden(C, k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_relat_1)).
% 3.16/1.48  tff(c_36, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.16/1.48  tff(c_43, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_36])).
% 3.16/1.48  tff(c_851, plain, (![A_145, B_146]: (r2_hidden(k4_tarski('#skF_2'(A_145, B_146), '#skF_1'(A_145, B_146)), A_145) | r2_hidden('#skF_3'(A_145, B_146), B_146) | k2_relat_1(A_145)=B_146)), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.16/1.48  tff(c_4, plain, (![A_1]: (r1_xboole_0(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_28])).
% 3.16/1.48  tff(c_53, plain, (![A_59, C_60, B_61]: (~r2_hidden(A_59, C_60) | ~r1_xboole_0(k2_tarski(A_59, B_61), C_60))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.16/1.48  tff(c_58, plain, (![A_59]: (~r2_hidden(A_59, k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_53])).
% 3.16/1.48  tff(c_936, plain, (![B_147]: (r2_hidden('#skF_3'(k1_xboole_0, B_147), B_147) | k2_relat_1(k1_xboole_0)=B_147)), inference(resolution, [status(thm)], [c_851, c_58])).
% 3.16/1.48  tff(c_1017, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_936, c_58])).
% 3.16/1.48  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.16/1.48  tff(c_38, plain, (![A_56]: (v1_relat_1(A_56) | ~v1_xboole_0(A_56))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.16/1.48  tff(c_42, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_38])).
% 3.16/1.48  tff(c_34, plain, (![A_52, B_53]: (r2_hidden('#skF_5'(A_52, B_53), k2_relat_1(B_53)) | ~r2_hidden(A_52, k1_relat_1(B_53)) | ~v1_relat_1(B_53))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.16/1.48  tff(c_80, plain, (![A_75, C_76]: (r2_hidden(k4_tarski('#skF_4'(A_75, k2_relat_1(A_75), C_76), C_76), A_75) | ~r2_hidden(C_76, k2_relat_1(A_75)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.16/1.48  tff(c_90, plain, (![C_77]: (~r2_hidden(C_77, k2_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_80, c_58])).
% 3.16/1.48  tff(c_98, plain, (![A_52]: (~r2_hidden(A_52, k1_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_34, c_90])).
% 3.16/1.48  tff(c_102, plain, (![A_52]: (~r2_hidden(A_52, k1_relat_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_98])).
% 3.16/1.48  tff(c_1014, plain, (k2_relat_1(k1_xboole_0)=k1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_936, c_102])).
% 3.16/1.48  tff(c_1046, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1017, c_1014])).
% 3.16/1.48  tff(c_1047, plain, $false, inference(negUnitSimplification, [status(thm)], [c_43, c_1046])).
% 3.16/1.48  tff(c_1048, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_36])).
% 3.16/1.48  tff(c_1333, plain, (![A_203, B_204]: (r2_hidden(k4_tarski('#skF_2'(A_203, B_204), '#skF_1'(A_203, B_204)), A_203) | r2_hidden('#skF_3'(A_203, B_204), B_204) | k2_relat_1(A_203)=B_204)), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.16/1.48  tff(c_1063, plain, (![A_150, C_151, B_152]: (~r2_hidden(A_150, C_151) | ~r1_xboole_0(k2_tarski(A_150, B_152), C_151))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.16/1.48  tff(c_1068, plain, (![A_150]: (~r2_hidden(A_150, k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_1063])).
% 3.16/1.48  tff(c_1403, plain, (![B_205]: (r2_hidden('#skF_3'(k1_xboole_0, B_205), B_205) | k2_relat_1(k1_xboole_0)=B_205)), inference(resolution, [status(thm)], [c_1333, c_1068])).
% 3.16/1.48  tff(c_1455, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_1403, c_1068])).
% 3.16/1.48  tff(c_1472, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1048, c_1455])).
% 3.16/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.48  
% 3.16/1.48  Inference rules
% 3.16/1.48  ----------------------
% 3.16/1.48  #Ref     : 0
% 3.16/1.48  #Sup     : 267
% 3.16/1.48  #Fact    : 0
% 3.16/1.48  #Define  : 0
% 3.16/1.48  #Split   : 12
% 3.16/1.48  #Chain   : 0
% 3.16/1.48  #Close   : 0
% 3.16/1.48  
% 3.16/1.48  Ordering : KBO
% 3.16/1.48  
% 3.16/1.48  Simplification rules
% 3.16/1.48  ----------------------
% 3.16/1.48  #Subsume      : 56
% 3.16/1.48  #Demod        : 95
% 3.16/1.48  #Tautology    : 40
% 3.16/1.48  #SimpNegUnit  : 4
% 3.16/1.48  #BackRed      : 34
% 3.16/1.48  
% 3.16/1.48  #Partial instantiations: 0
% 3.16/1.48  #Strategies tried      : 1
% 3.16/1.48  
% 3.16/1.48  Timing (in seconds)
% 3.16/1.48  ----------------------
% 3.16/1.49  Preprocessing        : 0.31
% 3.16/1.49  Parsing              : 0.16
% 3.16/1.49  CNF conversion       : 0.02
% 3.16/1.49  Main loop            : 0.41
% 3.16/1.49  Inferencing          : 0.15
% 3.16/1.49  Reduction            : 0.11
% 3.16/1.49  Demodulation         : 0.07
% 3.16/1.49  BG Simplification    : 0.02
% 3.16/1.49  Subsumption          : 0.09
% 3.16/1.49  Abstraction          : 0.03
% 3.16/1.49  MUC search           : 0.00
% 3.16/1.49  Cooper               : 0.00
% 3.16/1.49  Total                : 0.75
% 3.16/1.49  Index Insertion      : 0.00
% 3.16/1.49  Index Deletion       : 0.00
% 3.16/1.49  Index Matching       : 0.00
% 3.16/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
