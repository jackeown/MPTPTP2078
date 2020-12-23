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
% DateTime   : Thu Dec  3 10:02:23 EST 2020

% Result     : Theorem 3.21s
% Output     : CNFRefutation 3.21s
% Verified   : 
% Statistics : Number of formulae       :   68 (  82 expanded)
%              Number of leaves         :   37 (  45 expanded)
%              Depth                    :    7
%              Number of atoms          :   79 ( 112 expanded)
%              Number of equality atoms :   21 (  31 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > k11_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

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

tff(f_99,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k1_relat_1(B))
        <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_35,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

tff(c_50,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_52,plain,
    ( k11_relat_1('#skF_4','#skF_3') = k1_xboole_0
    | ~ r2_hidden('#skF_3',k1_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_117,plain,(
    ~ r2_hidden('#skF_3',k1_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_58,plain,
    ( r2_hidden('#skF_3',k1_relat_1('#skF_4'))
    | k11_relat_1('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_118,plain,(
    k11_relat_1('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_117,c_58])).

tff(c_4,plain,(
    ! [A_3] :
      ( r2_hidden('#skF_1'(A_3),A_3)
      | k1_xboole_0 = A_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_260,plain,(
    ! [A_96,B_97,C_98] :
      ( r2_hidden(k4_tarski(A_96,B_97),C_98)
      | ~ r2_hidden(B_97,k11_relat_1(C_98,A_96))
      | ~ v1_relat_1(C_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_48,plain,(
    ! [A_51,C_53,B_52] :
      ( r2_hidden(A_51,k1_relat_1(C_53))
      | ~ r2_hidden(k4_tarski(A_51,B_52),C_53)
      | ~ v1_relat_1(C_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_340,plain,(
    ! [A_105,C_106,B_107] :
      ( r2_hidden(A_105,k1_relat_1(C_106))
      | ~ r2_hidden(B_107,k11_relat_1(C_106,A_105))
      | ~ v1_relat_1(C_106) ) ),
    inference(resolution,[status(thm)],[c_260,c_48])).

tff(c_353,plain,(
    ! [A_108,C_109] :
      ( r2_hidden(A_108,k1_relat_1(C_109))
      | ~ v1_relat_1(C_109)
      | k11_relat_1(C_109,A_108) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_340])).

tff(c_368,plain,
    ( ~ v1_relat_1('#skF_4')
    | k11_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_353,c_117])).

tff(c_374,plain,(
    k11_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_368])).

tff(c_376,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_374])).

tff(c_378,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_40,plain,(
    ! [A_47] :
      ( k10_relat_1(A_47,k2_relat_1(A_47)) = k1_relat_1(A_47)
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_8,plain,(
    ! [A_7] : k5_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_394,plain,(
    ! [A_111,B_112] : k5_xboole_0(A_111,k3_xboole_0(A_111,B_112)) = k4_xboole_0(A_111,B_112) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_403,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_394])).

tff(c_407,plain,(
    ! [A_113] : k4_xboole_0(A_113,A_113) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_403])).

tff(c_26,plain,(
    ! [C_38,B_37] : ~ r2_hidden(C_38,k4_xboole_0(B_37,k1_tarski(C_38))) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_412,plain,(
    ! [C_38] : ~ r2_hidden(C_38,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_407,c_26])).

tff(c_377,plain,(
    k11_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_798,plain,(
    ! [A_176,B_177,C_178] :
      ( r2_hidden(k4_tarski(A_176,'#skF_2'(A_176,B_177,C_178)),C_178)
      | ~ r2_hidden(A_176,k10_relat_1(C_178,B_177))
      | ~ v1_relat_1(C_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_44,plain,(
    ! [B_49,C_50,A_48] :
      ( r2_hidden(B_49,k11_relat_1(C_50,A_48))
      | ~ r2_hidden(k4_tarski(A_48,B_49),C_50)
      | ~ v1_relat_1(C_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1129,plain,(
    ! [A_223,B_224,C_225] :
      ( r2_hidden('#skF_2'(A_223,B_224,C_225),k11_relat_1(C_225,A_223))
      | ~ r2_hidden(A_223,k10_relat_1(C_225,B_224))
      | ~ v1_relat_1(C_225) ) ),
    inference(resolution,[status(thm)],[c_798,c_44])).

tff(c_1145,plain,(
    ! [B_224] :
      ( r2_hidden('#skF_2'('#skF_3',B_224,'#skF_4'),k1_xboole_0)
      | ~ r2_hidden('#skF_3',k10_relat_1('#skF_4',B_224))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_377,c_1129])).

tff(c_1151,plain,(
    ! [B_224] :
      ( r2_hidden('#skF_2'('#skF_3',B_224,'#skF_4'),k1_xboole_0)
      | ~ r2_hidden('#skF_3',k10_relat_1('#skF_4',B_224)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1145])).

tff(c_1193,plain,(
    ! [B_230] : ~ r2_hidden('#skF_3',k10_relat_1('#skF_4',B_230)) ),
    inference(negUnitSimplification,[status(thm)],[c_412,c_1151])).

tff(c_1203,plain,
    ( ~ r2_hidden('#skF_3',k1_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_1193])).

tff(c_1208,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_378,c_1203])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n021.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 10:11:19 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.21/1.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.21/1.61  
% 3.21/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.21/1.61  %$ r2_hidden > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > k11_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 3.21/1.61  
% 3.21/1.61  %Foreground sorts:
% 3.21/1.61  
% 3.21/1.61  
% 3.21/1.61  %Background operators:
% 3.21/1.61  
% 3.21/1.61  
% 3.21/1.61  %Foreground operators:
% 3.21/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.21/1.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.21/1.61  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.21/1.61  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.21/1.61  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.21/1.61  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.21/1.61  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.21/1.61  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.21/1.61  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.21/1.61  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.21/1.61  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.21/1.61  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.21/1.61  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 3.21/1.61  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.21/1.61  tff('#skF_3', type, '#skF_3': $i).
% 3.21/1.61  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.21/1.61  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.21/1.61  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.21/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.21/1.61  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.21/1.61  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.21/1.61  tff('#skF_4', type, '#skF_4': $i).
% 3.21/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.21/1.61  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.21/1.61  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.21/1.61  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.21/1.61  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.21/1.61  
% 3.21/1.63  tff(f_99, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 3.21/1.63  tff(f_35, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.21/1.63  tff(f_83, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t204_relat_1)).
% 3.21/1.63  tff(f_91, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_relat_1)).
% 3.21/1.63  tff(f_77, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 3.21/1.63  tff(f_39, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.21/1.63  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.21/1.63  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.21/1.63  tff(f_60, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 3.21/1.63  tff(f_73, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 3.21/1.63  tff(c_50, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.21/1.63  tff(c_52, plain, (k11_relat_1('#skF_4', '#skF_3')=k1_xboole_0 | ~r2_hidden('#skF_3', k1_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.21/1.63  tff(c_117, plain, (~r2_hidden('#skF_3', k1_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_52])).
% 3.21/1.63  tff(c_58, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_4')) | k11_relat_1('#skF_4', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.21/1.63  tff(c_118, plain, (k11_relat_1('#skF_4', '#skF_3')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_117, c_58])).
% 3.21/1.63  tff(c_4, plain, (![A_3]: (r2_hidden('#skF_1'(A_3), A_3) | k1_xboole_0=A_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.21/1.63  tff(c_260, plain, (![A_96, B_97, C_98]: (r2_hidden(k4_tarski(A_96, B_97), C_98) | ~r2_hidden(B_97, k11_relat_1(C_98, A_96)) | ~v1_relat_1(C_98))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.21/1.63  tff(c_48, plain, (![A_51, C_53, B_52]: (r2_hidden(A_51, k1_relat_1(C_53)) | ~r2_hidden(k4_tarski(A_51, B_52), C_53) | ~v1_relat_1(C_53))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.21/1.63  tff(c_340, plain, (![A_105, C_106, B_107]: (r2_hidden(A_105, k1_relat_1(C_106)) | ~r2_hidden(B_107, k11_relat_1(C_106, A_105)) | ~v1_relat_1(C_106))), inference(resolution, [status(thm)], [c_260, c_48])).
% 3.21/1.63  tff(c_353, plain, (![A_108, C_109]: (r2_hidden(A_108, k1_relat_1(C_109)) | ~v1_relat_1(C_109) | k11_relat_1(C_109, A_108)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_340])).
% 3.21/1.63  tff(c_368, plain, (~v1_relat_1('#skF_4') | k11_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_353, c_117])).
% 3.21/1.63  tff(c_374, plain, (k11_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_50, c_368])).
% 3.21/1.63  tff(c_376, plain, $false, inference(negUnitSimplification, [status(thm)], [c_118, c_374])).
% 3.21/1.63  tff(c_378, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_52])).
% 3.21/1.63  tff(c_40, plain, (![A_47]: (k10_relat_1(A_47, k2_relat_1(A_47))=k1_relat_1(A_47) | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.21/1.63  tff(c_8, plain, (![A_7]: (k5_xboole_0(A_7, A_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.21/1.63  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.21/1.63  tff(c_394, plain, (![A_111, B_112]: (k5_xboole_0(A_111, k3_xboole_0(A_111, B_112))=k4_xboole_0(A_111, B_112))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.21/1.63  tff(c_403, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_394])).
% 3.21/1.63  tff(c_407, plain, (![A_113]: (k4_xboole_0(A_113, A_113)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_403])).
% 3.21/1.63  tff(c_26, plain, (![C_38, B_37]: (~r2_hidden(C_38, k4_xboole_0(B_37, k1_tarski(C_38))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.21/1.63  tff(c_412, plain, (![C_38]: (~r2_hidden(C_38, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_407, c_26])).
% 3.21/1.63  tff(c_377, plain, (k11_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_52])).
% 3.21/1.63  tff(c_798, plain, (![A_176, B_177, C_178]: (r2_hidden(k4_tarski(A_176, '#skF_2'(A_176, B_177, C_178)), C_178) | ~r2_hidden(A_176, k10_relat_1(C_178, B_177)) | ~v1_relat_1(C_178))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.21/1.63  tff(c_44, plain, (![B_49, C_50, A_48]: (r2_hidden(B_49, k11_relat_1(C_50, A_48)) | ~r2_hidden(k4_tarski(A_48, B_49), C_50) | ~v1_relat_1(C_50))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.21/1.63  tff(c_1129, plain, (![A_223, B_224, C_225]: (r2_hidden('#skF_2'(A_223, B_224, C_225), k11_relat_1(C_225, A_223)) | ~r2_hidden(A_223, k10_relat_1(C_225, B_224)) | ~v1_relat_1(C_225))), inference(resolution, [status(thm)], [c_798, c_44])).
% 3.21/1.63  tff(c_1145, plain, (![B_224]: (r2_hidden('#skF_2'('#skF_3', B_224, '#skF_4'), k1_xboole_0) | ~r2_hidden('#skF_3', k10_relat_1('#skF_4', B_224)) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_377, c_1129])).
% 3.21/1.63  tff(c_1151, plain, (![B_224]: (r2_hidden('#skF_2'('#skF_3', B_224, '#skF_4'), k1_xboole_0) | ~r2_hidden('#skF_3', k10_relat_1('#skF_4', B_224)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1145])).
% 3.21/1.63  tff(c_1193, plain, (![B_230]: (~r2_hidden('#skF_3', k10_relat_1('#skF_4', B_230)))), inference(negUnitSimplification, [status(thm)], [c_412, c_1151])).
% 3.21/1.63  tff(c_1203, plain, (~r2_hidden('#skF_3', k1_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_40, c_1193])).
% 3.21/1.63  tff(c_1208, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_378, c_1203])).
% 3.21/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.21/1.63  
% 3.21/1.63  Inference rules
% 3.21/1.63  ----------------------
% 3.21/1.63  #Ref     : 0
% 3.21/1.63  #Sup     : 249
% 3.21/1.63  #Fact    : 0
% 3.21/1.63  #Define  : 0
% 3.21/1.63  #Split   : 3
% 3.21/1.63  #Chain   : 0
% 3.21/1.63  #Close   : 0
% 3.21/1.63  
% 3.21/1.63  Ordering : KBO
% 3.21/1.63  
% 3.21/1.63  Simplification rules
% 3.21/1.63  ----------------------
% 3.21/1.63  #Subsume      : 40
% 3.21/1.63  #Demod        : 40
% 3.21/1.63  #Tautology    : 82
% 3.21/1.63  #SimpNegUnit  : 11
% 3.21/1.63  #BackRed      : 0
% 3.21/1.63  
% 3.21/1.63  #Partial instantiations: 0
% 3.21/1.63  #Strategies tried      : 1
% 3.21/1.63  
% 3.21/1.63  Timing (in seconds)
% 3.21/1.63  ----------------------
% 3.21/1.63  Preprocessing        : 0.39
% 3.21/1.63  Parsing              : 0.21
% 3.21/1.63  CNF conversion       : 0.02
% 3.21/1.63  Main loop            : 0.43
% 3.21/1.63  Inferencing          : 0.17
% 3.21/1.63  Reduction            : 0.12
% 3.21/1.63  Demodulation         : 0.08
% 3.21/1.63  BG Simplification    : 0.03
% 3.21/1.63  Subsumption          : 0.08
% 3.21/1.63  Abstraction          : 0.03
% 3.21/1.63  MUC search           : 0.00
% 3.21/1.63  Cooper               : 0.00
% 3.21/1.63  Total                : 0.85
% 3.21/1.63  Index Insertion      : 0.00
% 3.21/1.63  Index Deletion       : 0.00
% 3.21/1.63  Index Matching       : 0.00
% 3.21/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
