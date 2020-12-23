%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:22 EST 2020

% Result     : Theorem 2.82s
% Output     : CNFRefutation 2.82s
% Verified   : 
% Statistics : Number of formulae       :   75 (  89 expanded)
%              Number of leaves         :   40 (  48 expanded)
%              Depth                    :    8
%              Number of atoms          :   89 ( 122 expanded)
%              Number of equality atoms :   27 (  38 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > k11_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_105,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k1_relat_1(B))
        <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_35,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).

tff(f_83,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_43,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_41,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

tff(c_54,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_62,plain,
    ( r2_hidden('#skF_3',k1_relat_1('#skF_4'))
    | k11_relat_1('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_104,plain,(
    k11_relat_1('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_4,plain,(
    ! [A_3] :
      ( r2_hidden('#skF_1'(A_3),A_3)
      | k1_xboole_0 = A_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_222,plain,(
    ! [A_96,B_97,C_98] :
      ( r2_hidden(k4_tarski(A_96,B_97),C_98)
      | ~ r2_hidden(B_97,k11_relat_1(C_98,A_96))
      | ~ v1_relat_1(C_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_52,plain,(
    ! [A_53,C_55,B_54] :
      ( r2_hidden(A_53,k1_relat_1(C_55))
      | ~ r2_hidden(k4_tarski(A_53,B_54),C_55)
      | ~ v1_relat_1(C_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_277,plain,(
    ! [A_105,C_106,B_107] :
      ( r2_hidden(A_105,k1_relat_1(C_106))
      | ~ r2_hidden(B_107,k11_relat_1(C_106,A_105))
      | ~ v1_relat_1(C_106) ) ),
    inference(resolution,[status(thm)],[c_222,c_52])).

tff(c_299,plain,(
    ! [A_113,C_114] :
      ( r2_hidden(A_113,k1_relat_1(C_114))
      | ~ v1_relat_1(C_114)
      | k11_relat_1(C_114,A_113) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_277])).

tff(c_56,plain,
    ( k11_relat_1('#skF_4','#skF_3') = k1_xboole_0
    | ~ r2_hidden('#skF_3',k1_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_150,plain,(
    ~ r2_hidden('#skF_3',k1_relat_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_56])).

tff(c_314,plain,
    ( ~ v1_relat_1('#skF_4')
    | k11_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_299,c_150])).

tff(c_320,plain,(
    k11_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_314])).

tff(c_322,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_320])).

tff(c_323,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_44,plain,(
    ! [A_49] :
      ( k10_relat_1(A_49,k2_relat_1(A_49)) = k1_relat_1(A_49)
      | ~ v1_relat_1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_10,plain,(
    ! [A_8] : k5_xboole_0(A_8,A_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_367,plain,(
    ! [A_122,B_123] : k5_xboole_0(A_122,k3_xboole_0(A_122,B_123)) = k4_xboole_0(A_122,B_123) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_376,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_367])).

tff(c_379,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_376])).

tff(c_30,plain,(
    ! [B_40] : k4_xboole_0(k1_tarski(B_40),k1_tarski(B_40)) != k1_tarski(B_40) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_389,plain,(
    ! [B_40] : k1_tarski(B_40) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_379,c_30])).

tff(c_91,plain,(
    ! [A_62,B_63] :
      ( r1_tarski(k1_tarski(A_62),B_63)
      | ~ r2_hidden(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_8,plain,(
    ! [A_7] :
      ( k1_xboole_0 = A_7
      | ~ r1_tarski(A_7,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_96,plain,(
    ! [A_62] :
      ( k1_tarski(A_62) = k1_xboole_0
      | ~ r2_hidden(A_62,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_91,c_8])).

tff(c_397,plain,(
    ! [A_62] : ~ r2_hidden(A_62,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_389,c_96])).

tff(c_324,plain,(
    k11_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_606,plain,(
    ! [A_176,B_177,C_178] :
      ( r2_hidden(k4_tarski(A_176,'#skF_2'(A_176,B_177,C_178)),C_178)
      | ~ r2_hidden(A_176,k10_relat_1(C_178,B_177))
      | ~ v1_relat_1(C_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_48,plain,(
    ! [B_51,C_52,A_50] :
      ( r2_hidden(B_51,k11_relat_1(C_52,A_50))
      | ~ r2_hidden(k4_tarski(A_50,B_51),C_52)
      | ~ v1_relat_1(C_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_772,plain,(
    ! [A_202,B_203,C_204] :
      ( r2_hidden('#skF_2'(A_202,B_203,C_204),k11_relat_1(C_204,A_202))
      | ~ r2_hidden(A_202,k10_relat_1(C_204,B_203))
      | ~ v1_relat_1(C_204) ) ),
    inference(resolution,[status(thm)],[c_606,c_48])).

tff(c_784,plain,(
    ! [B_203] :
      ( r2_hidden('#skF_2'('#skF_3',B_203,'#skF_4'),k1_xboole_0)
      | ~ r2_hidden('#skF_3',k10_relat_1('#skF_4',B_203))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_324,c_772])).

tff(c_789,plain,(
    ! [B_203] :
      ( r2_hidden('#skF_2'('#skF_3',B_203,'#skF_4'),k1_xboole_0)
      | ~ r2_hidden('#skF_3',k10_relat_1('#skF_4',B_203)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_784])).

tff(c_791,plain,(
    ! [B_205] : ~ r2_hidden('#skF_3',k10_relat_1('#skF_4',B_205)) ),
    inference(negUnitSimplification,[status(thm)],[c_397,c_789])).

tff(c_801,plain,
    ( ~ r2_hidden('#skF_3',k1_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_791])).

tff(c_806,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_323,c_801])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:49:14 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.82/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.82/1.40  
% 2.82/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.82/1.40  %$ r2_hidden > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > k11_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 2.82/1.40  
% 2.82/1.40  %Foreground sorts:
% 2.82/1.40  
% 2.82/1.40  
% 2.82/1.40  %Background operators:
% 2.82/1.40  
% 2.82/1.40  
% 2.82/1.40  %Foreground operators:
% 2.82/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.82/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.82/1.40  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.82/1.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.82/1.40  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.82/1.40  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.82/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.82/1.40  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.82/1.40  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.82/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.82/1.40  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.82/1.40  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.82/1.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.82/1.40  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 2.82/1.40  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.82/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.82/1.40  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.82/1.40  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.82/1.40  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.82/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.82/1.40  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.82/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.82/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.82/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.82/1.40  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.82/1.40  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.82/1.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.82/1.40  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.82/1.40  
% 2.82/1.42  tff(f_105, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t205_relat_1)).
% 2.82/1.42  tff(f_35, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.82/1.42  tff(f_89, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t204_relat_1)).
% 2.82/1.42  tff(f_97, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_relat_1)).
% 2.82/1.42  tff(f_83, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 2.82/1.42  tff(f_43, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.82/1.42  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.82/1.42  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.82/1.42  tff(f_66, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.82/1.42  tff(f_61, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.82/1.42  tff(f_41, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.82/1.42  tff(f_79, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 2.82/1.42  tff(c_54, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.82/1.42  tff(c_62, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_4')) | k11_relat_1('#skF_4', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.82/1.42  tff(c_104, plain, (k11_relat_1('#skF_4', '#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_62])).
% 2.82/1.42  tff(c_4, plain, (![A_3]: (r2_hidden('#skF_1'(A_3), A_3) | k1_xboole_0=A_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.82/1.42  tff(c_222, plain, (![A_96, B_97, C_98]: (r2_hidden(k4_tarski(A_96, B_97), C_98) | ~r2_hidden(B_97, k11_relat_1(C_98, A_96)) | ~v1_relat_1(C_98))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.82/1.42  tff(c_52, plain, (![A_53, C_55, B_54]: (r2_hidden(A_53, k1_relat_1(C_55)) | ~r2_hidden(k4_tarski(A_53, B_54), C_55) | ~v1_relat_1(C_55))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.82/1.42  tff(c_277, plain, (![A_105, C_106, B_107]: (r2_hidden(A_105, k1_relat_1(C_106)) | ~r2_hidden(B_107, k11_relat_1(C_106, A_105)) | ~v1_relat_1(C_106))), inference(resolution, [status(thm)], [c_222, c_52])).
% 2.82/1.42  tff(c_299, plain, (![A_113, C_114]: (r2_hidden(A_113, k1_relat_1(C_114)) | ~v1_relat_1(C_114) | k11_relat_1(C_114, A_113)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_277])).
% 2.82/1.42  tff(c_56, plain, (k11_relat_1('#skF_4', '#skF_3')=k1_xboole_0 | ~r2_hidden('#skF_3', k1_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.82/1.42  tff(c_150, plain, (~r2_hidden('#skF_3', k1_relat_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_104, c_56])).
% 2.82/1.42  tff(c_314, plain, (~v1_relat_1('#skF_4') | k11_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_299, c_150])).
% 2.82/1.42  tff(c_320, plain, (k11_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_54, c_314])).
% 2.82/1.42  tff(c_322, plain, $false, inference(negUnitSimplification, [status(thm)], [c_104, c_320])).
% 2.82/1.42  tff(c_323, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_62])).
% 2.82/1.42  tff(c_44, plain, (![A_49]: (k10_relat_1(A_49, k2_relat_1(A_49))=k1_relat_1(A_49) | ~v1_relat_1(A_49))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.82/1.42  tff(c_10, plain, (![A_8]: (k5_xboole_0(A_8, A_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.82/1.42  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.82/1.42  tff(c_367, plain, (![A_122, B_123]: (k5_xboole_0(A_122, k3_xboole_0(A_122, B_123))=k4_xboole_0(A_122, B_123))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.82/1.42  tff(c_376, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_367])).
% 2.82/1.42  tff(c_379, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_376])).
% 2.82/1.42  tff(c_30, plain, (![B_40]: (k4_xboole_0(k1_tarski(B_40), k1_tarski(B_40))!=k1_tarski(B_40))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.82/1.42  tff(c_389, plain, (![B_40]: (k1_tarski(B_40)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_379, c_30])).
% 2.82/1.42  tff(c_91, plain, (![A_62, B_63]: (r1_tarski(k1_tarski(A_62), B_63) | ~r2_hidden(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.82/1.42  tff(c_8, plain, (![A_7]: (k1_xboole_0=A_7 | ~r1_tarski(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.82/1.42  tff(c_96, plain, (![A_62]: (k1_tarski(A_62)=k1_xboole_0 | ~r2_hidden(A_62, k1_xboole_0))), inference(resolution, [status(thm)], [c_91, c_8])).
% 2.82/1.42  tff(c_397, plain, (![A_62]: (~r2_hidden(A_62, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_389, c_96])).
% 2.82/1.42  tff(c_324, plain, (k11_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_62])).
% 2.82/1.42  tff(c_606, plain, (![A_176, B_177, C_178]: (r2_hidden(k4_tarski(A_176, '#skF_2'(A_176, B_177, C_178)), C_178) | ~r2_hidden(A_176, k10_relat_1(C_178, B_177)) | ~v1_relat_1(C_178))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.82/1.42  tff(c_48, plain, (![B_51, C_52, A_50]: (r2_hidden(B_51, k11_relat_1(C_52, A_50)) | ~r2_hidden(k4_tarski(A_50, B_51), C_52) | ~v1_relat_1(C_52))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.82/1.42  tff(c_772, plain, (![A_202, B_203, C_204]: (r2_hidden('#skF_2'(A_202, B_203, C_204), k11_relat_1(C_204, A_202)) | ~r2_hidden(A_202, k10_relat_1(C_204, B_203)) | ~v1_relat_1(C_204))), inference(resolution, [status(thm)], [c_606, c_48])).
% 2.82/1.42  tff(c_784, plain, (![B_203]: (r2_hidden('#skF_2'('#skF_3', B_203, '#skF_4'), k1_xboole_0) | ~r2_hidden('#skF_3', k10_relat_1('#skF_4', B_203)) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_324, c_772])).
% 2.82/1.42  tff(c_789, plain, (![B_203]: (r2_hidden('#skF_2'('#skF_3', B_203, '#skF_4'), k1_xboole_0) | ~r2_hidden('#skF_3', k10_relat_1('#skF_4', B_203)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_784])).
% 2.82/1.42  tff(c_791, plain, (![B_205]: (~r2_hidden('#skF_3', k10_relat_1('#skF_4', B_205)))), inference(negUnitSimplification, [status(thm)], [c_397, c_789])).
% 2.82/1.42  tff(c_801, plain, (~r2_hidden('#skF_3', k1_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_44, c_791])).
% 2.82/1.42  tff(c_806, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_323, c_801])).
% 2.82/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.82/1.42  
% 2.82/1.42  Inference rules
% 2.82/1.42  ----------------------
% 2.82/1.42  #Ref     : 0
% 2.82/1.42  #Sup     : 154
% 2.82/1.42  #Fact    : 0
% 2.82/1.42  #Define  : 0
% 2.82/1.42  #Split   : 3
% 2.82/1.42  #Chain   : 0
% 2.82/1.42  #Close   : 0
% 2.82/1.42  
% 2.82/1.42  Ordering : KBO
% 2.82/1.42  
% 2.82/1.42  Simplification rules
% 2.82/1.42  ----------------------
% 2.82/1.42  #Subsume      : 22
% 2.82/1.42  #Demod        : 33
% 2.82/1.42  #Tautology    : 73
% 2.82/1.42  #SimpNegUnit  : 7
% 2.82/1.42  #BackRed      : 4
% 2.82/1.42  
% 2.82/1.42  #Partial instantiations: 0
% 2.82/1.42  #Strategies tried      : 1
% 2.82/1.42  
% 2.82/1.42  Timing (in seconds)
% 2.82/1.42  ----------------------
% 2.82/1.42  Preprocessing        : 0.34
% 2.82/1.42  Parsing              : 0.18
% 2.82/1.42  CNF conversion       : 0.02
% 2.82/1.42  Main loop            : 0.32
% 2.82/1.42  Inferencing          : 0.13
% 2.82/1.42  Reduction            : 0.09
% 2.82/1.42  Demodulation         : 0.06
% 2.82/1.42  BG Simplification    : 0.02
% 2.82/1.42  Subsumption          : 0.06
% 2.82/1.42  Abstraction          : 0.02
% 2.82/1.42  MUC search           : 0.00
% 2.82/1.42  Cooper               : 0.00
% 2.82/1.42  Total                : 0.69
% 2.82/1.42  Index Insertion      : 0.00
% 2.82/1.42  Index Deletion       : 0.00
% 2.82/1.42  Index Matching       : 0.00
% 2.82/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
