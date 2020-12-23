%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:23 EST 2020

% Result     : Theorem 3.15s
% Output     : CNFRefutation 3.15s
% Verified   : 
% Statistics : Number of formulae       :   78 (  95 expanded)
%              Number of leaves         :   41 (  50 expanded)
%              Depth                    :    9
%              Number of atoms          :   92 ( 131 expanded)
%              Number of equality atoms :   30 (  43 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

tff(f_83,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_43,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_41,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : k3_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_39,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

tff(c_54,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_56,plain,
    ( k11_relat_1('#skF_4','#skF_3') = k1_xboole_0
    | ~ r2_hidden('#skF_3',k1_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_123,plain,(
    ~ r2_hidden('#skF_3',k1_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_62,plain,
    ( r2_hidden('#skF_3',k1_relat_1('#skF_4'))
    | k11_relat_1('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_160,plain,(
    k11_relat_1('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_123,c_62])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_296,plain,(
    ! [A_102,B_103,C_104] :
      ( r2_hidden(k4_tarski(A_102,B_103),C_104)
      | ~ r2_hidden(B_103,k11_relat_1(C_104,A_102))
      | ~ v1_relat_1(C_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_52,plain,(
    ! [A_53,C_55,B_54] :
      ( r2_hidden(A_53,k1_relat_1(C_55))
      | ~ r2_hidden(k4_tarski(A_53,B_54),C_55)
      | ~ v1_relat_1(C_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_324,plain,(
    ! [A_110,C_111,B_112] :
      ( r2_hidden(A_110,k1_relat_1(C_111))
      | ~ r2_hidden(B_112,k11_relat_1(C_111,A_110))
      | ~ v1_relat_1(C_111) ) ),
    inference(resolution,[status(thm)],[c_296,c_52])).

tff(c_333,plain,(
    ! [A_113,C_114] :
      ( r2_hidden(A_113,k1_relat_1(C_114))
      | ~ v1_relat_1(C_114)
      | k11_relat_1(C_114,A_113) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_324])).

tff(c_348,plain,
    ( ~ v1_relat_1('#skF_4')
    | k11_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_333,c_123])).

tff(c_354,plain,(
    k11_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_348])).

tff(c_356,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_160,c_354])).

tff(c_357,plain,(
    k11_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_364,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_357,c_62])).

tff(c_44,plain,(
    ! [A_49] :
      ( k10_relat_1(A_49,k2_relat_1(A_49)) = k1_relat_1(A_49)
      | ~ v1_relat_1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_10,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8,plain,(
    ! [A_6] : k5_xboole_0(A_6,A_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_393,plain,(
    ! [A_122,B_123] : k3_xboole_0(k1_tarski(A_122),k2_tarski(A_122,B_123)) = k1_tarski(A_122) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_399,plain,(
    ! [A_122,B_123] : k5_xboole_0(k1_tarski(A_122),k1_tarski(A_122)) = k4_xboole_0(k1_tarski(A_122),k2_tarski(A_122,B_123)) ),
    inference(superposition,[status(thm),theory(equality)],[c_393,c_4])).

tff(c_409,plain,(
    ! [A_124,B_125] : k4_xboole_0(k1_tarski(A_124),k2_tarski(A_124,B_125)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_399])).

tff(c_416,plain,(
    ! [A_7] : k4_xboole_0(k1_tarski(A_7),k1_tarski(A_7)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_409])).

tff(c_30,plain,(
    ! [B_40] : k4_xboole_0(k1_tarski(B_40),k1_tarski(B_40)) != k1_tarski(B_40) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_419,plain,(
    ! [B_40] : k1_tarski(B_40) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_416,c_30])).

tff(c_81,plain,(
    ! [A_60,B_61] :
      ( r1_tarski(k1_tarski(A_60),B_61)
      | ~ r2_hidden(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ r1_tarski(A_5,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_86,plain,(
    ! [A_60] :
      ( k1_tarski(A_60) = k1_xboole_0
      | ~ r2_hidden(A_60,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_81,c_6])).

tff(c_427,plain,(
    ! [A_60] : ~ r2_hidden(A_60,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_419,c_86])).

tff(c_731,plain,(
    ! [A_194,B_195,C_196] :
      ( r2_hidden(k4_tarski(A_194,'#skF_2'(A_194,B_195,C_196)),C_196)
      | ~ r2_hidden(A_194,k10_relat_1(C_196,B_195))
      | ~ v1_relat_1(C_196) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_48,plain,(
    ! [B_51,C_52,A_50] :
      ( r2_hidden(B_51,k11_relat_1(C_52,A_50))
      | ~ r2_hidden(k4_tarski(A_50,B_51),C_52)
      | ~ v1_relat_1(C_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_856,plain,(
    ! [A_207,B_208,C_209] :
      ( r2_hidden('#skF_2'(A_207,B_208,C_209),k11_relat_1(C_209,A_207))
      | ~ r2_hidden(A_207,k10_relat_1(C_209,B_208))
      | ~ v1_relat_1(C_209) ) ),
    inference(resolution,[status(thm)],[c_731,c_48])).

tff(c_868,plain,(
    ! [B_208] :
      ( r2_hidden('#skF_2'('#skF_3',B_208,'#skF_4'),k1_xboole_0)
      | ~ r2_hidden('#skF_3',k10_relat_1('#skF_4',B_208))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_357,c_856])).

tff(c_873,plain,(
    ! [B_208] :
      ( r2_hidden('#skF_2'('#skF_3',B_208,'#skF_4'),k1_xboole_0)
      | ~ r2_hidden('#skF_3',k10_relat_1('#skF_4',B_208)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_868])).

tff(c_884,plain,(
    ! [B_217] : ~ r2_hidden('#skF_3',k10_relat_1('#skF_4',B_217)) ),
    inference(negUnitSimplification,[status(thm)],[c_427,c_873])).

tff(c_894,plain,
    ( ~ r2_hidden('#skF_3',k1_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_884])).

tff(c_899,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_364,c_894])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.31  % Computer   : n005.cluster.edu
% 0.13/0.31  % Model      : x86_64 x86_64
% 0.13/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.31  % Memory     : 8042.1875MB
% 0.13/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 16:43:32 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.15/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.15/1.48  
% 3.15/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.15/1.49  %$ r2_hidden > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > k11_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 3.15/1.49  
% 3.15/1.49  %Foreground sorts:
% 3.15/1.49  
% 3.15/1.49  
% 3.15/1.49  %Background operators:
% 3.15/1.49  
% 3.15/1.49  
% 3.15/1.49  %Foreground operators:
% 3.15/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.15/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.15/1.49  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.15/1.49  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.15/1.49  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.15/1.49  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.15/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.15/1.49  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.15/1.49  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.15/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.15/1.49  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.15/1.49  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.15/1.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.15/1.49  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 3.15/1.49  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.15/1.49  tff('#skF_3', type, '#skF_3': $i).
% 3.15/1.49  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.15/1.49  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.15/1.49  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.15/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.15/1.49  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.15/1.49  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.15/1.49  tff('#skF_4', type, '#skF_4': $i).
% 3.15/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.15/1.49  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.15/1.49  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.15/1.49  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.15/1.49  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.15/1.49  
% 3.15/1.51  tff(f_105, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 3.15/1.51  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.15/1.51  tff(f_89, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t204_relat_1)).
% 3.15/1.51  tff(f_97, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_relat_1)).
% 3.15/1.51  tff(f_83, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 3.15/1.51  tff(f_43, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.15/1.51  tff(f_41, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.15/1.51  tff(f_61, axiom, (![A, B]: (k3_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_zfmisc_1)).
% 3.15/1.51  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.15/1.51  tff(f_66, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 3.15/1.51  tff(f_59, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.15/1.51  tff(f_39, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 3.15/1.51  tff(f_79, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 3.15/1.51  tff(c_54, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.15/1.51  tff(c_56, plain, (k11_relat_1('#skF_4', '#skF_3')=k1_xboole_0 | ~r2_hidden('#skF_3', k1_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.15/1.51  tff(c_123, plain, (~r2_hidden('#skF_3', k1_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_56])).
% 3.15/1.51  tff(c_62, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_4')) | k11_relat_1('#skF_4', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.15/1.51  tff(c_160, plain, (k11_relat_1('#skF_4', '#skF_3')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_123, c_62])).
% 3.15/1.51  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.15/1.51  tff(c_296, plain, (![A_102, B_103, C_104]: (r2_hidden(k4_tarski(A_102, B_103), C_104) | ~r2_hidden(B_103, k11_relat_1(C_104, A_102)) | ~v1_relat_1(C_104))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.15/1.51  tff(c_52, plain, (![A_53, C_55, B_54]: (r2_hidden(A_53, k1_relat_1(C_55)) | ~r2_hidden(k4_tarski(A_53, B_54), C_55) | ~v1_relat_1(C_55))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.15/1.51  tff(c_324, plain, (![A_110, C_111, B_112]: (r2_hidden(A_110, k1_relat_1(C_111)) | ~r2_hidden(B_112, k11_relat_1(C_111, A_110)) | ~v1_relat_1(C_111))), inference(resolution, [status(thm)], [c_296, c_52])).
% 3.15/1.51  tff(c_333, plain, (![A_113, C_114]: (r2_hidden(A_113, k1_relat_1(C_114)) | ~v1_relat_1(C_114) | k11_relat_1(C_114, A_113)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_324])).
% 3.15/1.51  tff(c_348, plain, (~v1_relat_1('#skF_4') | k11_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_333, c_123])).
% 3.15/1.51  tff(c_354, plain, (k11_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_54, c_348])).
% 3.15/1.51  tff(c_356, plain, $false, inference(negUnitSimplification, [status(thm)], [c_160, c_354])).
% 3.15/1.51  tff(c_357, plain, (k11_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_56])).
% 3.15/1.51  tff(c_364, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_357, c_62])).
% 3.15/1.51  tff(c_44, plain, (![A_49]: (k10_relat_1(A_49, k2_relat_1(A_49))=k1_relat_1(A_49) | ~v1_relat_1(A_49))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.15/1.51  tff(c_10, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.15/1.51  tff(c_8, plain, (![A_6]: (k5_xboole_0(A_6, A_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.15/1.51  tff(c_393, plain, (![A_122, B_123]: (k3_xboole_0(k1_tarski(A_122), k2_tarski(A_122, B_123))=k1_tarski(A_122))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.15/1.51  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.15/1.51  tff(c_399, plain, (![A_122, B_123]: (k5_xboole_0(k1_tarski(A_122), k1_tarski(A_122))=k4_xboole_0(k1_tarski(A_122), k2_tarski(A_122, B_123)))), inference(superposition, [status(thm), theory('equality')], [c_393, c_4])).
% 3.15/1.51  tff(c_409, plain, (![A_124, B_125]: (k4_xboole_0(k1_tarski(A_124), k2_tarski(A_124, B_125))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_399])).
% 3.15/1.51  tff(c_416, plain, (![A_7]: (k4_xboole_0(k1_tarski(A_7), k1_tarski(A_7))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10, c_409])).
% 3.15/1.51  tff(c_30, plain, (![B_40]: (k4_xboole_0(k1_tarski(B_40), k1_tarski(B_40))!=k1_tarski(B_40))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.15/1.51  tff(c_419, plain, (![B_40]: (k1_tarski(B_40)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_416, c_30])).
% 3.15/1.51  tff(c_81, plain, (![A_60, B_61]: (r1_tarski(k1_tarski(A_60), B_61) | ~r2_hidden(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.15/1.51  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~r1_tarski(A_5, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.15/1.51  tff(c_86, plain, (![A_60]: (k1_tarski(A_60)=k1_xboole_0 | ~r2_hidden(A_60, k1_xboole_0))), inference(resolution, [status(thm)], [c_81, c_6])).
% 3.15/1.51  tff(c_427, plain, (![A_60]: (~r2_hidden(A_60, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_419, c_86])).
% 3.15/1.51  tff(c_731, plain, (![A_194, B_195, C_196]: (r2_hidden(k4_tarski(A_194, '#skF_2'(A_194, B_195, C_196)), C_196) | ~r2_hidden(A_194, k10_relat_1(C_196, B_195)) | ~v1_relat_1(C_196))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.15/1.51  tff(c_48, plain, (![B_51, C_52, A_50]: (r2_hidden(B_51, k11_relat_1(C_52, A_50)) | ~r2_hidden(k4_tarski(A_50, B_51), C_52) | ~v1_relat_1(C_52))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.15/1.51  tff(c_856, plain, (![A_207, B_208, C_209]: (r2_hidden('#skF_2'(A_207, B_208, C_209), k11_relat_1(C_209, A_207)) | ~r2_hidden(A_207, k10_relat_1(C_209, B_208)) | ~v1_relat_1(C_209))), inference(resolution, [status(thm)], [c_731, c_48])).
% 3.15/1.51  tff(c_868, plain, (![B_208]: (r2_hidden('#skF_2'('#skF_3', B_208, '#skF_4'), k1_xboole_0) | ~r2_hidden('#skF_3', k10_relat_1('#skF_4', B_208)) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_357, c_856])).
% 3.15/1.51  tff(c_873, plain, (![B_208]: (r2_hidden('#skF_2'('#skF_3', B_208, '#skF_4'), k1_xboole_0) | ~r2_hidden('#skF_3', k10_relat_1('#skF_4', B_208)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_868])).
% 3.15/1.51  tff(c_884, plain, (![B_217]: (~r2_hidden('#skF_3', k10_relat_1('#skF_4', B_217)))), inference(negUnitSimplification, [status(thm)], [c_427, c_873])).
% 3.15/1.51  tff(c_894, plain, (~r2_hidden('#skF_3', k1_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_44, c_884])).
% 3.15/1.51  tff(c_899, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_364, c_894])).
% 3.15/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.15/1.51  
% 3.15/1.51  Inference rules
% 3.15/1.51  ----------------------
% 3.15/1.51  #Ref     : 0
% 3.15/1.51  #Sup     : 179
% 3.15/1.51  #Fact    : 0
% 3.15/1.51  #Define  : 0
% 3.15/1.51  #Split   : 3
% 3.15/1.51  #Chain   : 0
% 3.15/1.51  #Close   : 0
% 3.15/1.51  
% 3.15/1.51  Ordering : KBO
% 3.15/1.51  
% 3.15/1.51  Simplification rules
% 3.15/1.51  ----------------------
% 3.15/1.51  #Subsume      : 21
% 3.15/1.51  #Demod        : 42
% 3.15/1.51  #Tautology    : 98
% 3.15/1.51  #SimpNegUnit  : 7
% 3.15/1.51  #BackRed      : 4
% 3.15/1.51  
% 3.15/1.51  #Partial instantiations: 0
% 3.15/1.51  #Strategies tried      : 1
% 3.15/1.51  
% 3.15/1.51  Timing (in seconds)
% 3.15/1.51  ----------------------
% 3.15/1.51  Preprocessing        : 0.35
% 3.15/1.51  Parsing              : 0.18
% 3.15/1.51  CNF conversion       : 0.03
% 3.15/1.51  Main loop            : 0.41
% 3.15/1.51  Inferencing          : 0.17
% 3.15/1.51  Reduction            : 0.12
% 3.15/1.51  Demodulation         : 0.07
% 3.15/1.51  BG Simplification    : 0.02
% 3.15/1.51  Subsumption          : 0.07
% 3.15/1.51  Abstraction          : 0.02
% 3.15/1.51  MUC search           : 0.00
% 3.15/1.51  Cooper               : 0.00
% 3.15/1.51  Total                : 0.80
% 3.15/1.51  Index Insertion      : 0.00
% 3.15/1.51  Index Deletion       : 0.00
% 3.15/1.51  Index Matching       : 0.00
% 3.15/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
