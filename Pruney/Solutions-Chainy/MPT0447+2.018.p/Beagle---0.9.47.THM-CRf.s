%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:30 EST 2020

% Result     : Theorem 39.70s
% Output     : CNFRefutation 39.82s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 109 expanded)
%              Number of leaves         :   33 (  53 expanded)
%              Depth                    :    8
%              Number of atoms          :  117 ( 212 expanded)
%              Number of equality atoms :   15 (  25 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_111,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_tarski(A,B)
             => r1_tarski(k3_relat_1(A),k3_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_101,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_90,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_53,axiom,(
    ! [A,B,C] : r1_tarski(k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)),k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_56,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_54,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_52,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_12,plain,(
    ! [A_8,B_9] : r1_tarski(k3_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_69,plain,(
    ! [A_67,B_68] :
      ( k2_xboole_0(A_67,B_68) = B_68
      | ~ r1_tarski(A_67,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_79,plain,(
    ! [A_8,B_9] : k2_xboole_0(k3_xboole_0(A_8,B_9),A_8) = A_8 ),
    inference(resolution,[status(thm)],[c_12,c_69])).

tff(c_2939,plain,(
    ! [A_208,B_209] :
      ( r1_tarski(k2_relat_1(A_208),k2_relat_1(B_209))
      | ~ r1_tarski(A_208,B_209)
      | ~ v1_relat_1(B_209)
      | ~ v1_relat_1(A_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( k3_xboole_0(A_13,B_14) = A_13
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_14792,plain,(
    ! [A_433,B_434] :
      ( k3_xboole_0(k2_relat_1(A_433),k2_relat_1(B_434)) = k2_relat_1(A_433)
      | ~ r1_tarski(A_433,B_434)
      | ~ v1_relat_1(B_434)
      | ~ v1_relat_1(A_433) ) ),
    inference(resolution,[status(thm)],[c_2939,c_16])).

tff(c_44,plain,(
    ! [A_57] :
      ( k2_xboole_0(k1_relat_1(A_57),k2_relat_1(A_57)) = k3_relat_1(A_57)
      | ~ v1_relat_1(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2263,plain,(
    ! [A_194,B_195,C_196] : r1_tarski(k2_xboole_0(k3_xboole_0(A_194,B_195),k3_xboole_0(A_194,C_196)),k2_xboole_0(B_195,C_196)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2317,plain,(
    ! [A_194,A_57] :
      ( r1_tarski(k2_xboole_0(k3_xboole_0(A_194,k1_relat_1(A_57)),k3_xboole_0(A_194,k2_relat_1(A_57))),k3_relat_1(A_57))
      | ~ v1_relat_1(A_57) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_2263])).

tff(c_14801,plain,(
    ! [A_433,B_434] :
      ( r1_tarski(k2_xboole_0(k3_xboole_0(k2_relat_1(A_433),k1_relat_1(B_434)),k2_relat_1(A_433)),k3_relat_1(B_434))
      | ~ v1_relat_1(B_434)
      | ~ r1_tarski(A_433,B_434)
      | ~ v1_relat_1(B_434)
      | ~ v1_relat_1(A_433) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14792,c_2317])).

tff(c_168358,plain,(
    ! [A_1801,B_1802] :
      ( r1_tarski(k2_relat_1(A_1801),k3_relat_1(B_1802))
      | ~ v1_relat_1(B_1802)
      | ~ r1_tarski(A_1801,B_1802)
      | ~ v1_relat_1(B_1802)
      | ~ v1_relat_1(A_1801) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_14801])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_175,plain,(
    ! [A_85,C_86,B_87] :
      ( r1_tarski(A_85,C_86)
      | ~ r1_tarski(k2_xboole_0(A_85,B_87),C_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_189,plain,(
    ! [A_85,B_87] : r1_tarski(A_85,k2_xboole_0(A_85,B_87)) ),
    inference(resolution,[status(thm)],[c_6,c_175])).

tff(c_1525,plain,(
    ! [A_162,C_163,B_164] :
      ( r1_tarski(k2_xboole_0(A_162,C_163),B_164)
      | ~ r1_tarski(C_163,B_164)
      | ~ r1_tarski(A_162,B_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_17495,plain,(
    ! [A_476,C_477,B_478] :
      ( k2_xboole_0(A_476,C_477) = B_478
      | ~ r1_tarski(B_478,k2_xboole_0(A_476,C_477))
      | ~ r1_tarski(C_477,B_478)
      | ~ r1_tarski(A_476,B_478) ) ),
    inference(resolution,[status(thm)],[c_1525,c_2])).

tff(c_17695,plain,(
    ! [A_85,B_87] :
      ( k2_xboole_0(A_85,B_87) = A_85
      | ~ r1_tarski(B_87,A_85)
      | ~ r1_tarski(A_85,A_85) ) ),
    inference(resolution,[status(thm)],[c_189,c_17495])).

tff(c_17782,plain,(
    ! [A_479,B_480] :
      ( k2_xboole_0(A_479,B_480) = A_479
      | ~ r1_tarski(B_480,A_479) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_17695])).

tff(c_18012,plain,(
    ! [A_8,B_9] : k2_xboole_0(A_8,k3_xboole_0(A_8,B_9)) = A_8 ),
    inference(resolution,[status(thm)],[c_12,c_17782])).

tff(c_3637,plain,(
    ! [A_223,B_224] :
      ( r1_tarski(k1_relat_1(A_223),k1_relat_1(B_224))
      | ~ r1_tarski(A_223,B_224)
      | ~ v1_relat_1(B_224)
      | ~ v1_relat_1(A_223) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_3657,plain,(
    ! [A_223,B_224] :
      ( k3_xboole_0(k1_relat_1(A_223),k1_relat_1(B_224)) = k1_relat_1(A_223)
      | ~ r1_tarski(A_223,B_224)
      | ~ v1_relat_1(B_224)
      | ~ v1_relat_1(A_223) ) ),
    inference(resolution,[status(thm)],[c_3637,c_16])).

tff(c_12638,plain,(
    ! [A_413,A_414] :
      ( r1_tarski(k2_xboole_0(k3_xboole_0(A_413,k1_relat_1(A_414)),k3_xboole_0(A_413,k2_relat_1(A_414))),k3_relat_1(A_414))
      | ~ v1_relat_1(A_414) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_2263])).

tff(c_12662,plain,(
    ! [A_223,B_224] :
      ( r1_tarski(k2_xboole_0(k1_relat_1(A_223),k3_xboole_0(k1_relat_1(A_223),k2_relat_1(B_224))),k3_relat_1(B_224))
      | ~ v1_relat_1(B_224)
      | ~ r1_tarski(A_223,B_224)
      | ~ v1_relat_1(B_224)
      | ~ v1_relat_1(A_223) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3657,c_12638])).

tff(c_124618,plain,(
    ! [A_1364,B_1365] :
      ( r1_tarski(k1_relat_1(A_1364),k3_relat_1(B_1365))
      | ~ v1_relat_1(B_1365)
      | ~ r1_tarski(A_1364,B_1365)
      | ~ v1_relat_1(B_1365)
      | ~ v1_relat_1(A_1364) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18012,c_12662])).

tff(c_16661,plain,(
    ! [A_454,B_455] :
      ( r1_tarski(k3_relat_1(A_454),B_455)
      | ~ r1_tarski(k2_relat_1(A_454),B_455)
      | ~ r1_tarski(k1_relat_1(A_454),B_455)
      | ~ v1_relat_1(A_454) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_1525])).

tff(c_50,plain,(
    ~ r1_tarski(k3_relat_1('#skF_1'),k3_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_16729,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_1'),k3_relat_1('#skF_2'))
    | ~ r1_tarski(k1_relat_1('#skF_1'),k3_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_16661,c_50])).

tff(c_16751,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_1'),k3_relat_1('#skF_2'))
    | ~ r1_tarski(k1_relat_1('#skF_1'),k3_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_16729])).

tff(c_16914,plain,(
    ~ r1_tarski(k1_relat_1('#skF_1'),k3_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_16751])).

tff(c_124656,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_124618,c_16914])).

tff(c_124692,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_124656])).

tff(c_124693,plain,(
    ~ r1_tarski(k2_relat_1('#skF_1'),k3_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_16751])).

tff(c_168370,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_168358,c_124693])).

tff(c_168393,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_168370])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:06:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 39.70/29.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 39.70/29.38  
% 39.70/29.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 39.70/29.38  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 39.70/29.38  
% 39.70/29.38  %Foreground sorts:
% 39.70/29.38  
% 39.70/29.38  
% 39.70/29.38  %Background operators:
% 39.70/29.38  
% 39.70/29.38  
% 39.70/29.38  %Foreground operators:
% 39.70/29.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 39.70/29.38  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 39.70/29.38  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 39.70/29.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 39.70/29.38  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 39.70/29.38  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 39.70/29.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 39.70/29.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 39.70/29.38  tff('#skF_2', type, '#skF_2': $i).
% 39.70/29.38  tff('#skF_1', type, '#skF_1': $i).
% 39.70/29.38  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 39.70/29.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 39.70/29.38  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 39.70/29.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 39.70/29.38  tff(k3_tarski, type, k3_tarski: $i > $i).
% 39.70/29.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 39.70/29.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 39.70/29.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 39.70/29.38  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 39.70/29.38  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 39.70/29.38  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 39.70/29.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 39.70/29.38  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 39.70/29.38  
% 39.82/29.39  tff(f_111, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => r1_tarski(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_relat_1)).
% 39.82/29.39  tff(f_41, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 39.82/29.39  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 39.82/29.39  tff(f_101, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 39.82/29.39  tff(f_51, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 39.82/29.39  tff(f_90, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 39.82/29.39  tff(f_53, axiom, (![A, B, C]: r1_tarski(k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)), k2_xboole_0(B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_xboole_1)).
% 39.82/29.39  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 39.82/29.39  tff(f_35, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 39.82/29.39  tff(f_59, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 39.82/29.39  tff(c_56, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 39.82/29.39  tff(c_54, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_111])).
% 39.82/29.39  tff(c_52, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_111])).
% 39.82/29.39  tff(c_12, plain, (![A_8, B_9]: (r1_tarski(k3_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 39.82/29.39  tff(c_69, plain, (![A_67, B_68]: (k2_xboole_0(A_67, B_68)=B_68 | ~r1_tarski(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_39])).
% 39.82/29.39  tff(c_79, plain, (![A_8, B_9]: (k2_xboole_0(k3_xboole_0(A_8, B_9), A_8)=A_8)), inference(resolution, [status(thm)], [c_12, c_69])).
% 39.82/29.39  tff(c_2939, plain, (![A_208, B_209]: (r1_tarski(k2_relat_1(A_208), k2_relat_1(B_209)) | ~r1_tarski(A_208, B_209) | ~v1_relat_1(B_209) | ~v1_relat_1(A_208))), inference(cnfTransformation, [status(thm)], [f_101])).
% 39.82/29.39  tff(c_16, plain, (![A_13, B_14]: (k3_xboole_0(A_13, B_14)=A_13 | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_51])).
% 39.82/29.39  tff(c_14792, plain, (![A_433, B_434]: (k3_xboole_0(k2_relat_1(A_433), k2_relat_1(B_434))=k2_relat_1(A_433) | ~r1_tarski(A_433, B_434) | ~v1_relat_1(B_434) | ~v1_relat_1(A_433))), inference(resolution, [status(thm)], [c_2939, c_16])).
% 39.82/29.39  tff(c_44, plain, (![A_57]: (k2_xboole_0(k1_relat_1(A_57), k2_relat_1(A_57))=k3_relat_1(A_57) | ~v1_relat_1(A_57))), inference(cnfTransformation, [status(thm)], [f_90])).
% 39.82/29.39  tff(c_2263, plain, (![A_194, B_195, C_196]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_194, B_195), k3_xboole_0(A_194, C_196)), k2_xboole_0(B_195, C_196)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 39.82/29.39  tff(c_2317, plain, (![A_194, A_57]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_194, k1_relat_1(A_57)), k3_xboole_0(A_194, k2_relat_1(A_57))), k3_relat_1(A_57)) | ~v1_relat_1(A_57))), inference(superposition, [status(thm), theory('equality')], [c_44, c_2263])).
% 39.82/29.39  tff(c_14801, plain, (![A_433, B_434]: (r1_tarski(k2_xboole_0(k3_xboole_0(k2_relat_1(A_433), k1_relat_1(B_434)), k2_relat_1(A_433)), k3_relat_1(B_434)) | ~v1_relat_1(B_434) | ~r1_tarski(A_433, B_434) | ~v1_relat_1(B_434) | ~v1_relat_1(A_433))), inference(superposition, [status(thm), theory('equality')], [c_14792, c_2317])).
% 39.82/29.39  tff(c_168358, plain, (![A_1801, B_1802]: (r1_tarski(k2_relat_1(A_1801), k3_relat_1(B_1802)) | ~v1_relat_1(B_1802) | ~r1_tarski(A_1801, B_1802) | ~v1_relat_1(B_1802) | ~v1_relat_1(A_1801))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_14801])).
% 39.82/29.39  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 39.82/29.39  tff(c_175, plain, (![A_85, C_86, B_87]: (r1_tarski(A_85, C_86) | ~r1_tarski(k2_xboole_0(A_85, B_87), C_86))), inference(cnfTransformation, [status(thm)], [f_35])).
% 39.82/29.39  tff(c_189, plain, (![A_85, B_87]: (r1_tarski(A_85, k2_xboole_0(A_85, B_87)))), inference(resolution, [status(thm)], [c_6, c_175])).
% 39.82/29.39  tff(c_1525, plain, (![A_162, C_163, B_164]: (r1_tarski(k2_xboole_0(A_162, C_163), B_164) | ~r1_tarski(C_163, B_164) | ~r1_tarski(A_162, B_164))), inference(cnfTransformation, [status(thm)], [f_59])).
% 39.82/29.39  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 39.82/29.39  tff(c_17495, plain, (![A_476, C_477, B_478]: (k2_xboole_0(A_476, C_477)=B_478 | ~r1_tarski(B_478, k2_xboole_0(A_476, C_477)) | ~r1_tarski(C_477, B_478) | ~r1_tarski(A_476, B_478))), inference(resolution, [status(thm)], [c_1525, c_2])).
% 39.82/29.39  tff(c_17695, plain, (![A_85, B_87]: (k2_xboole_0(A_85, B_87)=A_85 | ~r1_tarski(B_87, A_85) | ~r1_tarski(A_85, A_85))), inference(resolution, [status(thm)], [c_189, c_17495])).
% 39.82/29.39  tff(c_17782, plain, (![A_479, B_480]: (k2_xboole_0(A_479, B_480)=A_479 | ~r1_tarski(B_480, A_479))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_17695])).
% 39.82/29.39  tff(c_18012, plain, (![A_8, B_9]: (k2_xboole_0(A_8, k3_xboole_0(A_8, B_9))=A_8)), inference(resolution, [status(thm)], [c_12, c_17782])).
% 39.82/29.39  tff(c_3637, plain, (![A_223, B_224]: (r1_tarski(k1_relat_1(A_223), k1_relat_1(B_224)) | ~r1_tarski(A_223, B_224) | ~v1_relat_1(B_224) | ~v1_relat_1(A_223))), inference(cnfTransformation, [status(thm)], [f_101])).
% 39.82/29.39  tff(c_3657, plain, (![A_223, B_224]: (k3_xboole_0(k1_relat_1(A_223), k1_relat_1(B_224))=k1_relat_1(A_223) | ~r1_tarski(A_223, B_224) | ~v1_relat_1(B_224) | ~v1_relat_1(A_223))), inference(resolution, [status(thm)], [c_3637, c_16])).
% 39.82/29.39  tff(c_12638, plain, (![A_413, A_414]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_413, k1_relat_1(A_414)), k3_xboole_0(A_413, k2_relat_1(A_414))), k3_relat_1(A_414)) | ~v1_relat_1(A_414))), inference(superposition, [status(thm), theory('equality')], [c_44, c_2263])).
% 39.82/29.39  tff(c_12662, plain, (![A_223, B_224]: (r1_tarski(k2_xboole_0(k1_relat_1(A_223), k3_xboole_0(k1_relat_1(A_223), k2_relat_1(B_224))), k3_relat_1(B_224)) | ~v1_relat_1(B_224) | ~r1_tarski(A_223, B_224) | ~v1_relat_1(B_224) | ~v1_relat_1(A_223))), inference(superposition, [status(thm), theory('equality')], [c_3657, c_12638])).
% 39.82/29.39  tff(c_124618, plain, (![A_1364, B_1365]: (r1_tarski(k1_relat_1(A_1364), k3_relat_1(B_1365)) | ~v1_relat_1(B_1365) | ~r1_tarski(A_1364, B_1365) | ~v1_relat_1(B_1365) | ~v1_relat_1(A_1364))), inference(demodulation, [status(thm), theory('equality')], [c_18012, c_12662])).
% 39.82/29.39  tff(c_16661, plain, (![A_454, B_455]: (r1_tarski(k3_relat_1(A_454), B_455) | ~r1_tarski(k2_relat_1(A_454), B_455) | ~r1_tarski(k1_relat_1(A_454), B_455) | ~v1_relat_1(A_454))), inference(superposition, [status(thm), theory('equality')], [c_44, c_1525])).
% 39.82/29.39  tff(c_50, plain, (~r1_tarski(k3_relat_1('#skF_1'), k3_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_111])).
% 39.82/29.39  tff(c_16729, plain, (~r1_tarski(k2_relat_1('#skF_1'), k3_relat_1('#skF_2')) | ~r1_tarski(k1_relat_1('#skF_1'), k3_relat_1('#skF_2')) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_16661, c_50])).
% 39.82/29.39  tff(c_16751, plain, (~r1_tarski(k2_relat_1('#skF_1'), k3_relat_1('#skF_2')) | ~r1_tarski(k1_relat_1('#skF_1'), k3_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_16729])).
% 39.82/29.39  tff(c_16914, plain, (~r1_tarski(k1_relat_1('#skF_1'), k3_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_16751])).
% 39.82/29.39  tff(c_124656, plain, (~r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_124618, c_16914])).
% 39.82/29.39  tff(c_124692, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_124656])).
% 39.82/29.39  tff(c_124693, plain, (~r1_tarski(k2_relat_1('#skF_1'), k3_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_16751])).
% 39.82/29.39  tff(c_168370, plain, (~r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_168358, c_124693])).
% 39.82/29.39  tff(c_168393, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_168370])).
% 39.82/29.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 39.82/29.39  
% 39.82/29.39  Inference rules
% 39.82/29.39  ----------------------
% 39.82/29.39  #Ref     : 0
% 39.82/29.39  #Sup     : 43468
% 39.82/29.39  #Fact    : 0
% 39.82/29.39  #Define  : 0
% 39.82/29.39  #Split   : 16
% 39.82/29.39  #Chain   : 0
% 39.82/29.39  #Close   : 0
% 39.82/29.39  
% 39.82/29.39  Ordering : KBO
% 39.82/29.39  
% 39.82/29.39  Simplification rules
% 39.82/29.39  ----------------------
% 39.82/29.39  #Subsume      : 9858
% 39.82/29.39  #Demod        : 25493
% 39.82/29.39  #Tautology    : 17801
% 39.82/29.39  #SimpNegUnit  : 45
% 39.82/29.39  #BackRed      : 6
% 39.82/29.39  
% 39.82/29.39  #Partial instantiations: 0
% 39.82/29.39  #Strategies tried      : 1
% 39.82/29.39  
% 39.82/29.39  Timing (in seconds)
% 39.82/29.39  ----------------------
% 39.82/29.39  Preprocessing        : 0.35
% 39.82/29.39  Parsing              : 0.18
% 39.82/29.39  CNF conversion       : 0.02
% 39.82/29.39  Main loop            : 28.27
% 39.82/29.39  Inferencing          : 2.60
% 39.82/29.39  Reduction            : 15.44
% 39.82/29.39  Demodulation         : 13.95
% 39.82/29.39  BG Simplification    : 0.32
% 39.82/29.39  Subsumption          : 8.80
% 39.82/29.39  Abstraction          : 0.51
% 39.82/29.40  MUC search           : 0.00
% 39.82/29.40  Cooper               : 0.00
% 39.82/29.40  Total                : 28.65
% 39.82/29.40  Index Insertion      : 0.00
% 39.82/29.40  Index Deletion       : 0.00
% 39.82/29.40  Index Matching       : 0.00
% 39.82/29.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
