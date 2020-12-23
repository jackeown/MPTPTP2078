%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:32 EST 2020

% Result     : Theorem 8.35s
% Output     : CNFRefutation 8.35s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 180 expanded)
%              Number of leaves         :   47 (  82 expanded)
%              Depth                    :   12
%              Number of atoms          :  140 ( 294 expanded)
%              Number of equality atoms :   39 (  79 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k6_subset_1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_11 > #skF_1 > #skF_3 > #skF_10 > #skF_5 > #skF_8 > #skF_9 > #skF_2 > #skF_7 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_57,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_128,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_tarski(A,B)
             => r1_tarski(k3_relat_1(A),k3_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).

tff(f_35,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_100,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_82,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_84,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_118,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k6_subset_1(k2_relat_1(A),k2_relat_1(B)),k2_relat_1(k6_subset_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_relat_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_104,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_111,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k6_subset_1(k1_relat_1(A),k1_relat_1(B)),k1_relat_1(k6_subset_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_relat_1)).

tff(f_61,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_20,plain,(
    ! [A_15] : r1_tarski(k1_xboole_0,A_15) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_142,plain,(
    ! [A_96,B_97] :
      ( k4_xboole_0(A_96,B_97) = k1_xboole_0
      | ~ r1_tarski(A_96,B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_156,plain,(
    ! [A_15] : k4_xboole_0(k1_xboole_0,A_15) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_142])).

tff(c_80,plain,(
    v1_relat_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_78,plain,(
    v1_relat_1('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_4,plain,(
    ! [A_3] :
      ( r2_hidden('#skF_1'(A_3),A_3)
      | k1_xboole_0 = A_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2708,plain,(
    ! [A_207,C_208] :
      ( r2_hidden(k4_tarski('#skF_9'(A_207,k2_relat_1(A_207),C_208),C_208),A_207)
      | ~ r2_hidden(C_208,k2_relat_1(A_207)) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_36,plain,(
    ! [A_31] : k2_zfmisc_1(A_31,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_118,plain,(
    ! [A_90,B_91] : ~ r2_hidden(A_90,k2_zfmisc_1(A_90,B_91)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_124,plain,(
    ! [A_31] : ~ r2_hidden(A_31,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_118])).

tff(c_2722,plain,(
    ! [C_209] : ~ r2_hidden(C_209,k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_2708,c_124])).

tff(c_2737,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_2722])).

tff(c_76,plain,(
    r1_tarski('#skF_10','#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_157,plain,(
    k4_xboole_0('#skF_10','#skF_11') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_76,c_142])).

tff(c_42,plain,(
    ! [A_35,B_36] : k6_subset_1(A_35,B_36) = k4_xboole_0(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_72,plain,(
    ! [A_79,B_81] :
      ( r1_tarski(k6_subset_1(k2_relat_1(A_79),k2_relat_1(B_81)),k2_relat_1(k6_subset_1(A_79,B_81)))
      | ~ v1_relat_1(B_81)
      | ~ v1_relat_1(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_3812,plain,(
    ! [A_236,B_237] :
      ( r1_tarski(k4_xboole_0(k2_relat_1(A_236),k2_relat_1(B_237)),k2_relat_1(k4_xboole_0(A_236,B_237)))
      | ~ v1_relat_1(B_237)
      | ~ v1_relat_1(A_236) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_42,c_72])).

tff(c_3906,plain,
    ( r1_tarski(k4_xboole_0(k2_relat_1('#skF_10'),k2_relat_1('#skF_11')),k2_relat_1(k1_xboole_0))
    | ~ v1_relat_1('#skF_11')
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_3812])).

tff(c_3948,plain,(
    r1_tarski(k4_xboole_0(k2_relat_1('#skF_10'),k2_relat_1('#skF_11')),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_2737,c_3906])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | k4_xboole_0(A_7,B_8) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_366,plain,(
    ! [A_124,C_125,B_126] :
      ( r1_tarski(A_124,C_125)
      | ~ r1_tarski(B_126,C_125)
      | ~ r1_tarski(A_124,B_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_385,plain,(
    ! [A_127,A_128] :
      ( r1_tarski(A_127,A_128)
      | ~ r1_tarski(A_127,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_20,c_366])).

tff(c_416,plain,(
    ! [A_130,A_131] :
      ( r1_tarski(A_130,A_131)
      | k4_xboole_0(A_130,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_385])).

tff(c_6,plain,(
    ! [B_6,A_5] :
      ( B_6 = A_5
      | ~ r1_tarski(B_6,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_441,plain,(
    ! [A_131,A_130] :
      ( A_131 = A_130
      | ~ r1_tarski(A_131,A_130)
      | k4_xboole_0(A_130,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_416,c_6])).

tff(c_4039,plain,
    ( k4_xboole_0(k2_relat_1('#skF_10'),k2_relat_1('#skF_11')) = k1_xboole_0
    | k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3948,c_441])).

tff(c_4059,plain,(
    k4_xboole_0(k2_relat_1('#skF_10'),k2_relat_1('#skF_11')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_4039])).

tff(c_354,plain,(
    ! [A_123] :
      ( k2_xboole_0(k1_relat_1(A_123),k2_relat_1(A_123)) = k3_relat_1(A_123)
      | ~ v1_relat_1(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_16,plain,(
    ! [A_9,C_11,B_10] :
      ( r1_tarski(A_9,k2_xboole_0(C_11,B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_360,plain,(
    ! [A_9,A_123] :
      ( r1_tarski(A_9,k3_relat_1(A_123))
      | ~ r1_tarski(A_9,k2_relat_1(A_123))
      | ~ v1_relat_1(A_123) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_354,c_16])).

tff(c_68,plain,(
    ! [A_75] :
      ( k2_xboole_0(k1_relat_1(A_75),k2_relat_1(A_75)) = k3_relat_1(A_75)
      | ~ v1_relat_1(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2462,plain,(
    ! [C_198,A_199] :
      ( r2_hidden(k4_tarski(C_198,'#skF_5'(A_199,k1_relat_1(A_199),C_198)),A_199)
      | ~ r2_hidden(C_198,k1_relat_1(A_199)) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2476,plain,(
    ! [C_200] : ~ r2_hidden(C_200,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_2462,c_124])).

tff(c_2486,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_2476])).

tff(c_70,plain,(
    ! [A_76,B_78] :
      ( r1_tarski(k6_subset_1(k1_relat_1(A_76),k1_relat_1(B_78)),k1_relat_1(k6_subset_1(A_76,B_78)))
      | ~ v1_relat_1(B_78)
      | ~ v1_relat_1(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_4192,plain,(
    ! [A_241,B_242] :
      ( r1_tarski(k4_xboole_0(k1_relat_1(A_241),k1_relat_1(B_242)),k1_relat_1(k4_xboole_0(A_241,B_242)))
      | ~ v1_relat_1(B_242)
      | ~ v1_relat_1(A_241) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_42,c_70])).

tff(c_4292,plain,
    ( r1_tarski(k4_xboole_0(k1_relat_1('#skF_10'),k1_relat_1('#skF_11')),k1_relat_1(k1_xboole_0))
    | ~ v1_relat_1('#skF_11')
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_4192])).

tff(c_4337,plain,(
    r1_tarski(k4_xboole_0(k1_relat_1('#skF_10'),k1_relat_1('#skF_11')),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_2486,c_4292])).

tff(c_4341,plain,
    ( k4_xboole_0(k1_relat_1('#skF_10'),k1_relat_1('#skF_11')) = k1_xboole_0
    | k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4337,c_441])).

tff(c_4361,plain,(
    k4_xboole_0(k1_relat_1('#skF_10'),k1_relat_1('#skF_11')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_4341])).

tff(c_24,plain,(
    ! [A_18,B_19,C_20] : k4_xboole_0(k4_xboole_0(A_18,B_19),C_20) = k4_xboole_0(A_18,k2_xboole_0(B_19,C_20)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_4401,plain,(
    ! [C_20] : k4_xboole_0(k1_relat_1('#skF_10'),k2_xboole_0(k1_relat_1('#skF_11'),C_20)) = k4_xboole_0(k1_xboole_0,C_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_4361,c_24])).

tff(c_4693,plain,(
    ! [C_253] : k4_xboole_0(k1_relat_1('#skF_10'),k2_xboole_0(k1_relat_1('#skF_11'),C_253)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_4401])).

tff(c_4776,plain,
    ( k4_xboole_0(k1_relat_1('#skF_10'),k3_relat_1('#skF_11')) = k1_xboole_0
    | ~ v1_relat_1('#skF_11') ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_4693])).

tff(c_4805,plain,(
    k4_xboole_0(k1_relat_1('#skF_10'),k3_relat_1('#skF_11')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_4776])).

tff(c_1596,plain,(
    ! [A_172,C_173,B_174] :
      ( r1_tarski(k2_xboole_0(A_172,C_173),B_174)
      | ~ r1_tarski(C_173,B_174)
      | ~ r1_tarski(A_172,B_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_13233,plain,(
    ! [A_385,B_386] :
      ( r1_tarski(k3_relat_1(A_385),B_386)
      | ~ r1_tarski(k2_relat_1(A_385),B_386)
      | ~ r1_tarski(k1_relat_1(A_385),B_386)
      | ~ v1_relat_1(A_385) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_1596])).

tff(c_74,plain,(
    ~ r1_tarski(k3_relat_1('#skF_10'),k3_relat_1('#skF_11')) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_13315,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_10'),k3_relat_1('#skF_11'))
    | ~ r1_tarski(k1_relat_1('#skF_10'),k3_relat_1('#skF_11'))
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_13233,c_74])).

tff(c_13345,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_10'),k3_relat_1('#skF_11'))
    | ~ r1_tarski(k1_relat_1('#skF_10'),k3_relat_1('#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_13315])).

tff(c_16176,plain,(
    ~ r1_tarski(k1_relat_1('#skF_10'),k3_relat_1('#skF_11')) ),
    inference(splitLeft,[status(thm)],[c_13345])).

tff(c_16185,plain,(
    k4_xboole_0(k1_relat_1('#skF_10'),k3_relat_1('#skF_11')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_16176])).

tff(c_16193,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4805,c_16185])).

tff(c_16194,plain,(
    ~ r1_tarski(k2_relat_1('#skF_10'),k3_relat_1('#skF_11')) ),
    inference(splitRight,[status(thm)],[c_13345])).

tff(c_16201,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_10'),k2_relat_1('#skF_11'))
    | ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_360,c_16194])).

tff(c_16208,plain,(
    ~ r1_tarski(k2_relat_1('#skF_10'),k2_relat_1('#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_16201])).

tff(c_16248,plain,(
    k4_xboole_0(k2_relat_1('#skF_10'),k2_relat_1('#skF_11')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_16208])).

tff(c_16253,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4059,c_16248])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:59:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.35/2.86  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.35/2.86  
% 8.35/2.86  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.35/2.87  %$ r2_hidden > r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k6_subset_1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_11 > #skF_1 > #skF_3 > #skF_10 > #skF_5 > #skF_8 > #skF_9 > #skF_2 > #skF_7 > #skF_4
% 8.35/2.87  
% 8.35/2.87  %Foreground sorts:
% 8.35/2.87  
% 8.35/2.87  
% 8.35/2.87  %Background operators:
% 8.35/2.87  
% 8.35/2.87  
% 8.35/2.87  %Foreground operators:
% 8.35/2.87  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 8.35/2.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.35/2.87  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.35/2.87  tff('#skF_11', type, '#skF_11': $i).
% 8.35/2.87  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.35/2.87  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 8.35/2.87  tff('#skF_1', type, '#skF_1': $i > $i).
% 8.35/2.87  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.35/2.87  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 8.35/2.87  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 8.35/2.87  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.35/2.87  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.35/2.87  tff('#skF_10', type, '#skF_10': $i).
% 8.35/2.87  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.35/2.87  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.35/2.87  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 8.35/2.87  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.35/2.87  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 8.35/2.87  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 8.35/2.87  tff('#skF_9', type, '#skF_9': ($i * $i * $i) > $i).
% 8.35/2.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.35/2.87  tff(k3_tarski, type, k3_tarski: $i > $i).
% 8.35/2.87  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.35/2.87  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.35/2.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.35/2.87  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.35/2.87  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.35/2.87  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 8.35/2.87  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.35/2.87  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 8.35/2.87  
% 8.35/2.88  tff(f_57, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 8.35/2.88  tff(f_45, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 8.35/2.88  tff(f_128, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => r1_tarski(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_relat_1)).
% 8.35/2.88  tff(f_35, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 8.35/2.88  tff(f_100, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 8.35/2.88  tff(f_79, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 8.35/2.88  tff(f_82, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 8.35/2.88  tff(f_84, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 8.35/2.88  tff(f_118, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k6_subset_1(k2_relat_1(A), k2_relat_1(B)), k2_relat_1(k6_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_relat_1)).
% 8.35/2.88  tff(f_55, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 8.35/2.88  tff(f_41, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.35/2.88  tff(f_104, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 8.35/2.88  tff(f_49, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 8.35/2.88  tff(f_92, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 8.35/2.88  tff(f_111, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k6_subset_1(k1_relat_1(A), k1_relat_1(B)), k1_relat_1(k6_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_relat_1)).
% 8.35/2.88  tff(f_61, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 8.35/2.88  tff(f_67, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 8.35/2.88  tff(c_20, plain, (![A_15]: (r1_tarski(k1_xboole_0, A_15))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.35/2.88  tff(c_142, plain, (![A_96, B_97]: (k4_xboole_0(A_96, B_97)=k1_xboole_0 | ~r1_tarski(A_96, B_97))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.35/2.88  tff(c_156, plain, (![A_15]: (k4_xboole_0(k1_xboole_0, A_15)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_142])).
% 8.35/2.88  tff(c_80, plain, (v1_relat_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_128])).
% 8.35/2.88  tff(c_78, plain, (v1_relat_1('#skF_11')), inference(cnfTransformation, [status(thm)], [f_128])).
% 8.35/2.88  tff(c_4, plain, (![A_3]: (r2_hidden('#skF_1'(A_3), A_3) | k1_xboole_0=A_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.35/2.88  tff(c_2708, plain, (![A_207, C_208]: (r2_hidden(k4_tarski('#skF_9'(A_207, k2_relat_1(A_207), C_208), C_208), A_207) | ~r2_hidden(C_208, k2_relat_1(A_207)))), inference(cnfTransformation, [status(thm)], [f_100])).
% 8.35/2.88  tff(c_36, plain, (![A_31]: (k2_zfmisc_1(A_31, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_79])).
% 8.35/2.88  tff(c_118, plain, (![A_90, B_91]: (~r2_hidden(A_90, k2_zfmisc_1(A_90, B_91)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 8.35/2.88  tff(c_124, plain, (![A_31]: (~r2_hidden(A_31, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_36, c_118])).
% 8.35/2.88  tff(c_2722, plain, (![C_209]: (~r2_hidden(C_209, k2_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_2708, c_124])).
% 8.35/2.88  tff(c_2737, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_4, c_2722])).
% 8.35/2.88  tff(c_76, plain, (r1_tarski('#skF_10', '#skF_11')), inference(cnfTransformation, [status(thm)], [f_128])).
% 8.35/2.88  tff(c_157, plain, (k4_xboole_0('#skF_10', '#skF_11')=k1_xboole_0), inference(resolution, [status(thm)], [c_76, c_142])).
% 8.35/2.88  tff(c_42, plain, (![A_35, B_36]: (k6_subset_1(A_35, B_36)=k4_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_84])).
% 8.35/2.88  tff(c_72, plain, (![A_79, B_81]: (r1_tarski(k6_subset_1(k2_relat_1(A_79), k2_relat_1(B_81)), k2_relat_1(k6_subset_1(A_79, B_81))) | ~v1_relat_1(B_81) | ~v1_relat_1(A_79))), inference(cnfTransformation, [status(thm)], [f_118])).
% 8.35/2.88  tff(c_3812, plain, (![A_236, B_237]: (r1_tarski(k4_xboole_0(k2_relat_1(A_236), k2_relat_1(B_237)), k2_relat_1(k4_xboole_0(A_236, B_237))) | ~v1_relat_1(B_237) | ~v1_relat_1(A_236))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_42, c_72])).
% 8.35/2.88  tff(c_3906, plain, (r1_tarski(k4_xboole_0(k2_relat_1('#skF_10'), k2_relat_1('#skF_11')), k2_relat_1(k1_xboole_0)) | ~v1_relat_1('#skF_11') | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_157, c_3812])).
% 8.35/2.88  tff(c_3948, plain, (r1_tarski(k4_xboole_0(k2_relat_1('#skF_10'), k2_relat_1('#skF_11')), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_2737, c_3906])).
% 8.35/2.88  tff(c_12, plain, (![A_7, B_8]: (r1_tarski(A_7, B_8) | k4_xboole_0(A_7, B_8)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.35/2.88  tff(c_366, plain, (![A_124, C_125, B_126]: (r1_tarski(A_124, C_125) | ~r1_tarski(B_126, C_125) | ~r1_tarski(A_124, B_126))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.35/2.88  tff(c_385, plain, (![A_127, A_128]: (r1_tarski(A_127, A_128) | ~r1_tarski(A_127, k1_xboole_0))), inference(resolution, [status(thm)], [c_20, c_366])).
% 8.35/2.88  tff(c_416, plain, (![A_130, A_131]: (r1_tarski(A_130, A_131) | k4_xboole_0(A_130, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_385])).
% 8.35/2.88  tff(c_6, plain, (![B_6, A_5]: (B_6=A_5 | ~r1_tarski(B_6, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.35/2.88  tff(c_441, plain, (![A_131, A_130]: (A_131=A_130 | ~r1_tarski(A_131, A_130) | k4_xboole_0(A_130, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_416, c_6])).
% 8.35/2.88  tff(c_4039, plain, (k4_xboole_0(k2_relat_1('#skF_10'), k2_relat_1('#skF_11'))=k1_xboole_0 | k4_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_3948, c_441])).
% 8.35/2.88  tff(c_4059, plain, (k4_xboole_0(k2_relat_1('#skF_10'), k2_relat_1('#skF_11'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_156, c_4039])).
% 8.35/2.88  tff(c_354, plain, (![A_123]: (k2_xboole_0(k1_relat_1(A_123), k2_relat_1(A_123))=k3_relat_1(A_123) | ~v1_relat_1(A_123))), inference(cnfTransformation, [status(thm)], [f_104])).
% 8.35/2.88  tff(c_16, plain, (![A_9, C_11, B_10]: (r1_tarski(A_9, k2_xboole_0(C_11, B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.35/2.88  tff(c_360, plain, (![A_9, A_123]: (r1_tarski(A_9, k3_relat_1(A_123)) | ~r1_tarski(A_9, k2_relat_1(A_123)) | ~v1_relat_1(A_123))), inference(superposition, [status(thm), theory('equality')], [c_354, c_16])).
% 8.35/2.88  tff(c_68, plain, (![A_75]: (k2_xboole_0(k1_relat_1(A_75), k2_relat_1(A_75))=k3_relat_1(A_75) | ~v1_relat_1(A_75))), inference(cnfTransformation, [status(thm)], [f_104])).
% 8.35/2.88  tff(c_2462, plain, (![C_198, A_199]: (r2_hidden(k4_tarski(C_198, '#skF_5'(A_199, k1_relat_1(A_199), C_198)), A_199) | ~r2_hidden(C_198, k1_relat_1(A_199)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 8.35/2.88  tff(c_2476, plain, (![C_200]: (~r2_hidden(C_200, k1_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_2462, c_124])).
% 8.35/2.88  tff(c_2486, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_4, c_2476])).
% 8.35/2.88  tff(c_70, plain, (![A_76, B_78]: (r1_tarski(k6_subset_1(k1_relat_1(A_76), k1_relat_1(B_78)), k1_relat_1(k6_subset_1(A_76, B_78))) | ~v1_relat_1(B_78) | ~v1_relat_1(A_76))), inference(cnfTransformation, [status(thm)], [f_111])).
% 8.35/2.88  tff(c_4192, plain, (![A_241, B_242]: (r1_tarski(k4_xboole_0(k1_relat_1(A_241), k1_relat_1(B_242)), k1_relat_1(k4_xboole_0(A_241, B_242))) | ~v1_relat_1(B_242) | ~v1_relat_1(A_241))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_42, c_70])).
% 8.35/2.88  tff(c_4292, plain, (r1_tarski(k4_xboole_0(k1_relat_1('#skF_10'), k1_relat_1('#skF_11')), k1_relat_1(k1_xboole_0)) | ~v1_relat_1('#skF_11') | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_157, c_4192])).
% 8.35/2.88  tff(c_4337, plain, (r1_tarski(k4_xboole_0(k1_relat_1('#skF_10'), k1_relat_1('#skF_11')), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_2486, c_4292])).
% 8.35/2.88  tff(c_4341, plain, (k4_xboole_0(k1_relat_1('#skF_10'), k1_relat_1('#skF_11'))=k1_xboole_0 | k4_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_4337, c_441])).
% 8.35/2.88  tff(c_4361, plain, (k4_xboole_0(k1_relat_1('#skF_10'), k1_relat_1('#skF_11'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_156, c_4341])).
% 8.35/2.88  tff(c_24, plain, (![A_18, B_19, C_20]: (k4_xboole_0(k4_xboole_0(A_18, B_19), C_20)=k4_xboole_0(A_18, k2_xboole_0(B_19, C_20)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.35/2.88  tff(c_4401, plain, (![C_20]: (k4_xboole_0(k1_relat_1('#skF_10'), k2_xboole_0(k1_relat_1('#skF_11'), C_20))=k4_xboole_0(k1_xboole_0, C_20))), inference(superposition, [status(thm), theory('equality')], [c_4361, c_24])).
% 8.35/2.88  tff(c_4693, plain, (![C_253]: (k4_xboole_0(k1_relat_1('#skF_10'), k2_xboole_0(k1_relat_1('#skF_11'), C_253))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_156, c_4401])).
% 8.35/2.88  tff(c_4776, plain, (k4_xboole_0(k1_relat_1('#skF_10'), k3_relat_1('#skF_11'))=k1_xboole_0 | ~v1_relat_1('#skF_11')), inference(superposition, [status(thm), theory('equality')], [c_68, c_4693])).
% 8.35/2.88  tff(c_4805, plain, (k4_xboole_0(k1_relat_1('#skF_10'), k3_relat_1('#skF_11'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_78, c_4776])).
% 8.35/2.88  tff(c_1596, plain, (![A_172, C_173, B_174]: (r1_tarski(k2_xboole_0(A_172, C_173), B_174) | ~r1_tarski(C_173, B_174) | ~r1_tarski(A_172, B_174))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.35/2.88  tff(c_13233, plain, (![A_385, B_386]: (r1_tarski(k3_relat_1(A_385), B_386) | ~r1_tarski(k2_relat_1(A_385), B_386) | ~r1_tarski(k1_relat_1(A_385), B_386) | ~v1_relat_1(A_385))), inference(superposition, [status(thm), theory('equality')], [c_68, c_1596])).
% 8.35/2.88  tff(c_74, plain, (~r1_tarski(k3_relat_1('#skF_10'), k3_relat_1('#skF_11'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 8.35/2.88  tff(c_13315, plain, (~r1_tarski(k2_relat_1('#skF_10'), k3_relat_1('#skF_11')) | ~r1_tarski(k1_relat_1('#skF_10'), k3_relat_1('#skF_11')) | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_13233, c_74])).
% 8.35/2.88  tff(c_13345, plain, (~r1_tarski(k2_relat_1('#skF_10'), k3_relat_1('#skF_11')) | ~r1_tarski(k1_relat_1('#skF_10'), k3_relat_1('#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_13315])).
% 8.35/2.88  tff(c_16176, plain, (~r1_tarski(k1_relat_1('#skF_10'), k3_relat_1('#skF_11'))), inference(splitLeft, [status(thm)], [c_13345])).
% 8.35/2.88  tff(c_16185, plain, (k4_xboole_0(k1_relat_1('#skF_10'), k3_relat_1('#skF_11'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_12, c_16176])).
% 8.35/2.88  tff(c_16193, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4805, c_16185])).
% 8.35/2.88  tff(c_16194, plain, (~r1_tarski(k2_relat_1('#skF_10'), k3_relat_1('#skF_11'))), inference(splitRight, [status(thm)], [c_13345])).
% 8.35/2.88  tff(c_16201, plain, (~r1_tarski(k2_relat_1('#skF_10'), k2_relat_1('#skF_11')) | ~v1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_360, c_16194])).
% 8.35/2.88  tff(c_16208, plain, (~r1_tarski(k2_relat_1('#skF_10'), k2_relat_1('#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_16201])).
% 8.35/2.88  tff(c_16248, plain, (k4_xboole_0(k2_relat_1('#skF_10'), k2_relat_1('#skF_11'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_12, c_16208])).
% 8.35/2.88  tff(c_16253, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4059, c_16248])).
% 8.35/2.88  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.35/2.88  
% 8.35/2.88  Inference rules
% 8.35/2.88  ----------------------
% 8.35/2.88  #Ref     : 1
% 8.35/2.88  #Sup     : 3965
% 8.35/2.88  #Fact    : 0
% 8.35/2.88  #Define  : 0
% 8.35/2.88  #Split   : 4
% 8.35/2.88  #Chain   : 0
% 8.35/2.88  #Close   : 0
% 8.35/2.88  
% 8.35/2.88  Ordering : KBO
% 8.35/2.88  
% 8.35/2.88  Simplification rules
% 8.35/2.88  ----------------------
% 8.35/2.88  #Subsume      : 776
% 8.35/2.88  #Demod        : 2341
% 8.35/2.88  #Tautology    : 2154
% 8.35/2.88  #SimpNegUnit  : 10
% 8.35/2.88  #BackRed      : 19
% 8.35/2.88  
% 8.35/2.88  #Partial instantiations: 0
% 8.35/2.88  #Strategies tried      : 1
% 8.35/2.88  
% 8.35/2.88  Timing (in seconds)
% 8.35/2.88  ----------------------
% 8.35/2.89  Preprocessing        : 0.33
% 8.35/2.89  Parsing              : 0.17
% 8.35/2.89  CNF conversion       : 0.03
% 8.35/2.89  Main loop            : 1.77
% 8.35/2.89  Inferencing          : 0.45
% 8.35/2.89  Reduction            : 0.73
% 8.35/2.89  Demodulation         : 0.57
% 8.35/2.89  BG Simplification    : 0.05
% 8.35/2.89  Subsumption          : 0.42
% 8.35/2.89  Abstraction          : 0.07
% 8.35/2.89  MUC search           : 0.00
% 8.35/2.89  Cooper               : 0.00
% 8.35/2.89  Total                : 2.14
% 8.35/2.89  Index Insertion      : 0.00
% 8.63/2.89  Index Deletion       : 0.00
% 8.63/2.89  Index Matching       : 0.00
% 8.63/2.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
