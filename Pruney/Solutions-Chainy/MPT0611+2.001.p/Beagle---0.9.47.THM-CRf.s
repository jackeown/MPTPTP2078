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
% DateTime   : Thu Dec  3 10:02:39 EST 2020

% Result     : Theorem 6.21s
% Output     : CNFRefutation 6.21s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 102 expanded)
%              Number of leaves         :   41 (  58 expanded)
%              Depth                    :    9
%              Number of atoms          :   50 ( 145 expanded)
%              Number of equality atoms :   13 (  26 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k6_subset_1 > k5_relat_1 > k4_tarski > k3_xboole_0 > k10_relat_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_10 > #skF_13 > #skF_2 > #skF_8 > #skF_9 > #skF_5 > #skF_11 > #skF_3 > #skF_7 > #skF_1 > #skF_6 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_10',type,(
    '#skF_10': $i > $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_11',type,(
    '#skF_11': $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_205,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_xboole_0(k2_relat_1(A),k2_relat_1(B))
             => r1_xboole_0(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t215_relat_1)).

tff(f_107,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

tff(f_171,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k2_relat_1(A),k2_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_relat_1)).

tff(f_121,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_129,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k8_relat_1(k1_xboole_0,A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_relat_1)).

tff(c_290,plain,(
    ! [A_139,B_140] :
      ( r1_xboole_0(A_139,B_140)
      | k3_xboole_0(A_139,B_140) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_98,plain,(
    ~ r1_xboole_0('#skF_12','#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_303,plain,(
    k3_xboole_0('#skF_12','#skF_13') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_290,c_98])).

tff(c_104,plain,(
    v1_relat_1('#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_50,plain,(
    ! [A_79,B_80] :
      ( v1_relat_1(k3_xboole_0(A_79,B_80))
      | ~ v1_relat_1(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_102,plain,(
    v1_relat_1('#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_100,plain,(
    r1_xboole_0(k2_relat_1('#skF_12'),k2_relat_1('#skF_13')) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_240,plain,(
    ! [A_133,B_134] :
      ( k3_xboole_0(A_133,B_134) = k1_xboole_0
      | ~ r1_xboole_0(A_133,B_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_247,plain,(
    k3_xboole_0(k2_relat_1('#skF_12'),k2_relat_1('#skF_13')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_100,c_240])).

tff(c_4626,plain,(
    ! [A_378,B_379] :
      ( r1_tarski(k2_relat_1(k3_xboole_0(A_378,B_379)),k3_xboole_0(k2_relat_1(A_378),k2_relat_1(B_379)))
      | ~ v1_relat_1(B_379)
      | ~ v1_relat_1(A_378) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_4680,plain,
    ( r1_tarski(k2_relat_1(k3_xboole_0('#skF_12','#skF_13')),k1_xboole_0)
    | ~ v1_relat_1('#skF_13')
    | ~ v1_relat_1('#skF_12') ),
    inference(superposition,[status(thm),theory(equality)],[c_247,c_4626])).

tff(c_4708,plain,(
    r1_tarski(k2_relat_1(k3_xboole_0('#skF_12','#skF_13')),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_102,c_4680])).

tff(c_56,plain,(
    ! [A_85,B_86] :
      ( k8_relat_1(A_85,B_86) = B_86
      | ~ r1_tarski(k2_relat_1(B_86),A_85)
      | ~ v1_relat_1(B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_4723,plain,
    ( k8_relat_1(k1_xboole_0,k3_xboole_0('#skF_12','#skF_13')) = k3_xboole_0('#skF_12','#skF_13')
    | ~ v1_relat_1(k3_xboole_0('#skF_12','#skF_13')) ),
    inference(resolution,[status(thm)],[c_4708,c_56])).

tff(c_4883,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_12','#skF_13')) ),
    inference(splitLeft,[status(thm)],[c_4723])).

tff(c_4886,plain,(
    ~ v1_relat_1('#skF_12') ),
    inference(resolution,[status(thm)],[c_50,c_4883])).

tff(c_4890,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_4886])).

tff(c_4892,plain,(
    v1_relat_1(k3_xboole_0('#skF_12','#skF_13')) ),
    inference(splitRight,[status(thm)],[c_4723])).

tff(c_60,plain,(
    ! [A_90] :
      ( k8_relat_1(k1_xboole_0,A_90) = k1_xboole_0
      | ~ v1_relat_1(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_4922,plain,(
    k8_relat_1(k1_xboole_0,k3_xboole_0('#skF_12','#skF_13')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4892,c_60])).

tff(c_4891,plain,(
    k8_relat_1(k1_xboole_0,k3_xboole_0('#skF_12','#skF_13')) = k3_xboole_0('#skF_12','#skF_13') ),
    inference(splitRight,[status(thm)],[c_4723])).

tff(c_5834,plain,(
    k3_xboole_0('#skF_12','#skF_13') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4922,c_4891])).

tff(c_5835,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_303,c_5834])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:06:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.21/2.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.21/2.21  
% 6.21/2.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.21/2.21  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k6_subset_1 > k5_relat_1 > k4_tarski > k3_xboole_0 > k10_relat_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_10 > #skF_13 > #skF_2 > #skF_8 > #skF_9 > #skF_5 > #skF_11 > #skF_3 > #skF_7 > #skF_1 > #skF_6 > #skF_12
% 6.21/2.21  
% 6.21/2.21  %Foreground sorts:
% 6.21/2.21  
% 6.21/2.21  
% 6.21/2.21  %Background operators:
% 6.21/2.21  
% 6.21/2.21  
% 6.21/2.21  %Foreground operators:
% 6.21/2.21  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 6.21/2.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.21/2.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.21/2.21  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.21/2.21  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 6.21/2.21  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 6.21/2.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.21/2.21  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 6.21/2.21  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 6.21/2.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.21/2.21  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.21/2.21  tff('#skF_10', type, '#skF_10': $i > $i).
% 6.21/2.21  tff('#skF_13', type, '#skF_13': $i).
% 6.21/2.21  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.21/2.21  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 6.21/2.21  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 6.21/2.21  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.21/2.21  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 6.21/2.21  tff('#skF_9', type, '#skF_9': ($i * $i * $i) > $i).
% 6.21/2.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.21/2.21  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 6.21/2.21  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 6.21/2.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.21/2.21  tff('#skF_11', type, '#skF_11': $i > $i).
% 6.21/2.21  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 6.21/2.21  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.21/2.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.21/2.21  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.21/2.21  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 6.21/2.21  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.21/2.21  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.21/2.21  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.21/2.21  tff('#skF_6', type, '#skF_6': $i > $i).
% 6.21/2.21  tff('#skF_12', type, '#skF_12': $i).
% 6.21/2.21  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 6.21/2.21  
% 6.21/2.22  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 6.21/2.22  tff(f_205, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_xboole_0(k2_relat_1(A), k2_relat_1(B)) => r1_xboole_0(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t215_relat_1)).
% 6.21/2.22  tff(f_107, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_relat_1)).
% 6.21/2.22  tff(f_171, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k2_relat_1(A), k2_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_relat_1)).
% 6.21/2.22  tff(f_121, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_relat_1)).
% 6.21/2.22  tff(f_129, axiom, (![A]: (v1_relat_1(A) => (k8_relat_1(k1_xboole_0, A) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_relat_1)).
% 6.21/2.22  tff(c_290, plain, (![A_139, B_140]: (r1_xboole_0(A_139, B_140) | k3_xboole_0(A_139, B_140)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.21/2.22  tff(c_98, plain, (~r1_xboole_0('#skF_12', '#skF_13')), inference(cnfTransformation, [status(thm)], [f_205])).
% 6.21/2.22  tff(c_303, plain, (k3_xboole_0('#skF_12', '#skF_13')!=k1_xboole_0), inference(resolution, [status(thm)], [c_290, c_98])).
% 6.21/2.22  tff(c_104, plain, (v1_relat_1('#skF_12')), inference(cnfTransformation, [status(thm)], [f_205])).
% 6.21/2.22  tff(c_50, plain, (![A_79, B_80]: (v1_relat_1(k3_xboole_0(A_79, B_80)) | ~v1_relat_1(A_79))), inference(cnfTransformation, [status(thm)], [f_107])).
% 6.21/2.22  tff(c_102, plain, (v1_relat_1('#skF_13')), inference(cnfTransformation, [status(thm)], [f_205])).
% 6.21/2.22  tff(c_100, plain, (r1_xboole_0(k2_relat_1('#skF_12'), k2_relat_1('#skF_13'))), inference(cnfTransformation, [status(thm)], [f_205])).
% 6.21/2.22  tff(c_240, plain, (![A_133, B_134]: (k3_xboole_0(A_133, B_134)=k1_xboole_0 | ~r1_xboole_0(A_133, B_134))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.21/2.22  tff(c_247, plain, (k3_xboole_0(k2_relat_1('#skF_12'), k2_relat_1('#skF_13'))=k1_xboole_0), inference(resolution, [status(thm)], [c_100, c_240])).
% 6.21/2.22  tff(c_4626, plain, (![A_378, B_379]: (r1_tarski(k2_relat_1(k3_xboole_0(A_378, B_379)), k3_xboole_0(k2_relat_1(A_378), k2_relat_1(B_379))) | ~v1_relat_1(B_379) | ~v1_relat_1(A_378))), inference(cnfTransformation, [status(thm)], [f_171])).
% 6.21/2.22  tff(c_4680, plain, (r1_tarski(k2_relat_1(k3_xboole_0('#skF_12', '#skF_13')), k1_xboole_0) | ~v1_relat_1('#skF_13') | ~v1_relat_1('#skF_12')), inference(superposition, [status(thm), theory('equality')], [c_247, c_4626])).
% 6.21/2.22  tff(c_4708, plain, (r1_tarski(k2_relat_1(k3_xboole_0('#skF_12', '#skF_13')), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_104, c_102, c_4680])).
% 6.21/2.22  tff(c_56, plain, (![A_85, B_86]: (k8_relat_1(A_85, B_86)=B_86 | ~r1_tarski(k2_relat_1(B_86), A_85) | ~v1_relat_1(B_86))), inference(cnfTransformation, [status(thm)], [f_121])).
% 6.21/2.22  tff(c_4723, plain, (k8_relat_1(k1_xboole_0, k3_xboole_0('#skF_12', '#skF_13'))=k3_xboole_0('#skF_12', '#skF_13') | ~v1_relat_1(k3_xboole_0('#skF_12', '#skF_13'))), inference(resolution, [status(thm)], [c_4708, c_56])).
% 6.21/2.22  tff(c_4883, plain, (~v1_relat_1(k3_xboole_0('#skF_12', '#skF_13'))), inference(splitLeft, [status(thm)], [c_4723])).
% 6.21/2.22  tff(c_4886, plain, (~v1_relat_1('#skF_12')), inference(resolution, [status(thm)], [c_50, c_4883])).
% 6.21/2.22  tff(c_4890, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_104, c_4886])).
% 6.21/2.22  tff(c_4892, plain, (v1_relat_1(k3_xboole_0('#skF_12', '#skF_13'))), inference(splitRight, [status(thm)], [c_4723])).
% 6.21/2.22  tff(c_60, plain, (![A_90]: (k8_relat_1(k1_xboole_0, A_90)=k1_xboole_0 | ~v1_relat_1(A_90))), inference(cnfTransformation, [status(thm)], [f_129])).
% 6.21/2.22  tff(c_4922, plain, (k8_relat_1(k1_xboole_0, k3_xboole_0('#skF_12', '#skF_13'))=k1_xboole_0), inference(resolution, [status(thm)], [c_4892, c_60])).
% 6.21/2.22  tff(c_4891, plain, (k8_relat_1(k1_xboole_0, k3_xboole_0('#skF_12', '#skF_13'))=k3_xboole_0('#skF_12', '#skF_13')), inference(splitRight, [status(thm)], [c_4723])).
% 6.21/2.22  tff(c_5834, plain, (k3_xboole_0('#skF_12', '#skF_13')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4922, c_4891])).
% 6.21/2.22  tff(c_5835, plain, $false, inference(negUnitSimplification, [status(thm)], [c_303, c_5834])).
% 6.21/2.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.21/2.22  
% 6.21/2.22  Inference rules
% 6.21/2.22  ----------------------
% 6.21/2.22  #Ref     : 1
% 6.21/2.22  #Sup     : 1309
% 6.21/2.22  #Fact    : 0
% 6.21/2.22  #Define  : 0
% 6.21/2.22  #Split   : 14
% 6.21/2.22  #Chain   : 0
% 6.21/2.22  #Close   : 0
% 6.21/2.22  
% 6.21/2.22  Ordering : KBO
% 6.21/2.22  
% 6.21/2.22  Simplification rules
% 6.21/2.22  ----------------------
% 6.21/2.22  #Subsume      : 103
% 6.21/2.22  #Demod        : 1111
% 6.21/2.22  #Tautology    : 796
% 6.21/2.22  #SimpNegUnit  : 26
% 6.21/2.22  #BackRed      : 4
% 6.21/2.22  
% 6.21/2.22  #Partial instantiations: 0
% 6.21/2.22  #Strategies tried      : 1
% 6.21/2.22  
% 6.58/2.22  Timing (in seconds)
% 6.58/2.22  ----------------------
% 6.58/2.23  Preprocessing        : 0.37
% 6.58/2.23  Parsing              : 0.20
% 6.58/2.23  CNF conversion       : 0.04
% 6.58/2.23  Main loop            : 1.05
% 6.58/2.23  Inferencing          : 0.35
% 6.58/2.23  Reduction            : 0.36
% 6.58/2.23  Demodulation         : 0.25
% 6.58/2.23  BG Simplification    : 0.04
% 6.58/2.23  Subsumption          : 0.20
% 6.58/2.23  Abstraction          : 0.04
% 6.58/2.23  MUC search           : 0.00
% 6.58/2.23  Cooper               : 0.00
% 6.58/2.23  Total                : 1.45
% 6.58/2.23  Index Insertion      : 0.00
% 6.58/2.23  Index Deletion       : 0.00
% 6.58/2.23  Index Matching       : 0.00
% 6.58/2.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
