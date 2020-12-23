%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:40 EST 2020

% Result     : Theorem 2.52s
% Output     : CNFRefutation 2.81s
% Verified   : 
% Statistics : Number of formulae       :   72 (  92 expanded)
%              Number of leaves         :   37 (  47 expanded)
%              Depth                    :    8
%              Number of atoms          :   80 ( 125 expanded)
%              Number of equality atoms :   32 (  47 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_90,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k7_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_62,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_59,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_75,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_xboole_0(k2_relat_1(A),k1_relat_1(B))
           => k5_relat_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_relat_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_46,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_12,plain,(
    ! [A_7] : k5_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_34,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_54,plain,
    ( k7_relat_1('#skF_2','#skF_1') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_94,plain,(
    r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_48,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1')
    | k7_relat_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_121,plain,(
    k7_relat_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_48])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_97,plain,(
    r1_xboole_0('#skF_1',k1_relat_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_94,c_2])).

tff(c_30,plain,(
    ! [A_40] : v1_relat_1(k6_relat_1(A_40)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_40,plain,(
    ! [A_44] : k2_relat_1(k6_relat_1(A_44)) = A_44 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_206,plain,(
    ! [A_83,B_84] :
      ( k5_relat_1(A_83,B_84) = k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(A_83),k1_relat_1(B_84))
      | ~ v1_relat_1(B_84)
      | ~ v1_relat_1(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_212,plain,(
    ! [A_44,B_84] :
      ( k5_relat_1(k6_relat_1(A_44),B_84) = k1_xboole_0
      | ~ r1_xboole_0(A_44,k1_relat_1(B_84))
      | ~ v1_relat_1(B_84)
      | ~ v1_relat_1(k6_relat_1(A_44)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_206])).

tff(c_226,plain,(
    ! [A_85,B_86] :
      ( k5_relat_1(k6_relat_1(A_85),B_86) = k1_xboole_0
      | ~ r1_xboole_0(A_85,k1_relat_1(B_86))
      | ~ v1_relat_1(B_86) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_212])).

tff(c_236,plain,
    ( k5_relat_1(k6_relat_1('#skF_1'),'#skF_2') = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_97,c_226])).

tff(c_246,plain,(
    k5_relat_1(k6_relat_1('#skF_1'),'#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_236])).

tff(c_44,plain,(
    ! [A_47,B_48] :
      ( k5_relat_1(k6_relat_1(A_47),B_48) = k7_relat_1(B_48,A_47)
      | ~ v1_relat_1(B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_252,plain,
    ( k7_relat_1('#skF_2','#skF_1') = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_246,c_44])).

tff(c_259,plain,(
    k7_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_252])).

tff(c_261,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_121,c_259])).

tff(c_262,plain,(
    k7_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_338,plain,(
    ! [B_106,A_107] :
      ( k3_xboole_0(k1_relat_1(B_106),A_107) = k1_relat_1(k7_relat_1(B_106,A_107))
      | ~ v1_relat_1(B_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_10,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_649,plain,(
    ! [B_176,A_177] :
      ( k5_xboole_0(k1_relat_1(B_176),k1_relat_1(k7_relat_1(B_176,A_177))) = k4_xboole_0(k1_relat_1(B_176),A_177)
      | ~ v1_relat_1(B_176) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_338,c_10])).

tff(c_667,plain,
    ( k5_xboole_0(k1_relat_1('#skF_2'),k1_relat_1(k1_xboole_0)) = k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_262,c_649])).

tff(c_682,plain,(
    k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1') = k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_12,c_34,c_667])).

tff(c_296,plain,(
    ! [A_91,C_92,B_93] :
      ( r1_xboole_0(A_91,k4_xboole_0(C_92,B_93))
      | ~ r1_tarski(A_91,B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_299,plain,(
    ! [C_92,B_93,A_91] :
      ( r1_xboole_0(k4_xboole_0(C_92,B_93),A_91)
      | ~ r1_tarski(A_91,B_93) ) ),
    inference(resolution,[status(thm)],[c_296,c_2])).

tff(c_715,plain,(
    ! [A_178] :
      ( r1_xboole_0(k1_relat_1('#skF_2'),A_178)
      | ~ r1_tarski(A_178,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_682,c_299])).

tff(c_264,plain,(
    k7_relat_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_270,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_262,c_264])).

tff(c_271,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_725,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_715,c_271])).

tff(c_733,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_725])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:08:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.52/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.52/1.36  
% 2.52/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.52/1.36  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.52/1.36  
% 2.52/1.36  %Foreground sorts:
% 2.52/1.36  
% 2.52/1.36  
% 2.52/1.36  %Background operators:
% 2.52/1.36  
% 2.52/1.36  
% 2.52/1.36  %Foreground operators:
% 2.52/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.52/1.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.52/1.36  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.52/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.52/1.36  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.52/1.36  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.52/1.36  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.52/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.52/1.36  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.52/1.36  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.52/1.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.52/1.36  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.52/1.36  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.52/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.52/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.52/1.36  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.52/1.36  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.52/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.52/1.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.52/1.36  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.52/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.52/1.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.52/1.36  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.52/1.36  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.52/1.36  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.52/1.36  
% 2.81/1.38  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.81/1.38  tff(f_90, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 2.81/1.38  tff(f_39, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.81/1.38  tff(f_62, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.81/1.38  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.81/1.38  tff(f_59, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.81/1.38  tff(f_75, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.81/1.38  tff(f_71, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_xboole_0(k2_relat_1(A), k1_relat_1(B)) => (k5_relat_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_relat_1)).
% 2.81/1.38  tff(f_83, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 2.81/1.38  tff(f_79, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 2.81/1.38  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.81/1.38  tff(f_43, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 2.81/1.38  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.81/1.38  tff(c_46, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.81/1.38  tff(c_12, plain, (![A_7]: (k5_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.81/1.38  tff(c_34, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.81/1.38  tff(c_54, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0 | r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.81/1.38  tff(c_94, plain, (r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_54])).
% 2.81/1.38  tff(c_48, plain, (~r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1') | k7_relat_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.81/1.38  tff(c_121, plain, (k7_relat_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_94, c_48])).
% 2.81/1.38  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.81/1.38  tff(c_97, plain, (r1_xboole_0('#skF_1', k1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_94, c_2])).
% 2.81/1.38  tff(c_30, plain, (![A_40]: (v1_relat_1(k6_relat_1(A_40)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.81/1.38  tff(c_40, plain, (![A_44]: (k2_relat_1(k6_relat_1(A_44))=A_44)), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.81/1.38  tff(c_206, plain, (![A_83, B_84]: (k5_relat_1(A_83, B_84)=k1_xboole_0 | ~r1_xboole_0(k2_relat_1(A_83), k1_relat_1(B_84)) | ~v1_relat_1(B_84) | ~v1_relat_1(A_83))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.81/1.38  tff(c_212, plain, (![A_44, B_84]: (k5_relat_1(k6_relat_1(A_44), B_84)=k1_xboole_0 | ~r1_xboole_0(A_44, k1_relat_1(B_84)) | ~v1_relat_1(B_84) | ~v1_relat_1(k6_relat_1(A_44)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_206])).
% 2.81/1.38  tff(c_226, plain, (![A_85, B_86]: (k5_relat_1(k6_relat_1(A_85), B_86)=k1_xboole_0 | ~r1_xboole_0(A_85, k1_relat_1(B_86)) | ~v1_relat_1(B_86))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_212])).
% 2.81/1.38  tff(c_236, plain, (k5_relat_1(k6_relat_1('#skF_1'), '#skF_2')=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_97, c_226])).
% 2.81/1.38  tff(c_246, plain, (k5_relat_1(k6_relat_1('#skF_1'), '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_46, c_236])).
% 2.81/1.38  tff(c_44, plain, (![A_47, B_48]: (k5_relat_1(k6_relat_1(A_47), B_48)=k7_relat_1(B_48, A_47) | ~v1_relat_1(B_48))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.81/1.38  tff(c_252, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_246, c_44])).
% 2.81/1.38  tff(c_259, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_46, c_252])).
% 2.81/1.38  tff(c_261, plain, $false, inference(negUnitSimplification, [status(thm)], [c_121, c_259])).
% 2.81/1.38  tff(c_262, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_54])).
% 2.81/1.38  tff(c_338, plain, (![B_106, A_107]: (k3_xboole_0(k1_relat_1(B_106), A_107)=k1_relat_1(k7_relat_1(B_106, A_107)) | ~v1_relat_1(B_106))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.81/1.38  tff(c_10, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.81/1.38  tff(c_649, plain, (![B_176, A_177]: (k5_xboole_0(k1_relat_1(B_176), k1_relat_1(k7_relat_1(B_176, A_177)))=k4_xboole_0(k1_relat_1(B_176), A_177) | ~v1_relat_1(B_176))), inference(superposition, [status(thm), theory('equality')], [c_338, c_10])).
% 2.81/1.38  tff(c_667, plain, (k5_xboole_0(k1_relat_1('#skF_2'), k1_relat_1(k1_xboole_0))=k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_262, c_649])).
% 2.81/1.38  tff(c_682, plain, (k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1')=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_12, c_34, c_667])).
% 2.81/1.38  tff(c_296, plain, (![A_91, C_92, B_93]: (r1_xboole_0(A_91, k4_xboole_0(C_92, B_93)) | ~r1_tarski(A_91, B_93))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.81/1.38  tff(c_299, plain, (![C_92, B_93, A_91]: (r1_xboole_0(k4_xboole_0(C_92, B_93), A_91) | ~r1_tarski(A_91, B_93))), inference(resolution, [status(thm)], [c_296, c_2])).
% 2.81/1.38  tff(c_715, plain, (![A_178]: (r1_xboole_0(k1_relat_1('#skF_2'), A_178) | ~r1_tarski(A_178, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_682, c_299])).
% 2.81/1.38  tff(c_264, plain, (k7_relat_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_48])).
% 2.81/1.38  tff(c_270, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_262, c_264])).
% 2.81/1.38  tff(c_271, plain, (~r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_48])).
% 2.81/1.38  tff(c_725, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_715, c_271])).
% 2.81/1.38  tff(c_733, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_725])).
% 2.81/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.81/1.38  
% 2.81/1.38  Inference rules
% 2.81/1.38  ----------------------
% 2.81/1.38  #Ref     : 0
% 2.81/1.38  #Sup     : 167
% 2.81/1.38  #Fact    : 0
% 2.81/1.38  #Define  : 0
% 2.81/1.38  #Split   : 4
% 2.81/1.38  #Chain   : 0
% 2.81/1.38  #Close   : 0
% 2.81/1.38  
% 2.81/1.38  Ordering : KBO
% 2.81/1.38  
% 2.81/1.38  Simplification rules
% 2.81/1.38  ----------------------
% 2.81/1.38  #Subsume      : 18
% 2.81/1.38  #Demod        : 43
% 2.81/1.38  #Tautology    : 82
% 2.81/1.38  #SimpNegUnit  : 1
% 2.81/1.38  #BackRed      : 0
% 2.81/1.38  
% 2.81/1.38  #Partial instantiations: 0
% 2.81/1.38  #Strategies tried      : 1
% 2.81/1.38  
% 2.81/1.38  Timing (in seconds)
% 2.81/1.38  ----------------------
% 2.81/1.38  Preprocessing        : 0.32
% 2.81/1.38  Parsing              : 0.17
% 2.81/1.38  CNF conversion       : 0.02
% 2.81/1.38  Main loop            : 0.30
% 2.81/1.38  Inferencing          : 0.12
% 2.81/1.38  Reduction            : 0.09
% 2.81/1.38  Demodulation         : 0.06
% 2.81/1.38  BG Simplification    : 0.02
% 2.81/1.38  Subsumption          : 0.05
% 2.81/1.38  Abstraction          : 0.02
% 2.81/1.38  MUC search           : 0.00
% 2.81/1.38  Cooper               : 0.00
% 2.81/1.38  Total                : 0.65
% 2.81/1.38  Index Insertion      : 0.00
% 2.81/1.38  Index Deletion       : 0.00
% 2.81/1.38  Index Matching       : 0.00
% 2.81/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
