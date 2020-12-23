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
% DateTime   : Thu Dec  3 09:59:40 EST 2020

% Result     : Theorem 2.99s
% Output     : CNFRefutation 2.99s
% Verified   : 
% Statistics : Number of formulae       :   74 (  90 expanded)
%              Number of leaves         :   37 (  46 expanded)
%              Depth                    :    9
%              Number of atoms          :   83 ( 118 expanded)
%              Number of equality atoms :   36 (  48 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_41,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_39,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

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

tff(f_45,axiom,(
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

tff(c_14,plain,(
    ! [A_8] : k4_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_12,plain,(
    ! [A_7] : k3_xboole_0(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_411,plain,(
    ! [A_110,B_111] : k5_xboole_0(A_110,k3_xboole_0(A_110,B_111)) = k4_xboole_0(A_110,B_111) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_420,plain,(
    ! [A_7] : k5_xboole_0(A_7,k1_xboole_0) = k4_xboole_0(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_411])).

tff(c_423,plain,(
    ! [A_7] : k5_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_420])).

tff(c_34,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_48,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1')
    | k7_relat_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_100,plain,(
    k7_relat_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_54,plain,
    ( k7_relat_1('#skF_2','#skF_1') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_120,plain,(
    r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_54])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_123,plain,(
    r1_xboole_0('#skF_1',k1_relat_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_120,c_2])).

tff(c_30,plain,(
    ! [A_34] : v1_relat_1(k6_relat_1(A_34)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_40,plain,(
    ! [A_38] : k2_relat_1(k6_relat_1(A_38)) = A_38 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_280,plain,(
    ! [A_89,B_90] :
      ( k5_relat_1(A_89,B_90) = k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(A_89),k1_relat_1(B_90))
      | ~ v1_relat_1(B_90)
      | ~ v1_relat_1(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_295,plain,(
    ! [A_38,B_90] :
      ( k5_relat_1(k6_relat_1(A_38),B_90) = k1_xboole_0
      | ~ r1_xboole_0(A_38,k1_relat_1(B_90))
      | ~ v1_relat_1(B_90)
      | ~ v1_relat_1(k6_relat_1(A_38)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_280])).

tff(c_311,plain,(
    ! [A_91,B_92] :
      ( k5_relat_1(k6_relat_1(A_91),B_92) = k1_xboole_0
      | ~ r1_xboole_0(A_91,k1_relat_1(B_92))
      | ~ v1_relat_1(B_92) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_295])).

tff(c_332,plain,
    ( k5_relat_1(k6_relat_1('#skF_1'),'#skF_2') = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_123,c_311])).

tff(c_344,plain,(
    k5_relat_1(k6_relat_1('#skF_1'),'#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_332])).

tff(c_44,plain,(
    ! [A_41,B_42] :
      ( k5_relat_1(k6_relat_1(A_41),B_42) = k7_relat_1(B_42,A_41)
      | ~ v1_relat_1(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_359,plain,
    ( k7_relat_1('#skF_2','#skF_1') = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_344,c_44])).

tff(c_366,plain,(
    k7_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_359])).

tff(c_368,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_366])).

tff(c_370,plain,(
    k7_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_473,plain,(
    ! [B_125,A_126] :
      ( k3_xboole_0(k1_relat_1(B_125),A_126) = k1_relat_1(k7_relat_1(B_125,A_126))
      | ~ v1_relat_1(B_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_10,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_963,plain,(
    ! [B_172,A_173] :
      ( k5_xboole_0(k1_relat_1(B_172),k1_relat_1(k7_relat_1(B_172,A_173))) = k4_xboole_0(k1_relat_1(B_172),A_173)
      | ~ v1_relat_1(B_172) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_473,c_10])).

tff(c_996,plain,
    ( k5_xboole_0(k1_relat_1('#skF_2'),k1_relat_1(k1_xboole_0)) = k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_370,c_963])).

tff(c_1018,plain,(
    k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1') = k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_423,c_34,c_996])).

tff(c_396,plain,(
    ! [A_105,C_106,B_107] :
      ( r1_xboole_0(A_105,k4_xboole_0(C_106,B_107))
      | ~ r1_tarski(A_105,B_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_402,plain,(
    ! [C_106,B_107,A_105] :
      ( r1_xboole_0(k4_xboole_0(C_106,B_107),A_105)
      | ~ r1_tarski(A_105,B_107) ) ),
    inference(resolution,[status(thm)],[c_396,c_2])).

tff(c_1032,plain,(
    ! [A_174] :
      ( r1_xboole_0(k1_relat_1('#skF_2'),A_174)
      | ~ r1_tarski(A_174,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1018,c_402])).

tff(c_369,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_1044,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_1032,c_369])).

tff(c_1051,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1044])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:55:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.99/1.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.99/1.50  
% 2.99/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.99/1.50  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.99/1.50  
% 2.99/1.50  %Foreground sorts:
% 2.99/1.50  
% 2.99/1.50  
% 2.99/1.50  %Background operators:
% 2.99/1.50  
% 2.99/1.50  
% 2.99/1.50  %Foreground operators:
% 2.99/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.99/1.50  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.99/1.50  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.99/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.99/1.50  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.99/1.50  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.99/1.50  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.99/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.99/1.50  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.99/1.50  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.99/1.50  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.99/1.50  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.99/1.50  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.99/1.50  tff('#skF_2', type, '#skF_2': $i).
% 2.99/1.50  tff('#skF_1', type, '#skF_1': $i).
% 2.99/1.50  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.99/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.99/1.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.99/1.50  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.99/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.99/1.50  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.99/1.50  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.99/1.50  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.99/1.50  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.99/1.50  
% 2.99/1.51  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.99/1.51  tff(f_90, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 2.99/1.51  tff(f_41, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.99/1.51  tff(f_39, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.99/1.51  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.99/1.51  tff(f_62, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.99/1.51  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.99/1.51  tff(f_59, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.99/1.51  tff(f_75, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.99/1.51  tff(f_71, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_xboole_0(k2_relat_1(A), k1_relat_1(B)) => (k5_relat_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_relat_1)).
% 2.99/1.51  tff(f_83, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 2.99/1.51  tff(f_79, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 2.99/1.51  tff(f_45, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 2.99/1.51  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.99/1.51  tff(c_46, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.99/1.51  tff(c_14, plain, (![A_8]: (k4_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.99/1.51  tff(c_12, plain, (![A_7]: (k3_xboole_0(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.99/1.51  tff(c_411, plain, (![A_110, B_111]: (k5_xboole_0(A_110, k3_xboole_0(A_110, B_111))=k4_xboole_0(A_110, B_111))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.99/1.51  tff(c_420, plain, (![A_7]: (k5_xboole_0(A_7, k1_xboole_0)=k4_xboole_0(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_411])).
% 2.99/1.51  tff(c_423, plain, (![A_7]: (k5_xboole_0(A_7, k1_xboole_0)=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_420])).
% 2.99/1.51  tff(c_34, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.99/1.51  tff(c_48, plain, (~r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1') | k7_relat_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.99/1.51  tff(c_100, plain, (k7_relat_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_48])).
% 2.99/1.51  tff(c_54, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0 | r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.99/1.51  tff(c_120, plain, (r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_100, c_54])).
% 2.99/1.51  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.99/1.51  tff(c_123, plain, (r1_xboole_0('#skF_1', k1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_120, c_2])).
% 2.99/1.51  tff(c_30, plain, (![A_34]: (v1_relat_1(k6_relat_1(A_34)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.99/1.51  tff(c_40, plain, (![A_38]: (k2_relat_1(k6_relat_1(A_38))=A_38)), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.99/1.51  tff(c_280, plain, (![A_89, B_90]: (k5_relat_1(A_89, B_90)=k1_xboole_0 | ~r1_xboole_0(k2_relat_1(A_89), k1_relat_1(B_90)) | ~v1_relat_1(B_90) | ~v1_relat_1(A_89))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.99/1.51  tff(c_295, plain, (![A_38, B_90]: (k5_relat_1(k6_relat_1(A_38), B_90)=k1_xboole_0 | ~r1_xboole_0(A_38, k1_relat_1(B_90)) | ~v1_relat_1(B_90) | ~v1_relat_1(k6_relat_1(A_38)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_280])).
% 2.99/1.51  tff(c_311, plain, (![A_91, B_92]: (k5_relat_1(k6_relat_1(A_91), B_92)=k1_xboole_0 | ~r1_xboole_0(A_91, k1_relat_1(B_92)) | ~v1_relat_1(B_92))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_295])).
% 2.99/1.51  tff(c_332, plain, (k5_relat_1(k6_relat_1('#skF_1'), '#skF_2')=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_123, c_311])).
% 2.99/1.51  tff(c_344, plain, (k5_relat_1(k6_relat_1('#skF_1'), '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_46, c_332])).
% 2.99/1.51  tff(c_44, plain, (![A_41, B_42]: (k5_relat_1(k6_relat_1(A_41), B_42)=k7_relat_1(B_42, A_41) | ~v1_relat_1(B_42))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.99/1.51  tff(c_359, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_344, c_44])).
% 2.99/1.51  tff(c_366, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_46, c_359])).
% 2.99/1.51  tff(c_368, plain, $false, inference(negUnitSimplification, [status(thm)], [c_100, c_366])).
% 2.99/1.51  tff(c_370, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_48])).
% 2.99/1.51  tff(c_473, plain, (![B_125, A_126]: (k3_xboole_0(k1_relat_1(B_125), A_126)=k1_relat_1(k7_relat_1(B_125, A_126)) | ~v1_relat_1(B_125))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.99/1.51  tff(c_10, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.99/1.51  tff(c_963, plain, (![B_172, A_173]: (k5_xboole_0(k1_relat_1(B_172), k1_relat_1(k7_relat_1(B_172, A_173)))=k4_xboole_0(k1_relat_1(B_172), A_173) | ~v1_relat_1(B_172))), inference(superposition, [status(thm), theory('equality')], [c_473, c_10])).
% 2.99/1.51  tff(c_996, plain, (k5_xboole_0(k1_relat_1('#skF_2'), k1_relat_1(k1_xboole_0))=k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_370, c_963])).
% 2.99/1.51  tff(c_1018, plain, (k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1')=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_423, c_34, c_996])).
% 2.99/1.51  tff(c_396, plain, (![A_105, C_106, B_107]: (r1_xboole_0(A_105, k4_xboole_0(C_106, B_107)) | ~r1_tarski(A_105, B_107))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.99/1.51  tff(c_402, plain, (![C_106, B_107, A_105]: (r1_xboole_0(k4_xboole_0(C_106, B_107), A_105) | ~r1_tarski(A_105, B_107))), inference(resolution, [status(thm)], [c_396, c_2])).
% 2.99/1.51  tff(c_1032, plain, (![A_174]: (r1_xboole_0(k1_relat_1('#skF_2'), A_174) | ~r1_tarski(A_174, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1018, c_402])).
% 2.99/1.51  tff(c_369, plain, (~r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_48])).
% 2.99/1.51  tff(c_1044, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_1032, c_369])).
% 2.99/1.51  tff(c_1051, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_1044])).
% 2.99/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.99/1.51  
% 2.99/1.51  Inference rules
% 2.99/1.51  ----------------------
% 2.99/1.51  #Ref     : 0
% 2.99/1.51  #Sup     : 226
% 2.99/1.51  #Fact    : 0
% 2.99/1.51  #Define  : 0
% 2.99/1.51  #Split   : 3
% 2.99/1.51  #Chain   : 0
% 2.99/1.51  #Close   : 0
% 2.99/1.51  
% 2.99/1.51  Ordering : KBO
% 2.99/1.51  
% 2.99/1.51  Simplification rules
% 2.99/1.51  ----------------------
% 2.99/1.51  #Subsume      : 18
% 2.99/1.51  #Demod        : 110
% 2.99/1.51  #Tautology    : 131
% 2.99/1.51  #SimpNegUnit  : 3
% 2.99/1.51  #BackRed      : 0
% 2.99/1.51  
% 2.99/1.51  #Partial instantiations: 0
% 2.99/1.51  #Strategies tried      : 1
% 2.99/1.51  
% 2.99/1.51  Timing (in seconds)
% 2.99/1.51  ----------------------
% 2.99/1.52  Preprocessing        : 0.35
% 2.99/1.52  Parsing              : 0.19
% 2.99/1.52  CNF conversion       : 0.02
% 2.99/1.52  Main loop            : 0.35
% 2.99/1.52  Inferencing          : 0.14
% 2.99/1.52  Reduction            : 0.11
% 2.99/1.52  Demodulation         : 0.08
% 2.99/1.52  BG Simplification    : 0.02
% 2.99/1.52  Subsumption          : 0.05
% 2.99/1.52  Abstraction          : 0.02
% 2.99/1.52  MUC search           : 0.00
% 2.99/1.52  Cooper               : 0.00
% 2.99/1.52  Total                : 0.72
% 2.99/1.52  Index Insertion      : 0.00
% 2.99/1.52  Index Deletion       : 0.00
% 2.99/1.52  Index Matching       : 0.00
% 2.99/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
