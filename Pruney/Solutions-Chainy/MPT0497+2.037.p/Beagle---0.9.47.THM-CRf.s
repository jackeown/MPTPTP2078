%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:44 EST 2020

% Result     : Theorem 3.55s
% Output     : CNFRefutation 3.88s
% Verified   : 
% Statistics : Number of formulae       :   59 (  72 expanded)
%              Number of leaves         :   29 (  36 expanded)
%              Depth                    :    9
%              Number of atoms          :   70 ( 100 expanded)
%              Number of equality atoms :   33 (  44 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > v1_relat_1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_76,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k7_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_45,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_61,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_xboole_0(k2_relat_1(A),k1_relat_1(B))
           => k5_relat_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_relat_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_31,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_48,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(c_1520,plain,(
    ! [A_94,B_95] :
      ( r1_xboole_0(A_94,B_95)
      | k4_xboole_0(A_94,B_95) != A_94 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_36,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1')
    | k7_relat_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_84,plain,(
    k7_relat_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_34,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_42,plain,
    ( k7_relat_1('#skF_2','#skF_1') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_207,plain,(
    r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_42])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_214,plain,(
    r1_xboole_0('#skF_1',k1_relat_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_207,c_2])).

tff(c_18,plain,(
    ! [A_14] : v1_relat_1(k6_relat_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_28,plain,(
    ! [A_18] : k2_relat_1(k6_relat_1(A_18)) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_846,plain,(
    ! [A_73,B_74] :
      ( k5_relat_1(A_73,B_74) = k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(A_73),k1_relat_1(B_74))
      | ~ v1_relat_1(B_74)
      | ~ v1_relat_1(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_861,plain,(
    ! [A_18,B_74] :
      ( k5_relat_1(k6_relat_1(A_18),B_74) = k1_xboole_0
      | ~ r1_xboole_0(A_18,k1_relat_1(B_74))
      | ~ v1_relat_1(B_74)
      | ~ v1_relat_1(k6_relat_1(A_18)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_846])).

tff(c_1374,plain,(
    ! [A_83,B_84] :
      ( k5_relat_1(k6_relat_1(A_83),B_84) = k1_xboole_0
      | ~ r1_xboole_0(A_83,k1_relat_1(B_84))
      | ~ v1_relat_1(B_84) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_861])).

tff(c_1408,plain,
    ( k5_relat_1(k6_relat_1('#skF_1'),'#skF_2') = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_214,c_1374])).

tff(c_1443,plain,(
    k5_relat_1(k6_relat_1('#skF_1'),'#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1408])).

tff(c_32,plain,(
    ! [A_21,B_22] :
      ( k5_relat_1(k6_relat_1(A_21),B_22) = k7_relat_1(B_22,A_21)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1454,plain,
    ( k7_relat_1('#skF_2','#skF_1') = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1443,c_32])).

tff(c_1461,plain,(
    k7_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1454])).

tff(c_1463,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_1461])).

tff(c_1464,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_1531,plain,(
    k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1') != k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_1520,c_1464])).

tff(c_4,plain,(
    ! [A_3] : k4_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1465,plain,(
    k7_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_1762,plain,(
    ! [B_114,A_115] :
      ( k3_xboole_0(k1_relat_1(B_114),A_115) = k1_relat_1(k7_relat_1(B_114,A_115))
      | ~ v1_relat_1(B_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_6,plain,(
    ! [A_4,B_5] : k4_xboole_0(A_4,k3_xboole_0(A_4,B_5)) = k4_xboole_0(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_3046,plain,(
    ! [B_162,A_163] :
      ( k4_xboole_0(k1_relat_1(B_162),k1_relat_1(k7_relat_1(B_162,A_163))) = k4_xboole_0(k1_relat_1(B_162),A_163)
      | ~ v1_relat_1(B_162) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1762,c_6])).

tff(c_3108,plain,
    ( k4_xboole_0(k1_relat_1('#skF_2'),k1_relat_1(k1_xboole_0)) = k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1465,c_3046])).

tff(c_3131,plain,(
    k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1') = k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_4,c_22,c_3108])).

tff(c_3133,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1531,c_3131])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:39:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.55/1.65  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.55/1.65  
% 3.55/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.55/1.66  %$ r1_xboole_0 > v1_relat_1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 3.55/1.66  
% 3.55/1.66  %Foreground sorts:
% 3.55/1.66  
% 3.55/1.66  
% 3.55/1.66  %Background operators:
% 3.55/1.66  
% 3.55/1.66  
% 3.55/1.66  %Foreground operators:
% 3.55/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.55/1.66  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.55/1.66  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.55/1.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.55/1.66  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.55/1.66  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.55/1.66  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.55/1.66  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.55/1.66  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.55/1.66  tff('#skF_2', type, '#skF_2': $i).
% 3.55/1.66  tff('#skF_1', type, '#skF_1': $i).
% 3.55/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.55/1.66  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.55/1.66  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.55/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.55/1.66  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.55/1.66  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.55/1.66  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.55/1.66  
% 3.88/1.67  tff(f_39, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.88/1.67  tff(f_76, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 3.88/1.67  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.88/1.67  tff(f_45, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 3.88/1.67  tff(f_61, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 3.88/1.67  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_xboole_0(k2_relat_1(A), k1_relat_1(B)) => (k5_relat_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_relat_1)).
% 3.88/1.67  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 3.88/1.67  tff(f_31, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 3.88/1.67  tff(f_48, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.88/1.67  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 3.88/1.67  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 3.88/1.67  tff(c_1520, plain, (![A_94, B_95]: (r1_xboole_0(A_94, B_95) | k4_xboole_0(A_94, B_95)!=A_94)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.88/1.67  tff(c_36, plain, (~r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1') | k7_relat_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.88/1.67  tff(c_84, plain, (k7_relat_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_36])).
% 3.88/1.67  tff(c_34, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.88/1.67  tff(c_42, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0 | r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.88/1.67  tff(c_207, plain, (r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_84, c_42])).
% 3.88/1.67  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.88/1.67  tff(c_214, plain, (r1_xboole_0('#skF_1', k1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_207, c_2])).
% 3.88/1.67  tff(c_18, plain, (![A_14]: (v1_relat_1(k6_relat_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.88/1.67  tff(c_28, plain, (![A_18]: (k2_relat_1(k6_relat_1(A_18))=A_18)), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.88/1.67  tff(c_846, plain, (![A_73, B_74]: (k5_relat_1(A_73, B_74)=k1_xboole_0 | ~r1_xboole_0(k2_relat_1(A_73), k1_relat_1(B_74)) | ~v1_relat_1(B_74) | ~v1_relat_1(A_73))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.88/1.67  tff(c_861, plain, (![A_18, B_74]: (k5_relat_1(k6_relat_1(A_18), B_74)=k1_xboole_0 | ~r1_xboole_0(A_18, k1_relat_1(B_74)) | ~v1_relat_1(B_74) | ~v1_relat_1(k6_relat_1(A_18)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_846])).
% 3.88/1.67  tff(c_1374, plain, (![A_83, B_84]: (k5_relat_1(k6_relat_1(A_83), B_84)=k1_xboole_0 | ~r1_xboole_0(A_83, k1_relat_1(B_84)) | ~v1_relat_1(B_84))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_861])).
% 3.88/1.67  tff(c_1408, plain, (k5_relat_1(k6_relat_1('#skF_1'), '#skF_2')=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_214, c_1374])).
% 3.88/1.67  tff(c_1443, plain, (k5_relat_1(k6_relat_1('#skF_1'), '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1408])).
% 3.88/1.67  tff(c_32, plain, (![A_21, B_22]: (k5_relat_1(k6_relat_1(A_21), B_22)=k7_relat_1(B_22, A_21) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.88/1.67  tff(c_1454, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1443, c_32])).
% 3.88/1.67  tff(c_1461, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1454])).
% 3.88/1.67  tff(c_1463, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_1461])).
% 3.88/1.67  tff(c_1464, plain, (~r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_36])).
% 3.88/1.67  tff(c_1531, plain, (k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1')!=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_1520, c_1464])).
% 3.88/1.67  tff(c_4, plain, (![A_3]: (k4_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.88/1.67  tff(c_22, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.88/1.67  tff(c_1465, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_36])).
% 3.88/1.67  tff(c_1762, plain, (![B_114, A_115]: (k3_xboole_0(k1_relat_1(B_114), A_115)=k1_relat_1(k7_relat_1(B_114, A_115)) | ~v1_relat_1(B_114))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.88/1.67  tff(c_6, plain, (![A_4, B_5]: (k4_xboole_0(A_4, k3_xboole_0(A_4, B_5))=k4_xboole_0(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.88/1.67  tff(c_3046, plain, (![B_162, A_163]: (k4_xboole_0(k1_relat_1(B_162), k1_relat_1(k7_relat_1(B_162, A_163)))=k4_xboole_0(k1_relat_1(B_162), A_163) | ~v1_relat_1(B_162))), inference(superposition, [status(thm), theory('equality')], [c_1762, c_6])).
% 3.88/1.67  tff(c_3108, plain, (k4_xboole_0(k1_relat_1('#skF_2'), k1_relat_1(k1_xboole_0))=k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1465, c_3046])).
% 3.88/1.67  tff(c_3131, plain, (k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1')=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_4, c_22, c_3108])).
% 3.88/1.67  tff(c_3133, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1531, c_3131])).
% 3.88/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.88/1.67  
% 3.88/1.67  Inference rules
% 3.88/1.67  ----------------------
% 3.88/1.67  #Ref     : 0
% 3.88/1.67  #Sup     : 761
% 3.88/1.67  #Fact    : 0
% 3.88/1.67  #Define  : 0
% 3.88/1.67  #Split   : 3
% 3.88/1.67  #Chain   : 0
% 3.88/1.67  #Close   : 0
% 3.88/1.67  
% 3.88/1.67  Ordering : KBO
% 3.88/1.67  
% 3.88/1.67  Simplification rules
% 3.88/1.67  ----------------------
% 3.88/1.67  #Subsume      : 12
% 3.88/1.67  #Demod        : 518
% 3.88/1.67  #Tautology    : 430
% 3.88/1.67  #SimpNegUnit  : 4
% 3.88/1.67  #BackRed      : 12
% 3.88/1.67  
% 3.88/1.67  #Partial instantiations: 0
% 3.88/1.67  #Strategies tried      : 1
% 3.88/1.67  
% 3.88/1.67  Timing (in seconds)
% 3.88/1.67  ----------------------
% 3.88/1.67  Preprocessing        : 0.30
% 3.88/1.67  Parsing              : 0.16
% 3.88/1.67  CNF conversion       : 0.02
% 3.88/1.67  Main loop            : 0.62
% 3.88/1.67  Inferencing          : 0.21
% 3.88/1.67  Reduction            : 0.23
% 3.88/1.67  Demodulation         : 0.18
% 3.88/1.67  BG Simplification    : 0.03
% 3.88/1.67  Subsumption          : 0.10
% 3.88/1.67  Abstraction          : 0.04
% 3.88/1.67  MUC search           : 0.00
% 3.88/1.67  Cooper               : 0.00
% 3.88/1.67  Total                : 0.94
% 3.88/1.67  Index Insertion      : 0.00
% 3.88/1.67  Index Deletion       : 0.00
% 3.88/1.67  Index Matching       : 0.00
% 3.88/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
