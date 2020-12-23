%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:43 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.55s
% Verified   : 
% Statistics : Number of formulae       :   60 (  73 expanded)
%              Number of leaves         :   30 (  37 expanded)
%              Depth                    :    9
%              Number of atoms          :   68 (  98 expanded)
%              Number of equality atoms :   30 (  41 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > v1_relat_1 > k1_enumset1 > k7_relat_1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(f_72,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k7_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_41,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_xboole_0(k2_relat_1(A),k1_relat_1(B))
           => k5_relat_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_33,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_44,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(c_32,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1')
    | k7_relat_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_80,plain,(
    k7_relat_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_30,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_38,plain,
    ( k7_relat_1('#skF_2','#skF_1') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_113,plain,(
    r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_38])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_116,plain,(
    r1_xboole_0('#skF_1',k1_relat_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_113,c_2])).

tff(c_14,plain,(
    ! [A_12] : v1_relat_1(k6_relat_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_24,plain,(
    ! [A_16] : k2_relat_1(k6_relat_1(A_16)) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_150,plain,(
    ! [A_41,B_42] :
      ( k5_relat_1(A_41,B_42) = k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(A_41),k1_relat_1(B_42))
      | ~ v1_relat_1(B_42)
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_156,plain,(
    ! [A_16,B_42] :
      ( k5_relat_1(k6_relat_1(A_16),B_42) = k1_xboole_0
      | ~ r1_xboole_0(A_16,k1_relat_1(B_42))
      | ~ v1_relat_1(B_42)
      | ~ v1_relat_1(k6_relat_1(A_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_150])).

tff(c_217,plain,(
    ! [A_49,B_50] :
      ( k5_relat_1(k6_relat_1(A_49),B_50) = k1_xboole_0
      | ~ r1_xboole_0(A_49,k1_relat_1(B_50))
      | ~ v1_relat_1(B_50) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_156])).

tff(c_223,plain,
    ( k5_relat_1(k6_relat_1('#skF_1'),'#skF_2') = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_116,c_217])).

tff(c_236,plain,(
    k5_relat_1(k6_relat_1('#skF_1'),'#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_223])).

tff(c_28,plain,(
    ! [A_19,B_20] :
      ( k5_relat_1(k6_relat_1(A_19),B_20) = k7_relat_1(B_20,A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_243,plain,
    ( k7_relat_1('#skF_2','#skF_1') = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_236,c_28])).

tff(c_250,plain,(
    k7_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_243])).

tff(c_252,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_250])).

tff(c_253,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_6,plain,(
    ! [A_5] : k5_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_18,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_254,plain,(
    k7_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_302,plain,(
    ! [B_61,A_62] :
      ( k3_xboole_0(k1_relat_1(B_61),A_62) = k1_relat_1(k7_relat_1(B_61,A_62))
      | ~ v1_relat_1(B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_676,plain,(
    ! [B_93,A_94] :
      ( k5_xboole_0(k1_relat_1(B_93),k1_relat_1(k7_relat_1(B_93,A_94))) = k4_xboole_0(k1_relat_1(B_93),A_94)
      | ~ v1_relat_1(B_93) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_302,c_4])).

tff(c_700,plain,
    ( k5_xboole_0(k1_relat_1('#skF_2'),k1_relat_1(k1_xboole_0)) = k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_254,c_676])).

tff(c_719,plain,(
    k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1') = k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_6,c_18,c_700])).

tff(c_8,plain,(
    ! [A_6,B_7] : r1_xboole_0(k4_xboole_0(A_6,B_7),B_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_750,plain,(
    r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_719,c_8])).

tff(c_755,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_253,c_750])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:03:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.10/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.55/1.33  
% 2.55/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.55/1.33  %$ r1_xboole_0 > v1_relat_1 > k1_enumset1 > k7_relat_1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.55/1.33  
% 2.55/1.33  %Foreground sorts:
% 2.55/1.33  
% 2.55/1.33  
% 2.55/1.33  %Background operators:
% 2.55/1.33  
% 2.55/1.33  
% 2.55/1.33  %Foreground operators:
% 2.55/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.55/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.55/1.33  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.55/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.55/1.33  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.55/1.33  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.55/1.33  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.55/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.55/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.55/1.33  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.55/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.55/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.55/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.55/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.55/1.33  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.55/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.55/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.55/1.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.55/1.33  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.55/1.33  
% 2.55/1.34  tff(f_72, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 2.55/1.34  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.55/1.34  tff(f_41, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.55/1.34  tff(f_57, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.55/1.34  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_xboole_0(k2_relat_1(A), k1_relat_1(B)) => (k5_relat_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_relat_1)).
% 2.55/1.34  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 2.55/1.34  tff(f_33, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.55/1.34  tff(f_44, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.55/1.34  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 2.55/1.34  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.55/1.34  tff(f_35, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.55/1.34  tff(c_32, plain, (~r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1') | k7_relat_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.55/1.34  tff(c_80, plain, (k7_relat_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_32])).
% 2.55/1.34  tff(c_30, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.55/1.34  tff(c_38, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0 | r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.55/1.34  tff(c_113, plain, (r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_80, c_38])).
% 2.55/1.34  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.55/1.34  tff(c_116, plain, (r1_xboole_0('#skF_1', k1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_113, c_2])).
% 2.55/1.34  tff(c_14, plain, (![A_12]: (v1_relat_1(k6_relat_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.55/1.34  tff(c_24, plain, (![A_16]: (k2_relat_1(k6_relat_1(A_16))=A_16)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.55/1.34  tff(c_150, plain, (![A_41, B_42]: (k5_relat_1(A_41, B_42)=k1_xboole_0 | ~r1_xboole_0(k2_relat_1(A_41), k1_relat_1(B_42)) | ~v1_relat_1(B_42) | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.55/1.34  tff(c_156, plain, (![A_16, B_42]: (k5_relat_1(k6_relat_1(A_16), B_42)=k1_xboole_0 | ~r1_xboole_0(A_16, k1_relat_1(B_42)) | ~v1_relat_1(B_42) | ~v1_relat_1(k6_relat_1(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_150])).
% 2.55/1.34  tff(c_217, plain, (![A_49, B_50]: (k5_relat_1(k6_relat_1(A_49), B_50)=k1_xboole_0 | ~r1_xboole_0(A_49, k1_relat_1(B_50)) | ~v1_relat_1(B_50))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_156])).
% 2.55/1.34  tff(c_223, plain, (k5_relat_1(k6_relat_1('#skF_1'), '#skF_2')=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_116, c_217])).
% 2.55/1.34  tff(c_236, plain, (k5_relat_1(k6_relat_1('#skF_1'), '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30, c_223])).
% 2.55/1.34  tff(c_28, plain, (![A_19, B_20]: (k5_relat_1(k6_relat_1(A_19), B_20)=k7_relat_1(B_20, A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.55/1.34  tff(c_243, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_236, c_28])).
% 2.55/1.34  tff(c_250, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30, c_243])).
% 2.55/1.34  tff(c_252, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_250])).
% 2.55/1.34  tff(c_253, plain, (~r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_32])).
% 2.55/1.34  tff(c_6, plain, (![A_5]: (k5_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.55/1.34  tff(c_18, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.55/1.34  tff(c_254, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_32])).
% 2.55/1.34  tff(c_302, plain, (![B_61, A_62]: (k3_xboole_0(k1_relat_1(B_61), A_62)=k1_relat_1(k7_relat_1(B_61, A_62)) | ~v1_relat_1(B_61))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.55/1.34  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.55/1.34  tff(c_676, plain, (![B_93, A_94]: (k5_xboole_0(k1_relat_1(B_93), k1_relat_1(k7_relat_1(B_93, A_94)))=k4_xboole_0(k1_relat_1(B_93), A_94) | ~v1_relat_1(B_93))), inference(superposition, [status(thm), theory('equality')], [c_302, c_4])).
% 2.55/1.34  tff(c_700, plain, (k5_xboole_0(k1_relat_1('#skF_2'), k1_relat_1(k1_xboole_0))=k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_254, c_676])).
% 2.55/1.34  tff(c_719, plain, (k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1')=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_6, c_18, c_700])).
% 2.55/1.34  tff(c_8, plain, (![A_6, B_7]: (r1_xboole_0(k4_xboole_0(A_6, B_7), B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.55/1.34  tff(c_750, plain, (r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_719, c_8])).
% 2.55/1.34  tff(c_755, plain, $false, inference(negUnitSimplification, [status(thm)], [c_253, c_750])).
% 2.55/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.55/1.34  
% 2.55/1.34  Inference rules
% 2.55/1.34  ----------------------
% 2.55/1.34  #Ref     : 0
% 2.55/1.34  #Sup     : 170
% 2.55/1.34  #Fact    : 0
% 2.55/1.34  #Define  : 0
% 2.55/1.34  #Split   : 3
% 2.55/1.34  #Chain   : 0
% 2.55/1.34  #Close   : 0
% 2.55/1.34  
% 2.55/1.34  Ordering : KBO
% 2.55/1.34  
% 2.55/1.34  Simplification rules
% 2.55/1.34  ----------------------
% 2.55/1.34  #Subsume      : 12
% 2.55/1.34  #Demod        : 94
% 2.55/1.35  #Tautology    : 100
% 2.55/1.35  #SimpNegUnit  : 4
% 2.55/1.35  #BackRed      : 0
% 2.55/1.35  
% 2.55/1.35  #Partial instantiations: 0
% 2.55/1.35  #Strategies tried      : 1
% 2.55/1.35  
% 2.55/1.35  Timing (in seconds)
% 2.55/1.35  ----------------------
% 2.55/1.35  Preprocessing        : 0.29
% 2.55/1.35  Parsing              : 0.16
% 2.55/1.35  CNF conversion       : 0.02
% 2.55/1.35  Main loop            : 0.28
% 2.55/1.35  Inferencing          : 0.11
% 2.55/1.35  Reduction            : 0.09
% 2.55/1.35  Demodulation         : 0.07
% 2.55/1.35  BG Simplification    : 0.02
% 2.55/1.35  Subsumption          : 0.04
% 2.55/1.35  Abstraction          : 0.02
% 2.55/1.35  MUC search           : 0.00
% 2.55/1.35  Cooper               : 0.00
% 2.55/1.35  Total                : 0.60
% 2.55/1.35  Index Insertion      : 0.00
% 2.55/1.35  Index Deletion       : 0.00
% 2.55/1.35  Index Matching       : 0.00
% 2.55/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
