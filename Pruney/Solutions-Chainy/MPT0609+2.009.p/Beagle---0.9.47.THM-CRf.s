%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:32 EST 2020

% Result     : Theorem 14.81s
% Output     : CNFRefutation 14.81s
% Verified   : 
% Statistics : Number of formulae       :   58 (  74 expanded)
%              Number of leaves         :   31 (  40 expanded)
%              Depth                    :   10
%              Number of atoms          :   63 (  83 expanded)
%              Number of equality atoms :   31 (  45 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

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

tff(f_78,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k6_subset_1(k1_relat_1(B),k1_relat_1(k7_relat_1(B,A))) = k1_relat_1(k6_subset_1(B,k7_relat_1(B,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t213_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(k1_relat_1(C),A)
       => k6_subset_1(C,k7_relat_1(C,B)) = k7_relat_1(C,k6_subset_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t211_relat_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,k6_subset_1(k1_relat_1(B),A))) = k6_subset_1(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t191_relat_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_40,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_28,plain,(
    ! [A_39,B_40] : k6_subset_1(A_39,B_40) = k4_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_34,plain,(
    ! [C_47,A_45,B_46] :
      ( k7_relat_1(C_47,k6_subset_1(A_45,B_46)) = k6_subset_1(C_47,k7_relat_1(C_47,B_46))
      | ~ r1_tarski(k1_relat_1(C_47),A_45)
      | ~ v1_relat_1(C_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1104,plain,(
    ! [C_134,A_135,B_136] :
      ( k7_relat_1(C_134,k4_xboole_0(A_135,B_136)) = k4_xboole_0(C_134,k7_relat_1(C_134,B_136))
      | ~ r1_tarski(k1_relat_1(C_134),A_135)
      | ~ v1_relat_1(C_134) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_28,c_34])).

tff(c_1759,plain,(
    ! [C_164,B_165] :
      ( k7_relat_1(C_164,k4_xboole_0(k1_relat_1(C_164),B_165)) = k4_xboole_0(C_164,k7_relat_1(C_164,B_165))
      | ~ v1_relat_1(C_164) ) ),
    inference(resolution,[status(thm)],[c_8,c_1104])).

tff(c_32,plain,(
    ! [B_44,A_43] :
      ( k1_relat_1(k7_relat_1(B_44,k6_subset_1(k1_relat_1(B_44),A_43))) = k6_subset_1(k1_relat_1(B_44),A_43)
      | ~ v1_relat_1(B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_43,plain,(
    ! [B_44,A_43] :
      ( k1_relat_1(k7_relat_1(B_44,k4_xboole_0(k1_relat_1(B_44),A_43))) = k4_xboole_0(k1_relat_1(B_44),A_43)
      | ~ v1_relat_1(B_44) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_28,c_32])).

tff(c_1774,plain,(
    ! [C_164,B_165] :
      ( k1_relat_1(k4_xboole_0(C_164,k7_relat_1(C_164,B_165))) = k4_xboole_0(k1_relat_1(C_164),B_165)
      | ~ v1_relat_1(C_164)
      | ~ v1_relat_1(C_164) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1759,c_43])).

tff(c_36,plain,(
    ! [B_49,A_48] :
      ( k3_xboole_0(k1_relat_1(B_49),A_48) = k1_relat_1(k7_relat_1(B_49,A_48))
      | ~ v1_relat_1(B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_154,plain,(
    ! [A_67,C_68,B_69] :
      ( r1_tarski(k3_xboole_0(A_67,C_68),B_69)
      | ~ r1_tarski(A_67,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( k3_xboole_0(A_10,B_11) = A_10
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_380,plain,(
    ! [A_89,C_90,B_91] :
      ( k3_xboole_0(k3_xboole_0(A_89,C_90),B_91) = k3_xboole_0(A_89,C_90)
      | ~ r1_tarski(A_89,B_91) ) ),
    inference(resolution,[status(thm)],[c_154,c_14])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_120,plain,(
    ! [A_62,B_63] : k5_xboole_0(A_62,k3_xboole_0(A_62,B_63)) = k4_xboole_0(A_62,B_63) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_135,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_120])).

tff(c_1821,plain,(
    ! [B_168,A_169,C_170] :
      ( k5_xboole_0(B_168,k3_xboole_0(A_169,C_170)) = k4_xboole_0(B_168,k3_xboole_0(A_169,C_170))
      | ~ r1_tarski(A_169,B_168) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_380,c_135])).

tff(c_10,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1836,plain,(
    ! [A_169,C_170] :
      ( k4_xboole_0(A_169,k3_xboole_0(A_169,C_170)) = k4_xboole_0(A_169,C_170)
      | ~ r1_tarski(A_169,A_169) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1821,c_10])).

tff(c_1898,plain,(
    ! [A_171,C_172] : k4_xboole_0(A_171,k3_xboole_0(A_171,C_172)) = k4_xboole_0(A_171,C_172) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1836])).

tff(c_34492,plain,(
    ! [B_532,A_533] :
      ( k4_xboole_0(k1_relat_1(B_532),k1_relat_1(k7_relat_1(B_532,A_533))) = k4_xboole_0(k1_relat_1(B_532),A_533)
      | ~ v1_relat_1(B_532) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_1898])).

tff(c_38,plain,(
    k6_subset_1(k1_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k1_relat_1(k6_subset_1('#skF_2',k7_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_41,plain,(
    k4_xboole_0(k1_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_28,c_38])).

tff(c_34554,plain,
    ( k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_34492,c_41])).

tff(c_34631,plain,(
    k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_34554])).

tff(c_34639,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1774,c_34631])).

tff(c_34643,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_34639])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:21:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.81/6.72  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.81/6.72  
% 14.81/6.72  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.81/6.73  %$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 14.81/6.73  
% 14.81/6.73  %Foreground sorts:
% 14.81/6.73  
% 14.81/6.73  
% 14.81/6.73  %Background operators:
% 14.81/6.73  
% 14.81/6.73  
% 14.81/6.73  %Foreground operators:
% 14.81/6.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.81/6.73  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 14.81/6.73  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 14.81/6.73  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 14.81/6.73  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 14.81/6.73  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.81/6.73  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 14.81/6.73  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 14.81/6.73  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 14.81/6.73  tff('#skF_2', type, '#skF_2': $i).
% 14.81/6.73  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 14.81/6.73  tff('#skF_1', type, '#skF_1': $i).
% 14.81/6.73  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 14.81/6.73  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 14.81/6.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.81/6.73  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 14.81/6.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.81/6.73  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 14.81/6.73  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 14.81/6.73  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 14.81/6.73  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 14.81/6.73  
% 14.81/6.74  tff(f_78, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k6_subset_1(k1_relat_1(B), k1_relat_1(k7_relat_1(B, A))) = k1_relat_1(k6_subset_1(B, k7_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t213_relat_1)).
% 14.81/6.74  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 14.81/6.74  tff(f_57, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 14.81/6.74  tff(f_69, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(k1_relat_1(C), A) => (k6_subset_1(C, k7_relat_1(C, B)) = k7_relat_1(C, k6_subset_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t211_relat_1)).
% 14.81/6.74  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, k6_subset_1(k1_relat_1(B), A))) = k6_subset_1(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t191_relat_1)).
% 14.81/6.74  tff(f_73, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 14.81/6.74  tff(f_39, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_xboole_1)).
% 14.81/6.74  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 14.81/6.74  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 14.81/6.74  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 14.81/6.74  tff(c_40, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_78])).
% 14.81/6.74  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 14.81/6.74  tff(c_28, plain, (![A_39, B_40]: (k6_subset_1(A_39, B_40)=k4_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_57])).
% 14.81/6.74  tff(c_34, plain, (![C_47, A_45, B_46]: (k7_relat_1(C_47, k6_subset_1(A_45, B_46))=k6_subset_1(C_47, k7_relat_1(C_47, B_46)) | ~r1_tarski(k1_relat_1(C_47), A_45) | ~v1_relat_1(C_47))), inference(cnfTransformation, [status(thm)], [f_69])).
% 14.81/6.74  tff(c_1104, plain, (![C_134, A_135, B_136]: (k7_relat_1(C_134, k4_xboole_0(A_135, B_136))=k4_xboole_0(C_134, k7_relat_1(C_134, B_136)) | ~r1_tarski(k1_relat_1(C_134), A_135) | ~v1_relat_1(C_134))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_28, c_34])).
% 14.81/6.74  tff(c_1759, plain, (![C_164, B_165]: (k7_relat_1(C_164, k4_xboole_0(k1_relat_1(C_164), B_165))=k4_xboole_0(C_164, k7_relat_1(C_164, B_165)) | ~v1_relat_1(C_164))), inference(resolution, [status(thm)], [c_8, c_1104])).
% 14.81/6.74  tff(c_32, plain, (![B_44, A_43]: (k1_relat_1(k7_relat_1(B_44, k6_subset_1(k1_relat_1(B_44), A_43)))=k6_subset_1(k1_relat_1(B_44), A_43) | ~v1_relat_1(B_44))), inference(cnfTransformation, [status(thm)], [f_63])).
% 14.81/6.74  tff(c_43, plain, (![B_44, A_43]: (k1_relat_1(k7_relat_1(B_44, k4_xboole_0(k1_relat_1(B_44), A_43)))=k4_xboole_0(k1_relat_1(B_44), A_43) | ~v1_relat_1(B_44))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_28, c_32])).
% 14.81/6.74  tff(c_1774, plain, (![C_164, B_165]: (k1_relat_1(k4_xboole_0(C_164, k7_relat_1(C_164, B_165)))=k4_xboole_0(k1_relat_1(C_164), B_165) | ~v1_relat_1(C_164) | ~v1_relat_1(C_164))), inference(superposition, [status(thm), theory('equality')], [c_1759, c_43])).
% 14.81/6.74  tff(c_36, plain, (![B_49, A_48]: (k3_xboole_0(k1_relat_1(B_49), A_48)=k1_relat_1(k7_relat_1(B_49, A_48)) | ~v1_relat_1(B_49))), inference(cnfTransformation, [status(thm)], [f_73])).
% 14.81/6.74  tff(c_154, plain, (![A_67, C_68, B_69]: (r1_tarski(k3_xboole_0(A_67, C_68), B_69) | ~r1_tarski(A_67, B_69))), inference(cnfTransformation, [status(thm)], [f_39])).
% 14.81/6.74  tff(c_14, plain, (![A_10, B_11]: (k3_xboole_0(A_10, B_11)=A_10 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 14.81/6.74  tff(c_380, plain, (![A_89, C_90, B_91]: (k3_xboole_0(k3_xboole_0(A_89, C_90), B_91)=k3_xboole_0(A_89, C_90) | ~r1_tarski(A_89, B_91))), inference(resolution, [status(thm)], [c_154, c_14])).
% 14.81/6.74  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 14.81/6.74  tff(c_120, plain, (![A_62, B_63]: (k5_xboole_0(A_62, k3_xboole_0(A_62, B_63))=k4_xboole_0(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_35])).
% 14.81/6.74  tff(c_135, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_120])).
% 14.81/6.74  tff(c_1821, plain, (![B_168, A_169, C_170]: (k5_xboole_0(B_168, k3_xboole_0(A_169, C_170))=k4_xboole_0(B_168, k3_xboole_0(A_169, C_170)) | ~r1_tarski(A_169, B_168))), inference(superposition, [status(thm), theory('equality')], [c_380, c_135])).
% 14.81/6.74  tff(c_10, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 14.81/6.74  tff(c_1836, plain, (![A_169, C_170]: (k4_xboole_0(A_169, k3_xboole_0(A_169, C_170))=k4_xboole_0(A_169, C_170) | ~r1_tarski(A_169, A_169))), inference(superposition, [status(thm), theory('equality')], [c_1821, c_10])).
% 14.81/6.74  tff(c_1898, plain, (![A_171, C_172]: (k4_xboole_0(A_171, k3_xboole_0(A_171, C_172))=k4_xboole_0(A_171, C_172))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1836])).
% 14.81/6.74  tff(c_34492, plain, (![B_532, A_533]: (k4_xboole_0(k1_relat_1(B_532), k1_relat_1(k7_relat_1(B_532, A_533)))=k4_xboole_0(k1_relat_1(B_532), A_533) | ~v1_relat_1(B_532))), inference(superposition, [status(thm), theory('equality')], [c_36, c_1898])).
% 14.81/6.74  tff(c_38, plain, (k6_subset_1(k1_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k1_relat_1(k6_subset_1('#skF_2', k7_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_78])).
% 14.81/6.74  tff(c_41, plain, (k4_xboole_0(k1_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_28, c_38])).
% 14.81/6.74  tff(c_34554, plain, (k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_34492, c_41])).
% 14.81/6.74  tff(c_34631, plain, (k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_34554])).
% 14.81/6.74  tff(c_34639, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1774, c_34631])).
% 14.81/6.74  tff(c_34643, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_34639])).
% 14.81/6.74  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.81/6.74  
% 14.81/6.74  Inference rules
% 14.81/6.74  ----------------------
% 14.81/6.74  #Ref     : 0
% 14.81/6.74  #Sup     : 9560
% 14.81/6.74  #Fact    : 0
% 14.81/6.74  #Define  : 0
% 14.81/6.74  #Split   : 0
% 14.81/6.74  #Chain   : 0
% 14.81/6.74  #Close   : 0
% 14.81/6.74  
% 14.81/6.74  Ordering : KBO
% 14.81/6.74  
% 14.81/6.74  Simplification rules
% 14.81/6.74  ----------------------
% 14.81/6.74  #Subsume      : 2532
% 14.81/6.74  #Demod        : 3497
% 14.81/6.74  #Tautology    : 1585
% 14.81/6.74  #SimpNegUnit  : 0
% 14.81/6.74  #BackRed      : 0
% 14.81/6.74  
% 14.81/6.74  #Partial instantiations: 0
% 14.81/6.74  #Strategies tried      : 1
% 14.81/6.74  
% 14.81/6.74  Timing (in seconds)
% 14.81/6.74  ----------------------
% 14.81/6.74  Preprocessing        : 0.33
% 14.81/6.74  Parsing              : 0.19
% 14.81/6.74  CNF conversion       : 0.02
% 14.81/6.74  Main loop            : 5.60
% 14.81/6.74  Inferencing          : 1.11
% 14.81/6.74  Reduction            : 1.74
% 14.81/6.74  Demodulation         : 1.47
% 14.81/6.74  BG Simplification    : 0.18
% 14.81/6.74  Subsumption          : 2.27
% 14.81/6.74  Abstraction          : 0.26
% 14.81/6.74  MUC search           : 0.00
% 14.81/6.74  Cooper               : 0.00
% 14.81/6.74  Total                : 5.96
% 14.81/6.74  Index Insertion      : 0.00
% 14.81/6.74  Index Deletion       : 0.00
% 14.81/6.74  Index Matching       : 0.00
% 14.81/6.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
