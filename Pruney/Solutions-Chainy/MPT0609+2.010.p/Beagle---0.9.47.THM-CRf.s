%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:32 EST 2020

% Result     : Theorem 9.18s
% Output     : CNFRefutation 9.18s
% Verified   : 
% Statistics : Number of formulae       :   54 (  84 expanded)
%              Number of leaves         :   29 (  43 expanded)
%              Depth                    :   10
%              Number of atoms          :   46 (  82 expanded)
%              Number of equality atoms :   28 (  53 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

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

tff(f_80,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k6_subset_1(k1_relat_1(B),k1_relat_1(k7_relat_1(B,A))) = k1_relat_1(k6_subset_1(B,k7_relat_1(B,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t213_relat_1)).

tff(f_55,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k6_subset_1(B,k7_relat_1(B,A))) = k6_subset_1(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t212_relat_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(c_42,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_28,plain,(
    ! [A_38,B_39] : k6_subset_1(A_38,B_39) = k4_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_34,plain,(
    ! [B_46,A_45] :
      ( k1_relat_1(k6_subset_1(B_46,k7_relat_1(B_46,A_45))) = k6_subset_1(k1_relat_1(B_46),A_45)
      | ~ v1_relat_1(B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_44,plain,(
    ! [B_46,A_45] :
      ( k1_relat_1(k4_xboole_0(B_46,k7_relat_1(B_46,A_45))) = k4_xboole_0(k1_relat_1(B_46),A_45)
      | ~ v1_relat_1(B_46) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_28,c_34])).

tff(c_10,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_7,B_8] : r1_tarski(k3_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_116,plain,(
    ! [A_62,B_63] :
      ( k3_xboole_0(A_62,B_63) = A_62
      | ~ r1_tarski(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_236,plain,(
    ! [A_77,B_78] : k3_xboole_0(k3_xboole_0(A_77,B_78),A_77) = k3_xboole_0(A_77,B_78) ),
    inference(resolution,[status(thm)],[c_12,c_116])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_168,plain,(
    ! [A_69,B_70] : k5_xboole_0(A_69,k3_xboole_0(A_69,B_70)) = k4_xboole_0(A_69,B_70) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_183,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_168])).

tff(c_245,plain,(
    ! [A_77,B_78] : k5_xboole_0(A_77,k3_xboole_0(A_77,B_78)) = k4_xboole_0(A_77,k3_xboole_0(A_77,B_78)) ),
    inference(superposition,[status(thm),theory(equality)],[c_236,c_183])).

tff(c_286,plain,(
    ! [A_77,B_78] : k4_xboole_0(A_77,k3_xboole_0(A_77,B_78)) = k4_xboole_0(A_77,B_78) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_245])).

tff(c_599,plain,(
    ! [B_90,A_91] :
      ( k3_xboole_0(k1_relat_1(B_90),A_91) = k1_relat_1(k7_relat_1(B_90,A_91))
      | ~ v1_relat_1(B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_127,plain,(
    ! [A_7,B_8] : k3_xboole_0(k3_xboole_0(A_7,B_8),A_7) = k3_xboole_0(A_7,B_8) ),
    inference(resolution,[status(thm)],[c_12,c_116])).

tff(c_624,plain,(
    ! [B_90,A_91] :
      ( k3_xboole_0(k1_relat_1(k7_relat_1(B_90,A_91)),k1_relat_1(B_90)) = k3_xboole_0(k1_relat_1(B_90),A_91)
      | ~ v1_relat_1(B_90) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_599,c_127])).

tff(c_4180,plain,(
    ! [B_190,A_191] :
      ( k3_xboole_0(k1_relat_1(B_190),k1_relat_1(k7_relat_1(B_190,A_191))) = k3_xboole_0(k1_relat_1(B_190),A_191)
      | ~ v1_relat_1(B_190) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_624])).

tff(c_4274,plain,(
    ! [B_190,A_191] :
      ( k4_xboole_0(k1_relat_1(B_190),k3_xboole_0(k1_relat_1(B_190),A_191)) = k4_xboole_0(k1_relat_1(B_190),k1_relat_1(k7_relat_1(B_190,A_191)))
      | ~ v1_relat_1(B_190) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4180,c_286])).

tff(c_10463,plain,(
    ! [B_259,A_260] :
      ( k4_xboole_0(k1_relat_1(B_259),k1_relat_1(k7_relat_1(B_259,A_260))) = k4_xboole_0(k1_relat_1(B_259),A_260)
      | ~ v1_relat_1(B_259) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_286,c_4274])).

tff(c_40,plain,(
    k6_subset_1(k1_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k1_relat_1(k6_subset_1('#skF_2',k7_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_43,plain,(
    k4_xboole_0(k1_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_28,c_40])).

tff(c_10487,plain,
    ( k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_10463,c_43])).

tff(c_10567,plain,(
    k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_10487])).

tff(c_10576,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_10567])).

tff(c_10580,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_10576])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:52:01 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.18/3.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.18/3.27  
% 9.18/3.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.18/3.28  %$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 9.18/3.28  
% 9.18/3.28  %Foreground sorts:
% 9.18/3.28  
% 9.18/3.28  
% 9.18/3.28  %Background operators:
% 9.18/3.28  
% 9.18/3.28  
% 9.18/3.28  %Foreground operators:
% 9.18/3.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.18/3.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.18/3.28  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 9.18/3.28  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 9.18/3.28  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 9.18/3.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.18/3.28  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 9.18/3.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.18/3.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.18/3.28  tff('#skF_2', type, '#skF_2': $i).
% 9.18/3.28  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 9.18/3.28  tff('#skF_1', type, '#skF_1': $i).
% 9.18/3.28  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.18/3.28  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 9.18/3.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.18/3.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.18/3.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.18/3.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.18/3.28  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 9.18/3.28  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.18/3.28  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 9.18/3.28  
% 9.18/3.29  tff(f_80, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k6_subset_1(k1_relat_1(B), k1_relat_1(k7_relat_1(B, A))) = k1_relat_1(k6_subset_1(B, k7_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t213_relat_1)).
% 9.18/3.29  tff(f_55, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 9.18/3.29  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k6_subset_1(B, k7_relat_1(B, A))) = k6_subset_1(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t212_relat_1)).
% 9.18/3.29  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 9.18/3.29  tff(f_37, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 9.18/3.29  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 9.18/3.29  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 9.18/3.29  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 9.18/3.29  tff(c_42, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_80])).
% 9.18/3.29  tff(c_28, plain, (![A_38, B_39]: (k6_subset_1(A_38, B_39)=k4_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_55])).
% 9.18/3.29  tff(c_34, plain, (![B_46, A_45]: (k1_relat_1(k6_subset_1(B_46, k7_relat_1(B_46, A_45)))=k6_subset_1(k1_relat_1(B_46), A_45) | ~v1_relat_1(B_46))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.18/3.29  tff(c_44, plain, (![B_46, A_45]: (k1_relat_1(k4_xboole_0(B_46, k7_relat_1(B_46, A_45)))=k4_xboole_0(k1_relat_1(B_46), A_45) | ~v1_relat_1(B_46))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_28, c_34])).
% 9.18/3.29  tff(c_10, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.18/3.29  tff(c_12, plain, (![A_7, B_8]: (r1_tarski(k3_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.18/3.29  tff(c_116, plain, (![A_62, B_63]: (k3_xboole_0(A_62, B_63)=A_62 | ~r1_tarski(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.18/3.29  tff(c_236, plain, (![A_77, B_78]: (k3_xboole_0(k3_xboole_0(A_77, B_78), A_77)=k3_xboole_0(A_77, B_78))), inference(resolution, [status(thm)], [c_12, c_116])).
% 9.18/3.29  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.18/3.29  tff(c_168, plain, (![A_69, B_70]: (k5_xboole_0(A_69, k3_xboole_0(A_69, B_70))=k4_xboole_0(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.18/3.29  tff(c_183, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_168])).
% 9.18/3.29  tff(c_245, plain, (![A_77, B_78]: (k5_xboole_0(A_77, k3_xboole_0(A_77, B_78))=k4_xboole_0(A_77, k3_xboole_0(A_77, B_78)))), inference(superposition, [status(thm), theory('equality')], [c_236, c_183])).
% 9.18/3.29  tff(c_286, plain, (![A_77, B_78]: (k4_xboole_0(A_77, k3_xboole_0(A_77, B_78))=k4_xboole_0(A_77, B_78))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_245])).
% 9.18/3.29  tff(c_599, plain, (![B_90, A_91]: (k3_xboole_0(k1_relat_1(B_90), A_91)=k1_relat_1(k7_relat_1(B_90, A_91)) | ~v1_relat_1(B_90))), inference(cnfTransformation, [status(thm)], [f_69])).
% 9.18/3.29  tff(c_127, plain, (![A_7, B_8]: (k3_xboole_0(k3_xboole_0(A_7, B_8), A_7)=k3_xboole_0(A_7, B_8))), inference(resolution, [status(thm)], [c_12, c_116])).
% 9.18/3.29  tff(c_624, plain, (![B_90, A_91]: (k3_xboole_0(k1_relat_1(k7_relat_1(B_90, A_91)), k1_relat_1(B_90))=k3_xboole_0(k1_relat_1(B_90), A_91) | ~v1_relat_1(B_90))), inference(superposition, [status(thm), theory('equality')], [c_599, c_127])).
% 9.18/3.29  tff(c_4180, plain, (![B_190, A_191]: (k3_xboole_0(k1_relat_1(B_190), k1_relat_1(k7_relat_1(B_190, A_191)))=k3_xboole_0(k1_relat_1(B_190), A_191) | ~v1_relat_1(B_190))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_624])).
% 9.18/3.29  tff(c_4274, plain, (![B_190, A_191]: (k4_xboole_0(k1_relat_1(B_190), k3_xboole_0(k1_relat_1(B_190), A_191))=k4_xboole_0(k1_relat_1(B_190), k1_relat_1(k7_relat_1(B_190, A_191))) | ~v1_relat_1(B_190))), inference(superposition, [status(thm), theory('equality')], [c_4180, c_286])).
% 9.18/3.29  tff(c_10463, plain, (![B_259, A_260]: (k4_xboole_0(k1_relat_1(B_259), k1_relat_1(k7_relat_1(B_259, A_260)))=k4_xboole_0(k1_relat_1(B_259), A_260) | ~v1_relat_1(B_259))), inference(demodulation, [status(thm), theory('equality')], [c_286, c_4274])).
% 9.18/3.29  tff(c_40, plain, (k6_subset_1(k1_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k1_relat_1(k6_subset_1('#skF_2', k7_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 9.18/3.29  tff(c_43, plain, (k4_xboole_0(k1_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_28, c_40])).
% 9.18/3.29  tff(c_10487, plain, (k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_10463, c_43])).
% 9.18/3.29  tff(c_10567, plain, (k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_10487])).
% 9.18/3.29  tff(c_10576, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_44, c_10567])).
% 9.18/3.29  tff(c_10580, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_10576])).
% 9.18/3.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.18/3.29  
% 9.18/3.29  Inference rules
% 9.18/3.29  ----------------------
% 9.18/3.29  #Ref     : 0
% 9.18/3.29  #Sup     : 2751
% 9.18/3.29  #Fact    : 0
% 9.18/3.29  #Define  : 0
% 9.18/3.29  #Split   : 0
% 9.18/3.29  #Chain   : 0
% 9.18/3.29  #Close   : 0
% 9.18/3.29  
% 9.18/3.29  Ordering : KBO
% 9.18/3.29  
% 9.18/3.29  Simplification rules
% 9.18/3.29  ----------------------
% 9.18/3.29  #Subsume      : 572
% 9.18/3.29  #Demod        : 3444
% 9.18/3.29  #Tautology    : 1037
% 9.18/3.29  #SimpNegUnit  : 0
% 9.18/3.29  #BackRed      : 0
% 9.18/3.29  
% 9.18/3.29  #Partial instantiations: 0
% 9.18/3.29  #Strategies tried      : 1
% 9.18/3.29  
% 9.18/3.29  Timing (in seconds)
% 9.18/3.29  ----------------------
% 9.41/3.29  Preprocessing        : 0.32
% 9.41/3.29  Parsing              : 0.17
% 9.41/3.29  CNF conversion       : 0.02
% 9.41/3.29  Main loop            : 2.21
% 9.41/3.29  Inferencing          : 0.53
% 9.41/3.29  Reduction            : 1.15
% 9.41/3.29  Demodulation         : 1.01
% 9.41/3.29  BG Simplification    : 0.08
% 9.41/3.29  Subsumption          : 0.35
% 9.41/3.29  Abstraction          : 0.14
% 9.41/3.29  MUC search           : 0.00
% 9.41/3.29  Cooper               : 0.00
% 9.41/3.29  Total                : 2.55
% 9.41/3.29  Index Insertion      : 0.00
% 9.41/3.29  Index Deletion       : 0.00
% 9.41/3.29  Index Matching       : 0.00
% 9.41/3.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
