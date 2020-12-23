%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:35 EST 2020

% Result     : Theorem 2.32s
% Output     : CNFRefutation 2.32s
% Verified   : 
% Statistics : Number of formulae       :   48 (  64 expanded)
%              Number of leaves         :   28 (  37 expanded)
%              Depth                    :    9
%              Number of atoms          :   50 (  71 expanded)
%              Number of equality atoms :   22 (  35 expanded)
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

tff(f_64,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k6_subset_1(k1_relat_1(B),k1_relat_1(k7_relat_1(B,A))) = k1_relat_1(k6_subset_1(B,k7_relat_1(B,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t213_relat_1)).

tff(f_43,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k6_subset_1(B,k7_relat_1(B,A))) = k6_subset_1(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t212_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(c_30,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_18,plain,(
    ! [A_32,B_33] : k6_subset_1(A_32,B_33) = k4_xboole_0(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_22,plain,(
    ! [B_37,A_36] :
      ( k1_relat_1(k6_subset_1(B_37,k7_relat_1(B_37,A_36))) = k6_subset_1(k1_relat_1(B_37),A_36)
      | ~ v1_relat_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_32,plain,(
    ! [B_37,A_36] :
      ( k1_relat_1(k4_xboole_0(B_37,k7_relat_1(B_37,A_36))) = k4_xboole_0(k1_relat_1(B_37),A_36)
      | ~ v1_relat_1(B_37) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_22])).

tff(c_24,plain,(
    ! [B_39,A_38] :
      ( k3_xboole_0(k1_relat_1(B_39),A_38) = k1_relat_1(k7_relat_1(B_39,A_38))
      | ~ v1_relat_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(A_1,B_2)) = k4_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_104,plain,(
    ! [B_63,A_64] :
      ( k1_relat_1(k7_relat_1(B_63,A_64)) = A_64
      | ~ r1_tarski(A_64,k1_relat_1(B_63))
      | ~ v1_relat_1(B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_162,plain,(
    ! [B_80,B_81] :
      ( k1_relat_1(k7_relat_1(B_80,k3_xboole_0(k1_relat_1(B_80),B_81))) = k3_xboole_0(k1_relat_1(B_80),B_81)
      | ~ v1_relat_1(B_80) ) ),
    inference(resolution,[status(thm)],[c_4,c_104])).

tff(c_79,plain,(
    ! [B_55,A_56] :
      ( k3_xboole_0(k1_relat_1(B_55),A_56) = k1_relat_1(k7_relat_1(B_55,A_56))
      | ~ v1_relat_1(B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_85,plain,(
    ! [B_55,A_56] :
      ( k5_xboole_0(k1_relat_1(B_55),k1_relat_1(k7_relat_1(B_55,A_56))) = k4_xboole_0(k1_relat_1(B_55),A_56)
      | ~ v1_relat_1(B_55) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_2])).

tff(c_174,plain,(
    ! [B_80,B_81] :
      ( k5_xboole_0(k1_relat_1(B_80),k3_xboole_0(k1_relat_1(B_80),B_81)) = k4_xboole_0(k1_relat_1(B_80),k3_xboole_0(k1_relat_1(B_80),B_81))
      | ~ v1_relat_1(B_80)
      | ~ v1_relat_1(B_80) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_85])).

tff(c_245,plain,(
    ! [B_84,B_85] :
      ( k4_xboole_0(k1_relat_1(B_84),k3_xboole_0(k1_relat_1(B_84),B_85)) = k4_xboole_0(k1_relat_1(B_84),B_85)
      | ~ v1_relat_1(B_84)
      | ~ v1_relat_1(B_84) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_174])).

tff(c_343,plain,(
    ! [B_95,A_96] :
      ( k4_xboole_0(k1_relat_1(B_95),k1_relat_1(k7_relat_1(B_95,A_96))) = k4_xboole_0(k1_relat_1(B_95),A_96)
      | ~ v1_relat_1(B_95)
      | ~ v1_relat_1(B_95)
      | ~ v1_relat_1(B_95) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_245])).

tff(c_28,plain,(
    k6_subset_1(k1_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k1_relat_1(k6_subset_1('#skF_2',k7_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_31,plain,(
    k4_xboole_0(k1_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_28])).

tff(c_349,plain,
    ( k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_343,c_31])).

tff(c_376,plain,(
    k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_30,c_30,c_349])).

tff(c_382,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_376])).

tff(c_386,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_382])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:14:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.32/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.35  
% 2.32/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.35  %$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.32/1.35  
% 2.32/1.35  %Foreground sorts:
% 2.32/1.35  
% 2.32/1.35  
% 2.32/1.35  %Background operators:
% 2.32/1.35  
% 2.32/1.35  
% 2.32/1.35  %Foreground operators:
% 2.32/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.32/1.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.32/1.35  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.32/1.35  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.32/1.35  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.32/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.32/1.35  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.32/1.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.32/1.35  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.32/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.32/1.35  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.32/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.32/1.35  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.32/1.35  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.32/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.32/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.32/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.32/1.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.32/1.35  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.32/1.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.32/1.35  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.32/1.35  
% 2.32/1.36  tff(f_64, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k6_subset_1(k1_relat_1(B), k1_relat_1(k7_relat_1(B, A))) = k1_relat_1(k6_subset_1(B, k7_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t213_relat_1)).
% 2.32/1.36  tff(f_43, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.32/1.36  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k6_subset_1(B, k7_relat_1(B, A))) = k6_subset_1(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t212_relat_1)).
% 2.32/1.36  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 2.32/1.36  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.32/1.36  tff(f_29, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.32/1.36  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 2.32/1.36  tff(c_30, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.32/1.36  tff(c_18, plain, (![A_32, B_33]: (k6_subset_1(A_32, B_33)=k4_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.32/1.36  tff(c_22, plain, (![B_37, A_36]: (k1_relat_1(k6_subset_1(B_37, k7_relat_1(B_37, A_36)))=k6_subset_1(k1_relat_1(B_37), A_36) | ~v1_relat_1(B_37))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.32/1.36  tff(c_32, plain, (![B_37, A_36]: (k1_relat_1(k4_xboole_0(B_37, k7_relat_1(B_37, A_36)))=k4_xboole_0(k1_relat_1(B_37), A_36) | ~v1_relat_1(B_37))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_22])).
% 2.32/1.36  tff(c_24, plain, (![B_39, A_38]: (k3_xboole_0(k1_relat_1(B_39), A_38)=k1_relat_1(k7_relat_1(B_39, A_38)) | ~v1_relat_1(B_39))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.32/1.36  tff(c_2, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(A_1, B_2))=k4_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.32/1.36  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.32/1.36  tff(c_104, plain, (![B_63, A_64]: (k1_relat_1(k7_relat_1(B_63, A_64))=A_64 | ~r1_tarski(A_64, k1_relat_1(B_63)) | ~v1_relat_1(B_63))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.32/1.36  tff(c_162, plain, (![B_80, B_81]: (k1_relat_1(k7_relat_1(B_80, k3_xboole_0(k1_relat_1(B_80), B_81)))=k3_xboole_0(k1_relat_1(B_80), B_81) | ~v1_relat_1(B_80))), inference(resolution, [status(thm)], [c_4, c_104])).
% 2.32/1.36  tff(c_79, plain, (![B_55, A_56]: (k3_xboole_0(k1_relat_1(B_55), A_56)=k1_relat_1(k7_relat_1(B_55, A_56)) | ~v1_relat_1(B_55))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.32/1.36  tff(c_85, plain, (![B_55, A_56]: (k5_xboole_0(k1_relat_1(B_55), k1_relat_1(k7_relat_1(B_55, A_56)))=k4_xboole_0(k1_relat_1(B_55), A_56) | ~v1_relat_1(B_55))), inference(superposition, [status(thm), theory('equality')], [c_79, c_2])).
% 2.32/1.36  tff(c_174, plain, (![B_80, B_81]: (k5_xboole_0(k1_relat_1(B_80), k3_xboole_0(k1_relat_1(B_80), B_81))=k4_xboole_0(k1_relat_1(B_80), k3_xboole_0(k1_relat_1(B_80), B_81)) | ~v1_relat_1(B_80) | ~v1_relat_1(B_80))), inference(superposition, [status(thm), theory('equality')], [c_162, c_85])).
% 2.32/1.36  tff(c_245, plain, (![B_84, B_85]: (k4_xboole_0(k1_relat_1(B_84), k3_xboole_0(k1_relat_1(B_84), B_85))=k4_xboole_0(k1_relat_1(B_84), B_85) | ~v1_relat_1(B_84) | ~v1_relat_1(B_84))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_174])).
% 2.32/1.36  tff(c_343, plain, (![B_95, A_96]: (k4_xboole_0(k1_relat_1(B_95), k1_relat_1(k7_relat_1(B_95, A_96)))=k4_xboole_0(k1_relat_1(B_95), A_96) | ~v1_relat_1(B_95) | ~v1_relat_1(B_95) | ~v1_relat_1(B_95))), inference(superposition, [status(thm), theory('equality')], [c_24, c_245])).
% 2.32/1.36  tff(c_28, plain, (k6_subset_1(k1_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k1_relat_1(k6_subset_1('#skF_2', k7_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.32/1.36  tff(c_31, plain, (k4_xboole_0(k1_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_28])).
% 2.32/1.36  tff(c_349, plain, (k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_343, c_31])).
% 2.32/1.36  tff(c_376, plain, (k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_30, c_30, c_349])).
% 2.32/1.36  tff(c_382, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_32, c_376])).
% 2.32/1.36  tff(c_386, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_382])).
% 2.32/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.36  
% 2.32/1.36  Inference rules
% 2.32/1.36  ----------------------
% 2.32/1.36  #Ref     : 0
% 2.32/1.36  #Sup     : 94
% 2.32/1.36  #Fact    : 0
% 2.32/1.36  #Define  : 0
% 2.32/1.36  #Split   : 0
% 2.32/1.36  #Chain   : 0
% 2.32/1.36  #Close   : 0
% 2.32/1.36  
% 2.32/1.36  Ordering : KBO
% 2.32/1.36  
% 2.32/1.36  Simplification rules
% 2.32/1.36  ----------------------
% 2.32/1.36  #Subsume      : 5
% 2.32/1.36  #Demod        : 12
% 2.32/1.36  #Tautology    : 41
% 2.32/1.36  #SimpNegUnit  : 0
% 2.32/1.36  #BackRed      : 0
% 2.32/1.36  
% 2.32/1.36  #Partial instantiations: 0
% 2.32/1.36  #Strategies tried      : 1
% 2.32/1.36  
% 2.32/1.36  Timing (in seconds)
% 2.32/1.36  ----------------------
% 2.32/1.37  Preprocessing        : 0.31
% 2.32/1.37  Parsing              : 0.17
% 2.32/1.37  CNF conversion       : 0.02
% 2.32/1.37  Main loop            : 0.26
% 2.32/1.37  Inferencing          : 0.11
% 2.32/1.37  Reduction            : 0.07
% 2.32/1.37  Demodulation         : 0.06
% 2.32/1.37  BG Simplification    : 0.02
% 2.32/1.37  Subsumption          : 0.04
% 2.32/1.37  Abstraction          : 0.02
% 2.32/1.37  MUC search           : 0.00
% 2.32/1.37  Cooper               : 0.00
% 2.32/1.37  Total                : 0.60
% 2.32/1.37  Index Insertion      : 0.00
% 2.32/1.37  Index Deletion       : 0.00
% 2.32/1.37  Index Matching       : 0.00
% 2.32/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
