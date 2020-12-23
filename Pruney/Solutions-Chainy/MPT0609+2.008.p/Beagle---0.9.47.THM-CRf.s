%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:32 EST 2020

% Result     : Theorem 2.58s
% Output     : CNFRefutation 2.58s
% Verified   : 
% Statistics : Number of formulae       :   41 (  59 expanded)
%              Number of leaves         :   23 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :   47 (  72 expanded)
%              Number of equality atoms :   20 (  35 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k1_enumset1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_58,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k6_subset_1(k1_relat_1(B),k1_relat_1(k7_relat_1(B,A))) = k1_relat_1(k6_subset_1(B,k7_relat_1(B,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t213_relat_1)).

tff(f_33,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k6_subset_1(B,k7_relat_1(B,A))) = k6_subset_1(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t212_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_22,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_8,plain,(
    ! [A_7,B_8] : k6_subset_1(A_7,B_8) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    ! [B_12,A_11] :
      ( k1_relat_1(k6_subset_1(B_12,k7_relat_1(B_12,A_11))) = k6_subset_1(k1_relat_1(B_12),A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_24,plain,(
    ! [B_12,A_11] :
      ( k1_relat_1(k4_xboole_0(B_12,k7_relat_1(B_12,A_11))) = k4_xboole_0(k1_relat_1(B_12),A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_8,c_12])).

tff(c_14,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_14,A_13)),k1_relat_1(B_14))
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_221,plain,(
    ! [B_39,A_40] :
      ( k1_relat_1(k7_relat_1(B_39,A_40)) = A_40
      | ~ r1_tarski(A_40,k1_relat_1(B_39))
      | ~ v1_relat_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_315,plain,(
    ! [B_49,A_50] :
      ( k1_relat_1(k7_relat_1(B_49,k1_relat_1(k7_relat_1(B_49,A_50)))) = k1_relat_1(k7_relat_1(B_49,A_50))
      | ~ v1_relat_1(B_49) ) ),
    inference(resolution,[status(thm)],[c_14,c_221])).

tff(c_192,plain,(
    ! [B_37,A_38] :
      ( k3_xboole_0(k1_relat_1(B_37),A_38) = k1_relat_1(k7_relat_1(B_37,A_38))
      | ~ v1_relat_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(A_1,B_2)) = k4_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_207,plain,(
    ! [B_37,A_38] :
      ( k5_xboole_0(k1_relat_1(B_37),k1_relat_1(k7_relat_1(B_37,A_38))) = k4_xboole_0(k1_relat_1(B_37),A_38)
      | ~ v1_relat_1(B_37) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_192,c_2])).

tff(c_642,plain,(
    ! [B_60,A_61] :
      ( k5_xboole_0(k1_relat_1(B_60),k1_relat_1(k7_relat_1(B_60,A_61))) = k4_xboole_0(k1_relat_1(B_60),k1_relat_1(k7_relat_1(B_60,A_61)))
      | ~ v1_relat_1(B_60)
      | ~ v1_relat_1(B_60) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_315,c_207])).

tff(c_692,plain,(
    ! [B_62,A_63] :
      ( k4_xboole_0(k1_relat_1(B_62),k1_relat_1(k7_relat_1(B_62,A_63))) = k4_xboole_0(k1_relat_1(B_62),A_63)
      | ~ v1_relat_1(B_62)
      | ~ v1_relat_1(B_62)
      | ~ v1_relat_1(B_62) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_642,c_207])).

tff(c_20,plain,(
    k6_subset_1(k1_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k1_relat_1(k6_subset_1('#skF_2',k7_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_23,plain,(
    k4_xboole_0(k1_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_8,c_20])).

tff(c_701,plain,
    ( k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_692,c_23])).

tff(c_734,plain,(
    k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_22,c_701])).

tff(c_740,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_734])).

tff(c_744,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_740])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n016.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 17:01:19 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.18/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.58/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.58/1.33  
% 2.58/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.58/1.33  %$ r1_tarski > v1_relat_1 > k1_enumset1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.58/1.33  
% 2.58/1.33  %Foreground sorts:
% 2.58/1.33  
% 2.58/1.33  
% 2.58/1.33  %Background operators:
% 2.58/1.33  
% 2.58/1.33  
% 2.58/1.33  %Foreground operators:
% 2.58/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.58/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.58/1.33  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.58/1.33  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.58/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.58/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.58/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.58/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.58/1.33  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.58/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.58/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.58/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.58/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.58/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.58/1.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.58/1.33  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.58/1.33  
% 2.58/1.34  tff(f_58, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k6_subset_1(k1_relat_1(B), k1_relat_1(k7_relat_1(B, A))) = k1_relat_1(k6_subset_1(B, k7_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t213_relat_1)).
% 2.58/1.34  tff(f_33, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.58/1.34  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k6_subset_1(B, k7_relat_1(B, A))) = k6_subset_1(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t212_relat_1)).
% 2.58/1.34  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t89_relat_1)).
% 2.58/1.34  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 2.58/1.34  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 2.58/1.34  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.58/1.34  tff(c_22, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.58/1.34  tff(c_8, plain, (![A_7, B_8]: (k6_subset_1(A_7, B_8)=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.58/1.34  tff(c_12, plain, (![B_12, A_11]: (k1_relat_1(k6_subset_1(B_12, k7_relat_1(B_12, A_11)))=k6_subset_1(k1_relat_1(B_12), A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.58/1.34  tff(c_24, plain, (![B_12, A_11]: (k1_relat_1(k4_xboole_0(B_12, k7_relat_1(B_12, A_11)))=k4_xboole_0(k1_relat_1(B_12), A_11) | ~v1_relat_1(B_12))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_8, c_12])).
% 2.58/1.34  tff(c_14, plain, (![B_14, A_13]: (r1_tarski(k1_relat_1(k7_relat_1(B_14, A_13)), k1_relat_1(B_14)) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.58/1.34  tff(c_221, plain, (![B_39, A_40]: (k1_relat_1(k7_relat_1(B_39, A_40))=A_40 | ~r1_tarski(A_40, k1_relat_1(B_39)) | ~v1_relat_1(B_39))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.58/1.34  tff(c_315, plain, (![B_49, A_50]: (k1_relat_1(k7_relat_1(B_49, k1_relat_1(k7_relat_1(B_49, A_50))))=k1_relat_1(k7_relat_1(B_49, A_50)) | ~v1_relat_1(B_49))), inference(resolution, [status(thm)], [c_14, c_221])).
% 2.58/1.34  tff(c_192, plain, (![B_37, A_38]: (k3_xboole_0(k1_relat_1(B_37), A_38)=k1_relat_1(k7_relat_1(B_37, A_38)) | ~v1_relat_1(B_37))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.58/1.34  tff(c_2, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(A_1, B_2))=k4_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.58/1.34  tff(c_207, plain, (![B_37, A_38]: (k5_xboole_0(k1_relat_1(B_37), k1_relat_1(k7_relat_1(B_37, A_38)))=k4_xboole_0(k1_relat_1(B_37), A_38) | ~v1_relat_1(B_37))), inference(superposition, [status(thm), theory('equality')], [c_192, c_2])).
% 2.58/1.34  tff(c_642, plain, (![B_60, A_61]: (k5_xboole_0(k1_relat_1(B_60), k1_relat_1(k7_relat_1(B_60, A_61)))=k4_xboole_0(k1_relat_1(B_60), k1_relat_1(k7_relat_1(B_60, A_61))) | ~v1_relat_1(B_60) | ~v1_relat_1(B_60))), inference(superposition, [status(thm), theory('equality')], [c_315, c_207])).
% 2.58/1.34  tff(c_692, plain, (![B_62, A_63]: (k4_xboole_0(k1_relat_1(B_62), k1_relat_1(k7_relat_1(B_62, A_63)))=k4_xboole_0(k1_relat_1(B_62), A_63) | ~v1_relat_1(B_62) | ~v1_relat_1(B_62) | ~v1_relat_1(B_62))), inference(superposition, [status(thm), theory('equality')], [c_642, c_207])).
% 2.58/1.34  tff(c_20, plain, (k6_subset_1(k1_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k1_relat_1(k6_subset_1('#skF_2', k7_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.58/1.34  tff(c_23, plain, (k4_xboole_0(k1_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_8, c_20])).
% 2.58/1.34  tff(c_701, plain, (k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_692, c_23])).
% 2.58/1.34  tff(c_734, plain, (k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_22, c_701])).
% 2.58/1.34  tff(c_740, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_24, c_734])).
% 2.58/1.34  tff(c_744, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_740])).
% 2.58/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.58/1.34  
% 2.58/1.34  Inference rules
% 2.58/1.34  ----------------------
% 2.58/1.34  #Ref     : 0
% 2.58/1.34  #Sup     : 201
% 2.58/1.34  #Fact    : 0
% 2.58/1.34  #Define  : 0
% 2.58/1.34  #Split   : 0
% 2.58/1.34  #Chain   : 0
% 2.58/1.34  #Close   : 0
% 2.58/1.34  
% 2.58/1.34  Ordering : KBO
% 2.58/1.34  
% 2.58/1.34  Simplification rules
% 2.58/1.34  ----------------------
% 2.58/1.34  #Subsume      : 23
% 2.58/1.34  #Demod        : 14
% 2.58/1.34  #Tautology    : 69
% 2.58/1.34  #SimpNegUnit  : 0
% 2.58/1.34  #BackRed      : 0
% 2.58/1.34  
% 2.58/1.34  #Partial instantiations: 0
% 2.58/1.34  #Strategies tried      : 1
% 2.58/1.34  
% 2.58/1.34  Timing (in seconds)
% 2.58/1.34  ----------------------
% 2.58/1.34  Preprocessing        : 0.29
% 2.58/1.34  Parsing              : 0.16
% 2.58/1.35  CNF conversion       : 0.02
% 2.58/1.35  Main loop            : 0.30
% 2.58/1.35  Inferencing          : 0.12
% 2.58/1.35  Reduction            : 0.09
% 2.58/1.35  Demodulation         : 0.07
% 2.58/1.35  BG Simplification    : 0.02
% 2.58/1.35  Subsumption          : 0.05
% 2.58/1.35  Abstraction          : 0.02
% 2.58/1.35  MUC search           : 0.00
% 2.58/1.35  Cooper               : 0.00
% 2.58/1.35  Total                : 0.62
% 2.58/1.35  Index Insertion      : 0.00
% 2.58/1.35  Index Deletion       : 0.00
% 2.58/1.35  Index Matching       : 0.00
% 2.58/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
