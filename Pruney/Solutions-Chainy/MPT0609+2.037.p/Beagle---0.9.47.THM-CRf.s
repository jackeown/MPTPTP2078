%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:35 EST 2020

% Result     : Theorem 2.36s
% Output     : CNFRefutation 2.36s
% Verified   : 
% Statistics : Number of formulae       :   46 (  64 expanded)
%              Number of leaves         :   28 (  37 expanded)
%              Depth                    :    8
%              Number of atoms          :   47 (  72 expanded)
%              Number of equality atoms :   20 (  35 expanded)
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

tff(f_66,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k6_subset_1(k1_relat_1(B),k1_relat_1(k7_relat_1(B,A))) = k1_relat_1(k6_subset_1(B,k7_relat_1(B,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t213_relat_1)).

tff(f_41,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k6_subset_1(B,k7_relat_1(B,A))) = k6_subset_1(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t212_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_30,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_16,plain,(
    ! [A_30,B_31] : k6_subset_1(A_30,B_31) = k4_xboole_0(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_20,plain,(
    ! [B_35,A_34] :
      ( k1_relat_1(k6_subset_1(B_35,k7_relat_1(B_35,A_34))) = k6_subset_1(k1_relat_1(B_35),A_34)
      | ~ v1_relat_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_32,plain,(
    ! [B_35,A_34] :
      ( k1_relat_1(k4_xboole_0(B_35,k7_relat_1(B_35,A_34))) = k4_xboole_0(k1_relat_1(B_35),A_34)
      | ~ v1_relat_1(B_35) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_16,c_20])).

tff(c_22,plain,(
    ! [B_37,A_36] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_37,A_36)),k1_relat_1(B_37))
      | ~ v1_relat_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_100,plain,(
    ! [B_61,A_62] :
      ( k1_relat_1(k7_relat_1(B_61,A_62)) = A_62
      | ~ r1_tarski(A_62,k1_relat_1(B_61))
      | ~ v1_relat_1(B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_144,plain,(
    ! [B_72,A_73] :
      ( k1_relat_1(k7_relat_1(B_72,k1_relat_1(k7_relat_1(B_72,A_73)))) = k1_relat_1(k7_relat_1(B_72,A_73))
      | ~ v1_relat_1(B_72) ) ),
    inference(resolution,[status(thm)],[c_22,c_100])).

tff(c_79,plain,(
    ! [B_55,A_56] :
      ( k3_xboole_0(k1_relat_1(B_55),A_56) = k1_relat_1(k7_relat_1(B_55,A_56))
      | ~ v1_relat_1(B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(A_1,B_2)) = k4_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_85,plain,(
    ! [B_55,A_56] :
      ( k5_xboole_0(k1_relat_1(B_55),k1_relat_1(k7_relat_1(B_55,A_56))) = k4_xboole_0(k1_relat_1(B_55),A_56)
      | ~ v1_relat_1(B_55) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_2])).

tff(c_197,plain,(
    ! [B_87,A_88] :
      ( k5_xboole_0(k1_relat_1(B_87),k1_relat_1(k7_relat_1(B_87,A_88))) = k4_xboole_0(k1_relat_1(B_87),k1_relat_1(k7_relat_1(B_87,A_88)))
      | ~ v1_relat_1(B_87)
      | ~ v1_relat_1(B_87) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_85])).

tff(c_221,plain,(
    ! [B_89,A_90] :
      ( k4_xboole_0(k1_relat_1(B_89),k1_relat_1(k7_relat_1(B_89,A_90))) = k4_xboole_0(k1_relat_1(B_89),A_90)
      | ~ v1_relat_1(B_89)
      | ~ v1_relat_1(B_89)
      | ~ v1_relat_1(B_89) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_85])).

tff(c_28,plain,(
    k6_subset_1(k1_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k1_relat_1(k6_subset_1('#skF_2',k7_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_31,plain,(
    k4_xboole_0(k1_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_16,c_28])).

tff(c_227,plain,
    ( k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_221,c_31])).

tff(c_242,plain,(
    k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_30,c_30,c_227])).

tff(c_247,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_242])).

tff(c_251,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_247])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:54:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.36/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/1.28  
% 2.36/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/1.28  %$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.36/1.28  
% 2.36/1.28  %Foreground sorts:
% 2.36/1.28  
% 2.36/1.28  
% 2.36/1.28  %Background operators:
% 2.36/1.28  
% 2.36/1.28  
% 2.36/1.28  %Foreground operators:
% 2.36/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.36/1.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.36/1.28  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.36/1.28  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.36/1.28  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.36/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.36/1.28  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.36/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.36/1.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.36/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.36/1.28  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.36/1.28  tff('#skF_1', type, '#skF_1': $i).
% 2.36/1.28  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.36/1.28  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.36/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.36/1.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.36/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.36/1.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.36/1.28  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.36/1.28  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.36/1.28  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.36/1.28  
% 2.36/1.29  tff(f_66, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k6_subset_1(k1_relat_1(B), k1_relat_1(k7_relat_1(B, A))) = k1_relat_1(k6_subset_1(B, k7_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t213_relat_1)).
% 2.36/1.29  tff(f_41, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.36/1.29  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k6_subset_1(B, k7_relat_1(B, A))) = k6_subset_1(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t212_relat_1)).
% 2.36/1.29  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t89_relat_1)).
% 2.36/1.29  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 2.36/1.29  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 2.36/1.29  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.36/1.29  tff(c_30, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.36/1.29  tff(c_16, plain, (![A_30, B_31]: (k6_subset_1(A_30, B_31)=k4_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.36/1.29  tff(c_20, plain, (![B_35, A_34]: (k1_relat_1(k6_subset_1(B_35, k7_relat_1(B_35, A_34)))=k6_subset_1(k1_relat_1(B_35), A_34) | ~v1_relat_1(B_35))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.36/1.29  tff(c_32, plain, (![B_35, A_34]: (k1_relat_1(k4_xboole_0(B_35, k7_relat_1(B_35, A_34)))=k4_xboole_0(k1_relat_1(B_35), A_34) | ~v1_relat_1(B_35))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_16, c_20])).
% 2.36/1.29  tff(c_22, plain, (![B_37, A_36]: (r1_tarski(k1_relat_1(k7_relat_1(B_37, A_36)), k1_relat_1(B_37)) | ~v1_relat_1(B_37))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.36/1.29  tff(c_100, plain, (![B_61, A_62]: (k1_relat_1(k7_relat_1(B_61, A_62))=A_62 | ~r1_tarski(A_62, k1_relat_1(B_61)) | ~v1_relat_1(B_61))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.36/1.29  tff(c_144, plain, (![B_72, A_73]: (k1_relat_1(k7_relat_1(B_72, k1_relat_1(k7_relat_1(B_72, A_73))))=k1_relat_1(k7_relat_1(B_72, A_73)) | ~v1_relat_1(B_72))), inference(resolution, [status(thm)], [c_22, c_100])).
% 2.36/1.29  tff(c_79, plain, (![B_55, A_56]: (k3_xboole_0(k1_relat_1(B_55), A_56)=k1_relat_1(k7_relat_1(B_55, A_56)) | ~v1_relat_1(B_55))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.36/1.29  tff(c_2, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(A_1, B_2))=k4_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.36/1.29  tff(c_85, plain, (![B_55, A_56]: (k5_xboole_0(k1_relat_1(B_55), k1_relat_1(k7_relat_1(B_55, A_56)))=k4_xboole_0(k1_relat_1(B_55), A_56) | ~v1_relat_1(B_55))), inference(superposition, [status(thm), theory('equality')], [c_79, c_2])).
% 2.36/1.29  tff(c_197, plain, (![B_87, A_88]: (k5_xboole_0(k1_relat_1(B_87), k1_relat_1(k7_relat_1(B_87, A_88)))=k4_xboole_0(k1_relat_1(B_87), k1_relat_1(k7_relat_1(B_87, A_88))) | ~v1_relat_1(B_87) | ~v1_relat_1(B_87))), inference(superposition, [status(thm), theory('equality')], [c_144, c_85])).
% 2.36/1.29  tff(c_221, plain, (![B_89, A_90]: (k4_xboole_0(k1_relat_1(B_89), k1_relat_1(k7_relat_1(B_89, A_90)))=k4_xboole_0(k1_relat_1(B_89), A_90) | ~v1_relat_1(B_89) | ~v1_relat_1(B_89) | ~v1_relat_1(B_89))), inference(superposition, [status(thm), theory('equality')], [c_197, c_85])).
% 2.36/1.29  tff(c_28, plain, (k6_subset_1(k1_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k1_relat_1(k6_subset_1('#skF_2', k7_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.36/1.29  tff(c_31, plain, (k4_xboole_0(k1_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_16, c_28])).
% 2.36/1.29  tff(c_227, plain, (k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_221, c_31])).
% 2.36/1.29  tff(c_242, plain, (k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_30, c_30, c_227])).
% 2.36/1.29  tff(c_247, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_32, c_242])).
% 2.36/1.29  tff(c_251, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_247])).
% 2.36/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/1.29  
% 2.36/1.29  Inference rules
% 2.36/1.29  ----------------------
% 2.36/1.29  #Ref     : 0
% 2.36/1.29  #Sup     : 54
% 2.36/1.29  #Fact    : 0
% 2.36/1.29  #Define  : 0
% 2.36/1.29  #Split   : 0
% 2.36/1.29  #Chain   : 0
% 2.36/1.29  #Close   : 0
% 2.36/1.29  
% 2.36/1.29  Ordering : KBO
% 2.36/1.29  
% 2.36/1.29  Simplification rules
% 2.36/1.29  ----------------------
% 2.36/1.29  #Subsume      : 1
% 2.36/1.29  #Demod        : 8
% 2.36/1.29  #Tautology    : 33
% 2.36/1.29  #SimpNegUnit  : 0
% 2.36/1.29  #BackRed      : 0
% 2.36/1.29  
% 2.36/1.29  #Partial instantiations: 0
% 2.36/1.29  #Strategies tried      : 1
% 2.36/1.29  
% 2.36/1.29  Timing (in seconds)
% 2.36/1.29  ----------------------
% 2.36/1.29  Preprocessing        : 0.30
% 2.36/1.29  Parsing              : 0.16
% 2.36/1.29  CNF conversion       : 0.02
% 2.36/1.29  Main loop            : 0.17
% 2.36/1.29  Inferencing          : 0.08
% 2.36/1.29  Reduction            : 0.05
% 2.36/1.29  Demodulation         : 0.04
% 2.36/1.29  BG Simplification    : 0.02
% 2.36/1.29  Subsumption          : 0.02
% 2.36/1.29  Abstraction          : 0.01
% 2.36/1.29  MUC search           : 0.00
% 2.36/1.29  Cooper               : 0.00
% 2.36/1.29  Total                : 0.50
% 2.36/1.29  Index Insertion      : 0.00
% 2.36/1.29  Index Deletion       : 0.00
% 2.36/1.29  Index Matching       : 0.00
% 2.36/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
