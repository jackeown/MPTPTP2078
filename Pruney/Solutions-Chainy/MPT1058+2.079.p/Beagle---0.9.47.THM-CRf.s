%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:32 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   52 (  60 expanded)
%              Number of leaves         :   32 (  37 expanded)
%              Depth                    :    9
%              Number of atoms          :   54 (  71 expanded)
%              Number of equality atoms :   24 (  29 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

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

tff(f_81,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_tarski(k10_relat_1(A,C),B)
           => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_61,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_71,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k10_relat_1(k5_relat_1(B,C),A) = k10_relat_1(B,k10_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t181_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(c_34,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') != k10_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_40,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_28,plain,(
    ! [A_42] : v1_relat_1(k6_relat_1(A_42)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_22,plain,(
    ! [A_39] : k1_relat_1(k6_relat_1(A_39)) = A_39 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_32,plain,(
    ! [B_44,A_43] : k5_relat_1(k6_relat_1(B_44),k6_relat_1(A_43)) = k6_relat_1(k3_xboole_0(A_43,B_44)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_145,plain,(
    ! [A_70,B_71] :
      ( k10_relat_1(A_70,k1_relat_1(B_71)) = k1_relat_1(k5_relat_1(A_70,B_71))
      | ~ v1_relat_1(B_71)
      | ~ v1_relat_1(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_154,plain,(
    ! [A_70,A_39] :
      ( k1_relat_1(k5_relat_1(A_70,k6_relat_1(A_39))) = k10_relat_1(A_70,A_39)
      | ~ v1_relat_1(k6_relat_1(A_39))
      | ~ v1_relat_1(A_70) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_145])).

tff(c_168,plain,(
    ! [A_77,A_78] :
      ( k1_relat_1(k5_relat_1(A_77,k6_relat_1(A_78))) = k10_relat_1(A_77,A_78)
      | ~ v1_relat_1(A_77) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_154])).

tff(c_180,plain,(
    ! [A_43,B_44] :
      ( k1_relat_1(k6_relat_1(k3_xboole_0(A_43,B_44))) = k10_relat_1(k6_relat_1(B_44),A_43)
      | ~ v1_relat_1(k6_relat_1(B_44)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_168])).

tff(c_188,plain,(
    ! [B_44,A_43] : k10_relat_1(k6_relat_1(B_44),A_43) = k3_xboole_0(A_43,B_44) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_22,c_180])).

tff(c_26,plain,(
    ! [A_40,B_41] :
      ( k5_relat_1(k6_relat_1(A_40),B_41) = k7_relat_1(B_41,A_40)
      | ~ v1_relat_1(B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_245,plain,(
    ! [B_83,C_84,A_85] :
      ( k10_relat_1(k5_relat_1(B_83,C_84),A_85) = k10_relat_1(B_83,k10_relat_1(C_84,A_85))
      | ~ v1_relat_1(C_84)
      | ~ v1_relat_1(B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_265,plain,(
    ! [A_40,B_41,A_85] :
      ( k10_relat_1(k6_relat_1(A_40),k10_relat_1(B_41,A_85)) = k10_relat_1(k7_relat_1(B_41,A_40),A_85)
      | ~ v1_relat_1(B_41)
      | ~ v1_relat_1(k6_relat_1(A_40))
      | ~ v1_relat_1(B_41) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_245])).

tff(c_292,plain,(
    ! [B_89,A_90,A_91] :
      ( k3_xboole_0(k10_relat_1(B_89,A_90),A_91) = k10_relat_1(k7_relat_1(B_89,A_91),A_90)
      | ~ v1_relat_1(B_89) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_188,c_265])).

tff(c_36,plain,(
    r1_tarski(k10_relat_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_79,plain,(
    ! [A_55,B_56] :
      ( k3_xboole_0(A_55,B_56) = A_55
      | ~ r1_tarski(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_83,plain,(
    k3_xboole_0(k10_relat_1('#skF_1','#skF_3'),'#skF_2') = k10_relat_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_79])).

tff(c_301,plain,
    ( k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_292,c_83])).

tff(c_319,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_301])).

tff(c_321,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_319])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:29:55 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.27  
% 2.23/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.27  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.23/1.27  
% 2.23/1.27  %Foreground sorts:
% 2.23/1.27  
% 2.23/1.27  
% 2.23/1.27  %Background operators:
% 2.23/1.27  
% 2.23/1.27  
% 2.23/1.27  %Foreground operators:
% 2.23/1.27  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.23/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.23/1.27  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.23/1.27  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.23/1.27  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.23/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.23/1.27  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.23/1.27  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.23/1.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.23/1.27  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.23/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.23/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.23/1.27  tff('#skF_1', type, '#skF_1': $i).
% 2.23/1.27  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.23/1.27  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.23/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.23/1.27  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.23/1.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.23/1.27  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.23/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.23/1.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.23/1.27  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.23/1.27  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.23/1.27  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.23/1.27  
% 2.23/1.28  tff(f_81, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_funct_2)).
% 2.23/1.28  tff(f_69, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.23/1.28  tff(f_61, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.23/1.28  tff(f_71, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 2.23/1.28  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 2.23/1.28  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 2.23/1.28  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k10_relat_1(k5_relat_1(B, C), A) = k10_relat_1(B, k10_relat_1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t181_relat_1)).
% 2.23/1.28  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.23/1.28  tff(c_34, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')!=k10_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.23/1.28  tff(c_40, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.23/1.28  tff(c_28, plain, (![A_42]: (v1_relat_1(k6_relat_1(A_42)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.23/1.28  tff(c_22, plain, (![A_39]: (k1_relat_1(k6_relat_1(A_39))=A_39)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.23/1.28  tff(c_32, plain, (![B_44, A_43]: (k5_relat_1(k6_relat_1(B_44), k6_relat_1(A_43))=k6_relat_1(k3_xboole_0(A_43, B_44)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.23/1.28  tff(c_145, plain, (![A_70, B_71]: (k10_relat_1(A_70, k1_relat_1(B_71))=k1_relat_1(k5_relat_1(A_70, B_71)) | ~v1_relat_1(B_71) | ~v1_relat_1(A_70))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.23/1.28  tff(c_154, plain, (![A_70, A_39]: (k1_relat_1(k5_relat_1(A_70, k6_relat_1(A_39)))=k10_relat_1(A_70, A_39) | ~v1_relat_1(k6_relat_1(A_39)) | ~v1_relat_1(A_70))), inference(superposition, [status(thm), theory('equality')], [c_22, c_145])).
% 2.23/1.28  tff(c_168, plain, (![A_77, A_78]: (k1_relat_1(k5_relat_1(A_77, k6_relat_1(A_78)))=k10_relat_1(A_77, A_78) | ~v1_relat_1(A_77))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_154])).
% 2.23/1.28  tff(c_180, plain, (![A_43, B_44]: (k1_relat_1(k6_relat_1(k3_xboole_0(A_43, B_44)))=k10_relat_1(k6_relat_1(B_44), A_43) | ~v1_relat_1(k6_relat_1(B_44)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_168])).
% 2.23/1.28  tff(c_188, plain, (![B_44, A_43]: (k10_relat_1(k6_relat_1(B_44), A_43)=k3_xboole_0(A_43, B_44))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_22, c_180])).
% 2.23/1.28  tff(c_26, plain, (![A_40, B_41]: (k5_relat_1(k6_relat_1(A_40), B_41)=k7_relat_1(B_41, A_40) | ~v1_relat_1(B_41))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.23/1.28  tff(c_245, plain, (![B_83, C_84, A_85]: (k10_relat_1(k5_relat_1(B_83, C_84), A_85)=k10_relat_1(B_83, k10_relat_1(C_84, A_85)) | ~v1_relat_1(C_84) | ~v1_relat_1(B_83))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.23/1.28  tff(c_265, plain, (![A_40, B_41, A_85]: (k10_relat_1(k6_relat_1(A_40), k10_relat_1(B_41, A_85))=k10_relat_1(k7_relat_1(B_41, A_40), A_85) | ~v1_relat_1(B_41) | ~v1_relat_1(k6_relat_1(A_40)) | ~v1_relat_1(B_41))), inference(superposition, [status(thm), theory('equality')], [c_26, c_245])).
% 2.23/1.28  tff(c_292, plain, (![B_89, A_90, A_91]: (k3_xboole_0(k10_relat_1(B_89, A_90), A_91)=k10_relat_1(k7_relat_1(B_89, A_91), A_90) | ~v1_relat_1(B_89))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_188, c_265])).
% 2.23/1.28  tff(c_36, plain, (r1_tarski(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.23/1.28  tff(c_79, plain, (![A_55, B_56]: (k3_xboole_0(A_55, B_56)=A_55 | ~r1_tarski(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.23/1.28  tff(c_83, plain, (k3_xboole_0(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')=k10_relat_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_36, c_79])).
% 2.23/1.28  tff(c_301, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_292, c_83])).
% 2.23/1.28  tff(c_319, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_301])).
% 2.23/1.28  tff(c_321, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_319])).
% 2.23/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.28  
% 2.23/1.28  Inference rules
% 2.23/1.28  ----------------------
% 2.23/1.28  #Ref     : 0
% 2.23/1.28  #Sup     : 63
% 2.23/1.28  #Fact    : 0
% 2.23/1.28  #Define  : 0
% 2.23/1.28  #Split   : 0
% 2.23/1.28  #Chain   : 0
% 2.23/1.28  #Close   : 0
% 2.23/1.28  
% 2.23/1.28  Ordering : KBO
% 2.23/1.28  
% 2.23/1.28  Simplification rules
% 2.23/1.28  ----------------------
% 2.23/1.28  #Subsume      : 1
% 2.23/1.28  #Demod        : 38
% 2.23/1.28  #Tautology    : 42
% 2.23/1.28  #SimpNegUnit  : 1
% 2.23/1.28  #BackRed      : 0
% 2.23/1.28  
% 2.23/1.28  #Partial instantiations: 0
% 2.23/1.28  #Strategies tried      : 1
% 2.23/1.28  
% 2.23/1.28  Timing (in seconds)
% 2.23/1.28  ----------------------
% 2.23/1.29  Preprocessing        : 0.33
% 2.23/1.29  Parsing              : 0.17
% 2.23/1.29  CNF conversion       : 0.02
% 2.23/1.29  Main loop            : 0.20
% 2.23/1.29  Inferencing          : 0.08
% 2.23/1.29  Reduction            : 0.07
% 2.23/1.29  Demodulation         : 0.05
% 2.23/1.29  BG Simplification    : 0.02
% 2.23/1.29  Subsumption          : 0.02
% 2.23/1.29  Abstraction          : 0.02
% 2.23/1.29  MUC search           : 0.00
% 2.23/1.29  Cooper               : 0.00
% 2.23/1.29  Total                : 0.55
% 2.23/1.29  Index Insertion      : 0.00
% 2.23/1.29  Index Deletion       : 0.00
% 2.23/1.29  Index Matching       : 0.00
% 2.23/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
