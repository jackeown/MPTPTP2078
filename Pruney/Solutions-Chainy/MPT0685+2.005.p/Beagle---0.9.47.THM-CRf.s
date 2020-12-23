%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:31 EST 2020

% Result     : Theorem 5.10s
% Output     : CNFRefutation 5.45s
% Verified   : 
% Statistics : Number of formulae       :   46 (  53 expanded)
%              Number of leaves         :   28 (  32 expanded)
%              Depth                    :    9
%              Number of atoms          :   48 (  59 expanded)
%              Number of equality atoms :   22 (  26 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_53,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_63,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k10_relat_1(k5_relat_1(B,C),A) = k10_relat_1(B,k10_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t181_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_30,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_22,plain,(
    ! [A_24] : v1_relat_1(k6_relat_1(A_24)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_16,plain,(
    ! [A_21] : k1_relat_1(k6_relat_1(A_21)) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_26,plain,(
    ! [B_26,A_25] : k5_relat_1(k6_relat_1(B_26),k6_relat_1(A_25)) = k6_relat_1(k3_xboole_0(A_25,B_26)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_159,plain,(
    ! [A_50,B_51] :
      ( k10_relat_1(A_50,k1_relat_1(B_51)) = k1_relat_1(k5_relat_1(A_50,B_51))
      | ~ v1_relat_1(B_51)
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_168,plain,(
    ! [A_50,A_21] :
      ( k1_relat_1(k5_relat_1(A_50,k6_relat_1(A_21))) = k10_relat_1(A_50,A_21)
      | ~ v1_relat_1(k6_relat_1(A_21))
      | ~ v1_relat_1(A_50) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_159])).

tff(c_173,plain,(
    ! [A_52,A_53] :
      ( k1_relat_1(k5_relat_1(A_52,k6_relat_1(A_53))) = k10_relat_1(A_52,A_53)
      | ~ v1_relat_1(A_52) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_168])).

tff(c_185,plain,(
    ! [A_25,B_26] :
      ( k1_relat_1(k6_relat_1(k3_xboole_0(A_25,B_26))) = k10_relat_1(k6_relat_1(B_26),A_25)
      | ~ v1_relat_1(k6_relat_1(B_26)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_173])).

tff(c_193,plain,(
    ! [B_26,A_25] : k10_relat_1(k6_relat_1(B_26),A_25) = k3_xboole_0(A_25,B_26) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_16,c_185])).

tff(c_20,plain,(
    ! [A_22,B_23] :
      ( k5_relat_1(k6_relat_1(A_22),B_23) = k7_relat_1(B_23,A_22)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_218,plain,(
    ! [B_56,C_57,A_58] :
      ( k10_relat_1(k5_relat_1(B_56,C_57),A_58) = k10_relat_1(B_56,k10_relat_1(C_57,A_58))
      | ~ v1_relat_1(C_57)
      | ~ v1_relat_1(B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_238,plain,(
    ! [A_22,B_23,A_58] :
      ( k10_relat_1(k6_relat_1(A_22),k10_relat_1(B_23,A_58)) = k10_relat_1(k7_relat_1(B_23,A_22),A_58)
      | ~ v1_relat_1(B_23)
      | ~ v1_relat_1(k6_relat_1(A_22))
      | ~ v1_relat_1(B_23) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_218])).

tff(c_1772,plain,(
    ! [B_86,A_87,A_88] :
      ( k3_xboole_0(k10_relat_1(B_86,A_87),A_88) = k10_relat_1(k7_relat_1(B_86,A_88),A_87)
      | ~ v1_relat_1(B_86) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_193,c_238])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_2592,plain,(
    ! [A_103,B_104,A_105] :
      ( k3_xboole_0(A_103,k10_relat_1(B_104,A_105)) = k10_relat_1(k7_relat_1(B_104,A_103),A_105)
      | ~ v1_relat_1(B_104) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1772,c_2])).

tff(c_28,plain,(
    k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2')) != k10_relat_1(k7_relat_1('#skF_3','#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2664,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2592,c_28])).

tff(c_2726,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_2664])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:00:35 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.10/1.99  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.10/1.99  
% 5.10/1.99  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.10/1.99  %$ v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 5.10/1.99  
% 5.10/1.99  %Foreground sorts:
% 5.10/1.99  
% 5.10/1.99  
% 5.10/1.99  %Background operators:
% 5.10/1.99  
% 5.10/1.99  
% 5.10/1.99  %Foreground operators:
% 5.10/1.99  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.10/1.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.10/1.99  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.10/1.99  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.10/1.99  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.10/1.99  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.10/1.99  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.10/1.99  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.10/1.99  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.10/1.99  tff('#skF_2', type, '#skF_2': $i).
% 5.10/1.99  tff('#skF_3', type, '#skF_3': $i).
% 5.10/1.99  tff('#skF_1', type, '#skF_1': $i).
% 5.10/1.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.10/1.99  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 5.10/1.99  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.10/1.99  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.10/1.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.10/1.99  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.10/1.99  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.10/1.99  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.10/1.99  
% 5.45/2.00  tff(f_68, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 5.45/2.00  tff(f_61, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 5.45/2.00  tff(f_53, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 5.45/2.00  tff(f_63, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 5.45/2.00  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 5.45/2.00  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 5.45/2.00  tff(f_42, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k10_relat_1(k5_relat_1(B, C), A) = k10_relat_1(B, k10_relat_1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t181_relat_1)).
% 5.45/2.00  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.45/2.00  tff(c_30, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.45/2.00  tff(c_22, plain, (![A_24]: (v1_relat_1(k6_relat_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.45/2.00  tff(c_16, plain, (![A_21]: (k1_relat_1(k6_relat_1(A_21))=A_21)), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.45/2.00  tff(c_26, plain, (![B_26, A_25]: (k5_relat_1(k6_relat_1(B_26), k6_relat_1(A_25))=k6_relat_1(k3_xboole_0(A_25, B_26)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.45/2.00  tff(c_159, plain, (![A_50, B_51]: (k10_relat_1(A_50, k1_relat_1(B_51))=k1_relat_1(k5_relat_1(A_50, B_51)) | ~v1_relat_1(B_51) | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.45/2.00  tff(c_168, plain, (![A_50, A_21]: (k1_relat_1(k5_relat_1(A_50, k6_relat_1(A_21)))=k10_relat_1(A_50, A_21) | ~v1_relat_1(k6_relat_1(A_21)) | ~v1_relat_1(A_50))), inference(superposition, [status(thm), theory('equality')], [c_16, c_159])).
% 5.45/2.00  tff(c_173, plain, (![A_52, A_53]: (k1_relat_1(k5_relat_1(A_52, k6_relat_1(A_53)))=k10_relat_1(A_52, A_53) | ~v1_relat_1(A_52))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_168])).
% 5.45/2.00  tff(c_185, plain, (![A_25, B_26]: (k1_relat_1(k6_relat_1(k3_xboole_0(A_25, B_26)))=k10_relat_1(k6_relat_1(B_26), A_25) | ~v1_relat_1(k6_relat_1(B_26)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_173])).
% 5.45/2.00  tff(c_193, plain, (![B_26, A_25]: (k10_relat_1(k6_relat_1(B_26), A_25)=k3_xboole_0(A_25, B_26))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_16, c_185])).
% 5.45/2.00  tff(c_20, plain, (![A_22, B_23]: (k5_relat_1(k6_relat_1(A_22), B_23)=k7_relat_1(B_23, A_22) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.45/2.00  tff(c_218, plain, (![B_56, C_57, A_58]: (k10_relat_1(k5_relat_1(B_56, C_57), A_58)=k10_relat_1(B_56, k10_relat_1(C_57, A_58)) | ~v1_relat_1(C_57) | ~v1_relat_1(B_56))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.45/2.00  tff(c_238, plain, (![A_22, B_23, A_58]: (k10_relat_1(k6_relat_1(A_22), k10_relat_1(B_23, A_58))=k10_relat_1(k7_relat_1(B_23, A_22), A_58) | ~v1_relat_1(B_23) | ~v1_relat_1(k6_relat_1(A_22)) | ~v1_relat_1(B_23))), inference(superposition, [status(thm), theory('equality')], [c_20, c_218])).
% 5.45/2.00  tff(c_1772, plain, (![B_86, A_87, A_88]: (k3_xboole_0(k10_relat_1(B_86, A_87), A_88)=k10_relat_1(k7_relat_1(B_86, A_88), A_87) | ~v1_relat_1(B_86))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_193, c_238])).
% 5.45/2.00  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.45/2.00  tff(c_2592, plain, (![A_103, B_104, A_105]: (k3_xboole_0(A_103, k10_relat_1(B_104, A_105))=k10_relat_1(k7_relat_1(B_104, A_103), A_105) | ~v1_relat_1(B_104))), inference(superposition, [status(thm), theory('equality')], [c_1772, c_2])).
% 5.45/2.00  tff(c_28, plain, (k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))!=k10_relat_1(k7_relat_1('#skF_3', '#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.45/2.00  tff(c_2664, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2592, c_28])).
% 5.45/2.00  tff(c_2726, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_2664])).
% 5.45/2.00  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.45/2.00  
% 5.45/2.00  Inference rules
% 5.45/2.00  ----------------------
% 5.45/2.00  #Ref     : 0
% 5.45/2.00  #Sup     : 702
% 5.45/2.00  #Fact    : 0
% 5.45/2.00  #Define  : 0
% 5.45/2.00  #Split   : 0
% 5.45/2.00  #Chain   : 0
% 5.45/2.00  #Close   : 0
% 5.45/2.00  
% 5.45/2.00  Ordering : KBO
% 5.45/2.00  
% 5.45/2.00  Simplification rules
% 5.45/2.00  ----------------------
% 5.45/2.00  #Subsume      : 130
% 5.45/2.00  #Demod        : 413
% 5.45/2.00  #Tautology    : 144
% 5.45/2.00  #SimpNegUnit  : 0
% 5.45/2.00  #BackRed      : 0
% 5.45/2.00  
% 5.45/2.00  #Partial instantiations: 0
% 5.45/2.00  #Strategies tried      : 1
% 5.45/2.00  
% 5.45/2.00  Timing (in seconds)
% 5.45/2.00  ----------------------
% 5.45/2.00  Preprocessing        : 0.30
% 5.45/2.00  Parsing              : 0.17
% 5.45/2.00  CNF conversion       : 0.02
% 5.45/2.00  Main loop            : 0.94
% 5.45/2.00  Inferencing          : 0.23
% 5.45/2.00  Reduction            : 0.54
% 5.45/2.00  Demodulation         : 0.49
% 5.45/2.00  BG Simplification    : 0.04
% 5.45/2.00  Subsumption          : 0.09
% 5.45/2.00  Abstraction          : 0.06
% 5.45/2.00  MUC search           : 0.00
% 5.45/2.01  Cooper               : 0.00
% 5.45/2.01  Total                : 1.26
% 5.45/2.01  Index Insertion      : 0.00
% 5.45/2.01  Index Deletion       : 0.00
% 5.45/2.01  Index Matching       : 0.00
% 5.45/2.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------
