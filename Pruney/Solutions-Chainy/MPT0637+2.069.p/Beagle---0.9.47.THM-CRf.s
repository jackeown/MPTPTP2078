%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:33 EST 2020

% Result     : Theorem 2.86s
% Output     : CNFRefutation 2.86s
% Verified   : 
% Statistics : Number of formulae       :   53 (  71 expanded)
%              Number of leaves         :   30 (  39 expanded)
%              Depth                    :    8
%              Number of atoms          :   57 (  86 expanded)
%              Number of equality atoms :   28 (  35 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_104,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_90,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_100,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_96,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_107,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_40,plain,(
    ! [A_43] : v1_relat_1(k6_relat_1(A_43)) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_32,plain,(
    ! [A_38] : k2_relat_1(k6_relat_1(A_38)) = A_38 ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_174,plain,(
    ! [A_66,B_67] :
      ( k5_relat_1(k6_relat_1(A_66),B_67) = k7_relat_1(B_67,A_66)
      | ~ v1_relat_1(B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_36,plain,(
    ! [A_40] :
      ( k5_relat_1(A_40,k6_relat_1(k2_relat_1(A_40))) = A_40
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_192,plain,(
    ! [A_66] :
      ( k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_66))),A_66) = k6_relat_1(A_66)
      | ~ v1_relat_1(k6_relat_1(A_66))
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_66)))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_174,c_36])).

tff(c_218,plain,(
    ! [A_66] : k7_relat_1(k6_relat_1(A_66),A_66) = k6_relat_1(A_66) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_40,c_32,c_192])).

tff(c_551,plain,(
    ! [C_98,A_99,B_100] :
      ( k7_relat_1(k7_relat_1(C_98,A_99),B_100) = k7_relat_1(C_98,k3_xboole_0(A_99,B_100))
      | ~ v1_relat_1(C_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_572,plain,(
    ! [A_66,B_100] :
      ( k7_relat_1(k6_relat_1(A_66),k3_xboole_0(A_66,B_100)) = k7_relat_1(k6_relat_1(A_66),B_100)
      | ~ v1_relat_1(k6_relat_1(A_66)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_218,c_551])).

tff(c_828,plain,(
    ! [A_115,B_116] : k7_relat_1(k6_relat_1(A_115),k3_xboole_0(A_115,B_116)) = k7_relat_1(k6_relat_1(A_115),B_116) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_572])).

tff(c_18,plain,(
    ! [B_20,A_19] :
      ( k5_relat_1(B_20,k6_relat_1(A_19)) = k8_relat_1(A_19,B_20)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_202,plain,(
    ! [A_19,A_66] :
      ( k8_relat_1(A_19,k6_relat_1(A_66)) = k7_relat_1(k6_relat_1(A_19),A_66)
      | ~ v1_relat_1(k6_relat_1(A_19))
      | ~ v1_relat_1(k6_relat_1(A_66)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_174])).

tff(c_223,plain,(
    ! [A_19,A_66] : k8_relat_1(A_19,k6_relat_1(A_66)) = k7_relat_1(k6_relat_1(A_19),A_66) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_40,c_202])).

tff(c_262,plain,(
    ! [A_74,B_75] :
      ( k8_relat_1(A_74,B_75) = B_75
      | ~ r1_tarski(k2_relat_1(B_75),A_74)
      | ~ v1_relat_1(B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_265,plain,(
    ! [A_74,A_38] :
      ( k8_relat_1(A_74,k6_relat_1(A_38)) = k6_relat_1(A_38)
      | ~ r1_tarski(A_38,A_74)
      | ~ v1_relat_1(k6_relat_1(A_38)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_262])).

tff(c_267,plain,(
    ! [A_74,A_38] :
      ( k8_relat_1(A_74,k6_relat_1(A_38)) = k6_relat_1(A_38)
      | ~ r1_tarski(A_38,A_74) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_265])).

tff(c_326,plain,(
    ! [A_74,A_38] :
      ( k7_relat_1(k6_relat_1(A_74),A_38) = k6_relat_1(A_38)
      | ~ r1_tarski(A_38,A_74) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_267])).

tff(c_849,plain,(
    ! [A_115,B_116] :
      ( k7_relat_1(k6_relat_1(A_115),B_116) = k6_relat_1(k3_xboole_0(A_115,B_116))
      | ~ r1_tarski(k3_xboole_0(A_115,B_116),A_115) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_828,c_326])).

tff(c_885,plain,(
    ! [A_115,B_116] : k7_relat_1(k6_relat_1(A_115),B_116) = k6_relat_1(k3_xboole_0(A_115,B_116)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_849])).

tff(c_44,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_195,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_174,c_44])).

tff(c_220,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_195])).

tff(c_1131,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_885,c_220])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:10:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.86/1.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.86/1.47  
% 2.86/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.86/1.48  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.86/1.48  
% 2.86/1.48  %Foreground sorts:
% 2.86/1.48  
% 2.86/1.48  
% 2.86/1.48  %Background operators:
% 2.86/1.48  
% 2.86/1.48  
% 2.86/1.48  %Foreground operators:
% 2.86/1.48  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.86/1.48  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.86/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.86/1.48  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.86/1.48  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.86/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.86/1.48  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.86/1.48  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.86/1.48  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.86/1.48  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.86/1.48  tff('#skF_2', type, '#skF_2': $i).
% 2.86/1.48  tff('#skF_1', type, '#skF_1': $i).
% 2.86/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.86/1.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.86/1.48  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.86/1.48  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.86/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.86/1.48  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.86/1.48  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.86/1.48  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 2.86/1.48  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.86/1.48  
% 2.86/1.49  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.86/1.49  tff(f_104, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.86/1.49  tff(f_90, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.86/1.49  tff(f_100, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 2.86/1.49  tff(f_96, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 2.86/1.49  tff(f_47, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 2.86/1.49  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 2.86/1.49  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_relat_1)).
% 2.86/1.49  tff(f_107, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 2.86/1.49  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.86/1.49  tff(c_40, plain, (![A_43]: (v1_relat_1(k6_relat_1(A_43)))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.86/1.49  tff(c_32, plain, (![A_38]: (k2_relat_1(k6_relat_1(A_38))=A_38)), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.86/1.49  tff(c_174, plain, (![A_66, B_67]: (k5_relat_1(k6_relat_1(A_66), B_67)=k7_relat_1(B_67, A_66) | ~v1_relat_1(B_67))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.86/1.49  tff(c_36, plain, (![A_40]: (k5_relat_1(A_40, k6_relat_1(k2_relat_1(A_40)))=A_40 | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.86/1.49  tff(c_192, plain, (![A_66]: (k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_66))), A_66)=k6_relat_1(A_66) | ~v1_relat_1(k6_relat_1(A_66)) | ~v1_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_66)))))), inference(superposition, [status(thm), theory('equality')], [c_174, c_36])).
% 2.86/1.49  tff(c_218, plain, (![A_66]: (k7_relat_1(k6_relat_1(A_66), A_66)=k6_relat_1(A_66))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_40, c_32, c_192])).
% 2.86/1.49  tff(c_551, plain, (![C_98, A_99, B_100]: (k7_relat_1(k7_relat_1(C_98, A_99), B_100)=k7_relat_1(C_98, k3_xboole_0(A_99, B_100)) | ~v1_relat_1(C_98))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.86/1.49  tff(c_572, plain, (![A_66, B_100]: (k7_relat_1(k6_relat_1(A_66), k3_xboole_0(A_66, B_100))=k7_relat_1(k6_relat_1(A_66), B_100) | ~v1_relat_1(k6_relat_1(A_66)))), inference(superposition, [status(thm), theory('equality')], [c_218, c_551])).
% 2.86/1.49  tff(c_828, plain, (![A_115, B_116]: (k7_relat_1(k6_relat_1(A_115), k3_xboole_0(A_115, B_116))=k7_relat_1(k6_relat_1(A_115), B_116))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_572])).
% 2.86/1.49  tff(c_18, plain, (![B_20, A_19]: (k5_relat_1(B_20, k6_relat_1(A_19))=k8_relat_1(A_19, B_20) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.86/1.49  tff(c_202, plain, (![A_19, A_66]: (k8_relat_1(A_19, k6_relat_1(A_66))=k7_relat_1(k6_relat_1(A_19), A_66) | ~v1_relat_1(k6_relat_1(A_19)) | ~v1_relat_1(k6_relat_1(A_66)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_174])).
% 2.86/1.49  tff(c_223, plain, (![A_19, A_66]: (k8_relat_1(A_19, k6_relat_1(A_66))=k7_relat_1(k6_relat_1(A_19), A_66))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_40, c_202])).
% 2.86/1.49  tff(c_262, plain, (![A_74, B_75]: (k8_relat_1(A_74, B_75)=B_75 | ~r1_tarski(k2_relat_1(B_75), A_74) | ~v1_relat_1(B_75))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.86/1.49  tff(c_265, plain, (![A_74, A_38]: (k8_relat_1(A_74, k6_relat_1(A_38))=k6_relat_1(A_38) | ~r1_tarski(A_38, A_74) | ~v1_relat_1(k6_relat_1(A_38)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_262])).
% 2.86/1.49  tff(c_267, plain, (![A_74, A_38]: (k8_relat_1(A_74, k6_relat_1(A_38))=k6_relat_1(A_38) | ~r1_tarski(A_38, A_74))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_265])).
% 2.86/1.49  tff(c_326, plain, (![A_74, A_38]: (k7_relat_1(k6_relat_1(A_74), A_38)=k6_relat_1(A_38) | ~r1_tarski(A_38, A_74))), inference(demodulation, [status(thm), theory('equality')], [c_223, c_267])).
% 2.86/1.49  tff(c_849, plain, (![A_115, B_116]: (k7_relat_1(k6_relat_1(A_115), B_116)=k6_relat_1(k3_xboole_0(A_115, B_116)) | ~r1_tarski(k3_xboole_0(A_115, B_116), A_115))), inference(superposition, [status(thm), theory('equality')], [c_828, c_326])).
% 2.86/1.49  tff(c_885, plain, (![A_115, B_116]: (k7_relat_1(k6_relat_1(A_115), B_116)=k6_relat_1(k3_xboole_0(A_115, B_116)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_849])).
% 2.86/1.49  tff(c_44, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.86/1.49  tff(c_195, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_174, c_44])).
% 2.86/1.49  tff(c_220, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_195])).
% 2.86/1.49  tff(c_1131, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_885, c_220])).
% 2.86/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.86/1.49  
% 2.86/1.49  Inference rules
% 2.86/1.49  ----------------------
% 2.86/1.49  #Ref     : 0
% 2.86/1.49  #Sup     : 248
% 2.86/1.49  #Fact    : 0
% 2.86/1.49  #Define  : 0
% 2.86/1.49  #Split   : 1
% 2.86/1.49  #Chain   : 0
% 2.86/1.49  #Close   : 0
% 2.86/1.49  
% 2.86/1.49  Ordering : KBO
% 2.86/1.49  
% 2.86/1.49  Simplification rules
% 2.86/1.49  ----------------------
% 2.86/1.49  #Subsume      : 13
% 2.86/1.49  #Demod        : 186
% 2.86/1.49  #Tautology    : 129
% 2.86/1.49  #SimpNegUnit  : 0
% 2.86/1.49  #BackRed      : 10
% 2.86/1.49  
% 2.86/1.49  #Partial instantiations: 0
% 2.86/1.49  #Strategies tried      : 1
% 2.86/1.49  
% 2.86/1.49  Timing (in seconds)
% 2.86/1.49  ----------------------
% 2.86/1.49  Preprocessing        : 0.33
% 2.86/1.49  Parsing              : 0.18
% 2.86/1.49  CNF conversion       : 0.02
% 2.86/1.49  Main loop            : 0.36
% 2.86/1.49  Inferencing          : 0.14
% 2.86/1.49  Reduction            : 0.12
% 2.86/1.49  Demodulation         : 0.09
% 2.86/1.49  BG Simplification    : 0.02
% 2.86/1.49  Subsumption          : 0.05
% 2.86/1.49  Abstraction          : 0.03
% 2.86/1.49  MUC search           : 0.00
% 2.86/1.49  Cooper               : 0.00
% 2.86/1.49  Total                : 0.72
% 2.86/1.49  Index Insertion      : 0.00
% 2.86/1.49  Index Deletion       : 0.00
% 2.86/1.49  Index Matching       : 0.00
% 2.86/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
