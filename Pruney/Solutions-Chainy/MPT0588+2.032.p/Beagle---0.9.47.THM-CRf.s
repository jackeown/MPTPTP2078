%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:07 EST 2020

% Result     : Theorem 3.48s
% Output     : CNFRefutation 3.48s
% Verified   : 
% Statistics : Number of formulae       :   59 (  66 expanded)
%              Number of leaves         :   33 (  37 expanded)
%              Depth                    :   11
%              Number of atoms          :   55 (  64 expanded)
%              Number of equality atoms :   29 (  35 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_72,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k7_relat_1(B,A) = k7_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_relat_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_35,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,C,B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_49,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_36,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_26,plain,(
    ! [A_43,B_44] :
      ( v1_relat_1(k7_relat_1(A_43,B_44))
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_30,plain,(
    ! [B_49,A_48] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_49,A_48)),k1_relat_1(B_49))
      | ~ v1_relat_1(B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_200,plain,(
    ! [B_75,A_76] :
      ( k7_relat_1(B_75,A_76) = B_75
      | ~ r1_tarski(k1_relat_1(B_75),A_76)
      | ~ v1_relat_1(B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_887,plain,(
    ! [B_136,A_137] :
      ( k7_relat_1(k7_relat_1(B_136,A_137),k1_relat_1(B_136)) = k7_relat_1(B_136,A_137)
      | ~ v1_relat_1(k7_relat_1(B_136,A_137))
      | ~ v1_relat_1(B_136) ) ),
    inference(resolution,[status(thm)],[c_30,c_200])).

tff(c_28,plain,(
    ! [C_47,A_45,B_46] :
      ( k7_relat_1(k7_relat_1(C_47,A_45),B_46) = k7_relat_1(C_47,k3_xboole_0(A_45,B_46))
      | ~ v1_relat_1(C_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2026,plain,(
    ! [B_175,A_176] :
      ( k7_relat_1(B_175,k3_xboole_0(A_176,k1_relat_1(B_175))) = k7_relat_1(B_175,A_176)
      | ~ v1_relat_1(B_175)
      | ~ v1_relat_1(k7_relat_1(B_175,A_176))
      | ~ v1_relat_1(B_175) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_887,c_28])).

tff(c_4,plain,(
    ! [A_5,B_6] : k2_xboole_0(k1_tarski(A_5),k1_tarski(B_6)) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10,plain,(
    ! [A_12,B_13] : k1_enumset1(A_12,A_12,B_13) = k2_tarski(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_11] : k2_tarski(A_11,A_11) = k1_tarski(A_11) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_285,plain,(
    ! [A_86,B_87,C_88,D_89] : k2_xboole_0(k1_tarski(A_86),k1_enumset1(B_87,C_88,D_89)) = k2_enumset1(A_86,B_87,C_88,D_89) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_305,plain,(
    ! [A_90,A_91,B_92] : k2_xboole_0(k1_tarski(A_90),k2_tarski(A_91,B_92)) = k2_enumset1(A_90,A_91,A_91,B_92) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_285])).

tff(c_153,plain,(
    ! [D_71,C_72,B_73,A_74] : k2_enumset1(D_71,C_72,B_73,A_74) = k2_enumset1(A_74,B_73,C_72,D_71) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_14,B_15,C_16] : k2_enumset1(A_14,A_14,B_15,C_16) = k1_enumset1(A_14,B_15,C_16) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_169,plain,(
    ! [D_71,C_72,B_73] : k2_enumset1(D_71,C_72,B_73,B_73) = k1_enumset1(B_73,C_72,D_71) ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_12])).

tff(c_315,plain,(
    ! [A_90,B_92] : k2_xboole_0(k1_tarski(A_90),k2_tarski(B_92,B_92)) = k1_enumset1(B_92,B_92,A_90) ),
    inference(superposition,[status(thm),theory(equality)],[c_305,c_169])).

tff(c_381,plain,(
    ! [B_96,A_97] : k2_tarski(B_96,A_97) = k2_tarski(A_97,B_96) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_10,c_8,c_315])).

tff(c_24,plain,(
    ! [A_41,B_42] : k1_setfam_1(k2_tarski(A_41,B_42)) = k3_xboole_0(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_536,plain,(
    ! [A_107,B_108] : k1_setfam_1(k2_tarski(A_107,B_108)) = k3_xboole_0(B_108,A_107) ),
    inference(superposition,[status(thm),theory(equality)],[c_381,c_24])).

tff(c_542,plain,(
    ! [B_108,A_107] : k3_xboole_0(B_108,A_107) = k3_xboole_0(A_107,B_108) ),
    inference(superposition,[status(thm),theory(equality)],[c_536,c_24])).

tff(c_34,plain,(
    k7_relat_1('#skF_2',k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1')) != k7_relat_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_562,plain,(
    k7_relat_1('#skF_2',k3_xboole_0('#skF_1',k1_relat_1('#skF_2'))) != k7_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_542,c_34])).

tff(c_2048,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2026,c_562])).

tff(c_2088,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2048])).

tff(c_2092,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_2088])).

tff(c_2096,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2092])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:05:12 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.48/1.57  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.48/1.57  
% 3.48/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.48/1.57  %$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 3.48/1.57  
% 3.48/1.57  %Foreground sorts:
% 3.48/1.57  
% 3.48/1.57  
% 3.48/1.57  %Background operators:
% 3.48/1.57  
% 3.48/1.57  
% 3.48/1.57  %Foreground operators:
% 3.48/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.48/1.57  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.48/1.57  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.48/1.57  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.48/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.48/1.57  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.48/1.57  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.48/1.57  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.48/1.57  tff('#skF_2', type, '#skF_2': $i).
% 3.48/1.57  tff('#skF_1', type, '#skF_1': $i).
% 3.48/1.57  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.48/1.57  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.48/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.48/1.57  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.48/1.57  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.48/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.48/1.57  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.48/1.57  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.48/1.57  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.48/1.57  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.48/1.57  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.48/1.57  
% 3.48/1.58  tff(f_72, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k7_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t192_relat_1)).
% 3.48/1.58  tff(f_53, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 3.48/1.58  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t89_relat_1)).
% 3.48/1.58  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 3.48/1.58  tff(f_57, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 3.48/1.58  tff(f_29, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 3.48/1.58  tff(f_35, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.48/1.58  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.48/1.58  tff(f_31, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_enumset1)).
% 3.48/1.58  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, C, B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_enumset1)).
% 3.48/1.58  tff(f_37, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 3.48/1.58  tff(f_49, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.48/1.58  tff(c_36, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.48/1.58  tff(c_26, plain, (![A_43, B_44]: (v1_relat_1(k7_relat_1(A_43, B_44)) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.48/1.58  tff(c_30, plain, (![B_49, A_48]: (r1_tarski(k1_relat_1(k7_relat_1(B_49, A_48)), k1_relat_1(B_49)) | ~v1_relat_1(B_49))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.48/1.58  tff(c_200, plain, (![B_75, A_76]: (k7_relat_1(B_75, A_76)=B_75 | ~r1_tarski(k1_relat_1(B_75), A_76) | ~v1_relat_1(B_75))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.48/1.58  tff(c_887, plain, (![B_136, A_137]: (k7_relat_1(k7_relat_1(B_136, A_137), k1_relat_1(B_136))=k7_relat_1(B_136, A_137) | ~v1_relat_1(k7_relat_1(B_136, A_137)) | ~v1_relat_1(B_136))), inference(resolution, [status(thm)], [c_30, c_200])).
% 3.48/1.58  tff(c_28, plain, (![C_47, A_45, B_46]: (k7_relat_1(k7_relat_1(C_47, A_45), B_46)=k7_relat_1(C_47, k3_xboole_0(A_45, B_46)) | ~v1_relat_1(C_47))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.48/1.58  tff(c_2026, plain, (![B_175, A_176]: (k7_relat_1(B_175, k3_xboole_0(A_176, k1_relat_1(B_175)))=k7_relat_1(B_175, A_176) | ~v1_relat_1(B_175) | ~v1_relat_1(k7_relat_1(B_175, A_176)) | ~v1_relat_1(B_175))), inference(superposition, [status(thm), theory('equality')], [c_887, c_28])).
% 3.48/1.58  tff(c_4, plain, (![A_5, B_6]: (k2_xboole_0(k1_tarski(A_5), k1_tarski(B_6))=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.48/1.58  tff(c_10, plain, (![A_12, B_13]: (k1_enumset1(A_12, A_12, B_13)=k2_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.48/1.58  tff(c_8, plain, (![A_11]: (k2_tarski(A_11, A_11)=k1_tarski(A_11))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.48/1.58  tff(c_285, plain, (![A_86, B_87, C_88, D_89]: (k2_xboole_0(k1_tarski(A_86), k1_enumset1(B_87, C_88, D_89))=k2_enumset1(A_86, B_87, C_88, D_89))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.48/1.58  tff(c_305, plain, (![A_90, A_91, B_92]: (k2_xboole_0(k1_tarski(A_90), k2_tarski(A_91, B_92))=k2_enumset1(A_90, A_91, A_91, B_92))), inference(superposition, [status(thm), theory('equality')], [c_10, c_285])).
% 3.48/1.58  tff(c_153, plain, (![D_71, C_72, B_73, A_74]: (k2_enumset1(D_71, C_72, B_73, A_74)=k2_enumset1(A_74, B_73, C_72, D_71))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.48/1.58  tff(c_12, plain, (![A_14, B_15, C_16]: (k2_enumset1(A_14, A_14, B_15, C_16)=k1_enumset1(A_14, B_15, C_16))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.48/1.58  tff(c_169, plain, (![D_71, C_72, B_73]: (k2_enumset1(D_71, C_72, B_73, B_73)=k1_enumset1(B_73, C_72, D_71))), inference(superposition, [status(thm), theory('equality')], [c_153, c_12])).
% 3.48/1.58  tff(c_315, plain, (![A_90, B_92]: (k2_xboole_0(k1_tarski(A_90), k2_tarski(B_92, B_92))=k1_enumset1(B_92, B_92, A_90))), inference(superposition, [status(thm), theory('equality')], [c_305, c_169])).
% 3.48/1.58  tff(c_381, plain, (![B_96, A_97]: (k2_tarski(B_96, A_97)=k2_tarski(A_97, B_96))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_10, c_8, c_315])).
% 3.48/1.58  tff(c_24, plain, (![A_41, B_42]: (k1_setfam_1(k2_tarski(A_41, B_42))=k3_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.48/1.58  tff(c_536, plain, (![A_107, B_108]: (k1_setfam_1(k2_tarski(A_107, B_108))=k3_xboole_0(B_108, A_107))), inference(superposition, [status(thm), theory('equality')], [c_381, c_24])).
% 3.48/1.58  tff(c_542, plain, (![B_108, A_107]: (k3_xboole_0(B_108, A_107)=k3_xboole_0(A_107, B_108))), inference(superposition, [status(thm), theory('equality')], [c_536, c_24])).
% 3.48/1.58  tff(c_34, plain, (k7_relat_1('#skF_2', k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1'))!=k7_relat_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.48/1.58  tff(c_562, plain, (k7_relat_1('#skF_2', k3_xboole_0('#skF_1', k1_relat_1('#skF_2')))!=k7_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_542, c_34])).
% 3.48/1.58  tff(c_2048, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2026, c_562])).
% 3.48/1.58  tff(c_2088, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_2048])).
% 3.48/1.58  tff(c_2092, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_26, c_2088])).
% 3.48/1.58  tff(c_2096, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_2092])).
% 3.48/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.48/1.58  
% 3.48/1.58  Inference rules
% 3.48/1.58  ----------------------
% 3.48/1.58  #Ref     : 0
% 3.48/1.58  #Sup     : 503
% 3.48/1.58  #Fact    : 0
% 3.48/1.58  #Define  : 0
% 3.48/1.58  #Split   : 0
% 3.48/1.58  #Chain   : 0
% 3.48/1.58  #Close   : 0
% 3.48/1.58  
% 3.48/1.58  Ordering : KBO
% 3.48/1.58  
% 3.48/1.58  Simplification rules
% 3.48/1.58  ----------------------
% 3.48/1.58  #Subsume      : 75
% 3.48/1.58  #Demod        : 280
% 3.48/1.58  #Tautology    : 308
% 3.48/1.58  #SimpNegUnit  : 0
% 3.48/1.58  #BackRed      : 1
% 3.48/1.58  
% 3.48/1.58  #Partial instantiations: 0
% 3.48/1.58  #Strategies tried      : 1
% 3.48/1.58  
% 3.48/1.58  Timing (in seconds)
% 3.48/1.58  ----------------------
% 3.48/1.59  Preprocessing        : 0.32
% 3.48/1.59  Parsing              : 0.18
% 3.48/1.59  CNF conversion       : 0.02
% 3.48/1.59  Main loop            : 0.52
% 3.48/1.59  Inferencing          : 0.19
% 3.48/1.59  Reduction            : 0.20
% 3.48/1.59  Demodulation         : 0.17
% 3.48/1.59  BG Simplification    : 0.03
% 3.48/1.59  Subsumption          : 0.07
% 3.48/1.59  Abstraction          : 0.03
% 3.48/1.59  MUC search           : 0.00
% 3.48/1.59  Cooper               : 0.00
% 3.48/1.59  Total                : 0.87
% 3.48/1.59  Index Insertion      : 0.00
% 3.48/1.59  Index Deletion       : 0.00
% 3.48/1.59  Index Matching       : 0.00
% 3.48/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
