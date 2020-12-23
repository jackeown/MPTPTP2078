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
% DateTime   : Thu Dec  3 10:03:29 EST 2020

% Result     : Theorem 3.87s
% Output     : CNFRefutation 3.87s
% Verified   : 
% Statistics : Number of formulae       :   52 (  71 expanded)
%              Number of leaves         :   27 (  37 expanded)
%              Depth                    :   12
%              Number of atoms          :   63 (  85 expanded)
%              Number of equality atoms :   30 (  41 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_52,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_37,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_54,axiom,(
    ! [A] : k4_relat_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k5_relat_1(A,B)) = k5_relat_1(k4_relat_1(B),k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k7_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).

tff(f_71,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_18,plain,(
    ! [A_18] : k1_relat_1(k6_relat_1(A_18)) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_12,plain,(
    ! [A_12] : v1_relat_1(k6_relat_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_22,plain,(
    ! [A_19] : k4_relat_1(k6_relat_1(A_19)) = k6_relat_1(A_19) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_285,plain,(
    ! [A_55,B_56] :
      ( k5_relat_1(k6_relat_1(A_55),B_56) = B_56
      | ~ r1_tarski(k1_relat_1(B_56),A_55)
      | ~ v1_relat_1(B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_294,plain,(
    ! [A_55,A_18] :
      ( k5_relat_1(k6_relat_1(A_55),k6_relat_1(A_18)) = k6_relat_1(A_18)
      | ~ r1_tarski(A_18,A_55)
      | ~ v1_relat_1(k6_relat_1(A_18)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_285])).

tff(c_297,plain,(
    ! [A_55,A_18] :
      ( k5_relat_1(k6_relat_1(A_55),k6_relat_1(A_18)) = k6_relat_1(A_18)
      | ~ r1_tarski(A_18,A_55) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_294])).

tff(c_359,plain,(
    ! [B_61,A_62] :
      ( k5_relat_1(k4_relat_1(B_61),k4_relat_1(A_62)) = k4_relat_1(k5_relat_1(A_62,B_61))
      | ~ v1_relat_1(B_61)
      | ~ v1_relat_1(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_368,plain,(
    ! [A_19,A_62] :
      ( k5_relat_1(k6_relat_1(A_19),k4_relat_1(A_62)) = k4_relat_1(k5_relat_1(A_62,k6_relat_1(A_19)))
      | ~ v1_relat_1(k6_relat_1(A_19))
      | ~ v1_relat_1(A_62) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_359])).

tff(c_2576,plain,(
    ! [A_103,A_104] :
      ( k5_relat_1(k6_relat_1(A_103),k4_relat_1(A_104)) = k4_relat_1(k5_relat_1(A_104,k6_relat_1(A_103)))
      | ~ v1_relat_1(A_104) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_368])).

tff(c_2592,plain,(
    ! [A_19,A_103] :
      ( k4_relat_1(k5_relat_1(k6_relat_1(A_19),k6_relat_1(A_103))) = k5_relat_1(k6_relat_1(A_103),k6_relat_1(A_19))
      | ~ v1_relat_1(k6_relat_1(A_19)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_2576])).

tff(c_2705,plain,(
    ! [A_109,A_110] : k4_relat_1(k5_relat_1(k6_relat_1(A_109),k6_relat_1(A_110))) = k5_relat_1(k6_relat_1(A_110),k6_relat_1(A_109)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_2592])).

tff(c_2726,plain,(
    ! [A_18,A_55] :
      ( k5_relat_1(k6_relat_1(A_18),k6_relat_1(A_55)) = k4_relat_1(k6_relat_1(A_18))
      | ~ r1_tarski(A_18,A_55) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_297,c_2705])).

tff(c_2736,plain,(
    ! [A_111,A_112] :
      ( k5_relat_1(k6_relat_1(A_111),k6_relat_1(A_112)) = k6_relat_1(A_111)
      | ~ r1_tarski(A_111,A_112) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_2726])).

tff(c_28,plain,(
    ! [A_24,B_25] :
      ( k5_relat_1(k6_relat_1(A_24),B_25) = k7_relat_1(B_25,A_24)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2748,plain,(
    ! [A_112,A_111] :
      ( k7_relat_1(k6_relat_1(A_112),A_111) = k6_relat_1(A_111)
      | ~ v1_relat_1(k6_relat_1(A_112))
      | ~ r1_tarski(A_111,A_112) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2736,c_28])).

tff(c_2769,plain,(
    ! [A_113,A_114] :
      ( k7_relat_1(k6_relat_1(A_113),A_114) = k6_relat_1(A_114)
      | ~ r1_tarski(A_114,A_113) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_2748])).

tff(c_14,plain,(
    ! [B_14,A_13] :
      ( k7_relat_1(B_14,k3_xboole_0(k1_relat_1(B_14),A_13)) = k7_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2807,plain,(
    ! [A_113,A_13] :
      ( k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(A_113)),A_13)) = k7_relat_1(k6_relat_1(A_113),A_13)
      | ~ v1_relat_1(k6_relat_1(A_113))
      | ~ r1_tarski(k3_xboole_0(k1_relat_1(k6_relat_1(A_113)),A_13),A_113) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2769,c_14])).

tff(c_2852,plain,(
    ! [A_113,A_13] : k7_relat_1(k6_relat_1(A_113),A_13) = k6_relat_1(k3_xboole_0(A_113,A_13)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_18,c_12,c_18,c_2807])).

tff(c_136,plain,(
    ! [A_43,B_44] :
      ( k5_relat_1(k6_relat_1(A_43),B_44) = k7_relat_1(B_44,A_43)
      | ~ v1_relat_1(B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_30,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_142,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_30])).

tff(c_148,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_142])).

tff(c_2902,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2852,c_148])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:08:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.87/1.73  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.87/1.73  
% 3.87/1.73  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.87/1.73  %$ r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 3.87/1.73  
% 3.87/1.73  %Foreground sorts:
% 3.87/1.73  
% 3.87/1.73  
% 3.87/1.73  %Background operators:
% 3.87/1.73  
% 3.87/1.73  
% 3.87/1.73  %Foreground operators:
% 3.87/1.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.87/1.73  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.87/1.73  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.87/1.73  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.87/1.73  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.87/1.73  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.87/1.73  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.87/1.73  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.87/1.73  tff('#skF_2', type, '#skF_2': $i).
% 3.87/1.73  tff('#skF_1', type, '#skF_1': $i).
% 3.87/1.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.87/1.73  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.87/1.73  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.87/1.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.87/1.73  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.87/1.73  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.87/1.73  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 3.87/1.73  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.87/1.73  
% 3.87/1.74  tff(f_29, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.87/1.74  tff(f_52, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 3.87/1.74  tff(f_37, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 3.87/1.74  tff(f_54, axiom, (![A]: (k4_relat_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_relat_1)).
% 3.87/1.74  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_relat_1)).
% 3.87/1.74  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k5_relat_1(A, B)) = k5_relat_1(k4_relat_1(B), k4_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_relat_1)).
% 3.87/1.74  tff(f_68, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 3.87/1.74  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k7_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t192_relat_1)).
% 3.87/1.74  tff(f_71, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 3.87/1.74  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.87/1.74  tff(c_18, plain, (![A_18]: (k1_relat_1(k6_relat_1(A_18))=A_18)), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.87/1.74  tff(c_12, plain, (![A_12]: (v1_relat_1(k6_relat_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.87/1.74  tff(c_22, plain, (![A_19]: (k4_relat_1(k6_relat_1(A_19))=k6_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.87/1.74  tff(c_285, plain, (![A_55, B_56]: (k5_relat_1(k6_relat_1(A_55), B_56)=B_56 | ~r1_tarski(k1_relat_1(B_56), A_55) | ~v1_relat_1(B_56))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.87/1.74  tff(c_294, plain, (![A_55, A_18]: (k5_relat_1(k6_relat_1(A_55), k6_relat_1(A_18))=k6_relat_1(A_18) | ~r1_tarski(A_18, A_55) | ~v1_relat_1(k6_relat_1(A_18)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_285])).
% 3.87/1.74  tff(c_297, plain, (![A_55, A_18]: (k5_relat_1(k6_relat_1(A_55), k6_relat_1(A_18))=k6_relat_1(A_18) | ~r1_tarski(A_18, A_55))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_294])).
% 3.87/1.74  tff(c_359, plain, (![B_61, A_62]: (k5_relat_1(k4_relat_1(B_61), k4_relat_1(A_62))=k4_relat_1(k5_relat_1(A_62, B_61)) | ~v1_relat_1(B_61) | ~v1_relat_1(A_62))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.87/1.74  tff(c_368, plain, (![A_19, A_62]: (k5_relat_1(k6_relat_1(A_19), k4_relat_1(A_62))=k4_relat_1(k5_relat_1(A_62, k6_relat_1(A_19))) | ~v1_relat_1(k6_relat_1(A_19)) | ~v1_relat_1(A_62))), inference(superposition, [status(thm), theory('equality')], [c_22, c_359])).
% 3.87/1.74  tff(c_2576, plain, (![A_103, A_104]: (k5_relat_1(k6_relat_1(A_103), k4_relat_1(A_104))=k4_relat_1(k5_relat_1(A_104, k6_relat_1(A_103))) | ~v1_relat_1(A_104))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_368])).
% 3.87/1.74  tff(c_2592, plain, (![A_19, A_103]: (k4_relat_1(k5_relat_1(k6_relat_1(A_19), k6_relat_1(A_103)))=k5_relat_1(k6_relat_1(A_103), k6_relat_1(A_19)) | ~v1_relat_1(k6_relat_1(A_19)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_2576])).
% 3.87/1.74  tff(c_2705, plain, (![A_109, A_110]: (k4_relat_1(k5_relat_1(k6_relat_1(A_109), k6_relat_1(A_110)))=k5_relat_1(k6_relat_1(A_110), k6_relat_1(A_109)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_2592])).
% 3.87/1.74  tff(c_2726, plain, (![A_18, A_55]: (k5_relat_1(k6_relat_1(A_18), k6_relat_1(A_55))=k4_relat_1(k6_relat_1(A_18)) | ~r1_tarski(A_18, A_55))), inference(superposition, [status(thm), theory('equality')], [c_297, c_2705])).
% 3.87/1.74  tff(c_2736, plain, (![A_111, A_112]: (k5_relat_1(k6_relat_1(A_111), k6_relat_1(A_112))=k6_relat_1(A_111) | ~r1_tarski(A_111, A_112))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_2726])).
% 3.87/1.74  tff(c_28, plain, (![A_24, B_25]: (k5_relat_1(k6_relat_1(A_24), B_25)=k7_relat_1(B_25, A_24) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.87/1.74  tff(c_2748, plain, (![A_112, A_111]: (k7_relat_1(k6_relat_1(A_112), A_111)=k6_relat_1(A_111) | ~v1_relat_1(k6_relat_1(A_112)) | ~r1_tarski(A_111, A_112))), inference(superposition, [status(thm), theory('equality')], [c_2736, c_28])).
% 3.87/1.74  tff(c_2769, plain, (![A_113, A_114]: (k7_relat_1(k6_relat_1(A_113), A_114)=k6_relat_1(A_114) | ~r1_tarski(A_114, A_113))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_2748])).
% 3.87/1.74  tff(c_14, plain, (![B_14, A_13]: (k7_relat_1(B_14, k3_xboole_0(k1_relat_1(B_14), A_13))=k7_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.87/1.74  tff(c_2807, plain, (![A_113, A_13]: (k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(A_113)), A_13))=k7_relat_1(k6_relat_1(A_113), A_13) | ~v1_relat_1(k6_relat_1(A_113)) | ~r1_tarski(k3_xboole_0(k1_relat_1(k6_relat_1(A_113)), A_13), A_113))), inference(superposition, [status(thm), theory('equality')], [c_2769, c_14])).
% 3.87/1.74  tff(c_2852, plain, (![A_113, A_13]: (k7_relat_1(k6_relat_1(A_113), A_13)=k6_relat_1(k3_xboole_0(A_113, A_13)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_18, c_12, c_18, c_2807])).
% 3.87/1.74  tff(c_136, plain, (![A_43, B_44]: (k5_relat_1(k6_relat_1(A_43), B_44)=k7_relat_1(B_44, A_43) | ~v1_relat_1(B_44))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.87/1.74  tff(c_30, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.87/1.74  tff(c_142, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_136, c_30])).
% 3.87/1.74  tff(c_148, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_142])).
% 3.87/1.74  tff(c_2902, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2852, c_148])).
% 3.87/1.74  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.87/1.74  
% 3.87/1.74  Inference rules
% 3.87/1.74  ----------------------
% 3.87/1.74  #Ref     : 0
% 3.87/1.74  #Sup     : 698
% 3.87/1.74  #Fact    : 0
% 3.87/1.74  #Define  : 0
% 3.87/1.74  #Split   : 2
% 3.87/1.74  #Chain   : 0
% 3.87/1.74  #Close   : 0
% 3.87/1.74  
% 3.87/1.74  Ordering : KBO
% 3.87/1.74  
% 3.87/1.74  Simplification rules
% 3.87/1.74  ----------------------
% 3.87/1.74  #Subsume      : 83
% 3.87/1.74  #Demod        : 897
% 3.87/1.74  #Tautology    : 420
% 3.87/1.74  #SimpNegUnit  : 0
% 3.87/1.74  #BackRed      : 6
% 3.87/1.74  
% 3.87/1.74  #Partial instantiations: 0
% 3.87/1.74  #Strategies tried      : 1
% 3.87/1.74  
% 3.87/1.74  Timing (in seconds)
% 3.87/1.74  ----------------------
% 3.87/1.75  Preprocessing        : 0.32
% 3.87/1.75  Parsing              : 0.17
% 3.87/1.75  CNF conversion       : 0.02
% 3.87/1.75  Main loop            : 0.62
% 3.87/1.75  Inferencing          : 0.18
% 3.87/1.75  Reduction            : 0.30
% 3.87/1.75  Demodulation         : 0.26
% 3.87/1.75  BG Simplification    : 0.03
% 3.87/1.75  Subsumption          : 0.08
% 3.87/1.75  Abstraction          : 0.04
% 3.87/1.75  MUC search           : 0.00
% 3.87/1.75  Cooper               : 0.00
% 3.87/1.75  Total                : 0.97
% 3.87/1.75  Index Insertion      : 0.00
% 3.87/1.75  Index Deletion       : 0.00
% 3.87/1.75  Index Matching       : 0.00
% 3.87/1.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
