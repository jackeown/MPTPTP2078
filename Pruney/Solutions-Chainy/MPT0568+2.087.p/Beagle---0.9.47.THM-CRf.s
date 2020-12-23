%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:31 EST 2020

% Result     : Theorem 2.76s
% Output     : CNFRefutation 2.76s
% Verified   : 
% Statistics : Number of formulae       :   67 (  95 expanded)
%              Number of leaves         :   36 (  48 expanded)
%              Depth                    :    8
%              Number of atoms          :   66 ( 110 expanded)
%              Number of equality atoms :   37 (  52 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_60,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_83,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_68,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_relat_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_32,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_30,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_28,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_42,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_44,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_79,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k10_relat_1(B,A) = k10_relat_1(B,k3_xboole_0(k2_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).

tff(f_86,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_30,plain,(
    ! [A_40] : v1_relat_1(k6_relat_1(A_40)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_42,plain,(
    ! [A_45] : k1_relat_1(k6_relat_1(A_45)) = A_45 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_135,plain,(
    ! [A_59] :
      ( ~ v1_xboole_0(k1_relat_1(A_59))
      | ~ v1_relat_1(A_59)
      | v1_xboole_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_138,plain,(
    ! [A_45] :
      ( ~ v1_xboole_0(A_45)
      | ~ v1_relat_1(k6_relat_1(A_45))
      | v1_xboole_0(k6_relat_1(A_45)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_135])).

tff(c_155,plain,(
    ! [A_62] :
      ( ~ v1_xboole_0(A_62)
      | v1_xboole_0(k6_relat_1(A_62)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_138])).

tff(c_107,plain,(
    ! [B_52,A_53] :
      ( ~ v1_xboole_0(B_52)
      | B_52 = A_53
      | ~ v1_xboole_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_110,plain,(
    ! [A_53] :
      ( k1_xboole_0 = A_53
      | ~ v1_xboole_0(A_53) ) ),
    inference(resolution,[status(thm)],[c_2,c_107])).

tff(c_163,plain,(
    ! [A_63] :
      ( k6_relat_1(A_63) = k1_xboole_0
      | ~ v1_xboole_0(A_63) ) ),
    inference(resolution,[status(thm)],[c_155,c_110])).

tff(c_171,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_163])).

tff(c_183,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_30])).

tff(c_44,plain,(
    ! [A_45] : k2_relat_1(k6_relat_1(A_45)) = A_45 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_191,plain,(
    ! [A_64] :
      ( k10_relat_1(A_64,k2_relat_1(A_64)) = k1_relat_1(A_64)
      | ~ v1_relat_1(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_200,plain,(
    ! [A_45] :
      ( k10_relat_1(k6_relat_1(A_45),A_45) = k1_relat_1(k6_relat_1(A_45))
      | ~ v1_relat_1(k6_relat_1(A_45)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_191])).

tff(c_209,plain,(
    ! [A_65] : k10_relat_1(k6_relat_1(A_65),A_65) = A_65 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_42,c_200])).

tff(c_218,plain,(
    k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_209])).

tff(c_8,plain,(
    ! [A_4] : k5_xboole_0(A_4,k1_xboole_0) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_6,plain,(
    ! [A_3] : k4_xboole_0(k1_xboole_0,A_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_4,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(A_1,B_2)) = k4_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_307,plain,(
    ! [A_75,B_76,C_77] : k5_xboole_0(k5_xboole_0(A_75,B_76),C_77) = k5_xboole_0(A_75,k5_xboole_0(B_76,C_77)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_14,plain,(
    ! [A_10] : k5_xboole_0(A_10,A_10) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_359,plain,(
    ! [A_78,B_79] : k5_xboole_0(A_78,k5_xboole_0(B_79,k5_xboole_0(A_78,B_79))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_307,c_14])).

tff(c_405,plain,(
    ! [A_80] : k5_xboole_0(A_80,k5_xboole_0(k1_xboole_0,A_80)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_359])).

tff(c_442,plain,(
    ! [B_2] : k5_xboole_0(k3_xboole_0(k1_xboole_0,B_2),k4_xboole_0(k1_xboole_0,B_2)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_405])).

tff(c_459,plain,(
    ! [B_2] : k3_xboole_0(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_6,c_442])).

tff(c_38,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_838,plain,(
    ! [B_92,A_93] :
      ( k10_relat_1(B_92,k3_xboole_0(k2_relat_1(B_92),A_93)) = k10_relat_1(B_92,A_93)
      | ~ v1_relat_1(B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_850,plain,(
    ! [A_93] :
      ( k10_relat_1(k1_xboole_0,k3_xboole_0(k1_xboole_0,A_93)) = k10_relat_1(k1_xboole_0,A_93)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_838])).

tff(c_856,plain,(
    ! [A_93] : k10_relat_1(k1_xboole_0,A_93) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_218,c_459,c_850])).

tff(c_46,plain,(
    k10_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_861,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_856,c_46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:50:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.76/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/1.50  
% 2.76/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/1.51  %$ v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 2.76/1.51  
% 2.76/1.51  %Foreground sorts:
% 2.76/1.51  
% 2.76/1.51  
% 2.76/1.51  %Background operators:
% 2.76/1.51  
% 2.76/1.51  
% 2.76/1.51  %Foreground operators:
% 2.76/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.76/1.51  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.76/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.76/1.51  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.76/1.51  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.76/1.51  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.76/1.51  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.76/1.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.76/1.51  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.76/1.51  tff('#skF_1', type, '#skF_1': $i).
% 2.76/1.51  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.76/1.51  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.76/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.76/1.51  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.76/1.51  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.76/1.51  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.76/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.76/1.51  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.76/1.51  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.76/1.51  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.76/1.51  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.76/1.51  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.76/1.51  
% 2.76/1.52  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.76/1.52  tff(f_60, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.76/1.52  tff(f_83, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.76/1.52  tff(f_68, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_relat_1)).
% 2.76/1.52  tff(f_40, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 2.76/1.52  tff(f_76, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 2.76/1.52  tff(f_32, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.76/1.52  tff(f_30, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 2.76/1.52  tff(f_28, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.76/1.52  tff(f_42, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 2.76/1.52  tff(f_44, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.76/1.52  tff(f_79, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.76/1.52  tff(f_72, axiom, (![A, B]: (v1_relat_1(B) => (k10_relat_1(B, A) = k10_relat_1(B, k3_xboole_0(k2_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t168_relat_1)).
% 2.76/1.52  tff(f_86, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_relat_1)).
% 2.76/1.52  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.76/1.52  tff(c_30, plain, (![A_40]: (v1_relat_1(k6_relat_1(A_40)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.76/1.52  tff(c_42, plain, (![A_45]: (k1_relat_1(k6_relat_1(A_45))=A_45)), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.76/1.52  tff(c_135, plain, (![A_59]: (~v1_xboole_0(k1_relat_1(A_59)) | ~v1_relat_1(A_59) | v1_xboole_0(A_59))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.76/1.52  tff(c_138, plain, (![A_45]: (~v1_xboole_0(A_45) | ~v1_relat_1(k6_relat_1(A_45)) | v1_xboole_0(k6_relat_1(A_45)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_135])).
% 2.76/1.52  tff(c_155, plain, (![A_62]: (~v1_xboole_0(A_62) | v1_xboole_0(k6_relat_1(A_62)))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_138])).
% 2.76/1.52  tff(c_107, plain, (![B_52, A_53]: (~v1_xboole_0(B_52) | B_52=A_53 | ~v1_xboole_0(A_53))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.76/1.52  tff(c_110, plain, (![A_53]: (k1_xboole_0=A_53 | ~v1_xboole_0(A_53))), inference(resolution, [status(thm)], [c_2, c_107])).
% 2.76/1.52  tff(c_163, plain, (![A_63]: (k6_relat_1(A_63)=k1_xboole_0 | ~v1_xboole_0(A_63))), inference(resolution, [status(thm)], [c_155, c_110])).
% 2.76/1.52  tff(c_171, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_163])).
% 2.76/1.52  tff(c_183, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_171, c_30])).
% 2.76/1.52  tff(c_44, plain, (![A_45]: (k2_relat_1(k6_relat_1(A_45))=A_45)), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.76/1.52  tff(c_191, plain, (![A_64]: (k10_relat_1(A_64, k2_relat_1(A_64))=k1_relat_1(A_64) | ~v1_relat_1(A_64))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.76/1.52  tff(c_200, plain, (![A_45]: (k10_relat_1(k6_relat_1(A_45), A_45)=k1_relat_1(k6_relat_1(A_45)) | ~v1_relat_1(k6_relat_1(A_45)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_191])).
% 2.76/1.52  tff(c_209, plain, (![A_65]: (k10_relat_1(k6_relat_1(A_65), A_65)=A_65)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_42, c_200])).
% 2.76/1.52  tff(c_218, plain, (k10_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_171, c_209])).
% 2.76/1.52  tff(c_8, plain, (![A_4]: (k5_xboole_0(A_4, k1_xboole_0)=A_4)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.76/1.52  tff(c_6, plain, (![A_3]: (k4_xboole_0(k1_xboole_0, A_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.76/1.52  tff(c_4, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(A_1, B_2))=k4_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.76/1.52  tff(c_307, plain, (![A_75, B_76, C_77]: (k5_xboole_0(k5_xboole_0(A_75, B_76), C_77)=k5_xboole_0(A_75, k5_xboole_0(B_76, C_77)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.76/1.52  tff(c_14, plain, (![A_10]: (k5_xboole_0(A_10, A_10)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.76/1.52  tff(c_359, plain, (![A_78, B_79]: (k5_xboole_0(A_78, k5_xboole_0(B_79, k5_xboole_0(A_78, B_79)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_307, c_14])).
% 2.76/1.52  tff(c_405, plain, (![A_80]: (k5_xboole_0(A_80, k5_xboole_0(k1_xboole_0, A_80))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8, c_359])).
% 2.76/1.52  tff(c_442, plain, (![B_2]: (k5_xboole_0(k3_xboole_0(k1_xboole_0, B_2), k4_xboole_0(k1_xboole_0, B_2))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_405])).
% 2.76/1.52  tff(c_459, plain, (![B_2]: (k3_xboole_0(k1_xboole_0, B_2)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_6, c_442])).
% 2.76/1.52  tff(c_38, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.76/1.52  tff(c_838, plain, (![B_92, A_93]: (k10_relat_1(B_92, k3_xboole_0(k2_relat_1(B_92), A_93))=k10_relat_1(B_92, A_93) | ~v1_relat_1(B_92))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.76/1.52  tff(c_850, plain, (![A_93]: (k10_relat_1(k1_xboole_0, k3_xboole_0(k1_xboole_0, A_93))=k10_relat_1(k1_xboole_0, A_93) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_38, c_838])).
% 2.76/1.52  tff(c_856, plain, (![A_93]: (k10_relat_1(k1_xboole_0, A_93)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_183, c_218, c_459, c_850])).
% 2.76/1.52  tff(c_46, plain, (k10_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.76/1.52  tff(c_861, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_856, c_46])).
% 2.76/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/1.52  
% 2.76/1.52  Inference rules
% 2.76/1.52  ----------------------
% 2.76/1.52  #Ref     : 0
% 2.76/1.52  #Sup     : 188
% 2.76/1.52  #Fact    : 0
% 2.76/1.52  #Define  : 0
% 2.76/1.52  #Split   : 0
% 2.76/1.52  #Chain   : 0
% 2.76/1.52  #Close   : 0
% 2.76/1.52  
% 2.76/1.52  Ordering : KBO
% 2.76/1.52  
% 2.76/1.52  Simplification rules
% 2.76/1.52  ----------------------
% 2.76/1.52  #Subsume      : 8
% 2.76/1.52  #Demod        : 178
% 2.76/1.52  #Tautology    : 142
% 2.76/1.52  #SimpNegUnit  : 0
% 2.76/1.52  #BackRed      : 5
% 2.76/1.52  
% 2.76/1.52  #Partial instantiations: 0
% 2.76/1.52  #Strategies tried      : 1
% 2.76/1.52  
% 2.76/1.52  Timing (in seconds)
% 2.76/1.52  ----------------------
% 2.76/1.52  Preprocessing        : 0.39
% 2.76/1.52  Parsing              : 0.22
% 2.76/1.52  CNF conversion       : 0.02
% 2.76/1.52  Main loop            : 0.29
% 2.76/1.52  Inferencing          : 0.11
% 2.76/1.52  Reduction            : 0.11
% 2.76/1.52  Demodulation         : 0.08
% 2.76/1.52  BG Simplification    : 0.02
% 2.76/1.52  Subsumption          : 0.04
% 2.76/1.52  Abstraction          : 0.02
% 2.76/1.52  MUC search           : 0.00
% 2.76/1.52  Cooper               : 0.00
% 2.76/1.52  Total                : 0.71
% 2.76/1.52  Index Insertion      : 0.00
% 2.76/1.53  Index Deletion       : 0.00
% 2.76/1.53  Index Matching       : 0.00
% 2.76/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
