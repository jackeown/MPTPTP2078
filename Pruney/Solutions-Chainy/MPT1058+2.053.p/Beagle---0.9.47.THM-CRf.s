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
% DateTime   : Thu Dec  3 10:17:29 EST 2020

% Result     : Theorem 4.08s
% Output     : CNFRefutation 4.49s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 257 expanded)
%              Number of leaves         :   32 ( 107 expanded)
%              Depth                    :   16
%              Number of atoms          :   83 ( 394 expanded)
%              Number of equality atoms :   43 ( 201 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(f_105,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_tarski(k10_relat_1(A,C),B)
           => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_59,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_95,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => k9_relat_1(B,k10_relat_1(B,A)) = k3_xboole_0(A,k9_relat_1(B,k1_relat_1(B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_funct_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

tff(c_44,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') != k10_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_50,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_46,plain,(
    r1_tarski(k10_relat_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_24,plain,(
    ! [A_20] : k1_relat_1(k6_relat_1(A_20)) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_32,plain,(
    ! [A_25] : v1_relat_1(k6_relat_1(A_25)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_159,plain,(
    ! [A_63,B_64] :
      ( k5_relat_1(k6_relat_1(A_63),B_64) = k7_relat_1(B_64,A_63)
      | ~ v1_relat_1(B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_42,plain,(
    ! [B_35,A_34] : k5_relat_1(k6_relat_1(B_35),k6_relat_1(A_34)) = k6_relat_1(k3_xboole_0(A_34,B_35)) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_166,plain,(
    ! [A_34,A_63] :
      ( k7_relat_1(k6_relat_1(A_34),A_63) = k6_relat_1(k3_xboole_0(A_34,A_63))
      | ~ v1_relat_1(k6_relat_1(A_34)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_42])).

tff(c_175,plain,(
    ! [A_34,A_63] : k7_relat_1(k6_relat_1(A_34),A_63) = k6_relat_1(k3_xboole_0(A_34,A_63)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_166])).

tff(c_381,plain,(
    ! [B_92,A_93] :
      ( k7_relat_1(B_92,A_93) = B_92
      | ~ r1_tarski(k1_relat_1(B_92),A_93)
      | ~ v1_relat_1(B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_384,plain,(
    ! [A_20,A_93] :
      ( k7_relat_1(k6_relat_1(A_20),A_93) = k6_relat_1(A_20)
      | ~ r1_tarski(A_20,A_93)
      | ~ v1_relat_1(k6_relat_1(A_20)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_381])).

tff(c_693,plain,(
    ! [A_113,A_114] :
      ( k6_relat_1(k3_xboole_0(A_113,A_114)) = k6_relat_1(A_113)
      | ~ r1_tarski(A_113,A_114) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_175,c_384])).

tff(c_720,plain,(
    ! [A_113,A_114] :
      ( k3_xboole_0(A_113,A_114) = k1_relat_1(k6_relat_1(A_113))
      | ~ r1_tarski(A_113,A_114) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_693,c_24])).

tff(c_751,plain,(
    ! [A_115,A_116] :
      ( k3_xboole_0(A_115,A_116) = A_115
      | ~ r1_tarski(A_115,A_116) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_720])).

tff(c_814,plain,(
    k3_xboole_0(k10_relat_1('#skF_1','#skF_3'),'#skF_2') = k10_relat_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_751])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_392,plain,(
    ! [B_94] :
      ( k7_relat_1(B_94,k1_relat_1(B_94)) = B_94
      | ~ v1_relat_1(B_94) ) ),
    inference(resolution,[status(thm)],[c_6,c_381])).

tff(c_402,plain,(
    ! [A_34] :
      ( k6_relat_1(k3_xboole_0(A_34,k1_relat_1(k6_relat_1(A_34)))) = k6_relat_1(A_34)
      | ~ v1_relat_1(k6_relat_1(A_34)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_392,c_175])).

tff(c_421,plain,(
    ! [A_95] : k6_relat_1(k3_xboole_0(A_95,A_95)) = k6_relat_1(A_95) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_24,c_402])).

tff(c_445,plain,(
    ! [A_95] : k3_xboole_0(A_95,A_95) = k1_relat_1(k6_relat_1(A_95)) ),
    inference(superposition,[status(thm),theory(equality)],[c_421,c_24])).

tff(c_461,plain,(
    ! [A_95] : k3_xboole_0(A_95,A_95) = A_95 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_445])).

tff(c_34,plain,(
    ! [A_25] : v1_funct_1(k6_relat_1(A_25)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_26,plain,(
    ! [A_20] : k2_relat_1(k6_relat_1(A_20)) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_189,plain,(
    ! [B_67,A_68] :
      ( k2_relat_1(k7_relat_1(B_67,A_68)) = k9_relat_1(B_67,A_68)
      | ~ v1_relat_1(B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_198,plain,(
    ! [A_34,A_63] :
      ( k2_relat_1(k6_relat_1(k3_xboole_0(A_34,A_63))) = k9_relat_1(k6_relat_1(A_34),A_63)
      | ~ v1_relat_1(k6_relat_1(A_34)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_189])).

tff(c_202,plain,(
    ! [A_34,A_63] : k9_relat_1(k6_relat_1(A_34),A_63) = k3_xboole_0(A_34,A_63) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_26,c_198])).

tff(c_817,plain,(
    ! [A_117,B_118] :
      ( k3_xboole_0(A_117,k9_relat_1(B_118,k1_relat_1(B_118))) = k9_relat_1(B_118,k10_relat_1(B_118,A_117))
      | ~ v1_funct_1(B_118)
      | ~ v1_relat_1(B_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_872,plain,(
    ! [A_34,A_117] :
      ( k9_relat_1(k6_relat_1(A_34),k10_relat_1(k6_relat_1(A_34),A_117)) = k3_xboole_0(A_117,k3_xboole_0(A_34,k1_relat_1(k6_relat_1(A_34))))
      | ~ v1_funct_1(k6_relat_1(A_34))
      | ~ v1_relat_1(k6_relat_1(A_34)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_817])).

tff(c_1922,plain,(
    ! [A_171,A_172] : k3_xboole_0(A_171,k10_relat_1(k6_relat_1(A_171),A_172)) = k3_xboole_0(A_172,A_171) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_34,c_461,c_202,c_24,c_872])).

tff(c_36,plain,(
    ! [A_26,C_28,B_27] :
      ( k3_xboole_0(A_26,k10_relat_1(C_28,B_27)) = k10_relat_1(k7_relat_1(C_28,A_26),B_27)
      | ~ v1_relat_1(C_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1980,plain,(
    ! [A_171,A_172] :
      ( k10_relat_1(k7_relat_1(k6_relat_1(A_171),A_171),A_172) = k3_xboole_0(A_172,A_171)
      | ~ v1_relat_1(k6_relat_1(A_171)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1922,c_36])).

tff(c_2023,plain,(
    ! [A_171,A_172] : k10_relat_1(k6_relat_1(A_171),A_172) = k3_xboole_0(A_172,A_171) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_461,c_175,c_1980])).

tff(c_879,plain,(
    ! [A_34,A_117] : k3_xboole_0(A_34,k10_relat_1(k6_relat_1(A_34),A_117)) = k3_xboole_0(A_117,A_34) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_34,c_461,c_202,c_24,c_872])).

tff(c_2771,plain,(
    ! [A_204,A_205] : k3_xboole_0(A_204,k3_xboole_0(A_205,A_204)) = k3_xboole_0(A_205,A_204) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2023,c_879])).

tff(c_2900,plain,(
    k3_xboole_0(k10_relat_1('#skF_1','#skF_3'),'#skF_2') = k3_xboole_0('#skF_2',k10_relat_1('#skF_1','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_814,c_2771])).

tff(c_2935,plain,(
    k3_xboole_0('#skF_2',k10_relat_1('#skF_1','#skF_3')) = k10_relat_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_814,c_2900])).

tff(c_3183,plain,
    ( k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2935,c_36])).

tff(c_3217,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_3183])).

tff(c_3219,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_3217])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:32:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.08/1.77  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.49/1.78  
% 4.49/1.78  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.49/1.78  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 4.49/1.78  
% 4.49/1.78  %Foreground sorts:
% 4.49/1.78  
% 4.49/1.78  
% 4.49/1.78  %Background operators:
% 4.49/1.78  
% 4.49/1.78  
% 4.49/1.78  %Foreground operators:
% 4.49/1.78  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.49/1.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.49/1.78  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.49/1.78  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.49/1.78  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.49/1.78  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.49/1.78  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.49/1.78  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.49/1.78  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.49/1.78  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.49/1.78  tff('#skF_2', type, '#skF_2': $i).
% 4.49/1.78  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.49/1.78  tff('#skF_3', type, '#skF_3': $i).
% 4.49/1.78  tff('#skF_1', type, '#skF_1': $i).
% 4.49/1.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.49/1.78  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.49/1.78  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.49/1.78  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.49/1.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.49/1.78  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.49/1.78  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.49/1.78  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.49/1.78  
% 4.49/1.80  tff(f_105, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_funct_2)).
% 4.49/1.80  tff(f_59, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 4.49/1.80  tff(f_73, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 4.49/1.80  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 4.49/1.80  tff(f_95, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 4.49/1.80  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 4.49/1.80  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.49/1.80  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 4.49/1.80  tff(f_83, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = k3_xboole_0(A, k9_relat_1(B, k1_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_funct_1)).
% 4.49/1.80  tff(f_77, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 4.49/1.80  tff(c_44, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')!=k10_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.49/1.80  tff(c_50, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.49/1.80  tff(c_46, plain, (r1_tarski(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.49/1.80  tff(c_24, plain, (![A_20]: (k1_relat_1(k6_relat_1(A_20))=A_20)), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.49/1.80  tff(c_32, plain, (![A_25]: (v1_relat_1(k6_relat_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.49/1.80  tff(c_159, plain, (![A_63, B_64]: (k5_relat_1(k6_relat_1(A_63), B_64)=k7_relat_1(B_64, A_63) | ~v1_relat_1(B_64))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.49/1.80  tff(c_42, plain, (![B_35, A_34]: (k5_relat_1(k6_relat_1(B_35), k6_relat_1(A_34))=k6_relat_1(k3_xboole_0(A_34, B_35)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.49/1.80  tff(c_166, plain, (![A_34, A_63]: (k7_relat_1(k6_relat_1(A_34), A_63)=k6_relat_1(k3_xboole_0(A_34, A_63)) | ~v1_relat_1(k6_relat_1(A_34)))), inference(superposition, [status(thm), theory('equality')], [c_159, c_42])).
% 4.49/1.80  tff(c_175, plain, (![A_34, A_63]: (k7_relat_1(k6_relat_1(A_34), A_63)=k6_relat_1(k3_xboole_0(A_34, A_63)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_166])).
% 4.49/1.80  tff(c_381, plain, (![B_92, A_93]: (k7_relat_1(B_92, A_93)=B_92 | ~r1_tarski(k1_relat_1(B_92), A_93) | ~v1_relat_1(B_92))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.49/1.80  tff(c_384, plain, (![A_20, A_93]: (k7_relat_1(k6_relat_1(A_20), A_93)=k6_relat_1(A_20) | ~r1_tarski(A_20, A_93) | ~v1_relat_1(k6_relat_1(A_20)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_381])).
% 4.49/1.80  tff(c_693, plain, (![A_113, A_114]: (k6_relat_1(k3_xboole_0(A_113, A_114))=k6_relat_1(A_113) | ~r1_tarski(A_113, A_114))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_175, c_384])).
% 4.49/1.80  tff(c_720, plain, (![A_113, A_114]: (k3_xboole_0(A_113, A_114)=k1_relat_1(k6_relat_1(A_113)) | ~r1_tarski(A_113, A_114))), inference(superposition, [status(thm), theory('equality')], [c_693, c_24])).
% 4.49/1.80  tff(c_751, plain, (![A_115, A_116]: (k3_xboole_0(A_115, A_116)=A_115 | ~r1_tarski(A_115, A_116))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_720])).
% 4.49/1.80  tff(c_814, plain, (k3_xboole_0(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')=k10_relat_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_751])).
% 4.49/1.80  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.49/1.80  tff(c_392, plain, (![B_94]: (k7_relat_1(B_94, k1_relat_1(B_94))=B_94 | ~v1_relat_1(B_94))), inference(resolution, [status(thm)], [c_6, c_381])).
% 4.49/1.80  tff(c_402, plain, (![A_34]: (k6_relat_1(k3_xboole_0(A_34, k1_relat_1(k6_relat_1(A_34))))=k6_relat_1(A_34) | ~v1_relat_1(k6_relat_1(A_34)))), inference(superposition, [status(thm), theory('equality')], [c_392, c_175])).
% 4.49/1.80  tff(c_421, plain, (![A_95]: (k6_relat_1(k3_xboole_0(A_95, A_95))=k6_relat_1(A_95))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_24, c_402])).
% 4.49/1.80  tff(c_445, plain, (![A_95]: (k3_xboole_0(A_95, A_95)=k1_relat_1(k6_relat_1(A_95)))), inference(superposition, [status(thm), theory('equality')], [c_421, c_24])).
% 4.49/1.80  tff(c_461, plain, (![A_95]: (k3_xboole_0(A_95, A_95)=A_95)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_445])).
% 4.49/1.80  tff(c_34, plain, (![A_25]: (v1_funct_1(k6_relat_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.49/1.80  tff(c_26, plain, (![A_20]: (k2_relat_1(k6_relat_1(A_20))=A_20)), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.49/1.80  tff(c_189, plain, (![B_67, A_68]: (k2_relat_1(k7_relat_1(B_67, A_68))=k9_relat_1(B_67, A_68) | ~v1_relat_1(B_67))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.49/1.80  tff(c_198, plain, (![A_34, A_63]: (k2_relat_1(k6_relat_1(k3_xboole_0(A_34, A_63)))=k9_relat_1(k6_relat_1(A_34), A_63) | ~v1_relat_1(k6_relat_1(A_34)))), inference(superposition, [status(thm), theory('equality')], [c_175, c_189])).
% 4.49/1.80  tff(c_202, plain, (![A_34, A_63]: (k9_relat_1(k6_relat_1(A_34), A_63)=k3_xboole_0(A_34, A_63))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_26, c_198])).
% 4.49/1.80  tff(c_817, plain, (![A_117, B_118]: (k3_xboole_0(A_117, k9_relat_1(B_118, k1_relat_1(B_118)))=k9_relat_1(B_118, k10_relat_1(B_118, A_117)) | ~v1_funct_1(B_118) | ~v1_relat_1(B_118))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.49/1.80  tff(c_872, plain, (![A_34, A_117]: (k9_relat_1(k6_relat_1(A_34), k10_relat_1(k6_relat_1(A_34), A_117))=k3_xboole_0(A_117, k3_xboole_0(A_34, k1_relat_1(k6_relat_1(A_34)))) | ~v1_funct_1(k6_relat_1(A_34)) | ~v1_relat_1(k6_relat_1(A_34)))), inference(superposition, [status(thm), theory('equality')], [c_202, c_817])).
% 4.49/1.80  tff(c_1922, plain, (![A_171, A_172]: (k3_xboole_0(A_171, k10_relat_1(k6_relat_1(A_171), A_172))=k3_xboole_0(A_172, A_171))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_34, c_461, c_202, c_24, c_872])).
% 4.49/1.80  tff(c_36, plain, (![A_26, C_28, B_27]: (k3_xboole_0(A_26, k10_relat_1(C_28, B_27))=k10_relat_1(k7_relat_1(C_28, A_26), B_27) | ~v1_relat_1(C_28))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.49/1.80  tff(c_1980, plain, (![A_171, A_172]: (k10_relat_1(k7_relat_1(k6_relat_1(A_171), A_171), A_172)=k3_xboole_0(A_172, A_171) | ~v1_relat_1(k6_relat_1(A_171)))), inference(superposition, [status(thm), theory('equality')], [c_1922, c_36])).
% 4.49/1.80  tff(c_2023, plain, (![A_171, A_172]: (k10_relat_1(k6_relat_1(A_171), A_172)=k3_xboole_0(A_172, A_171))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_461, c_175, c_1980])).
% 4.49/1.80  tff(c_879, plain, (![A_34, A_117]: (k3_xboole_0(A_34, k10_relat_1(k6_relat_1(A_34), A_117))=k3_xboole_0(A_117, A_34))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_34, c_461, c_202, c_24, c_872])).
% 4.49/1.80  tff(c_2771, plain, (![A_204, A_205]: (k3_xboole_0(A_204, k3_xboole_0(A_205, A_204))=k3_xboole_0(A_205, A_204))), inference(demodulation, [status(thm), theory('equality')], [c_2023, c_879])).
% 4.49/1.80  tff(c_2900, plain, (k3_xboole_0(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')=k3_xboole_0('#skF_2', k10_relat_1('#skF_1', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_814, c_2771])).
% 4.49/1.80  tff(c_2935, plain, (k3_xboole_0('#skF_2', k10_relat_1('#skF_1', '#skF_3'))=k10_relat_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_814, c_2900])).
% 4.49/1.80  tff(c_3183, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2935, c_36])).
% 4.49/1.80  tff(c_3217, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_3183])).
% 4.49/1.80  tff(c_3219, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_3217])).
% 4.49/1.80  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.49/1.80  
% 4.49/1.80  Inference rules
% 4.49/1.80  ----------------------
% 4.49/1.80  #Ref     : 0
% 4.49/1.80  #Sup     : 751
% 4.49/1.80  #Fact    : 0
% 4.49/1.80  #Define  : 0
% 4.49/1.80  #Split   : 1
% 4.49/1.80  #Chain   : 0
% 4.49/1.80  #Close   : 0
% 4.49/1.80  
% 4.49/1.80  Ordering : KBO
% 4.49/1.80  
% 4.49/1.80  Simplification rules
% 4.49/1.80  ----------------------
% 4.49/1.80  #Subsume      : 18
% 4.49/1.80  #Demod        : 377
% 4.49/1.80  #Tautology    : 321
% 4.49/1.80  #SimpNegUnit  : 1
% 4.49/1.80  #BackRed      : 9
% 4.49/1.80  
% 4.49/1.80  #Partial instantiations: 0
% 4.49/1.80  #Strategies tried      : 1
% 4.49/1.80  
% 4.49/1.80  Timing (in seconds)
% 4.49/1.80  ----------------------
% 4.49/1.80  Preprocessing        : 0.34
% 4.49/1.80  Parsing              : 0.18
% 4.49/1.80  CNF conversion       : 0.02
% 4.49/1.80  Main loop            : 0.69
% 4.49/1.80  Inferencing          : 0.22
% 4.49/1.80  Reduction            : 0.26
% 4.49/1.80  Demodulation         : 0.20
% 4.49/1.80  BG Simplification    : 0.03
% 4.49/1.80  Subsumption          : 0.13
% 4.49/1.80  Abstraction          : 0.04
% 4.49/1.80  MUC search           : 0.00
% 4.49/1.80  Cooper               : 0.00
% 4.49/1.80  Total                : 1.06
% 4.49/1.80  Index Insertion      : 0.00
% 4.49/1.80  Index Deletion       : 0.00
% 4.49/1.80  Index Matching       : 0.00
% 4.49/1.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
