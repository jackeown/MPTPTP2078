%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:31 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.64s
% Verified   : 
% Statistics : Number of formulae       :   58 (  72 expanded)
%              Number of leaves         :   33 (  41 expanded)
%              Depth                    :   10
%              Number of atoms          :   68 (  90 expanded)
%              Number of equality atoms :   28 (  37 expanded)
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

tff(f_82,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_63,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k10_relat_1(B,A) = k10_relat_1(B,k3_xboole_0(k2_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k10_relat_1(k5_relat_1(B,C),A) = k10_relat_1(B,k10_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t181_relat_1)).

tff(c_38,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_32,plain,(
    ! [A_46] : v1_relat_1(k6_relat_1(A_46)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_24,plain,(
    ! [A_41] : k1_relat_1(k6_relat_1(A_41)) = A_41 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_128,plain,(
    ! [A_70,B_71] :
      ( k5_relat_1(k6_relat_1(A_70),B_71) = B_71
      | ~ r1_tarski(k1_relat_1(B_71),A_70)
      | ~ v1_relat_1(B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_131,plain,(
    ! [A_70,A_41] :
      ( k5_relat_1(k6_relat_1(A_70),k6_relat_1(A_41)) = k6_relat_1(A_41)
      | ~ r1_tarski(A_41,A_70)
      | ~ v1_relat_1(k6_relat_1(A_41)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_128])).

tff(c_133,plain,(
    ! [A_70,A_41] :
      ( k5_relat_1(k6_relat_1(A_70),k6_relat_1(A_41)) = k6_relat_1(A_41)
      | ~ r1_tarski(A_41,A_70) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_131])).

tff(c_134,plain,(
    ! [A_72,B_73] :
      ( k10_relat_1(A_72,k1_relat_1(B_73)) = k1_relat_1(k5_relat_1(A_72,B_73))
      | ~ v1_relat_1(B_73)
      | ~ v1_relat_1(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_143,plain,(
    ! [A_72,A_41] :
      ( k1_relat_1(k5_relat_1(A_72,k6_relat_1(A_41))) = k10_relat_1(A_72,A_41)
      | ~ v1_relat_1(k6_relat_1(A_41))
      | ~ v1_relat_1(A_72) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_134])).

tff(c_186,plain,(
    ! [A_83,A_84] :
      ( k1_relat_1(k5_relat_1(A_83,k6_relat_1(A_84))) = k10_relat_1(A_83,A_84)
      | ~ v1_relat_1(A_83) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_143])).

tff(c_201,plain,(
    ! [A_70,A_41] :
      ( k10_relat_1(k6_relat_1(A_70),A_41) = k1_relat_1(k6_relat_1(A_41))
      | ~ v1_relat_1(k6_relat_1(A_70))
      | ~ r1_tarski(A_41,A_70) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_186])).

tff(c_212,plain,(
    ! [A_85,A_86] :
      ( k10_relat_1(k6_relat_1(A_85),A_86) = A_86
      | ~ r1_tarski(A_86,A_85) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_24,c_201])).

tff(c_26,plain,(
    ! [A_41] : k2_relat_1(k6_relat_1(A_41)) = A_41 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_105,plain,(
    ! [B_66,A_67] :
      ( k10_relat_1(B_66,k3_xboole_0(k2_relat_1(B_66),A_67)) = k10_relat_1(B_66,A_67)
      | ~ v1_relat_1(B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_114,plain,(
    ! [A_41,A_67] :
      ( k10_relat_1(k6_relat_1(A_41),k3_xboole_0(A_41,A_67)) = k10_relat_1(k6_relat_1(A_41),A_67)
      | ~ v1_relat_1(k6_relat_1(A_41)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_105])).

tff(c_118,plain,(
    ! [A_41,A_67] : k10_relat_1(k6_relat_1(A_41),k3_xboole_0(A_41,A_67)) = k10_relat_1(k6_relat_1(A_41),A_67) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_114])).

tff(c_223,plain,(
    ! [A_85,A_67] :
      ( k10_relat_1(k6_relat_1(A_85),A_67) = k3_xboole_0(A_85,A_67)
      | ~ r1_tarski(k3_xboole_0(A_85,A_67),A_85) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_212,c_118])).

tff(c_246,plain,(
    ! [A_85,A_67] : k10_relat_1(k6_relat_1(A_85),A_67) = k3_xboole_0(A_85,A_67) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_223])).

tff(c_30,plain,(
    ! [A_44,B_45] :
      ( k5_relat_1(k6_relat_1(A_44),B_45) = k7_relat_1(B_45,A_44)
      | ~ v1_relat_1(B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_293,plain,(
    ! [B_89,C_90,A_91] :
      ( k10_relat_1(k5_relat_1(B_89,C_90),A_91) = k10_relat_1(B_89,k10_relat_1(C_90,A_91))
      | ~ v1_relat_1(C_90)
      | ~ v1_relat_1(B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_321,plain,(
    ! [A_44,B_45,A_91] :
      ( k10_relat_1(k6_relat_1(A_44),k10_relat_1(B_45,A_91)) = k10_relat_1(k7_relat_1(B_45,A_44),A_91)
      | ~ v1_relat_1(B_45)
      | ~ v1_relat_1(k6_relat_1(A_44))
      | ~ v1_relat_1(B_45) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_293])).

tff(c_651,plain,(
    ! [A_137,B_138,A_139] :
      ( k3_xboole_0(A_137,k10_relat_1(B_138,A_139)) = k10_relat_1(k7_relat_1(B_138,A_137),A_139)
      | ~ v1_relat_1(B_138) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_246,c_321])).

tff(c_36,plain,(
    k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2')) != k10_relat_1(k7_relat_1('#skF_3','#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_686,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_651,c_36])).

tff(c_713,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_686])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:20:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.33  
% 2.23/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.64/1.33  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.64/1.33  
% 2.64/1.33  %Foreground sorts:
% 2.64/1.33  
% 2.64/1.33  
% 2.64/1.33  %Background operators:
% 2.64/1.33  
% 2.64/1.33  
% 2.64/1.33  %Foreground operators:
% 2.64/1.33  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.64/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.64/1.33  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.64/1.33  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.64/1.33  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.64/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.64/1.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.64/1.33  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.64/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.64/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.64/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.64/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.64/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.64/1.33  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.64/1.33  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.64/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.64/1.33  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.64/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.64/1.33  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.64/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.64/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.64/1.33  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.64/1.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.64/1.33  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.64/1.33  
% 2.64/1.34  tff(f_82, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 2.64/1.34  tff(f_77, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.64/1.34  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.64/1.34  tff(f_63, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.64/1.34  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_relat_1)).
% 2.64/1.34  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 2.64/1.34  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (k10_relat_1(B, A) = k10_relat_1(B, k3_xboole_0(k2_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t168_relat_1)).
% 2.64/1.34  tff(f_73, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 2.64/1.34  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k10_relat_1(k5_relat_1(B, C), A) = k10_relat_1(B, k10_relat_1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t181_relat_1)).
% 2.64/1.34  tff(c_38, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.64/1.34  tff(c_32, plain, (![A_46]: (v1_relat_1(k6_relat_1(A_46)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.64/1.34  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.64/1.34  tff(c_24, plain, (![A_41]: (k1_relat_1(k6_relat_1(A_41))=A_41)), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.64/1.34  tff(c_128, plain, (![A_70, B_71]: (k5_relat_1(k6_relat_1(A_70), B_71)=B_71 | ~r1_tarski(k1_relat_1(B_71), A_70) | ~v1_relat_1(B_71))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.64/1.34  tff(c_131, plain, (![A_70, A_41]: (k5_relat_1(k6_relat_1(A_70), k6_relat_1(A_41))=k6_relat_1(A_41) | ~r1_tarski(A_41, A_70) | ~v1_relat_1(k6_relat_1(A_41)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_128])).
% 2.64/1.34  tff(c_133, plain, (![A_70, A_41]: (k5_relat_1(k6_relat_1(A_70), k6_relat_1(A_41))=k6_relat_1(A_41) | ~r1_tarski(A_41, A_70))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_131])).
% 2.64/1.34  tff(c_134, plain, (![A_72, B_73]: (k10_relat_1(A_72, k1_relat_1(B_73))=k1_relat_1(k5_relat_1(A_72, B_73)) | ~v1_relat_1(B_73) | ~v1_relat_1(A_72))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.64/1.34  tff(c_143, plain, (![A_72, A_41]: (k1_relat_1(k5_relat_1(A_72, k6_relat_1(A_41)))=k10_relat_1(A_72, A_41) | ~v1_relat_1(k6_relat_1(A_41)) | ~v1_relat_1(A_72))), inference(superposition, [status(thm), theory('equality')], [c_24, c_134])).
% 2.64/1.34  tff(c_186, plain, (![A_83, A_84]: (k1_relat_1(k5_relat_1(A_83, k6_relat_1(A_84)))=k10_relat_1(A_83, A_84) | ~v1_relat_1(A_83))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_143])).
% 2.64/1.34  tff(c_201, plain, (![A_70, A_41]: (k10_relat_1(k6_relat_1(A_70), A_41)=k1_relat_1(k6_relat_1(A_41)) | ~v1_relat_1(k6_relat_1(A_70)) | ~r1_tarski(A_41, A_70))), inference(superposition, [status(thm), theory('equality')], [c_133, c_186])).
% 2.64/1.34  tff(c_212, plain, (![A_85, A_86]: (k10_relat_1(k6_relat_1(A_85), A_86)=A_86 | ~r1_tarski(A_86, A_85))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_24, c_201])).
% 2.64/1.34  tff(c_26, plain, (![A_41]: (k2_relat_1(k6_relat_1(A_41))=A_41)), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.64/1.34  tff(c_105, plain, (![B_66, A_67]: (k10_relat_1(B_66, k3_xboole_0(k2_relat_1(B_66), A_67))=k10_relat_1(B_66, A_67) | ~v1_relat_1(B_66))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.64/1.34  tff(c_114, plain, (![A_41, A_67]: (k10_relat_1(k6_relat_1(A_41), k3_xboole_0(A_41, A_67))=k10_relat_1(k6_relat_1(A_41), A_67) | ~v1_relat_1(k6_relat_1(A_41)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_105])).
% 2.64/1.34  tff(c_118, plain, (![A_41, A_67]: (k10_relat_1(k6_relat_1(A_41), k3_xboole_0(A_41, A_67))=k10_relat_1(k6_relat_1(A_41), A_67))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_114])).
% 2.64/1.34  tff(c_223, plain, (![A_85, A_67]: (k10_relat_1(k6_relat_1(A_85), A_67)=k3_xboole_0(A_85, A_67) | ~r1_tarski(k3_xboole_0(A_85, A_67), A_85))), inference(superposition, [status(thm), theory('equality')], [c_212, c_118])).
% 2.64/1.34  tff(c_246, plain, (![A_85, A_67]: (k10_relat_1(k6_relat_1(A_85), A_67)=k3_xboole_0(A_85, A_67))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_223])).
% 2.64/1.34  tff(c_30, plain, (![A_44, B_45]: (k5_relat_1(k6_relat_1(A_44), B_45)=k7_relat_1(B_45, A_44) | ~v1_relat_1(B_45))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.64/1.34  tff(c_293, plain, (![B_89, C_90, A_91]: (k10_relat_1(k5_relat_1(B_89, C_90), A_91)=k10_relat_1(B_89, k10_relat_1(C_90, A_91)) | ~v1_relat_1(C_90) | ~v1_relat_1(B_89))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.64/1.34  tff(c_321, plain, (![A_44, B_45, A_91]: (k10_relat_1(k6_relat_1(A_44), k10_relat_1(B_45, A_91))=k10_relat_1(k7_relat_1(B_45, A_44), A_91) | ~v1_relat_1(B_45) | ~v1_relat_1(k6_relat_1(A_44)) | ~v1_relat_1(B_45))), inference(superposition, [status(thm), theory('equality')], [c_30, c_293])).
% 2.64/1.34  tff(c_651, plain, (![A_137, B_138, A_139]: (k3_xboole_0(A_137, k10_relat_1(B_138, A_139))=k10_relat_1(k7_relat_1(B_138, A_137), A_139) | ~v1_relat_1(B_138))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_246, c_321])).
% 2.64/1.34  tff(c_36, plain, (k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))!=k10_relat_1(k7_relat_1('#skF_3', '#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.64/1.34  tff(c_686, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_651, c_36])).
% 2.64/1.34  tff(c_713, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_686])).
% 2.64/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.64/1.34  
% 2.64/1.34  Inference rules
% 2.64/1.34  ----------------------
% 2.64/1.34  #Ref     : 0
% 2.64/1.34  #Sup     : 157
% 2.64/1.34  #Fact    : 0
% 2.64/1.34  #Define  : 0
% 2.64/1.34  #Split   : 0
% 2.64/1.34  #Chain   : 0
% 2.64/1.34  #Close   : 0
% 2.64/1.34  
% 2.64/1.34  Ordering : KBO
% 2.64/1.34  
% 2.64/1.34  Simplification rules
% 2.64/1.34  ----------------------
% 2.64/1.34  #Subsume      : 8
% 2.64/1.34  #Demod        : 81
% 2.64/1.34  #Tautology    : 76
% 2.64/1.34  #SimpNegUnit  : 0
% 2.64/1.34  #BackRed      : 2
% 2.64/1.34  
% 2.64/1.34  #Partial instantiations: 0
% 2.64/1.34  #Strategies tried      : 1
% 2.64/1.34  
% 2.64/1.34  Timing (in seconds)
% 2.64/1.34  ----------------------
% 2.64/1.35  Preprocessing        : 0.31
% 2.64/1.35  Parsing              : 0.17
% 2.64/1.35  CNF conversion       : 0.02
% 2.64/1.35  Main loop            : 0.28
% 2.64/1.35  Inferencing          : 0.12
% 2.64/1.35  Reduction            : 0.09
% 2.64/1.35  Demodulation         : 0.06
% 2.64/1.35  BG Simplification    : 0.02
% 2.64/1.35  Subsumption          : 0.04
% 2.64/1.35  Abstraction          : 0.02
% 2.64/1.35  MUC search           : 0.00
% 2.64/1.35  Cooper               : 0.00
% 2.64/1.35  Total                : 0.61
% 2.64/1.35  Index Insertion      : 0.00
% 2.64/1.35  Index Deletion       : 0.00
% 2.64/1.35  Index Matching       : 0.00
% 2.64/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
