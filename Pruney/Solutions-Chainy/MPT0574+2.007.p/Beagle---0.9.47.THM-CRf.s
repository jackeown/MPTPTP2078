%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:51 EST 2020

% Result     : Theorem 2.39s
% Output     : CNFRefutation 2.63s
% Verified   : 
% Statistics : Number of formulae       :   50 (  66 expanded)
%              Number of leaves         :   23 (  32 expanded)
%              Depth                    :   14
%              Number of atoms          :   51 (  71 expanded)
%              Number of equality atoms :   23 (  35 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_relat_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_45,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_relat_1)).

tff(c_26,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_16,plain,(
    ! [B_12,A_11] : k2_tarski(B_12,A_11) = k2_tarski(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_76,plain,(
    ! [A_24,B_25] : k3_tarski(k2_tarski(A_24,B_25)) = k2_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_91,plain,(
    ! [B_26,A_27] : k3_tarski(k2_tarski(B_26,A_27)) = k2_xboole_0(A_27,B_26) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_76])).

tff(c_18,plain,(
    ! [A_13,B_14] : k3_tarski(k2_tarski(A_13,B_14)) = k2_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_97,plain,(
    ! [B_26,A_27] : k2_xboole_0(B_26,A_27) = k2_xboole_0(A_27,B_26) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_18])).

tff(c_8,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_24,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_302,plain,(
    ! [A_40,B_41,C_42] :
      ( r1_tarski(k4_xboole_0(A_40,B_41),C_42)
      | ~ r1_tarski(A_40,k2_xboole_0(B_41,C_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_127,plain,(
    ! [B_30,A_31] : k2_xboole_0(B_30,A_31) = k2_xboole_0(A_31,B_30) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_18])).

tff(c_180,plain,(
    ! [A_32] : k2_xboole_0(k1_xboole_0,A_32) = A_32 ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_8])).

tff(c_14,plain,(
    ! [A_9,B_10] : r1_tarski(A_9,k2_xboole_0(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_196,plain,(
    ! [A_32] : r1_tarski(k1_xboole_0,A_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_14])).

tff(c_233,plain,(
    ! [B_34,A_35] :
      ( B_34 = A_35
      | ~ r1_tarski(B_34,A_35)
      | ~ r1_tarski(A_35,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_242,plain,(
    ! [A_32] :
      ( k1_xboole_0 = A_32
      | ~ r1_tarski(A_32,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_196,c_233])).

tff(c_306,plain,(
    ! [A_40,B_41] :
      ( k4_xboole_0(A_40,B_41) = k1_xboole_0
      | ~ r1_tarski(A_40,k2_xboole_0(B_41,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_302,c_242])).

tff(c_417,plain,(
    ! [A_51,B_52] :
      ( k4_xboole_0(A_51,B_52) = k1_xboole_0
      | ~ r1_tarski(A_51,B_52) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_306])).

tff(c_453,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_417])).

tff(c_10,plain,(
    ! [A_4,B_5] : k2_xboole_0(A_4,k4_xboole_0(B_5,A_4)) = k2_xboole_0(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_567,plain,(
    k2_xboole_0('#skF_2',k1_xboole_0) = k2_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_453,c_10])).

tff(c_573,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_8,c_567])).

tff(c_356,plain,(
    ! [C_46,A_47,B_48] :
      ( k2_xboole_0(k10_relat_1(C_46,A_47),k10_relat_1(C_46,B_48)) = k10_relat_1(C_46,k2_xboole_0(A_47,B_48))
      | ~ v1_relat_1(C_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_797,plain,(
    ! [C_62,A_63,B_64] :
      ( r1_tarski(k10_relat_1(C_62,A_63),k10_relat_1(C_62,k2_xboole_0(A_63,B_64)))
      | ~ v1_relat_1(C_62) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_356,c_14])).

tff(c_894,plain,(
    ! [C_65] :
      ( r1_tarski(k10_relat_1(C_65,'#skF_1'),k10_relat_1(C_65,'#skF_2'))
      | ~ v1_relat_1(C_65) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_573,c_797])).

tff(c_22,plain,(
    ~ r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_902,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_894,c_22])).

tff(c_908,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_902])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:36:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.39/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.39/1.36  
% 2.39/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.39/1.36  %$ r1_tarski > v1_relat_1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.39/1.36  
% 2.39/1.36  %Foreground sorts:
% 2.39/1.36  
% 2.39/1.36  
% 2.39/1.36  %Background operators:
% 2.39/1.36  
% 2.39/1.36  
% 2.39/1.36  %Foreground operators:
% 2.39/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.39/1.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.39/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.39/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.39/1.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.39/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.39/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.39/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.39/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.39/1.36  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.39/1.36  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.39/1.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.39/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.39/1.36  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.39/1.36  
% 2.63/1.37  tff(f_56, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t178_relat_1)).
% 2.63/1.37  tff(f_43, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.63/1.37  tff(f_45, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.63/1.37  tff(f_33, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.63/1.37  tff(f_39, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 2.63/1.37  tff(f_41, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.63/1.37  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.63/1.37  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.63/1.37  tff(f_49, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_relat_1)).
% 2.63/1.37  tff(c_26, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.63/1.37  tff(c_16, plain, (![B_12, A_11]: (k2_tarski(B_12, A_11)=k2_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.63/1.37  tff(c_76, plain, (![A_24, B_25]: (k3_tarski(k2_tarski(A_24, B_25))=k2_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.63/1.37  tff(c_91, plain, (![B_26, A_27]: (k3_tarski(k2_tarski(B_26, A_27))=k2_xboole_0(A_27, B_26))), inference(superposition, [status(thm), theory('equality')], [c_16, c_76])).
% 2.63/1.37  tff(c_18, plain, (![A_13, B_14]: (k3_tarski(k2_tarski(A_13, B_14))=k2_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.63/1.37  tff(c_97, plain, (![B_26, A_27]: (k2_xboole_0(B_26, A_27)=k2_xboole_0(A_27, B_26))), inference(superposition, [status(thm), theory('equality')], [c_91, c_18])).
% 2.63/1.37  tff(c_8, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.63/1.37  tff(c_24, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.63/1.37  tff(c_302, plain, (![A_40, B_41, C_42]: (r1_tarski(k4_xboole_0(A_40, B_41), C_42) | ~r1_tarski(A_40, k2_xboole_0(B_41, C_42)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.63/1.37  tff(c_127, plain, (![B_30, A_31]: (k2_xboole_0(B_30, A_31)=k2_xboole_0(A_31, B_30))), inference(superposition, [status(thm), theory('equality')], [c_91, c_18])).
% 2.63/1.37  tff(c_180, plain, (![A_32]: (k2_xboole_0(k1_xboole_0, A_32)=A_32)), inference(superposition, [status(thm), theory('equality')], [c_127, c_8])).
% 2.63/1.37  tff(c_14, plain, (![A_9, B_10]: (r1_tarski(A_9, k2_xboole_0(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.63/1.37  tff(c_196, plain, (![A_32]: (r1_tarski(k1_xboole_0, A_32))), inference(superposition, [status(thm), theory('equality')], [c_180, c_14])).
% 2.63/1.37  tff(c_233, plain, (![B_34, A_35]: (B_34=A_35 | ~r1_tarski(B_34, A_35) | ~r1_tarski(A_35, B_34))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.63/1.37  tff(c_242, plain, (![A_32]: (k1_xboole_0=A_32 | ~r1_tarski(A_32, k1_xboole_0))), inference(resolution, [status(thm)], [c_196, c_233])).
% 2.63/1.37  tff(c_306, plain, (![A_40, B_41]: (k4_xboole_0(A_40, B_41)=k1_xboole_0 | ~r1_tarski(A_40, k2_xboole_0(B_41, k1_xboole_0)))), inference(resolution, [status(thm)], [c_302, c_242])).
% 2.63/1.37  tff(c_417, plain, (![A_51, B_52]: (k4_xboole_0(A_51, B_52)=k1_xboole_0 | ~r1_tarski(A_51, B_52))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_306])).
% 2.63/1.37  tff(c_453, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_24, c_417])).
% 2.63/1.37  tff(c_10, plain, (![A_4, B_5]: (k2_xboole_0(A_4, k4_xboole_0(B_5, A_4))=k2_xboole_0(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.63/1.37  tff(c_567, plain, (k2_xboole_0('#skF_2', k1_xboole_0)=k2_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_453, c_10])).
% 2.63/1.37  tff(c_573, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_97, c_8, c_567])).
% 2.63/1.37  tff(c_356, plain, (![C_46, A_47, B_48]: (k2_xboole_0(k10_relat_1(C_46, A_47), k10_relat_1(C_46, B_48))=k10_relat_1(C_46, k2_xboole_0(A_47, B_48)) | ~v1_relat_1(C_46))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.63/1.37  tff(c_797, plain, (![C_62, A_63, B_64]: (r1_tarski(k10_relat_1(C_62, A_63), k10_relat_1(C_62, k2_xboole_0(A_63, B_64))) | ~v1_relat_1(C_62))), inference(superposition, [status(thm), theory('equality')], [c_356, c_14])).
% 2.63/1.37  tff(c_894, plain, (![C_65]: (r1_tarski(k10_relat_1(C_65, '#skF_1'), k10_relat_1(C_65, '#skF_2')) | ~v1_relat_1(C_65))), inference(superposition, [status(thm), theory('equality')], [c_573, c_797])).
% 2.63/1.37  tff(c_22, plain, (~r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.63/1.37  tff(c_902, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_894, c_22])).
% 2.63/1.37  tff(c_908, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_902])).
% 2.63/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.63/1.37  
% 2.63/1.37  Inference rules
% 2.63/1.37  ----------------------
% 2.63/1.37  #Ref     : 0
% 2.63/1.37  #Sup     : 220
% 2.63/1.37  #Fact    : 0
% 2.63/1.37  #Define  : 0
% 2.63/1.37  #Split   : 1
% 2.63/1.37  #Chain   : 0
% 2.63/1.37  #Close   : 0
% 2.63/1.37  
% 2.63/1.37  Ordering : KBO
% 2.63/1.37  
% 2.63/1.37  Simplification rules
% 2.63/1.37  ----------------------
% 2.63/1.37  #Subsume      : 5
% 2.63/1.37  #Demod        : 121
% 2.63/1.37  #Tautology    : 154
% 2.63/1.37  #SimpNegUnit  : 0
% 2.63/1.37  #BackRed      : 1
% 2.63/1.37  
% 2.63/1.37  #Partial instantiations: 0
% 2.63/1.37  #Strategies tried      : 1
% 2.63/1.37  
% 2.63/1.37  Timing (in seconds)
% 2.63/1.37  ----------------------
% 2.63/1.38  Preprocessing        : 0.28
% 2.63/1.38  Parsing              : 0.16
% 2.63/1.38  CNF conversion       : 0.02
% 2.63/1.38  Main loop            : 0.31
% 2.63/1.38  Inferencing          : 0.11
% 2.63/1.38  Reduction            : 0.11
% 2.63/1.38  Demodulation         : 0.09
% 2.63/1.38  BG Simplification    : 0.01
% 2.63/1.38  Subsumption          : 0.05
% 2.63/1.38  Abstraction          : 0.01
% 2.63/1.38  MUC search           : 0.00
% 2.63/1.38  Cooper               : 0.00
% 2.63/1.38  Total                : 0.62
% 2.63/1.38  Index Insertion      : 0.00
% 2.63/1.38  Index Deletion       : 0.00
% 2.63/1.38  Index Matching       : 0.00
% 2.63/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
