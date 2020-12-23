%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:51 EST 2020

% Result     : Theorem 2.59s
% Output     : CNFRefutation 2.59s
% Verified   : 
% Statistics : Number of formulae       :   48 (  55 expanded)
%              Number of leaves         :   26 (  31 expanded)
%              Depth                    :    6
%              Number of atoms          :   64 (  79 expanded)
%              Number of equality atoms :   25 (  30 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_68,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => k9_relat_1(B,k10_relat_1(B,A)) = k3_xboole_0(A,k9_relat_1(B,k1_relat_1(B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_funct_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_41,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k10_relat_1(B,A) = k10_relat_1(B,k3_xboole_0(k2_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(c_28,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_26,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_10,plain,(
    ! [B_7,A_6] : k2_tarski(B_7,A_6) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_64,plain,(
    ! [A_22,B_23] : k1_setfam_1(k2_tarski(A_22,B_23)) = k3_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_97,plain,(
    ! [A_27,B_28] : k1_setfam_1(k2_tarski(A_27,B_28)) = k3_xboole_0(B_28,A_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_64])).

tff(c_14,plain,(
    ! [A_10,B_11] : k1_setfam_1(k2_tarski(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_103,plain,(
    ! [B_28,A_27] : k3_xboole_0(B_28,A_27) = k3_xboole_0(A_27,B_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_14])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    ! [B_15,A_14] :
      ( k10_relat_1(B_15,k3_xboole_0(k2_relat_1(B_15),A_14)) = k10_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(k3_xboole_0(A_3,C_5),B_4)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_302,plain,(
    ! [B_52,A_53] :
      ( k9_relat_1(B_52,k10_relat_1(B_52,A_53)) = A_53
      | ~ r1_tarski(A_53,k2_relat_1(B_52))
      | ~ v1_funct_1(B_52)
      | ~ v1_relat_1(B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_466,plain,(
    ! [B_74,A_75,C_76] :
      ( k9_relat_1(B_74,k10_relat_1(B_74,k3_xboole_0(A_75,C_76))) = k3_xboole_0(A_75,C_76)
      | ~ v1_funct_1(B_74)
      | ~ v1_relat_1(B_74)
      | ~ r1_tarski(A_75,k2_relat_1(B_74)) ) ),
    inference(resolution,[status(thm)],[c_8,c_302])).

tff(c_478,plain,(
    ! [B_15,A_14] :
      ( k9_relat_1(B_15,k10_relat_1(B_15,A_14)) = k3_xboole_0(k2_relat_1(B_15),A_14)
      | ~ v1_funct_1(B_15)
      | ~ v1_relat_1(B_15)
      | ~ r1_tarski(k2_relat_1(B_15),k2_relat_1(B_15))
      | ~ v1_relat_1(B_15) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_466])).

tff(c_489,plain,(
    ! [B_77,A_78] :
      ( k9_relat_1(B_77,k10_relat_1(B_77,A_78)) = k3_xboole_0(k2_relat_1(B_77),A_78)
      | ~ v1_funct_1(B_77)
      | ~ v1_relat_1(B_77) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_478])).

tff(c_20,plain,(
    ! [A_16] :
      ( k7_relat_1(A_16,k1_relat_1(A_16)) = A_16
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_181,plain,(
    ! [B_39,A_40] :
      ( k2_relat_1(k7_relat_1(B_39,A_40)) = k9_relat_1(B_39,A_40)
      | ~ v1_relat_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_193,plain,(
    ! [A_41] :
      ( k9_relat_1(A_41,k1_relat_1(A_41)) = k2_relat_1(A_41)
      | ~ v1_relat_1(A_41)
      | ~ v1_relat_1(A_41) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_181])).

tff(c_24,plain,(
    k3_xboole_0('#skF_1',k9_relat_1('#skF_2',k1_relat_1('#skF_2'))) != k9_relat_1('#skF_2',k10_relat_1('#skF_2','#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_199,plain,
    ( k9_relat_1('#skF_2',k10_relat_1('#skF_2','#skF_1')) != k3_xboole_0('#skF_1',k2_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_24])).

tff(c_205,plain,(
    k9_relat_1('#skF_2',k10_relat_1('#skF_2','#skF_1')) != k3_xboole_0('#skF_1',k2_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_28,c_199])).

tff(c_503,plain,
    ( k3_xboole_0(k2_relat_1('#skF_2'),'#skF_1') != k3_xboole_0('#skF_1',k2_relat_1('#skF_2'))
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_489,c_205])).

tff(c_522,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_103,c_503])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:31:00 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.59/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.39  
% 2.59/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.40  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.59/1.40  
% 2.59/1.40  %Foreground sorts:
% 2.59/1.40  
% 2.59/1.40  
% 2.59/1.40  %Background operators:
% 2.59/1.40  
% 2.59/1.40  
% 2.59/1.40  %Foreground operators:
% 2.59/1.40  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.59/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.59/1.40  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.59/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.59/1.40  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.59/1.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.59/1.40  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.59/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.59/1.40  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.59/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.59/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.59/1.40  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.59/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.59/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.59/1.40  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.59/1.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.59/1.40  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.59/1.40  
% 2.59/1.41  tff(f_68, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = k3_xboole_0(A, k9_relat_1(B, k1_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_funct_1)).
% 2.59/1.41  tff(f_37, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.59/1.41  tff(f_41, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.59/1.41  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.59/1.41  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (k10_relat_1(B, A) = k10_relat_1(B, k3_xboole_0(k2_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t168_relat_1)).
% 2.59/1.41  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_xboole_1)).
% 2.59/1.41  tff(f_61, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_funct_1)).
% 2.59/1.41  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 2.59/1.41  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 2.59/1.41  tff(c_28, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.59/1.41  tff(c_26, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.59/1.41  tff(c_10, plain, (![B_7, A_6]: (k2_tarski(B_7, A_6)=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.59/1.41  tff(c_64, plain, (![A_22, B_23]: (k1_setfam_1(k2_tarski(A_22, B_23))=k3_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.59/1.41  tff(c_97, plain, (![A_27, B_28]: (k1_setfam_1(k2_tarski(A_27, B_28))=k3_xboole_0(B_28, A_27))), inference(superposition, [status(thm), theory('equality')], [c_10, c_64])).
% 2.59/1.41  tff(c_14, plain, (![A_10, B_11]: (k1_setfam_1(k2_tarski(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.59/1.41  tff(c_103, plain, (![B_28, A_27]: (k3_xboole_0(B_28, A_27)=k3_xboole_0(A_27, B_28))), inference(superposition, [status(thm), theory('equality')], [c_97, c_14])).
% 2.59/1.41  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.59/1.41  tff(c_18, plain, (![B_15, A_14]: (k10_relat_1(B_15, k3_xboole_0(k2_relat_1(B_15), A_14))=k10_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.59/1.41  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(k3_xboole_0(A_3, C_5), B_4) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.59/1.41  tff(c_302, plain, (![B_52, A_53]: (k9_relat_1(B_52, k10_relat_1(B_52, A_53))=A_53 | ~r1_tarski(A_53, k2_relat_1(B_52)) | ~v1_funct_1(B_52) | ~v1_relat_1(B_52))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.59/1.41  tff(c_466, plain, (![B_74, A_75, C_76]: (k9_relat_1(B_74, k10_relat_1(B_74, k3_xboole_0(A_75, C_76)))=k3_xboole_0(A_75, C_76) | ~v1_funct_1(B_74) | ~v1_relat_1(B_74) | ~r1_tarski(A_75, k2_relat_1(B_74)))), inference(resolution, [status(thm)], [c_8, c_302])).
% 2.59/1.41  tff(c_478, plain, (![B_15, A_14]: (k9_relat_1(B_15, k10_relat_1(B_15, A_14))=k3_xboole_0(k2_relat_1(B_15), A_14) | ~v1_funct_1(B_15) | ~v1_relat_1(B_15) | ~r1_tarski(k2_relat_1(B_15), k2_relat_1(B_15)) | ~v1_relat_1(B_15))), inference(superposition, [status(thm), theory('equality')], [c_18, c_466])).
% 2.59/1.41  tff(c_489, plain, (![B_77, A_78]: (k9_relat_1(B_77, k10_relat_1(B_77, A_78))=k3_xboole_0(k2_relat_1(B_77), A_78) | ~v1_funct_1(B_77) | ~v1_relat_1(B_77))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_478])).
% 2.59/1.41  tff(c_20, plain, (![A_16]: (k7_relat_1(A_16, k1_relat_1(A_16))=A_16 | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.59/1.41  tff(c_181, plain, (![B_39, A_40]: (k2_relat_1(k7_relat_1(B_39, A_40))=k9_relat_1(B_39, A_40) | ~v1_relat_1(B_39))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.59/1.41  tff(c_193, plain, (![A_41]: (k9_relat_1(A_41, k1_relat_1(A_41))=k2_relat_1(A_41) | ~v1_relat_1(A_41) | ~v1_relat_1(A_41))), inference(superposition, [status(thm), theory('equality')], [c_20, c_181])).
% 2.59/1.41  tff(c_24, plain, (k3_xboole_0('#skF_1', k9_relat_1('#skF_2', k1_relat_1('#skF_2')))!=k9_relat_1('#skF_2', k10_relat_1('#skF_2', '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.59/1.41  tff(c_199, plain, (k9_relat_1('#skF_2', k10_relat_1('#skF_2', '#skF_1'))!=k3_xboole_0('#skF_1', k2_relat_1('#skF_2')) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_193, c_24])).
% 2.59/1.41  tff(c_205, plain, (k9_relat_1('#skF_2', k10_relat_1('#skF_2', '#skF_1'))!=k3_xboole_0('#skF_1', k2_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_28, c_199])).
% 2.59/1.41  tff(c_503, plain, (k3_xboole_0(k2_relat_1('#skF_2'), '#skF_1')!=k3_xboole_0('#skF_1', k2_relat_1('#skF_2')) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_489, c_205])).
% 2.59/1.41  tff(c_522, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_103, c_503])).
% 2.59/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.41  
% 2.59/1.41  Inference rules
% 2.59/1.41  ----------------------
% 2.59/1.41  #Ref     : 0
% 2.59/1.41  #Sup     : 120
% 2.59/1.41  #Fact    : 0
% 2.59/1.41  #Define  : 0
% 2.59/1.41  #Split   : 0
% 2.59/1.41  #Chain   : 0
% 2.59/1.41  #Close   : 0
% 2.59/1.41  
% 2.59/1.41  Ordering : KBO
% 2.59/1.41  
% 2.59/1.41  Simplification rules
% 2.59/1.41  ----------------------
% 2.59/1.41  #Subsume      : 20
% 2.59/1.41  #Demod        : 11
% 2.59/1.41  #Tautology    : 46
% 2.59/1.41  #SimpNegUnit  : 0
% 2.59/1.41  #BackRed      : 0
% 2.59/1.41  
% 2.59/1.41  #Partial instantiations: 0
% 2.59/1.41  #Strategies tried      : 1
% 2.59/1.41  
% 2.59/1.41  Timing (in seconds)
% 2.59/1.41  ----------------------
% 2.59/1.41  Preprocessing        : 0.32
% 2.59/1.41  Parsing              : 0.17
% 2.59/1.41  CNF conversion       : 0.02
% 2.59/1.41  Main loop            : 0.28
% 2.59/1.41  Inferencing          : 0.10
% 2.59/1.41  Reduction            : 0.09
% 2.59/1.41  Demodulation         : 0.07
% 2.59/1.41  BG Simplification    : 0.02
% 2.59/1.41  Subsumption          : 0.05
% 2.59/1.41  Abstraction          : 0.02
% 2.59/1.41  MUC search           : 0.00
% 2.59/1.41  Cooper               : 0.00
% 2.59/1.41  Total                : 0.62
% 2.59/1.41  Index Insertion      : 0.00
% 2.59/1.41  Index Deletion       : 0.00
% 2.59/1.41  Index Matching       : 0.00
% 2.59/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
