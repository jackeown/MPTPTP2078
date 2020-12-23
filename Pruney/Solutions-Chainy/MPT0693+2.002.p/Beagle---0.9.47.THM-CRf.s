%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:51 EST 2020

% Result     : Theorem 2.12s
% Output     : CNFRefutation 2.38s
% Verified   : 
% Statistics : Number of formulae       :   44 (  49 expanded)
%              Number of leaves         :   24 (  28 expanded)
%              Depth                    :    6
%              Number of atoms          :   56 (  67 expanded)
%              Number of equality atoms :   22 (  26 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(f_64,negated_conjecture,(
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

tff(f_57,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(c_26,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_24,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_10,plain,(
    ! [B_7,A_6] : k2_tarski(B_7,A_6) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_71,plain,(
    ! [A_22,B_23] : k1_setfam_1(k2_tarski(A_22,B_23)) = k3_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_86,plain,(
    ! [B_24,A_25] : k1_setfam_1(k2_tarski(B_24,A_25)) = k3_xboole_0(A_25,B_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_71])).

tff(c_14,plain,(
    ! [A_10,B_11] : k1_setfam_1(k2_tarski(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_92,plain,(
    ! [B_24,A_25] : k3_xboole_0(B_24,A_25) = k3_xboole_0(A_25,B_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_14])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    ! [B_14,A_13] :
      ( k10_relat_1(B_14,k3_xboole_0(k2_relat_1(B_14),A_13)) = k10_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(k3_xboole_0(A_3,C_5),B_4)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_228,plain,(
    ! [B_41,A_42] :
      ( k9_relat_1(B_41,k10_relat_1(B_41,A_42)) = A_42
      | ~ r1_tarski(A_42,k2_relat_1(B_41))
      | ~ v1_funct_1(B_41)
      | ~ v1_relat_1(B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_295,plain,(
    ! [B_50,A_51,C_52] :
      ( k9_relat_1(B_50,k10_relat_1(B_50,k3_xboole_0(A_51,C_52))) = k3_xboole_0(A_51,C_52)
      | ~ v1_funct_1(B_50)
      | ~ v1_relat_1(B_50)
      | ~ r1_tarski(A_51,k2_relat_1(B_50)) ) ),
    inference(resolution,[status(thm)],[c_8,c_228])).

tff(c_307,plain,(
    ! [B_14,A_13] :
      ( k9_relat_1(B_14,k10_relat_1(B_14,A_13)) = k3_xboole_0(k2_relat_1(B_14),A_13)
      | ~ v1_funct_1(B_14)
      | ~ v1_relat_1(B_14)
      | ~ r1_tarski(k2_relat_1(B_14),k2_relat_1(B_14))
      | ~ v1_relat_1(B_14) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_295])).

tff(c_380,plain,(
    ! [B_63,A_64] :
      ( k9_relat_1(B_63,k10_relat_1(B_63,A_64)) = k3_xboole_0(k2_relat_1(B_63),A_64)
      | ~ v1_funct_1(B_63)
      | ~ v1_relat_1(B_63) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_307])).

tff(c_160,plain,(
    ! [A_33] :
      ( k9_relat_1(A_33,k1_relat_1(A_33)) = k2_relat_1(A_33)
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_22,plain,(
    k3_xboole_0('#skF_1',k9_relat_1('#skF_2',k1_relat_1('#skF_2'))) != k9_relat_1('#skF_2',k10_relat_1('#skF_2','#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_166,plain,
    ( k9_relat_1('#skF_2',k10_relat_1('#skF_2','#skF_1')) != k3_xboole_0('#skF_1',k2_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_22])).

tff(c_172,plain,(
    k9_relat_1('#skF_2',k10_relat_1('#skF_2','#skF_1')) != k3_xboole_0('#skF_1',k2_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_166])).

tff(c_394,plain,
    ( k3_xboole_0(k2_relat_1('#skF_2'),'#skF_1') != k3_xboole_0('#skF_1',k2_relat_1('#skF_2'))
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_380,c_172])).

tff(c_413,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_92,c_394])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:55:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.12/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.38/1.33  
% 2.38/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.38/1.33  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.38/1.33  
% 2.38/1.33  %Foreground sorts:
% 2.38/1.33  
% 2.38/1.33  
% 2.38/1.33  %Background operators:
% 2.38/1.33  
% 2.38/1.33  
% 2.38/1.33  %Foreground operators:
% 2.38/1.33  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.38/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.38/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.38/1.33  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.38/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.38/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.38/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.38/1.33  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.38/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.38/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.38/1.33  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.38/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.38/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.38/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.38/1.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.38/1.33  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.38/1.33  
% 2.38/1.35  tff(f_64, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = k3_xboole_0(A, k9_relat_1(B, k1_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_funct_1)).
% 2.38/1.35  tff(f_37, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.38/1.35  tff(f_41, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.38/1.35  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.38/1.35  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (k10_relat_1(B, A) = k10_relat_1(B, k3_xboole_0(k2_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t168_relat_1)).
% 2.38/1.35  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_xboole_1)).
% 2.38/1.35  tff(f_57, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_funct_1)).
% 2.38/1.35  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 2.38/1.35  tff(c_26, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.38/1.35  tff(c_24, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.38/1.35  tff(c_10, plain, (![B_7, A_6]: (k2_tarski(B_7, A_6)=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.38/1.35  tff(c_71, plain, (![A_22, B_23]: (k1_setfam_1(k2_tarski(A_22, B_23))=k3_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.38/1.35  tff(c_86, plain, (![B_24, A_25]: (k1_setfam_1(k2_tarski(B_24, A_25))=k3_xboole_0(A_25, B_24))), inference(superposition, [status(thm), theory('equality')], [c_10, c_71])).
% 2.38/1.35  tff(c_14, plain, (![A_10, B_11]: (k1_setfam_1(k2_tarski(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.38/1.35  tff(c_92, plain, (![B_24, A_25]: (k3_xboole_0(B_24, A_25)=k3_xboole_0(A_25, B_24))), inference(superposition, [status(thm), theory('equality')], [c_86, c_14])).
% 2.38/1.35  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.38/1.35  tff(c_18, plain, (![B_14, A_13]: (k10_relat_1(B_14, k3_xboole_0(k2_relat_1(B_14), A_13))=k10_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.38/1.35  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(k3_xboole_0(A_3, C_5), B_4) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.38/1.35  tff(c_228, plain, (![B_41, A_42]: (k9_relat_1(B_41, k10_relat_1(B_41, A_42))=A_42 | ~r1_tarski(A_42, k2_relat_1(B_41)) | ~v1_funct_1(B_41) | ~v1_relat_1(B_41))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.38/1.35  tff(c_295, plain, (![B_50, A_51, C_52]: (k9_relat_1(B_50, k10_relat_1(B_50, k3_xboole_0(A_51, C_52)))=k3_xboole_0(A_51, C_52) | ~v1_funct_1(B_50) | ~v1_relat_1(B_50) | ~r1_tarski(A_51, k2_relat_1(B_50)))), inference(resolution, [status(thm)], [c_8, c_228])).
% 2.38/1.35  tff(c_307, plain, (![B_14, A_13]: (k9_relat_1(B_14, k10_relat_1(B_14, A_13))=k3_xboole_0(k2_relat_1(B_14), A_13) | ~v1_funct_1(B_14) | ~v1_relat_1(B_14) | ~r1_tarski(k2_relat_1(B_14), k2_relat_1(B_14)) | ~v1_relat_1(B_14))), inference(superposition, [status(thm), theory('equality')], [c_18, c_295])).
% 2.38/1.35  tff(c_380, plain, (![B_63, A_64]: (k9_relat_1(B_63, k10_relat_1(B_63, A_64))=k3_xboole_0(k2_relat_1(B_63), A_64) | ~v1_funct_1(B_63) | ~v1_relat_1(B_63))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_307])).
% 2.38/1.35  tff(c_160, plain, (![A_33]: (k9_relat_1(A_33, k1_relat_1(A_33))=k2_relat_1(A_33) | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.38/1.35  tff(c_22, plain, (k3_xboole_0('#skF_1', k9_relat_1('#skF_2', k1_relat_1('#skF_2')))!=k9_relat_1('#skF_2', k10_relat_1('#skF_2', '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.38/1.35  tff(c_166, plain, (k9_relat_1('#skF_2', k10_relat_1('#skF_2', '#skF_1'))!=k3_xboole_0('#skF_1', k2_relat_1('#skF_2')) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_160, c_22])).
% 2.38/1.35  tff(c_172, plain, (k9_relat_1('#skF_2', k10_relat_1('#skF_2', '#skF_1'))!=k3_xboole_0('#skF_1', k2_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_166])).
% 2.38/1.35  tff(c_394, plain, (k3_xboole_0(k2_relat_1('#skF_2'), '#skF_1')!=k3_xboole_0('#skF_1', k2_relat_1('#skF_2')) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_380, c_172])).
% 2.38/1.35  tff(c_413, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_92, c_394])).
% 2.38/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.38/1.35  
% 2.38/1.35  Inference rules
% 2.38/1.35  ----------------------
% 2.38/1.35  #Ref     : 0
% 2.38/1.35  #Sup     : 93
% 2.38/1.35  #Fact    : 0
% 2.38/1.35  #Define  : 0
% 2.38/1.35  #Split   : 0
% 2.38/1.35  #Chain   : 0
% 2.38/1.35  #Close   : 0
% 2.38/1.35  
% 2.38/1.35  Ordering : KBO
% 2.38/1.35  
% 2.38/1.35  Simplification rules
% 2.38/1.35  ----------------------
% 2.38/1.35  #Subsume      : 15
% 2.38/1.35  #Demod        : 10
% 2.38/1.35  #Tautology    : 42
% 2.38/1.35  #SimpNegUnit  : 0
% 2.38/1.35  #BackRed      : 0
% 2.38/1.35  
% 2.38/1.35  #Partial instantiations: 0
% 2.38/1.35  #Strategies tried      : 1
% 2.38/1.35  
% 2.38/1.35  Timing (in seconds)
% 2.38/1.35  ----------------------
% 2.38/1.35  Preprocessing        : 0.31
% 2.38/1.35  Parsing              : 0.16
% 2.38/1.35  CNF conversion       : 0.02
% 2.38/1.35  Main loop            : 0.26
% 2.38/1.35  Inferencing          : 0.09
% 2.38/1.35  Reduction            : 0.09
% 2.38/1.35  Demodulation         : 0.07
% 2.38/1.35  BG Simplification    : 0.02
% 2.38/1.35  Subsumption          : 0.06
% 2.38/1.35  Abstraction          : 0.02
% 2.38/1.35  MUC search           : 0.00
% 2.38/1.35  Cooper               : 0.00
% 2.38/1.35  Total                : 0.60
% 2.38/1.35  Index Insertion      : 0.00
% 2.38/1.35  Index Deletion       : 0.00
% 2.38/1.35  Index Matching       : 0.00
% 2.38/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
