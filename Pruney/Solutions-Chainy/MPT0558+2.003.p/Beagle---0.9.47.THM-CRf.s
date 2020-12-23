%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:08 EST 2020

% Result     : Theorem 2.31s
% Output     : CNFRefutation 2.31s
% Verified   : 
% Statistics : Number of formulae       :   38 (  46 expanded)
%              Number of leaves         :   19 (  24 expanded)
%              Depth                    :    8
%              Number of atoms          :   76 (  96 expanded)
%              Number of equality atoms :   19 (  26 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_69,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k7_relat_1(k5_relat_1(B,C),A) = k5_relat_1(k7_relat_1(B,A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k9_relat_1(k5_relat_1(B,C),A) = k9_relat_1(C,k9_relat_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_relat_1)).

tff(c_22,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_20,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( v1_relat_1(k5_relat_1(A_3,B_4))
      | ~ v1_relat_1(B_4)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_42,plain,(
    ! [B_25,A_26] :
      ( k7_relat_1(B_25,A_26) = B_25
      | ~ r1_tarski(k1_relat_1(B_25),A_26)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_48,plain,(
    ! [B_27] :
      ( k7_relat_1(B_27,k1_relat_1(B_27)) = B_27
      | ~ v1_relat_1(B_27) ) ),
    inference(resolution,[status(thm)],[c_6,c_42])).

tff(c_12,plain,(
    ! [B_10,A_9] :
      ( k2_relat_1(k7_relat_1(B_10,A_9)) = k9_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_54,plain,(
    ! [B_27] :
      ( k9_relat_1(B_27,k1_relat_1(B_27)) = k2_relat_1(B_27)
      | ~ v1_relat_1(B_27)
      | ~ v1_relat_1(B_27) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_12])).

tff(c_47,plain,(
    ! [B_25] :
      ( k7_relat_1(B_25,k1_relat_1(B_25)) = B_25
      | ~ v1_relat_1(B_25) ) ),
    inference(resolution,[status(thm)],[c_6,c_42])).

tff(c_60,plain,(
    ! [B_28,C_29,A_30] :
      ( k7_relat_1(k5_relat_1(B_28,C_29),A_30) = k5_relat_1(k7_relat_1(B_28,A_30),C_29)
      | ~ v1_relat_1(C_29)
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_106,plain,(
    ! [B_35,A_36,C_37] :
      ( k2_relat_1(k5_relat_1(k7_relat_1(B_35,A_36),C_37)) = k9_relat_1(k5_relat_1(B_35,C_37),A_36)
      | ~ v1_relat_1(k5_relat_1(B_35,C_37))
      | ~ v1_relat_1(C_37)
      | ~ v1_relat_1(B_35) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_12])).

tff(c_152,plain,(
    ! [B_40,C_41] :
      ( k9_relat_1(k5_relat_1(B_40,C_41),k1_relat_1(B_40)) = k2_relat_1(k5_relat_1(B_40,C_41))
      | ~ v1_relat_1(k5_relat_1(B_40,C_41))
      | ~ v1_relat_1(C_41)
      | ~ v1_relat_1(B_40)
      | ~ v1_relat_1(B_40) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_47,c_106])).

tff(c_14,plain,(
    ! [B_12,C_14,A_11] :
      ( k9_relat_1(k5_relat_1(B_12,C_14),A_11) = k9_relat_1(C_14,k9_relat_1(B_12,A_11))
      | ~ v1_relat_1(C_14)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_195,plain,(
    ! [C_44,B_45] :
      ( k9_relat_1(C_44,k9_relat_1(B_45,k1_relat_1(B_45))) = k2_relat_1(k5_relat_1(B_45,C_44))
      | ~ v1_relat_1(C_44)
      | ~ v1_relat_1(B_45)
      | ~ v1_relat_1(k5_relat_1(B_45,C_44))
      | ~ v1_relat_1(C_44)
      | ~ v1_relat_1(B_45)
      | ~ v1_relat_1(B_45) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_14])).

tff(c_219,plain,(
    ! [C_46,B_47] :
      ( k9_relat_1(C_46,k2_relat_1(B_47)) = k2_relat_1(k5_relat_1(B_47,C_46))
      | ~ v1_relat_1(C_46)
      | ~ v1_relat_1(B_47)
      | ~ v1_relat_1(k5_relat_1(B_47,C_46))
      | ~ v1_relat_1(C_46)
      | ~ v1_relat_1(B_47)
      | ~ v1_relat_1(B_47)
      | ~ v1_relat_1(B_47)
      | ~ v1_relat_1(B_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_195])).

tff(c_227,plain,(
    ! [B_48,A_49] :
      ( k9_relat_1(B_48,k2_relat_1(A_49)) = k2_relat_1(k5_relat_1(A_49,B_48))
      | ~ v1_relat_1(B_48)
      | ~ v1_relat_1(A_49) ) ),
    inference(resolution,[status(thm)],[c_8,c_219])).

tff(c_18,plain,(
    k9_relat_1('#skF_2',k2_relat_1('#skF_1')) != k2_relat_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_237,plain,
    ( ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_227,c_18])).

tff(c_255,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_237])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:16:54 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.31/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.31/1.28  
% 2.31/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.31/1.28  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.31/1.28  
% 2.31/1.28  %Foreground sorts:
% 2.31/1.28  
% 2.31/1.28  
% 2.31/1.28  %Background operators:
% 2.31/1.28  
% 2.31/1.28  
% 2.31/1.28  %Foreground operators:
% 2.31/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.31/1.28  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.31/1.28  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.31/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.31/1.28  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.31/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.31/1.28  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.31/1.28  tff('#skF_1', type, '#skF_1': $i).
% 2.31/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.31/1.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.31/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.31/1.28  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.31/1.28  
% 2.31/1.30  tff(f_69, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t160_relat_1)).
% 2.31/1.30  tff(f_37, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 2.31/1.30  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.31/1.30  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 2.31/1.30  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 2.31/1.30  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k7_relat_1(k5_relat_1(B, C), A) = k5_relat_1(k7_relat_1(B, A), C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t112_relat_1)).
% 2.31/1.30  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k9_relat_1(k5_relat_1(B, C), A) = k9_relat_1(C, k9_relat_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t159_relat_1)).
% 2.31/1.30  tff(c_22, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.31/1.30  tff(c_20, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.31/1.30  tff(c_8, plain, (![A_3, B_4]: (v1_relat_1(k5_relat_1(A_3, B_4)) | ~v1_relat_1(B_4) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.31/1.30  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.31/1.30  tff(c_42, plain, (![B_25, A_26]: (k7_relat_1(B_25, A_26)=B_25 | ~r1_tarski(k1_relat_1(B_25), A_26) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.31/1.30  tff(c_48, plain, (![B_27]: (k7_relat_1(B_27, k1_relat_1(B_27))=B_27 | ~v1_relat_1(B_27))), inference(resolution, [status(thm)], [c_6, c_42])).
% 2.31/1.30  tff(c_12, plain, (![B_10, A_9]: (k2_relat_1(k7_relat_1(B_10, A_9))=k9_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.31/1.30  tff(c_54, plain, (![B_27]: (k9_relat_1(B_27, k1_relat_1(B_27))=k2_relat_1(B_27) | ~v1_relat_1(B_27) | ~v1_relat_1(B_27))), inference(superposition, [status(thm), theory('equality')], [c_48, c_12])).
% 2.31/1.30  tff(c_47, plain, (![B_25]: (k7_relat_1(B_25, k1_relat_1(B_25))=B_25 | ~v1_relat_1(B_25))), inference(resolution, [status(thm)], [c_6, c_42])).
% 2.31/1.30  tff(c_60, plain, (![B_28, C_29, A_30]: (k7_relat_1(k5_relat_1(B_28, C_29), A_30)=k5_relat_1(k7_relat_1(B_28, A_30), C_29) | ~v1_relat_1(C_29) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.31/1.30  tff(c_106, plain, (![B_35, A_36, C_37]: (k2_relat_1(k5_relat_1(k7_relat_1(B_35, A_36), C_37))=k9_relat_1(k5_relat_1(B_35, C_37), A_36) | ~v1_relat_1(k5_relat_1(B_35, C_37)) | ~v1_relat_1(C_37) | ~v1_relat_1(B_35))), inference(superposition, [status(thm), theory('equality')], [c_60, c_12])).
% 2.31/1.30  tff(c_152, plain, (![B_40, C_41]: (k9_relat_1(k5_relat_1(B_40, C_41), k1_relat_1(B_40))=k2_relat_1(k5_relat_1(B_40, C_41)) | ~v1_relat_1(k5_relat_1(B_40, C_41)) | ~v1_relat_1(C_41) | ~v1_relat_1(B_40) | ~v1_relat_1(B_40))), inference(superposition, [status(thm), theory('equality')], [c_47, c_106])).
% 2.31/1.30  tff(c_14, plain, (![B_12, C_14, A_11]: (k9_relat_1(k5_relat_1(B_12, C_14), A_11)=k9_relat_1(C_14, k9_relat_1(B_12, A_11)) | ~v1_relat_1(C_14) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.31/1.30  tff(c_195, plain, (![C_44, B_45]: (k9_relat_1(C_44, k9_relat_1(B_45, k1_relat_1(B_45)))=k2_relat_1(k5_relat_1(B_45, C_44)) | ~v1_relat_1(C_44) | ~v1_relat_1(B_45) | ~v1_relat_1(k5_relat_1(B_45, C_44)) | ~v1_relat_1(C_44) | ~v1_relat_1(B_45) | ~v1_relat_1(B_45))), inference(superposition, [status(thm), theory('equality')], [c_152, c_14])).
% 2.31/1.30  tff(c_219, plain, (![C_46, B_47]: (k9_relat_1(C_46, k2_relat_1(B_47))=k2_relat_1(k5_relat_1(B_47, C_46)) | ~v1_relat_1(C_46) | ~v1_relat_1(B_47) | ~v1_relat_1(k5_relat_1(B_47, C_46)) | ~v1_relat_1(C_46) | ~v1_relat_1(B_47) | ~v1_relat_1(B_47) | ~v1_relat_1(B_47) | ~v1_relat_1(B_47))), inference(superposition, [status(thm), theory('equality')], [c_54, c_195])).
% 2.31/1.30  tff(c_227, plain, (![B_48, A_49]: (k9_relat_1(B_48, k2_relat_1(A_49))=k2_relat_1(k5_relat_1(A_49, B_48)) | ~v1_relat_1(B_48) | ~v1_relat_1(A_49))), inference(resolution, [status(thm)], [c_8, c_219])).
% 2.31/1.30  tff(c_18, plain, (k9_relat_1('#skF_2', k2_relat_1('#skF_1'))!=k2_relat_1(k5_relat_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.31/1.30  tff(c_237, plain, (~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_227, c_18])).
% 2.31/1.30  tff(c_255, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_237])).
% 2.31/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.31/1.30  
% 2.31/1.30  Inference rules
% 2.31/1.30  ----------------------
% 2.31/1.30  #Ref     : 0
% 2.31/1.30  #Sup     : 57
% 2.31/1.30  #Fact    : 0
% 2.31/1.30  #Define  : 0
% 2.31/1.30  #Split   : 0
% 2.31/1.30  #Chain   : 0
% 2.31/1.30  #Close   : 0
% 2.31/1.30  
% 2.31/1.30  Ordering : KBO
% 2.31/1.30  
% 2.31/1.30  Simplification rules
% 2.31/1.30  ----------------------
% 2.31/1.30  #Subsume      : 6
% 2.31/1.30  #Demod        : 4
% 2.31/1.30  #Tautology    : 23
% 2.31/1.30  #SimpNegUnit  : 0
% 2.31/1.30  #BackRed      : 0
% 2.31/1.30  
% 2.31/1.30  #Partial instantiations: 0
% 2.31/1.30  #Strategies tried      : 1
% 2.31/1.30  
% 2.31/1.30  Timing (in seconds)
% 2.31/1.30  ----------------------
% 2.31/1.30  Preprocessing        : 0.31
% 2.31/1.30  Parsing              : 0.16
% 2.31/1.30  CNF conversion       : 0.02
% 2.31/1.30  Main loop            : 0.22
% 2.31/1.30  Inferencing          : 0.09
% 2.31/1.30  Reduction            : 0.06
% 2.31/1.30  Demodulation         : 0.04
% 2.31/1.30  BG Simplification    : 0.02
% 2.31/1.30  Subsumption          : 0.04
% 2.31/1.30  Abstraction          : 0.01
% 2.31/1.30  MUC search           : 0.00
% 2.31/1.30  Cooper               : 0.00
% 2.31/1.30  Total                : 0.56
% 2.31/1.30  Index Insertion      : 0.00
% 2.31/1.30  Index Deletion       : 0.00
% 2.31/1.30  Index Matching       : 0.00
% 2.31/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
