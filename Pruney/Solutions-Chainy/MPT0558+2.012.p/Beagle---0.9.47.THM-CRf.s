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
% DateTime   : Thu Dec  3 10:01:09 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.31s
% Verified   : 
% Statistics : Number of formulae       :   37 (  43 expanded)
%              Number of leaves         :   19 (  23 expanded)
%              Depth                    :   10
%              Number of atoms          :   73 (  89 expanded)
%              Number of equality atoms :   17 (  21 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k9_relat_1 > k5_relat_1 > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_65,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k9_relat_1(k5_relat_1(B,C),A) = k9_relat_1(C,k9_relat_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t159_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k9_relat_1(B,A) = k9_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_relat_1)).

tff(c_18,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_16,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( v1_relat_1(k5_relat_1(A_3,B_4))
      | ~ v1_relat_1(B_4)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_7] :
      ( k9_relat_1(A_7,k1_relat_1(A_7)) = k2_relat_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10,plain,(
    ! [B_9,C_11,A_8] :
      ( k9_relat_1(k5_relat_1(B_9,C_11),A_8) = k9_relat_1(C_11,k9_relat_1(B_9,A_8))
      | ~ v1_relat_1(C_11)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_39,plain,(
    ! [A_23,B_24] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_23,B_24)),k1_relat_1(A_23))
      | ~ v1_relat_1(B_24)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_69,plain,(
    ! [A_28,B_29] :
      ( k3_xboole_0(k1_relat_1(k5_relat_1(A_28,B_29)),k1_relat_1(A_28)) = k1_relat_1(k5_relat_1(A_28,B_29))
      | ~ v1_relat_1(B_29)
      | ~ v1_relat_1(A_28) ) ),
    inference(resolution,[status(thm)],[c_39,c_2])).

tff(c_6,plain,(
    ! [B_6,A_5] :
      ( k9_relat_1(B_6,k3_xboole_0(k1_relat_1(B_6),A_5)) = k9_relat_1(B_6,A_5)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_102,plain,(
    ! [A_32,B_33] :
      ( k9_relat_1(k5_relat_1(A_32,B_33),k1_relat_1(k5_relat_1(A_32,B_33))) = k9_relat_1(k5_relat_1(A_32,B_33),k1_relat_1(A_32))
      | ~ v1_relat_1(k5_relat_1(A_32,B_33))
      | ~ v1_relat_1(B_33)
      | ~ v1_relat_1(A_32) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_6])).

tff(c_124,plain,(
    ! [A_34,B_35] :
      ( k9_relat_1(k5_relat_1(A_34,B_35),k1_relat_1(A_34)) = k2_relat_1(k5_relat_1(A_34,B_35))
      | ~ v1_relat_1(k5_relat_1(A_34,B_35))
      | ~ v1_relat_1(k5_relat_1(A_34,B_35))
      | ~ v1_relat_1(B_35)
      | ~ v1_relat_1(A_34) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_8])).

tff(c_191,plain,(
    ! [C_41,B_42] :
      ( k9_relat_1(C_41,k9_relat_1(B_42,k1_relat_1(B_42))) = k2_relat_1(k5_relat_1(B_42,C_41))
      | ~ v1_relat_1(k5_relat_1(B_42,C_41))
      | ~ v1_relat_1(k5_relat_1(B_42,C_41))
      | ~ v1_relat_1(C_41)
      | ~ v1_relat_1(B_42)
      | ~ v1_relat_1(C_41)
      | ~ v1_relat_1(B_42) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_124])).

tff(c_218,plain,(
    ! [C_43,A_44] :
      ( k9_relat_1(C_43,k2_relat_1(A_44)) = k2_relat_1(k5_relat_1(A_44,C_43))
      | ~ v1_relat_1(k5_relat_1(A_44,C_43))
      | ~ v1_relat_1(k5_relat_1(A_44,C_43))
      | ~ v1_relat_1(C_43)
      | ~ v1_relat_1(A_44)
      | ~ v1_relat_1(C_43)
      | ~ v1_relat_1(A_44)
      | ~ v1_relat_1(A_44) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_191])).

tff(c_222,plain,(
    ! [B_45,A_46] :
      ( k9_relat_1(B_45,k2_relat_1(A_46)) = k2_relat_1(k5_relat_1(A_46,B_45))
      | ~ v1_relat_1(k5_relat_1(A_46,B_45))
      | ~ v1_relat_1(B_45)
      | ~ v1_relat_1(A_46) ) ),
    inference(resolution,[status(thm)],[c_4,c_218])).

tff(c_227,plain,(
    ! [B_47,A_48] :
      ( k9_relat_1(B_47,k2_relat_1(A_48)) = k2_relat_1(k5_relat_1(A_48,B_47))
      | ~ v1_relat_1(B_47)
      | ~ v1_relat_1(A_48) ) ),
    inference(resolution,[status(thm)],[c_4,c_222])).

tff(c_14,plain,(
    k9_relat_1('#skF_2',k2_relat_1('#skF_1')) != k2_relat_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_237,plain,
    ( ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_227,c_14])).

tff(c_249,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16,c_237])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:08:35 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.02/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.30  
% 2.02/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.31  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k5_relat_1 > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.02/1.31  
% 2.02/1.31  %Foreground sorts:
% 2.02/1.31  
% 2.02/1.31  
% 2.02/1.31  %Background operators:
% 2.02/1.31  
% 2.02/1.31  
% 2.02/1.31  %Foreground operators:
% 2.02/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.02/1.31  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.02/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.02/1.31  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.02/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.02/1.31  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.02/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.02/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.02/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.02/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.02/1.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.02/1.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.02/1.31  
% 2.31/1.32  tff(f_65, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t160_relat_1)).
% 2.31/1.32  tff(f_35, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 2.31/1.32  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 2.31/1.32  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k9_relat_1(k5_relat_1(B, C), A) = k9_relat_1(C, k9_relat_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t159_relat_1)).
% 2.31/1.32  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_relat_1)).
% 2.31/1.32  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.31/1.32  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (k9_relat_1(B, A) = k9_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_relat_1)).
% 2.31/1.32  tff(c_18, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.31/1.32  tff(c_16, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.31/1.32  tff(c_4, plain, (![A_3, B_4]: (v1_relat_1(k5_relat_1(A_3, B_4)) | ~v1_relat_1(B_4) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.31/1.32  tff(c_8, plain, (![A_7]: (k9_relat_1(A_7, k1_relat_1(A_7))=k2_relat_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.31/1.32  tff(c_10, plain, (![B_9, C_11, A_8]: (k9_relat_1(k5_relat_1(B_9, C_11), A_8)=k9_relat_1(C_11, k9_relat_1(B_9, A_8)) | ~v1_relat_1(C_11) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.31/1.32  tff(c_39, plain, (![A_23, B_24]: (r1_tarski(k1_relat_1(k5_relat_1(A_23, B_24)), k1_relat_1(A_23)) | ~v1_relat_1(B_24) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.31/1.32  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.31/1.32  tff(c_69, plain, (![A_28, B_29]: (k3_xboole_0(k1_relat_1(k5_relat_1(A_28, B_29)), k1_relat_1(A_28))=k1_relat_1(k5_relat_1(A_28, B_29)) | ~v1_relat_1(B_29) | ~v1_relat_1(A_28))), inference(resolution, [status(thm)], [c_39, c_2])).
% 2.31/1.32  tff(c_6, plain, (![B_6, A_5]: (k9_relat_1(B_6, k3_xboole_0(k1_relat_1(B_6), A_5))=k9_relat_1(B_6, A_5) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.31/1.32  tff(c_102, plain, (![A_32, B_33]: (k9_relat_1(k5_relat_1(A_32, B_33), k1_relat_1(k5_relat_1(A_32, B_33)))=k9_relat_1(k5_relat_1(A_32, B_33), k1_relat_1(A_32)) | ~v1_relat_1(k5_relat_1(A_32, B_33)) | ~v1_relat_1(B_33) | ~v1_relat_1(A_32))), inference(superposition, [status(thm), theory('equality')], [c_69, c_6])).
% 2.31/1.32  tff(c_124, plain, (![A_34, B_35]: (k9_relat_1(k5_relat_1(A_34, B_35), k1_relat_1(A_34))=k2_relat_1(k5_relat_1(A_34, B_35)) | ~v1_relat_1(k5_relat_1(A_34, B_35)) | ~v1_relat_1(k5_relat_1(A_34, B_35)) | ~v1_relat_1(B_35) | ~v1_relat_1(A_34))), inference(superposition, [status(thm), theory('equality')], [c_102, c_8])).
% 2.31/1.32  tff(c_191, plain, (![C_41, B_42]: (k9_relat_1(C_41, k9_relat_1(B_42, k1_relat_1(B_42)))=k2_relat_1(k5_relat_1(B_42, C_41)) | ~v1_relat_1(k5_relat_1(B_42, C_41)) | ~v1_relat_1(k5_relat_1(B_42, C_41)) | ~v1_relat_1(C_41) | ~v1_relat_1(B_42) | ~v1_relat_1(C_41) | ~v1_relat_1(B_42))), inference(superposition, [status(thm), theory('equality')], [c_10, c_124])).
% 2.31/1.32  tff(c_218, plain, (![C_43, A_44]: (k9_relat_1(C_43, k2_relat_1(A_44))=k2_relat_1(k5_relat_1(A_44, C_43)) | ~v1_relat_1(k5_relat_1(A_44, C_43)) | ~v1_relat_1(k5_relat_1(A_44, C_43)) | ~v1_relat_1(C_43) | ~v1_relat_1(A_44) | ~v1_relat_1(C_43) | ~v1_relat_1(A_44) | ~v1_relat_1(A_44))), inference(superposition, [status(thm), theory('equality')], [c_8, c_191])).
% 2.31/1.32  tff(c_222, plain, (![B_45, A_46]: (k9_relat_1(B_45, k2_relat_1(A_46))=k2_relat_1(k5_relat_1(A_46, B_45)) | ~v1_relat_1(k5_relat_1(A_46, B_45)) | ~v1_relat_1(B_45) | ~v1_relat_1(A_46))), inference(resolution, [status(thm)], [c_4, c_218])).
% 2.31/1.32  tff(c_227, plain, (![B_47, A_48]: (k9_relat_1(B_47, k2_relat_1(A_48))=k2_relat_1(k5_relat_1(A_48, B_47)) | ~v1_relat_1(B_47) | ~v1_relat_1(A_48))), inference(resolution, [status(thm)], [c_4, c_222])).
% 2.31/1.32  tff(c_14, plain, (k9_relat_1('#skF_2', k2_relat_1('#skF_1'))!=k2_relat_1(k5_relat_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.31/1.32  tff(c_237, plain, (~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_227, c_14])).
% 2.31/1.32  tff(c_249, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_16, c_237])).
% 2.31/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.32  
% 2.31/1.32  Inference rules
% 2.31/1.32  ----------------------
% 2.31/1.32  #Ref     : 0
% 2.31/1.32  #Sup     : 56
% 2.31/1.32  #Fact    : 0
% 2.31/1.32  #Define  : 0
% 2.31/1.32  #Split   : 0
% 2.31/1.32  #Chain   : 0
% 2.31/1.32  #Close   : 0
% 2.31/1.32  
% 2.31/1.32  Ordering : KBO
% 2.31/1.32  
% 2.31/1.32  Simplification rules
% 2.31/1.32  ----------------------
% 2.31/1.32  #Subsume      : 10
% 2.31/1.32  #Demod        : 2
% 2.31/1.32  #Tautology    : 21
% 2.31/1.32  #SimpNegUnit  : 0
% 2.31/1.32  #BackRed      : 0
% 2.31/1.32  
% 2.31/1.32  #Partial instantiations: 0
% 2.31/1.32  #Strategies tried      : 1
% 2.31/1.32  
% 2.31/1.32  Timing (in seconds)
% 2.31/1.32  ----------------------
% 2.31/1.32  Preprocessing        : 0.30
% 2.31/1.32  Parsing              : 0.17
% 2.31/1.32  CNF conversion       : 0.02
% 2.31/1.32  Main loop            : 0.22
% 2.31/1.32  Inferencing          : 0.10
% 2.31/1.32  Reduction            : 0.05
% 2.31/1.32  Demodulation         : 0.04
% 2.31/1.32  BG Simplification    : 0.02
% 2.31/1.32  Subsumption          : 0.04
% 2.31/1.32  Abstraction          : 0.01
% 2.31/1.32  MUC search           : 0.00
% 2.31/1.32  Cooper               : 0.00
% 2.31/1.32  Total                : 0.54
% 2.31/1.32  Index Insertion      : 0.00
% 2.31/1.32  Index Deletion       : 0.00
% 2.31/1.32  Index Matching       : 0.00
% 2.31/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
