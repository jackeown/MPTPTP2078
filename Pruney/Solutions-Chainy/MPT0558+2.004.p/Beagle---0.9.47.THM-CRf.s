%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:08 EST 2020

% Result     : Theorem 2.53s
% Output     : CNFRefutation 2.53s
% Verified   : 
% Statistics : Number of formulae       :   39 (  46 expanded)
%              Number of leaves         :   19 (  24 expanded)
%              Depth                    :    9
%              Number of atoms          :   81 ( 100 expanded)
%              Number of equality atoms :   18 (  23 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k9_relat_1(k5_relat_1(B,C),A) = k9_relat_1(C,k9_relat_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t159_relat_1)).

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
    ! [B_24,A_25] :
      ( k7_relat_1(B_24,A_25) = B_24
      | ~ r1_tarski(k1_relat_1(B_24),A_25)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_48,plain,(
    ! [B_26] :
      ( k7_relat_1(B_26,k1_relat_1(B_26)) = B_26
      | ~ v1_relat_1(B_26) ) ),
    inference(resolution,[status(thm)],[c_6,c_42])).

tff(c_10,plain,(
    ! [B_6,A_5] :
      ( k2_relat_1(k7_relat_1(B_6,A_5)) = k9_relat_1(B_6,A_5)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_54,plain,(
    ! [B_26] :
      ( k9_relat_1(B_26,k1_relat_1(B_26)) = k2_relat_1(B_26)
      | ~ v1_relat_1(B_26)
      | ~ v1_relat_1(B_26) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_10])).

tff(c_60,plain,(
    ! [A_27,B_28] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_27,B_28)),k1_relat_1(A_27))
      | ~ v1_relat_1(B_28)
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_16,plain,(
    ! [B_15,A_14] :
      ( k7_relat_1(B_15,A_14) = B_15
      | ~ r1_tarski(k1_relat_1(B_15),A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_94,plain,(
    ! [A_33,B_34] :
      ( k7_relat_1(k5_relat_1(A_33,B_34),k1_relat_1(A_33)) = k5_relat_1(A_33,B_34)
      | ~ v1_relat_1(k5_relat_1(A_33,B_34))
      | ~ v1_relat_1(B_34)
      | ~ v1_relat_1(A_33) ) ),
    inference(resolution,[status(thm)],[c_60,c_16])).

tff(c_107,plain,(
    ! [A_37,B_38] :
      ( k9_relat_1(k5_relat_1(A_37,B_38),k1_relat_1(A_37)) = k2_relat_1(k5_relat_1(A_37,B_38))
      | ~ v1_relat_1(k5_relat_1(A_37,B_38))
      | ~ v1_relat_1(k5_relat_1(A_37,B_38))
      | ~ v1_relat_1(B_38)
      | ~ v1_relat_1(A_37) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_10])).

tff(c_12,plain,(
    ! [B_8,C_10,A_7] :
      ( k9_relat_1(k5_relat_1(B_8,C_10),A_7) = k9_relat_1(C_10,k9_relat_1(B_8,A_7))
      | ~ v1_relat_1(C_10)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_144,plain,(
    ! [B_41,A_42] :
      ( k9_relat_1(B_41,k9_relat_1(A_42,k1_relat_1(A_42))) = k2_relat_1(k5_relat_1(A_42,B_41))
      | ~ v1_relat_1(B_41)
      | ~ v1_relat_1(A_42)
      | ~ v1_relat_1(k5_relat_1(A_42,B_41))
      | ~ v1_relat_1(k5_relat_1(A_42,B_41))
      | ~ v1_relat_1(B_41)
      | ~ v1_relat_1(A_42) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_12])).

tff(c_193,plain,(
    ! [B_46,B_47] :
      ( k9_relat_1(B_46,k2_relat_1(B_47)) = k2_relat_1(k5_relat_1(B_47,B_46))
      | ~ v1_relat_1(B_46)
      | ~ v1_relat_1(B_47)
      | ~ v1_relat_1(k5_relat_1(B_47,B_46))
      | ~ v1_relat_1(k5_relat_1(B_47,B_46))
      | ~ v1_relat_1(B_46)
      | ~ v1_relat_1(B_47)
      | ~ v1_relat_1(B_47)
      | ~ v1_relat_1(B_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_144])).

tff(c_197,plain,(
    ! [B_48,A_49] :
      ( k9_relat_1(B_48,k2_relat_1(A_49)) = k2_relat_1(k5_relat_1(A_49,B_48))
      | ~ v1_relat_1(k5_relat_1(A_49,B_48))
      | ~ v1_relat_1(B_48)
      | ~ v1_relat_1(A_49) ) ),
    inference(resolution,[status(thm)],[c_8,c_193])).

tff(c_202,plain,(
    ! [B_50,A_51] :
      ( k9_relat_1(B_50,k2_relat_1(A_51)) = k2_relat_1(k5_relat_1(A_51,B_50))
      | ~ v1_relat_1(B_50)
      | ~ v1_relat_1(A_51) ) ),
    inference(resolution,[status(thm)],[c_8,c_197])).

tff(c_18,plain,(
    k9_relat_1('#skF_2',k2_relat_1('#skF_1')) != k2_relat_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_212,plain,
    ( ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_18])).

tff(c_227,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_212])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:24:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.53/1.70  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.70  
% 2.53/1.70  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.71  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.53/1.71  
% 2.53/1.71  %Foreground sorts:
% 2.53/1.71  
% 2.53/1.71  
% 2.53/1.71  %Background operators:
% 2.53/1.71  
% 2.53/1.71  
% 2.53/1.71  %Foreground operators:
% 2.53/1.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.53/1.71  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.53/1.71  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.53/1.71  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.53/1.71  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.53/1.71  tff('#skF_2', type, '#skF_2': $i).
% 2.53/1.71  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.53/1.71  tff('#skF_1', type, '#skF_1': $i).
% 2.53/1.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.53/1.71  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.53/1.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.53/1.71  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.53/1.71  
% 2.53/1.73  tff(f_69, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t160_relat_1)).
% 2.53/1.73  tff(f_37, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 2.53/1.73  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.53/1.73  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 2.53/1.73  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 2.53/1.73  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_relat_1)).
% 2.53/1.73  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k9_relat_1(k5_relat_1(B, C), A) = k9_relat_1(C, k9_relat_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t159_relat_1)).
% 2.53/1.73  tff(c_22, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.53/1.73  tff(c_20, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.53/1.73  tff(c_8, plain, (![A_3, B_4]: (v1_relat_1(k5_relat_1(A_3, B_4)) | ~v1_relat_1(B_4) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.53/1.73  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.53/1.73  tff(c_42, plain, (![B_24, A_25]: (k7_relat_1(B_24, A_25)=B_24 | ~r1_tarski(k1_relat_1(B_24), A_25) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.53/1.73  tff(c_48, plain, (![B_26]: (k7_relat_1(B_26, k1_relat_1(B_26))=B_26 | ~v1_relat_1(B_26))), inference(resolution, [status(thm)], [c_6, c_42])).
% 2.53/1.73  tff(c_10, plain, (![B_6, A_5]: (k2_relat_1(k7_relat_1(B_6, A_5))=k9_relat_1(B_6, A_5) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.53/1.73  tff(c_54, plain, (![B_26]: (k9_relat_1(B_26, k1_relat_1(B_26))=k2_relat_1(B_26) | ~v1_relat_1(B_26) | ~v1_relat_1(B_26))), inference(superposition, [status(thm), theory('equality')], [c_48, c_10])).
% 2.53/1.73  tff(c_60, plain, (![A_27, B_28]: (r1_tarski(k1_relat_1(k5_relat_1(A_27, B_28)), k1_relat_1(A_27)) | ~v1_relat_1(B_28) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.53/1.73  tff(c_16, plain, (![B_15, A_14]: (k7_relat_1(B_15, A_14)=B_15 | ~r1_tarski(k1_relat_1(B_15), A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.53/1.73  tff(c_94, plain, (![A_33, B_34]: (k7_relat_1(k5_relat_1(A_33, B_34), k1_relat_1(A_33))=k5_relat_1(A_33, B_34) | ~v1_relat_1(k5_relat_1(A_33, B_34)) | ~v1_relat_1(B_34) | ~v1_relat_1(A_33))), inference(resolution, [status(thm)], [c_60, c_16])).
% 2.53/1.73  tff(c_107, plain, (![A_37, B_38]: (k9_relat_1(k5_relat_1(A_37, B_38), k1_relat_1(A_37))=k2_relat_1(k5_relat_1(A_37, B_38)) | ~v1_relat_1(k5_relat_1(A_37, B_38)) | ~v1_relat_1(k5_relat_1(A_37, B_38)) | ~v1_relat_1(B_38) | ~v1_relat_1(A_37))), inference(superposition, [status(thm), theory('equality')], [c_94, c_10])).
% 2.53/1.73  tff(c_12, plain, (![B_8, C_10, A_7]: (k9_relat_1(k5_relat_1(B_8, C_10), A_7)=k9_relat_1(C_10, k9_relat_1(B_8, A_7)) | ~v1_relat_1(C_10) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.53/1.73  tff(c_144, plain, (![B_41, A_42]: (k9_relat_1(B_41, k9_relat_1(A_42, k1_relat_1(A_42)))=k2_relat_1(k5_relat_1(A_42, B_41)) | ~v1_relat_1(B_41) | ~v1_relat_1(A_42) | ~v1_relat_1(k5_relat_1(A_42, B_41)) | ~v1_relat_1(k5_relat_1(A_42, B_41)) | ~v1_relat_1(B_41) | ~v1_relat_1(A_42))), inference(superposition, [status(thm), theory('equality')], [c_107, c_12])).
% 2.53/1.73  tff(c_193, plain, (![B_46, B_47]: (k9_relat_1(B_46, k2_relat_1(B_47))=k2_relat_1(k5_relat_1(B_47, B_46)) | ~v1_relat_1(B_46) | ~v1_relat_1(B_47) | ~v1_relat_1(k5_relat_1(B_47, B_46)) | ~v1_relat_1(k5_relat_1(B_47, B_46)) | ~v1_relat_1(B_46) | ~v1_relat_1(B_47) | ~v1_relat_1(B_47) | ~v1_relat_1(B_47))), inference(superposition, [status(thm), theory('equality')], [c_54, c_144])).
% 2.53/1.73  tff(c_197, plain, (![B_48, A_49]: (k9_relat_1(B_48, k2_relat_1(A_49))=k2_relat_1(k5_relat_1(A_49, B_48)) | ~v1_relat_1(k5_relat_1(A_49, B_48)) | ~v1_relat_1(B_48) | ~v1_relat_1(A_49))), inference(resolution, [status(thm)], [c_8, c_193])).
% 2.53/1.73  tff(c_202, plain, (![B_50, A_51]: (k9_relat_1(B_50, k2_relat_1(A_51))=k2_relat_1(k5_relat_1(A_51, B_50)) | ~v1_relat_1(B_50) | ~v1_relat_1(A_51))), inference(resolution, [status(thm)], [c_8, c_197])).
% 2.53/1.73  tff(c_18, plain, (k9_relat_1('#skF_2', k2_relat_1('#skF_1'))!=k2_relat_1(k5_relat_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.53/1.73  tff(c_212, plain, (~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_202, c_18])).
% 2.53/1.73  tff(c_227, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_212])).
% 2.53/1.73  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.73  
% 2.53/1.73  Inference rules
% 2.53/1.73  ----------------------
% 2.53/1.73  #Ref     : 0
% 2.53/1.73  #Sup     : 47
% 2.53/1.73  #Fact    : 0
% 2.53/1.73  #Define  : 0
% 2.53/1.73  #Split   : 0
% 2.53/1.73  #Chain   : 0
% 2.53/1.73  #Close   : 0
% 2.53/1.73  
% 2.53/1.73  Ordering : KBO
% 2.53/1.73  
% 2.53/1.73  Simplification rules
% 2.53/1.73  ----------------------
% 2.53/1.73  #Subsume      : 4
% 2.53/1.73  #Demod        : 4
% 2.53/1.73  #Tautology    : 21
% 2.53/1.73  #SimpNegUnit  : 0
% 2.53/1.73  #BackRed      : 0
% 2.53/1.73  
% 2.53/1.73  #Partial instantiations: 0
% 2.53/1.73  #Strategies tried      : 1
% 2.53/1.73  
% 2.53/1.73  Timing (in seconds)
% 2.53/1.73  ----------------------
% 2.53/1.73  Preprocessing        : 0.45
% 2.53/1.73  Parsing              : 0.24
% 2.53/1.73  CNF conversion       : 0.03
% 2.53/1.73  Main loop            : 0.35
% 2.53/1.73  Inferencing          : 0.15
% 2.53/1.73  Reduction            : 0.08
% 2.53/1.73  Demodulation         : 0.06
% 2.53/1.73  BG Simplification    : 0.03
% 2.53/1.73  Subsumption          : 0.07
% 2.53/1.73  Abstraction          : 0.02
% 2.53/1.73  MUC search           : 0.00
% 2.53/1.73  Cooper               : 0.00
% 2.53/1.73  Total                : 0.84
% 2.53/1.73  Index Insertion      : 0.00
% 2.53/1.73  Index Deletion       : 0.00
% 2.53/1.73  Index Matching       : 0.00
% 2.53/1.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
