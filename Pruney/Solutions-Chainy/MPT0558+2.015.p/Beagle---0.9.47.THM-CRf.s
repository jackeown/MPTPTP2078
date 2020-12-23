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
% DateTime   : Thu Dec  3 10:01:09 EST 2020

% Result     : Theorem 1.81s
% Output     : CNFRefutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :   38 (  43 expanded)
%              Number of leaves         :   19 (  23 expanded)
%              Depth                    :    9
%              Number of atoms          :   78 (  92 expanded)
%              Number of equality atoms :   18 (  21 expanded)
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

tff(f_67,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k9_relat_1(k5_relat_1(B,C),A) = k9_relat_1(C,k9_relat_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t159_relat_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(c_18,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_16,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( v1_relat_1(k5_relat_1(A_1,B_2))
      | ~ v1_relat_1(B_2)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_14] :
      ( k7_relat_1(A_14,k1_relat_1(A_14)) = A_14
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_29,plain,(
    ! [B_19,A_20] :
      ( k2_relat_1(k7_relat_1(B_19,A_20)) = k9_relat_1(B_19,A_20)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_38,plain,(
    ! [A_14] :
      ( k9_relat_1(A_14,k1_relat_1(A_14)) = k2_relat_1(A_14)
      | ~ v1_relat_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_29])).

tff(c_6,plain,(
    ! [B_6,C_8,A_5] :
      ( k9_relat_1(k5_relat_1(B_6,C_8),A_5) = k9_relat_1(C_8,k9_relat_1(B_6,A_5))
      | ~ v1_relat_1(C_8)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_51,plain,(
    ! [A_24,B_25] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_24,B_25)),k1_relat_1(A_24))
      | ~ v1_relat_1(B_25)
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_10,plain,(
    ! [B_13,A_12] :
      ( k7_relat_1(B_13,A_12) = B_13
      | ~ r1_tarski(k1_relat_1(B_13),A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_73,plain,(
    ! [A_29,B_30] :
      ( k7_relat_1(k5_relat_1(A_29,B_30),k1_relat_1(A_29)) = k5_relat_1(A_29,B_30)
      | ~ v1_relat_1(k5_relat_1(A_29,B_30))
      | ~ v1_relat_1(B_30)
      | ~ v1_relat_1(A_29) ) ),
    inference(resolution,[status(thm)],[c_51,c_10])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( k2_relat_1(k7_relat_1(B_4,A_3)) = k9_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_85,plain,(
    ! [A_31,B_32] :
      ( k9_relat_1(k5_relat_1(A_31,B_32),k1_relat_1(A_31)) = k2_relat_1(k5_relat_1(A_31,B_32))
      | ~ v1_relat_1(k5_relat_1(A_31,B_32))
      | ~ v1_relat_1(k5_relat_1(A_31,B_32))
      | ~ v1_relat_1(B_32)
      | ~ v1_relat_1(A_31) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_4])).

tff(c_122,plain,(
    ! [C_35,B_36] :
      ( k9_relat_1(C_35,k9_relat_1(B_36,k1_relat_1(B_36))) = k2_relat_1(k5_relat_1(B_36,C_35))
      | ~ v1_relat_1(k5_relat_1(B_36,C_35))
      | ~ v1_relat_1(k5_relat_1(B_36,C_35))
      | ~ v1_relat_1(C_35)
      | ~ v1_relat_1(B_36)
      | ~ v1_relat_1(C_35)
      | ~ v1_relat_1(B_36) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_85])).

tff(c_146,plain,(
    ! [C_37,A_38] :
      ( k9_relat_1(C_37,k2_relat_1(A_38)) = k2_relat_1(k5_relat_1(A_38,C_37))
      | ~ v1_relat_1(k5_relat_1(A_38,C_37))
      | ~ v1_relat_1(k5_relat_1(A_38,C_37))
      | ~ v1_relat_1(C_37)
      | ~ v1_relat_1(A_38)
      | ~ v1_relat_1(C_37)
      | ~ v1_relat_1(A_38)
      | ~ v1_relat_1(A_38)
      | ~ v1_relat_1(A_38) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_122])).

tff(c_150,plain,(
    ! [B_39,A_40] :
      ( k9_relat_1(B_39,k2_relat_1(A_40)) = k2_relat_1(k5_relat_1(A_40,B_39))
      | ~ v1_relat_1(k5_relat_1(A_40,B_39))
      | ~ v1_relat_1(B_39)
      | ~ v1_relat_1(A_40) ) ),
    inference(resolution,[status(thm)],[c_2,c_146])).

tff(c_155,plain,(
    ! [B_41,A_42] :
      ( k9_relat_1(B_41,k2_relat_1(A_42)) = k2_relat_1(k5_relat_1(A_42,B_41))
      | ~ v1_relat_1(B_41)
      | ~ v1_relat_1(A_42) ) ),
    inference(resolution,[status(thm)],[c_2,c_150])).

tff(c_14,plain,(
    k9_relat_1('#skF_2',k2_relat_1('#skF_1')) != k2_relat_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_165,plain,
    ( ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_14])).

tff(c_180,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16,c_165])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:08:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.81/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.20  
% 1.81/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.20  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.81/1.20  
% 1.81/1.20  %Foreground sorts:
% 1.81/1.20  
% 1.81/1.20  
% 1.81/1.20  %Background operators:
% 1.81/1.20  
% 1.81/1.20  
% 1.81/1.20  %Foreground operators:
% 1.81/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.81/1.20  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.81/1.20  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.81/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.81/1.20  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.81/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.81/1.20  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.81/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.81/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.81/1.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.81/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.81/1.20  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.81/1.20  
% 1.81/1.21  tff(f_67, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t160_relat_1)).
% 1.81/1.21  tff(f_31, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 1.81/1.21  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 1.81/1.21  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 1.81/1.21  tff(f_42, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k9_relat_1(k5_relat_1(B, C), A) = k9_relat_1(C, k9_relat_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t159_relat_1)).
% 1.81/1.21  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_relat_1)).
% 1.81/1.21  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 1.81/1.21  tff(c_18, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.81/1.21  tff(c_16, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.81/1.21  tff(c_2, plain, (![A_1, B_2]: (v1_relat_1(k5_relat_1(A_1, B_2)) | ~v1_relat_1(B_2) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.81/1.21  tff(c_12, plain, (![A_14]: (k7_relat_1(A_14, k1_relat_1(A_14))=A_14 | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.81/1.21  tff(c_29, plain, (![B_19, A_20]: (k2_relat_1(k7_relat_1(B_19, A_20))=k9_relat_1(B_19, A_20) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.81/1.21  tff(c_38, plain, (![A_14]: (k9_relat_1(A_14, k1_relat_1(A_14))=k2_relat_1(A_14) | ~v1_relat_1(A_14) | ~v1_relat_1(A_14))), inference(superposition, [status(thm), theory('equality')], [c_12, c_29])).
% 1.81/1.21  tff(c_6, plain, (![B_6, C_8, A_5]: (k9_relat_1(k5_relat_1(B_6, C_8), A_5)=k9_relat_1(C_8, k9_relat_1(B_6, A_5)) | ~v1_relat_1(C_8) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.81/1.21  tff(c_51, plain, (![A_24, B_25]: (r1_tarski(k1_relat_1(k5_relat_1(A_24, B_25)), k1_relat_1(A_24)) | ~v1_relat_1(B_25) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.81/1.21  tff(c_10, plain, (![B_13, A_12]: (k7_relat_1(B_13, A_12)=B_13 | ~r1_tarski(k1_relat_1(B_13), A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.81/1.21  tff(c_73, plain, (![A_29, B_30]: (k7_relat_1(k5_relat_1(A_29, B_30), k1_relat_1(A_29))=k5_relat_1(A_29, B_30) | ~v1_relat_1(k5_relat_1(A_29, B_30)) | ~v1_relat_1(B_30) | ~v1_relat_1(A_29))), inference(resolution, [status(thm)], [c_51, c_10])).
% 1.81/1.21  tff(c_4, plain, (![B_4, A_3]: (k2_relat_1(k7_relat_1(B_4, A_3))=k9_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.81/1.21  tff(c_85, plain, (![A_31, B_32]: (k9_relat_1(k5_relat_1(A_31, B_32), k1_relat_1(A_31))=k2_relat_1(k5_relat_1(A_31, B_32)) | ~v1_relat_1(k5_relat_1(A_31, B_32)) | ~v1_relat_1(k5_relat_1(A_31, B_32)) | ~v1_relat_1(B_32) | ~v1_relat_1(A_31))), inference(superposition, [status(thm), theory('equality')], [c_73, c_4])).
% 1.81/1.21  tff(c_122, plain, (![C_35, B_36]: (k9_relat_1(C_35, k9_relat_1(B_36, k1_relat_1(B_36)))=k2_relat_1(k5_relat_1(B_36, C_35)) | ~v1_relat_1(k5_relat_1(B_36, C_35)) | ~v1_relat_1(k5_relat_1(B_36, C_35)) | ~v1_relat_1(C_35) | ~v1_relat_1(B_36) | ~v1_relat_1(C_35) | ~v1_relat_1(B_36))), inference(superposition, [status(thm), theory('equality')], [c_6, c_85])).
% 1.81/1.21  tff(c_146, plain, (![C_37, A_38]: (k9_relat_1(C_37, k2_relat_1(A_38))=k2_relat_1(k5_relat_1(A_38, C_37)) | ~v1_relat_1(k5_relat_1(A_38, C_37)) | ~v1_relat_1(k5_relat_1(A_38, C_37)) | ~v1_relat_1(C_37) | ~v1_relat_1(A_38) | ~v1_relat_1(C_37) | ~v1_relat_1(A_38) | ~v1_relat_1(A_38) | ~v1_relat_1(A_38))), inference(superposition, [status(thm), theory('equality')], [c_38, c_122])).
% 1.81/1.21  tff(c_150, plain, (![B_39, A_40]: (k9_relat_1(B_39, k2_relat_1(A_40))=k2_relat_1(k5_relat_1(A_40, B_39)) | ~v1_relat_1(k5_relat_1(A_40, B_39)) | ~v1_relat_1(B_39) | ~v1_relat_1(A_40))), inference(resolution, [status(thm)], [c_2, c_146])).
% 1.81/1.21  tff(c_155, plain, (![B_41, A_42]: (k9_relat_1(B_41, k2_relat_1(A_42))=k2_relat_1(k5_relat_1(A_42, B_41)) | ~v1_relat_1(B_41) | ~v1_relat_1(A_42))), inference(resolution, [status(thm)], [c_2, c_150])).
% 1.81/1.21  tff(c_14, plain, (k9_relat_1('#skF_2', k2_relat_1('#skF_1'))!=k2_relat_1(k5_relat_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.81/1.21  tff(c_165, plain, (~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_155, c_14])).
% 1.81/1.21  tff(c_180, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_16, c_165])).
% 1.81/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.21  
% 1.81/1.21  Inference rules
% 1.81/1.21  ----------------------
% 1.81/1.21  #Ref     : 0
% 1.81/1.21  #Sup     : 38
% 1.81/1.21  #Fact    : 0
% 1.81/1.21  #Define  : 0
% 1.81/1.21  #Split   : 0
% 1.81/1.21  #Chain   : 0
% 1.81/1.21  #Close   : 0
% 1.81/1.21  
% 1.81/1.21  Ordering : KBO
% 1.81/1.21  
% 1.81/1.21  Simplification rules
% 1.81/1.21  ----------------------
% 1.81/1.21  #Subsume      : 4
% 1.81/1.21  #Demod        : 2
% 1.81/1.21  #Tautology    : 17
% 1.81/1.21  #SimpNegUnit  : 0
% 1.81/1.21  #BackRed      : 0
% 1.81/1.21  
% 1.81/1.21  #Partial instantiations: 0
% 1.81/1.21  #Strategies tried      : 1
% 1.81/1.21  
% 1.81/1.21  Timing (in seconds)
% 1.81/1.21  ----------------------
% 1.81/1.21  Preprocessing        : 0.26
% 1.81/1.21  Parsing              : 0.13
% 1.81/1.21  CNF conversion       : 0.02
% 1.81/1.21  Main loop            : 0.17
% 1.81/1.21  Inferencing          : 0.08
% 1.81/1.21  Reduction            : 0.04
% 1.81/1.21  Demodulation         : 0.03
% 1.81/1.21  BG Simplification    : 0.01
% 1.81/1.21  Subsumption          : 0.03
% 1.81/1.21  Abstraction          : 0.01
% 1.81/1.21  MUC search           : 0.00
% 1.81/1.21  Cooper               : 0.00
% 1.81/1.21  Total                : 0.45
% 1.81/1.21  Index Insertion      : 0.00
% 1.81/1.21  Index Deletion       : 0.00
% 1.81/1.21  Index Matching       : 0.00
% 1.81/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
