%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:55 EST 2020

% Result     : Theorem 2.92s
% Output     : CNFRefutation 3.01s
% Verified   : 
% Statistics : Number of formulae       :   38 (  48 expanded)
%              Number of leaves         :   17 (  24 expanded)
%              Depth                    :   10
%              Number of atoms          :   87 ( 114 expanded)
%              Number of equality atoms :   21 (  29 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k5_relat_1 > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(f_56,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k10_relat_1(k5_relat_1(B,C),A) = k10_relat_1(B,k10_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t181_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k10_relat_1(B,A) = k10_relat_1(B,k3_xboole_0(k2_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

tff(c_16,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_14,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( v1_relat_1(k5_relat_1(A_3,B_4))
      | ~ v1_relat_1(B_4)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_8,plain,(
    ! [A_7] :
      ( k10_relat_1(A_7,k2_relat_1(A_7)) = k1_relat_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_104,plain,(
    ! [B_22,C_23,A_24] :
      ( k10_relat_1(k5_relat_1(B_22,C_23),A_24) = k10_relat_1(B_22,k10_relat_1(C_23,A_24))
      | ~ v1_relat_1(C_23)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_119,plain,(
    ! [B_22,C_23] :
      ( k10_relat_1(B_22,k10_relat_1(C_23,k2_relat_1(k5_relat_1(B_22,C_23)))) = k1_relat_1(k5_relat_1(B_22,C_23))
      | ~ v1_relat_1(k5_relat_1(B_22,C_23))
      | ~ v1_relat_1(C_23)
      | ~ v1_relat_1(B_22) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_8])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_60,plain,(
    ! [B_18,A_19] :
      ( k10_relat_1(B_18,k3_xboole_0(k2_relat_1(B_18),A_19)) = k10_relat_1(B_18,A_19)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_70,plain,(
    ! [B_18,B_2] :
      ( k10_relat_1(B_18,k3_xboole_0(B_2,k2_relat_1(B_18))) = k10_relat_1(B_18,B_2)
      | ~ v1_relat_1(B_18) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_60])).

tff(c_6,plain,(
    ! [B_6,A_5] :
      ( k10_relat_1(B_6,k3_xboole_0(k2_relat_1(B_6),A_5)) = k10_relat_1(B_6,A_5)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_158,plain,(
    ! [B_27,C_28,A_29] :
      ( k10_relat_1(B_27,k10_relat_1(C_28,k3_xboole_0(k2_relat_1(k5_relat_1(B_27,C_28)),A_29))) = k10_relat_1(k5_relat_1(B_27,C_28),A_29)
      | ~ v1_relat_1(C_28)
      | ~ v1_relat_1(B_27)
      | ~ v1_relat_1(k5_relat_1(B_27,C_28)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_104])).

tff(c_234,plain,(
    ! [B_33,B_34] :
      ( k10_relat_1(B_33,k10_relat_1(B_34,k2_relat_1(k5_relat_1(B_33,B_34)))) = k10_relat_1(k5_relat_1(B_33,B_34),k2_relat_1(B_34))
      | ~ v1_relat_1(B_34)
      | ~ v1_relat_1(B_33)
      | ~ v1_relat_1(k5_relat_1(B_33,B_34))
      | ~ v1_relat_1(B_34) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_158])).

tff(c_261,plain,(
    ! [B_35,C_36] :
      ( k10_relat_1(k5_relat_1(B_35,C_36),k2_relat_1(C_36)) = k1_relat_1(k5_relat_1(B_35,C_36))
      | ~ v1_relat_1(C_36)
      | ~ v1_relat_1(B_35)
      | ~ v1_relat_1(k5_relat_1(B_35,C_36))
      | ~ v1_relat_1(C_36)
      | ~ v1_relat_1(k5_relat_1(B_35,C_36))
      | ~ v1_relat_1(C_36)
      | ~ v1_relat_1(B_35) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_234])).

tff(c_10,plain,(
    ! [B_9,C_11,A_8] :
      ( k10_relat_1(k5_relat_1(B_9,C_11),A_8) = k10_relat_1(B_9,k10_relat_1(C_11,A_8))
      | ~ v1_relat_1(C_11)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_277,plain,(
    ! [B_37,C_38] :
      ( k10_relat_1(B_37,k10_relat_1(C_38,k2_relat_1(C_38))) = k1_relat_1(k5_relat_1(B_37,C_38))
      | ~ v1_relat_1(C_38)
      | ~ v1_relat_1(B_37)
      | ~ v1_relat_1(C_38)
      | ~ v1_relat_1(B_37)
      | ~ v1_relat_1(k5_relat_1(B_37,C_38))
      | ~ v1_relat_1(C_38)
      | ~ v1_relat_1(k5_relat_1(B_37,C_38))
      | ~ v1_relat_1(C_38)
      | ~ v1_relat_1(B_37) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_261,c_10])).

tff(c_301,plain,(
    ! [B_39,A_40] :
      ( k10_relat_1(B_39,k1_relat_1(A_40)) = k1_relat_1(k5_relat_1(B_39,A_40))
      | ~ v1_relat_1(A_40)
      | ~ v1_relat_1(B_39)
      | ~ v1_relat_1(A_40)
      | ~ v1_relat_1(B_39)
      | ~ v1_relat_1(k5_relat_1(B_39,A_40))
      | ~ v1_relat_1(A_40)
      | ~ v1_relat_1(k5_relat_1(B_39,A_40))
      | ~ v1_relat_1(A_40)
      | ~ v1_relat_1(B_39)
      | ~ v1_relat_1(A_40) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_277])).

tff(c_330,plain,(
    ! [A_44,B_45] :
      ( k10_relat_1(A_44,k1_relat_1(B_45)) = k1_relat_1(k5_relat_1(A_44,B_45))
      | ~ v1_relat_1(k5_relat_1(A_44,B_45))
      | ~ v1_relat_1(B_45)
      | ~ v1_relat_1(A_44) ) ),
    inference(resolution,[status(thm)],[c_4,c_301])).

tff(c_335,plain,(
    ! [A_46,B_47] :
      ( k10_relat_1(A_46,k1_relat_1(B_47)) = k1_relat_1(k5_relat_1(A_46,B_47))
      | ~ v1_relat_1(B_47)
      | ~ v1_relat_1(A_46) ) ),
    inference(resolution,[status(thm)],[c_4,c_330])).

tff(c_12,plain,(
    k10_relat_1('#skF_1',k1_relat_1('#skF_2')) != k1_relat_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_345,plain,
    ( ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_335,c_12])).

tff(c_357,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_345])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:43:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.92/1.76  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.92/1.76  
% 2.92/1.77  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.92/1.77  %$ v1_relat_1 > k5_relat_1 > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.92/1.77  
% 2.92/1.77  %Foreground sorts:
% 2.92/1.77  
% 2.92/1.77  
% 2.92/1.77  %Background operators:
% 2.92/1.77  
% 2.92/1.77  
% 2.92/1.77  %Foreground operators:
% 2.92/1.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.92/1.77  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.92/1.77  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.92/1.77  tff('#skF_2', type, '#skF_2': $i).
% 2.92/1.77  tff('#skF_1', type, '#skF_1': $i).
% 2.92/1.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.92/1.77  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.92/1.77  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.92/1.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.92/1.77  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.92/1.77  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.92/1.77  
% 3.01/1.79  tff(f_56, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 3.01/1.79  tff(f_33, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 3.01/1.79  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 3.01/1.79  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k10_relat_1(k5_relat_1(B, C), A) = k10_relat_1(B, k10_relat_1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t181_relat_1)).
% 3.01/1.79  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.01/1.79  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (k10_relat_1(B, A) = k10_relat_1(B, k3_xboole_0(k2_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t168_relat_1)).
% 3.01/1.79  tff(c_16, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.01/1.79  tff(c_14, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.01/1.79  tff(c_4, plain, (![A_3, B_4]: (v1_relat_1(k5_relat_1(A_3, B_4)) | ~v1_relat_1(B_4) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.01/1.79  tff(c_8, plain, (![A_7]: (k10_relat_1(A_7, k2_relat_1(A_7))=k1_relat_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.01/1.79  tff(c_104, plain, (![B_22, C_23, A_24]: (k10_relat_1(k5_relat_1(B_22, C_23), A_24)=k10_relat_1(B_22, k10_relat_1(C_23, A_24)) | ~v1_relat_1(C_23) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.01/1.79  tff(c_119, plain, (![B_22, C_23]: (k10_relat_1(B_22, k10_relat_1(C_23, k2_relat_1(k5_relat_1(B_22, C_23))))=k1_relat_1(k5_relat_1(B_22, C_23)) | ~v1_relat_1(k5_relat_1(B_22, C_23)) | ~v1_relat_1(C_23) | ~v1_relat_1(B_22))), inference(superposition, [status(thm), theory('equality')], [c_104, c_8])).
% 3.01/1.79  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.01/1.79  tff(c_60, plain, (![B_18, A_19]: (k10_relat_1(B_18, k3_xboole_0(k2_relat_1(B_18), A_19))=k10_relat_1(B_18, A_19) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.01/1.79  tff(c_70, plain, (![B_18, B_2]: (k10_relat_1(B_18, k3_xboole_0(B_2, k2_relat_1(B_18)))=k10_relat_1(B_18, B_2) | ~v1_relat_1(B_18))), inference(superposition, [status(thm), theory('equality')], [c_2, c_60])).
% 3.01/1.79  tff(c_6, plain, (![B_6, A_5]: (k10_relat_1(B_6, k3_xboole_0(k2_relat_1(B_6), A_5))=k10_relat_1(B_6, A_5) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.01/1.79  tff(c_158, plain, (![B_27, C_28, A_29]: (k10_relat_1(B_27, k10_relat_1(C_28, k3_xboole_0(k2_relat_1(k5_relat_1(B_27, C_28)), A_29)))=k10_relat_1(k5_relat_1(B_27, C_28), A_29) | ~v1_relat_1(C_28) | ~v1_relat_1(B_27) | ~v1_relat_1(k5_relat_1(B_27, C_28)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_104])).
% 3.01/1.79  tff(c_234, plain, (![B_33, B_34]: (k10_relat_1(B_33, k10_relat_1(B_34, k2_relat_1(k5_relat_1(B_33, B_34))))=k10_relat_1(k5_relat_1(B_33, B_34), k2_relat_1(B_34)) | ~v1_relat_1(B_34) | ~v1_relat_1(B_33) | ~v1_relat_1(k5_relat_1(B_33, B_34)) | ~v1_relat_1(B_34))), inference(superposition, [status(thm), theory('equality')], [c_70, c_158])).
% 3.01/1.79  tff(c_261, plain, (![B_35, C_36]: (k10_relat_1(k5_relat_1(B_35, C_36), k2_relat_1(C_36))=k1_relat_1(k5_relat_1(B_35, C_36)) | ~v1_relat_1(C_36) | ~v1_relat_1(B_35) | ~v1_relat_1(k5_relat_1(B_35, C_36)) | ~v1_relat_1(C_36) | ~v1_relat_1(k5_relat_1(B_35, C_36)) | ~v1_relat_1(C_36) | ~v1_relat_1(B_35))), inference(superposition, [status(thm), theory('equality')], [c_119, c_234])).
% 3.01/1.79  tff(c_10, plain, (![B_9, C_11, A_8]: (k10_relat_1(k5_relat_1(B_9, C_11), A_8)=k10_relat_1(B_9, k10_relat_1(C_11, A_8)) | ~v1_relat_1(C_11) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.01/1.79  tff(c_277, plain, (![B_37, C_38]: (k10_relat_1(B_37, k10_relat_1(C_38, k2_relat_1(C_38)))=k1_relat_1(k5_relat_1(B_37, C_38)) | ~v1_relat_1(C_38) | ~v1_relat_1(B_37) | ~v1_relat_1(C_38) | ~v1_relat_1(B_37) | ~v1_relat_1(k5_relat_1(B_37, C_38)) | ~v1_relat_1(C_38) | ~v1_relat_1(k5_relat_1(B_37, C_38)) | ~v1_relat_1(C_38) | ~v1_relat_1(B_37))), inference(superposition, [status(thm), theory('equality')], [c_261, c_10])).
% 3.01/1.79  tff(c_301, plain, (![B_39, A_40]: (k10_relat_1(B_39, k1_relat_1(A_40))=k1_relat_1(k5_relat_1(B_39, A_40)) | ~v1_relat_1(A_40) | ~v1_relat_1(B_39) | ~v1_relat_1(A_40) | ~v1_relat_1(B_39) | ~v1_relat_1(k5_relat_1(B_39, A_40)) | ~v1_relat_1(A_40) | ~v1_relat_1(k5_relat_1(B_39, A_40)) | ~v1_relat_1(A_40) | ~v1_relat_1(B_39) | ~v1_relat_1(A_40))), inference(superposition, [status(thm), theory('equality')], [c_8, c_277])).
% 3.01/1.79  tff(c_330, plain, (![A_44, B_45]: (k10_relat_1(A_44, k1_relat_1(B_45))=k1_relat_1(k5_relat_1(A_44, B_45)) | ~v1_relat_1(k5_relat_1(A_44, B_45)) | ~v1_relat_1(B_45) | ~v1_relat_1(A_44))), inference(resolution, [status(thm)], [c_4, c_301])).
% 3.01/1.79  tff(c_335, plain, (![A_46, B_47]: (k10_relat_1(A_46, k1_relat_1(B_47))=k1_relat_1(k5_relat_1(A_46, B_47)) | ~v1_relat_1(B_47) | ~v1_relat_1(A_46))), inference(resolution, [status(thm)], [c_4, c_330])).
% 3.01/1.79  tff(c_12, plain, (k10_relat_1('#skF_1', k1_relat_1('#skF_2'))!=k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.01/1.79  tff(c_345, plain, (~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_335, c_12])).
% 3.01/1.79  tff(c_357, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_345])).
% 3.01/1.79  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.01/1.79  
% 3.01/1.79  Inference rules
% 3.01/1.79  ----------------------
% 3.01/1.79  #Ref     : 0
% 3.01/1.79  #Sup     : 81
% 3.01/1.79  #Fact    : 0
% 3.01/1.79  #Define  : 0
% 3.01/1.79  #Split   : 0
% 3.01/1.79  #Chain   : 0
% 3.01/1.79  #Close   : 0
% 3.01/1.79  
% 3.01/1.79  Ordering : KBO
% 3.01/1.79  
% 3.01/1.79  Simplification rules
% 3.01/1.79  ----------------------
% 3.01/1.79  #Subsume      : 15
% 3.01/1.79  #Demod        : 2
% 3.01/1.79  #Tautology    : 35
% 3.01/1.79  #SimpNegUnit  : 0
% 3.01/1.79  #BackRed      : 0
% 3.01/1.79  
% 3.01/1.79  #Partial instantiations: 0
% 3.01/1.79  #Strategies tried      : 1
% 3.01/1.79  
% 3.01/1.79  Timing (in seconds)
% 3.01/1.79  ----------------------
% 3.01/1.79  Preprocessing        : 0.44
% 3.01/1.79  Parsing              : 0.23
% 3.01/1.79  CNF conversion       : 0.03
% 3.01/1.79  Main loop            : 0.43
% 3.01/1.79  Inferencing          : 0.19
% 3.01/1.79  Reduction            : 0.10
% 3.01/1.79  Demodulation         : 0.08
% 3.01/1.79  BG Simplification    : 0.03
% 3.01/1.79  Subsumption          : 0.09
% 3.01/1.80  Abstraction          : 0.02
% 3.01/1.80  MUC search           : 0.00
% 3.01/1.80  Cooper               : 0.00
% 3.01/1.80  Total                : 0.91
% 3.01/1.80  Index Insertion      : 0.00
% 3.01/1.80  Index Deletion       : 0.00
% 3.01/1.80  Index Matching       : 0.00
% 3.01/1.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
