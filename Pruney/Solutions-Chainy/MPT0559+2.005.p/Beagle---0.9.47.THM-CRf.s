%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:10 EST 2020

% Result     : Theorem 2.20s
% Output     : CNFRefutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :   43 (  54 expanded)
%              Number of leaves         :   21 (  27 expanded)
%              Depth                    :   10
%              Number of atoms          :   66 (  86 expanded)
%              Number of equality atoms :   11 (  15 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => r1_tarski(k9_relat_1(k7_relat_1(C,A),B),k9_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t161_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k9_relat_1(B,A) = k9_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_relat_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(c_18,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( v1_relat_1(k7_relat_1(A_1,B_2))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_51,plain,(
    ! [C_27,A_28,B_29] :
      ( k7_relat_1(k7_relat_1(C_27,A_28),B_29) = k7_relat_1(C_27,k3_xboole_0(A_28,B_29))
      | ~ v1_relat_1(C_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_14,A_13)),A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_63,plain,(
    ! [C_27,A_28,B_29] :
      ( r1_tarski(k1_relat_1(k7_relat_1(C_27,k3_xboole_0(A_28,B_29))),B_29)
      | ~ v1_relat_1(k7_relat_1(C_27,A_28))
      | ~ v1_relat_1(C_27) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_51,c_12])).

tff(c_14,plain,(
    ! [B_16,A_15] :
      ( k3_xboole_0(k1_relat_1(B_16),A_15) = k1_relat_1(k7_relat_1(B_16,A_15))
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_6,plain,(
    ! [B_7,A_6] :
      ( k9_relat_1(B_7,k3_xboole_0(k1_relat_1(B_7),A_6)) = k9_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_75,plain,(
    ! [C_30,A_31,B_32] :
      ( r1_tarski(k9_relat_1(C_30,A_31),k9_relat_1(C_30,B_32))
      | ~ r1_tarski(A_31,B_32)
      | ~ v1_relat_1(C_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_144,plain,(
    ! [B_44,A_45,B_46] :
      ( r1_tarski(k9_relat_1(B_44,A_45),k9_relat_1(B_44,B_46))
      | ~ r1_tarski(k3_xboole_0(k1_relat_1(B_44),A_45),B_46)
      | ~ v1_relat_1(B_44)
      | ~ v1_relat_1(B_44) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_75])).

tff(c_314,plain,(
    ! [B_63,A_64,B_65] :
      ( r1_tarski(k9_relat_1(B_63,A_64),k9_relat_1(B_63,B_65))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(B_63,A_64)),B_65)
      | ~ v1_relat_1(B_63)
      | ~ v1_relat_1(B_63)
      | ~ v1_relat_1(B_63) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_144])).

tff(c_410,plain,(
    ! [C_74,A_75,B_76] :
      ( r1_tarski(k9_relat_1(C_74,k3_xboole_0(A_75,B_76)),k9_relat_1(C_74,B_76))
      | ~ v1_relat_1(k7_relat_1(C_74,A_75))
      | ~ v1_relat_1(C_74) ) ),
    inference(resolution,[status(thm)],[c_63,c_314])).

tff(c_8,plain,(
    ! [B_9,A_8] :
      ( k2_relat_1(k7_relat_1(B_9,A_8)) = k9_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_108,plain,(
    ! [C_38,A_39,B_40] :
      ( k2_relat_1(k7_relat_1(C_38,k3_xboole_0(A_39,B_40))) = k9_relat_1(k7_relat_1(C_38,A_39),B_40)
      | ~ v1_relat_1(k7_relat_1(C_38,A_39))
      | ~ v1_relat_1(C_38) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_51,c_8])).

tff(c_216,plain,(
    ! [C_54,A_55,B_56] :
      ( k9_relat_1(k7_relat_1(C_54,A_55),B_56) = k9_relat_1(C_54,k3_xboole_0(A_55,B_56))
      | ~ v1_relat_1(C_54)
      | ~ v1_relat_1(k7_relat_1(C_54,A_55))
      | ~ v1_relat_1(C_54) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_8])).

tff(c_224,plain,(
    ! [A_57,B_58,B_59] :
      ( k9_relat_1(k7_relat_1(A_57,B_58),B_59) = k9_relat_1(A_57,k3_xboole_0(B_58,B_59))
      | ~ v1_relat_1(A_57) ) ),
    inference(resolution,[status(thm)],[c_2,c_216])).

tff(c_16,plain,(
    ~ r1_tarski(k9_relat_1(k7_relat_1('#skF_3','#skF_1'),'#skF_2'),k9_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_250,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_16])).

tff(c_270,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_250])).

tff(c_413,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_410,c_270])).

tff(c_435,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_413])).

tff(c_438,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2,c_435])).

tff(c_442,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_438])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:40:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.20/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.30  
% 2.20/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.31  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.20/1.31  
% 2.20/1.31  %Foreground sorts:
% 2.20/1.31  
% 2.20/1.31  
% 2.20/1.31  %Background operators:
% 2.20/1.31  
% 2.20/1.31  
% 2.20/1.31  %Foreground operators:
% 2.20/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.20/1.31  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.20/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.20/1.31  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.20/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.20/1.31  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.20/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.20/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.20/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.20/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.20/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.20/1.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.20/1.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.20/1.31  
% 2.20/1.32  tff(f_60, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => r1_tarski(k9_relat_1(k7_relat_1(C, A), B), k9_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t161_relat_1)).
% 2.20/1.32  tff(f_29, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.20/1.32  tff(f_33, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 2.20/1.32  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 2.20/1.32  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 2.20/1.32  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (k9_relat_1(B, A) = k9_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_relat_1)).
% 2.20/1.32  tff(f_47, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t156_relat_1)).
% 2.20/1.32  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 2.20/1.32  tff(c_18, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.20/1.32  tff(c_2, plain, (![A_1, B_2]: (v1_relat_1(k7_relat_1(A_1, B_2)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.20/1.32  tff(c_51, plain, (![C_27, A_28, B_29]: (k7_relat_1(k7_relat_1(C_27, A_28), B_29)=k7_relat_1(C_27, k3_xboole_0(A_28, B_29)) | ~v1_relat_1(C_27))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.20/1.32  tff(c_12, plain, (![B_14, A_13]: (r1_tarski(k1_relat_1(k7_relat_1(B_14, A_13)), A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.20/1.32  tff(c_63, plain, (![C_27, A_28, B_29]: (r1_tarski(k1_relat_1(k7_relat_1(C_27, k3_xboole_0(A_28, B_29))), B_29) | ~v1_relat_1(k7_relat_1(C_27, A_28)) | ~v1_relat_1(C_27))), inference(superposition, [status(thm), theory('equality')], [c_51, c_12])).
% 2.20/1.32  tff(c_14, plain, (![B_16, A_15]: (k3_xboole_0(k1_relat_1(B_16), A_15)=k1_relat_1(k7_relat_1(B_16, A_15)) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.20/1.32  tff(c_6, plain, (![B_7, A_6]: (k9_relat_1(B_7, k3_xboole_0(k1_relat_1(B_7), A_6))=k9_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.20/1.32  tff(c_75, plain, (![C_30, A_31, B_32]: (r1_tarski(k9_relat_1(C_30, A_31), k9_relat_1(C_30, B_32)) | ~r1_tarski(A_31, B_32) | ~v1_relat_1(C_30))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.20/1.32  tff(c_144, plain, (![B_44, A_45, B_46]: (r1_tarski(k9_relat_1(B_44, A_45), k9_relat_1(B_44, B_46)) | ~r1_tarski(k3_xboole_0(k1_relat_1(B_44), A_45), B_46) | ~v1_relat_1(B_44) | ~v1_relat_1(B_44))), inference(superposition, [status(thm), theory('equality')], [c_6, c_75])).
% 2.20/1.32  tff(c_314, plain, (![B_63, A_64, B_65]: (r1_tarski(k9_relat_1(B_63, A_64), k9_relat_1(B_63, B_65)) | ~r1_tarski(k1_relat_1(k7_relat_1(B_63, A_64)), B_65) | ~v1_relat_1(B_63) | ~v1_relat_1(B_63) | ~v1_relat_1(B_63))), inference(superposition, [status(thm), theory('equality')], [c_14, c_144])).
% 2.20/1.32  tff(c_410, plain, (![C_74, A_75, B_76]: (r1_tarski(k9_relat_1(C_74, k3_xboole_0(A_75, B_76)), k9_relat_1(C_74, B_76)) | ~v1_relat_1(k7_relat_1(C_74, A_75)) | ~v1_relat_1(C_74))), inference(resolution, [status(thm)], [c_63, c_314])).
% 2.20/1.32  tff(c_8, plain, (![B_9, A_8]: (k2_relat_1(k7_relat_1(B_9, A_8))=k9_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.20/1.32  tff(c_108, plain, (![C_38, A_39, B_40]: (k2_relat_1(k7_relat_1(C_38, k3_xboole_0(A_39, B_40)))=k9_relat_1(k7_relat_1(C_38, A_39), B_40) | ~v1_relat_1(k7_relat_1(C_38, A_39)) | ~v1_relat_1(C_38))), inference(superposition, [status(thm), theory('equality')], [c_51, c_8])).
% 2.20/1.32  tff(c_216, plain, (![C_54, A_55, B_56]: (k9_relat_1(k7_relat_1(C_54, A_55), B_56)=k9_relat_1(C_54, k3_xboole_0(A_55, B_56)) | ~v1_relat_1(C_54) | ~v1_relat_1(k7_relat_1(C_54, A_55)) | ~v1_relat_1(C_54))), inference(superposition, [status(thm), theory('equality')], [c_108, c_8])).
% 2.20/1.32  tff(c_224, plain, (![A_57, B_58, B_59]: (k9_relat_1(k7_relat_1(A_57, B_58), B_59)=k9_relat_1(A_57, k3_xboole_0(B_58, B_59)) | ~v1_relat_1(A_57))), inference(resolution, [status(thm)], [c_2, c_216])).
% 2.20/1.32  tff(c_16, plain, (~r1_tarski(k9_relat_1(k7_relat_1('#skF_3', '#skF_1'), '#skF_2'), k9_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.20/1.32  tff(c_250, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_224, c_16])).
% 2.20/1.32  tff(c_270, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_250])).
% 2.20/1.32  tff(c_413, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_410, c_270])).
% 2.20/1.32  tff(c_435, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_413])).
% 2.20/1.32  tff(c_438, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2, c_435])).
% 2.20/1.32  tff(c_442, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_438])).
% 2.20/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.32  
% 2.20/1.32  Inference rules
% 2.20/1.32  ----------------------
% 2.20/1.32  #Ref     : 0
% 2.20/1.32  #Sup     : 117
% 2.20/1.32  #Fact    : 0
% 2.20/1.32  #Define  : 0
% 2.20/1.32  #Split   : 0
% 2.20/1.32  #Chain   : 0
% 2.20/1.32  #Close   : 0
% 2.20/1.32  
% 2.20/1.32  Ordering : KBO
% 2.20/1.32  
% 2.20/1.32  Simplification rules
% 2.20/1.32  ----------------------
% 2.20/1.32  #Subsume      : 10
% 2.20/1.32  #Demod        : 7
% 2.20/1.32  #Tautology    : 16
% 2.20/1.32  #SimpNegUnit  : 0
% 2.20/1.32  #BackRed      : 0
% 2.20/1.32  
% 2.20/1.32  #Partial instantiations: 0
% 2.20/1.32  #Strategies tried      : 1
% 2.20/1.32  
% 2.20/1.32  Timing (in seconds)
% 2.20/1.32  ----------------------
% 2.50/1.32  Preprocessing        : 0.28
% 2.50/1.32  Parsing              : 0.16
% 2.50/1.32  CNF conversion       : 0.02
% 2.50/1.32  Main loop            : 0.28
% 2.50/1.32  Inferencing          : 0.12
% 2.50/1.32  Reduction            : 0.06
% 2.50/1.32  Demodulation         : 0.05
% 2.50/1.32  BG Simplification    : 0.02
% 2.50/1.32  Subsumption          : 0.06
% 2.50/1.32  Abstraction          : 0.02
% 2.50/1.32  MUC search           : 0.00
% 2.50/1.32  Cooper               : 0.00
% 2.50/1.32  Total                : 0.59
% 2.50/1.32  Index Insertion      : 0.00
% 2.50/1.32  Index Deletion       : 0.00
% 2.50/1.32  Index Matching       : 0.00
% 2.50/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
