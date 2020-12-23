%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:24 EST 2020

% Result     : Theorem 2.98s
% Output     : CNFRefutation 2.98s
% Verified   : 
% Statistics : Number of formulae       :   48 (  78 expanded)
%              Number of leaves         :   26 (  38 expanded)
%              Depth                    :   11
%              Number of atoms          :   55 ( 118 expanded)
%              Number of equality atoms :    8 (  20 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => r1_tarski(k9_relat_1(k8_relat_1(A,C),B),k9_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_funct_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => v1_relat_1(k8_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k8_relat_1(A,C),B) = k8_relat_1(A,k7_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k8_relat_1(A,B)) = k3_xboole_0(k2_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_relat_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(c_24,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( v1_relat_1(k7_relat_1(A_9,B_10))
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_12,plain,(
    ! [A_11,B_12] :
      ( v1_relat_1(k8_relat_1(A_11,B_12))
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    ! [B_19,A_18] :
      ( k2_relat_1(k7_relat_1(B_19,A_18)) = k9_relat_1(B_19,A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_113,plain,(
    ! [A_42,C_43,B_44] :
      ( k8_relat_1(A_42,k7_relat_1(C_43,B_44)) = k7_relat_1(k8_relat_1(A_42,C_43),B_44)
      | ~ v1_relat_1(C_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_74,plain,(
    ! [B_36,A_37] :
      ( k3_xboole_0(k2_relat_1(B_36),A_37) = k2_relat_1(k8_relat_1(A_37,B_36))
      | ~ v1_relat_1(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_46,plain,(
    ! [A_30,B_31] : k4_xboole_0(A_30,k4_xboole_0(A_30,B_31)) = k3_xboole_0(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k4_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_55,plain,(
    ! [A_30,B_31] : r1_tarski(k3_xboole_0(A_30,B_31),A_30) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_2])).

tff(c_80,plain,(
    ! [A_37,B_36] :
      ( r1_tarski(k2_relat_1(k8_relat_1(A_37,B_36)),k2_relat_1(B_36))
      | ~ v1_relat_1(B_36) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_55])).

tff(c_400,plain,(
    ! [A_64,C_65,B_66] :
      ( r1_tarski(k2_relat_1(k7_relat_1(k8_relat_1(A_64,C_65),B_66)),k2_relat_1(k7_relat_1(C_65,B_66)))
      | ~ v1_relat_1(k7_relat_1(C_65,B_66))
      | ~ v1_relat_1(C_65) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_80])).

tff(c_478,plain,(
    ! [A_69,B_70,A_71] :
      ( r1_tarski(k2_relat_1(k7_relat_1(k8_relat_1(A_69,B_70),A_71)),k9_relat_1(B_70,A_71))
      | ~ v1_relat_1(k7_relat_1(B_70,A_71))
      | ~ v1_relat_1(B_70)
      | ~ v1_relat_1(B_70) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_400])).

tff(c_950,plain,(
    ! [A_97,B_98,A_99] :
      ( r1_tarski(k9_relat_1(k8_relat_1(A_97,B_98),A_99),k9_relat_1(B_98,A_99))
      | ~ v1_relat_1(k7_relat_1(B_98,A_99))
      | ~ v1_relat_1(B_98)
      | ~ v1_relat_1(B_98)
      | ~ v1_relat_1(k8_relat_1(A_97,B_98)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_478])).

tff(c_20,plain,(
    ~ r1_tarski(k9_relat_1(k8_relat_1('#skF_1','#skF_3'),'#skF_2'),k9_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_953,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k8_relat_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_950,c_20])).

tff(c_959,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k8_relat_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_953])).

tff(c_960,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_959])).

tff(c_963,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_960])).

tff(c_967,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_963])).

tff(c_968,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_959])).

tff(c_972,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_968])).

tff(c_976,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_972])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:54:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.98/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.98/1.43  
% 2.98/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.98/1.43  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 2.98/1.43  
% 2.98/1.43  %Foreground sorts:
% 2.98/1.43  
% 2.98/1.43  
% 2.98/1.43  %Background operators:
% 2.98/1.43  
% 2.98/1.43  
% 2.98/1.43  %Foreground operators:
% 2.98/1.43  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.98/1.43  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.98/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.98/1.43  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.98/1.43  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.98/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.98/1.43  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.98/1.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.98/1.43  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.98/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.98/1.43  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.98/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.98/1.43  tff('#skF_1', type, '#skF_1': $i).
% 2.98/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.98/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.98/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.98/1.43  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.98/1.43  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.98/1.43  
% 2.98/1.44  tff(f_60, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => r1_tarski(k9_relat_1(k8_relat_1(A, C), B), k9_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t120_funct_1)).
% 2.98/1.44  tff(f_37, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.98/1.44  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => v1_relat_1(k8_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 2.98/1.44  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 2.98/1.44  tff(f_49, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k8_relat_1(A, C), B) = k8_relat_1(A, k7_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t140_relat_1)).
% 2.98/1.44  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k8_relat_1(A, B)) = k3_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t119_relat_1)).
% 2.98/1.44  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.98/1.44  tff(f_27, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.98/1.44  tff(c_24, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.98/1.44  tff(c_10, plain, (![A_9, B_10]: (v1_relat_1(k7_relat_1(A_9, B_10)) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.98/1.44  tff(c_12, plain, (![A_11, B_12]: (v1_relat_1(k8_relat_1(A_11, B_12)) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.98/1.44  tff(c_18, plain, (![B_19, A_18]: (k2_relat_1(k7_relat_1(B_19, A_18))=k9_relat_1(B_19, A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.98/1.44  tff(c_113, plain, (![A_42, C_43, B_44]: (k8_relat_1(A_42, k7_relat_1(C_43, B_44))=k7_relat_1(k8_relat_1(A_42, C_43), B_44) | ~v1_relat_1(C_43))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.98/1.44  tff(c_74, plain, (![B_36, A_37]: (k3_xboole_0(k2_relat_1(B_36), A_37)=k2_relat_1(k8_relat_1(A_37, B_36)) | ~v1_relat_1(B_36))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.98/1.44  tff(c_46, plain, (![A_30, B_31]: (k4_xboole_0(A_30, k4_xboole_0(A_30, B_31))=k3_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.98/1.44  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k4_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.98/1.44  tff(c_55, plain, (![A_30, B_31]: (r1_tarski(k3_xboole_0(A_30, B_31), A_30))), inference(superposition, [status(thm), theory('equality')], [c_46, c_2])).
% 2.98/1.44  tff(c_80, plain, (![A_37, B_36]: (r1_tarski(k2_relat_1(k8_relat_1(A_37, B_36)), k2_relat_1(B_36)) | ~v1_relat_1(B_36))), inference(superposition, [status(thm), theory('equality')], [c_74, c_55])).
% 2.98/1.44  tff(c_400, plain, (![A_64, C_65, B_66]: (r1_tarski(k2_relat_1(k7_relat_1(k8_relat_1(A_64, C_65), B_66)), k2_relat_1(k7_relat_1(C_65, B_66))) | ~v1_relat_1(k7_relat_1(C_65, B_66)) | ~v1_relat_1(C_65))), inference(superposition, [status(thm), theory('equality')], [c_113, c_80])).
% 2.98/1.44  tff(c_478, plain, (![A_69, B_70, A_71]: (r1_tarski(k2_relat_1(k7_relat_1(k8_relat_1(A_69, B_70), A_71)), k9_relat_1(B_70, A_71)) | ~v1_relat_1(k7_relat_1(B_70, A_71)) | ~v1_relat_1(B_70) | ~v1_relat_1(B_70))), inference(superposition, [status(thm), theory('equality')], [c_18, c_400])).
% 2.98/1.44  tff(c_950, plain, (![A_97, B_98, A_99]: (r1_tarski(k9_relat_1(k8_relat_1(A_97, B_98), A_99), k9_relat_1(B_98, A_99)) | ~v1_relat_1(k7_relat_1(B_98, A_99)) | ~v1_relat_1(B_98) | ~v1_relat_1(B_98) | ~v1_relat_1(k8_relat_1(A_97, B_98)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_478])).
% 2.98/1.44  tff(c_20, plain, (~r1_tarski(k9_relat_1(k8_relat_1('#skF_1', '#skF_3'), '#skF_2'), k9_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.98/1.44  tff(c_953, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1('#skF_3') | ~v1_relat_1(k8_relat_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_950, c_20])).
% 2.98/1.44  tff(c_959, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k8_relat_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_953])).
% 2.98/1.44  tff(c_960, plain, (~v1_relat_1(k8_relat_1('#skF_1', '#skF_3'))), inference(splitLeft, [status(thm)], [c_959])).
% 2.98/1.44  tff(c_963, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_12, c_960])).
% 2.98/1.44  tff(c_967, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_963])).
% 2.98/1.44  tff(c_968, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_959])).
% 2.98/1.44  tff(c_972, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_10, c_968])).
% 2.98/1.44  tff(c_976, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_972])).
% 2.98/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.98/1.44  
% 2.98/1.44  Inference rules
% 2.98/1.44  ----------------------
% 2.98/1.44  #Ref     : 0
% 2.98/1.44  #Sup     : 251
% 2.98/1.44  #Fact    : 0
% 2.98/1.44  #Define  : 0
% 2.98/1.44  #Split   : 1
% 2.98/1.44  #Chain   : 0
% 2.98/1.44  #Close   : 0
% 2.98/1.44  
% 2.98/1.44  Ordering : KBO
% 2.98/1.44  
% 2.98/1.44  Simplification rules
% 2.98/1.44  ----------------------
% 2.98/1.44  #Subsume      : 7
% 2.98/1.44  #Demod        : 110
% 2.98/1.44  #Tautology    : 82
% 2.98/1.44  #SimpNegUnit  : 0
% 2.98/1.44  #BackRed      : 0
% 2.98/1.44  
% 2.98/1.44  #Partial instantiations: 0
% 2.98/1.44  #Strategies tried      : 1
% 2.98/1.44  
% 2.98/1.44  Timing (in seconds)
% 2.98/1.44  ----------------------
% 3.13/1.45  Preprocessing        : 0.28
% 3.13/1.45  Parsing              : 0.15
% 3.13/1.45  CNF conversion       : 0.01
% 3.13/1.45  Main loop            : 0.41
% 3.13/1.45  Inferencing          : 0.17
% 3.13/1.45  Reduction            : 0.12
% 3.13/1.45  Demodulation         : 0.09
% 3.13/1.45  BG Simplification    : 0.03
% 3.13/1.45  Subsumption          : 0.07
% 3.13/1.45  Abstraction          : 0.03
% 3.13/1.45  MUC search           : 0.00
% 3.13/1.45  Cooper               : 0.00
% 3.13/1.45  Total                : 0.71
% 3.13/1.45  Index Insertion      : 0.00
% 3.13/1.45  Index Deletion       : 0.00
% 3.13/1.45  Index Matching       : 0.00
% 3.13/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
