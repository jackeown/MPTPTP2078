%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:29 EST 2020

% Result     : Theorem 2.68s
% Output     : CNFRefutation 2.68s
% Verified   : 
% Statistics : Number of formulae       :   42 (  46 expanded)
%              Number of leaves         :   23 (  26 expanded)
%              Depth                    :    8
%              Number of atoms          :   52 (  60 expanded)
%              Number of equality atoms :   21 (  25 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > v1_funct_1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => k9_relat_1(k8_relat_1(A,C),B) = k3_xboole_0(A,k9_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_funct_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_29,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => v1_relat_1(k8_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k8_relat_1(A,C),B) = k8_relat_1(A,k7_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k8_relat_1(A,B)) = k3_xboole_0(k2_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_relat_1)).

tff(c_20,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_tarski(B_2,A_1) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_56,plain,(
    ! [A_22,B_23] : k1_setfam_1(k2_tarski(A_22,B_23)) = k3_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_71,plain,(
    ! [B_24,A_25] : k1_setfam_1(k2_tarski(B_24,A_25)) = k3_xboole_0(A_25,B_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_56])).

tff(c_4,plain,(
    ! [A_3,B_4] : k1_setfam_1(k2_tarski(A_3,B_4)) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_77,plain,(
    ! [B_24,A_25] : k3_xboole_0(B_24,A_25) = k3_xboole_0(A_25,B_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_4])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( v1_relat_1(k8_relat_1(A_7,B_8))
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( v1_relat_1(k7_relat_1(A_5,B_6))
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_14,plain,(
    ! [B_15,A_14] :
      ( k2_relat_1(k7_relat_1(B_15,A_14)) = k9_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_12,plain,(
    ! [A_11,C_13,B_12] :
      ( k8_relat_1(A_11,k7_relat_1(C_13,B_12)) = k7_relat_1(k8_relat_1(A_11,C_13),B_12)
      | ~ v1_relat_1(C_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_137,plain,(
    ! [B_30,A_31] :
      ( k3_xboole_0(k2_relat_1(B_30),A_31) = k2_relat_1(k8_relat_1(A_31,B_30))
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_296,plain,(
    ! [A_42,B_43,A_44] :
      ( k2_relat_1(k8_relat_1(A_42,k7_relat_1(B_43,A_44))) = k3_xboole_0(k9_relat_1(B_43,A_44),A_42)
      | ~ v1_relat_1(k7_relat_1(B_43,A_44))
      | ~ v1_relat_1(B_43) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_137])).

tff(c_382,plain,(
    ! [A_48,C_49,B_50] :
      ( k2_relat_1(k7_relat_1(k8_relat_1(A_48,C_49),B_50)) = k3_xboole_0(k9_relat_1(C_49,B_50),A_48)
      | ~ v1_relat_1(k7_relat_1(C_49,B_50))
      | ~ v1_relat_1(C_49)
      | ~ v1_relat_1(C_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_296])).

tff(c_534,plain,(
    ! [A_61,C_62,A_63] :
      ( k9_relat_1(k8_relat_1(A_61,C_62),A_63) = k3_xboole_0(k9_relat_1(C_62,A_63),A_61)
      | ~ v1_relat_1(k7_relat_1(C_62,A_63))
      | ~ v1_relat_1(C_62)
      | ~ v1_relat_1(C_62)
      | ~ v1_relat_1(k8_relat_1(A_61,C_62)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_382])).

tff(c_544,plain,(
    ! [A_64,A_65,B_66] :
      ( k9_relat_1(k8_relat_1(A_64,A_65),B_66) = k3_xboole_0(k9_relat_1(A_65,B_66),A_64)
      | ~ v1_relat_1(k8_relat_1(A_64,A_65))
      | ~ v1_relat_1(A_65) ) ),
    inference(resolution,[status(thm)],[c_6,c_534])).

tff(c_550,plain,(
    ! [A_67,B_68,B_69] :
      ( k9_relat_1(k8_relat_1(A_67,B_68),B_69) = k3_xboole_0(k9_relat_1(B_68,B_69),A_67)
      | ~ v1_relat_1(B_68) ) ),
    inference(resolution,[status(thm)],[c_8,c_544])).

tff(c_16,plain,(
    k9_relat_1(k8_relat_1('#skF_1','#skF_3'),'#skF_2') != k3_xboole_0('#skF_1',k9_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_556,plain,
    ( k3_xboole_0(k9_relat_1('#skF_3','#skF_2'),'#skF_1') != k3_xboole_0('#skF_1',k9_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_550,c_16])).

tff(c_566,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_77,c_556])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:46:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.68/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.36  
% 2.68/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.36  %$ v1_relat_1 > v1_funct_1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 2.68/1.36  
% 2.68/1.36  %Foreground sorts:
% 2.68/1.36  
% 2.68/1.36  
% 2.68/1.36  %Background operators:
% 2.68/1.36  
% 2.68/1.36  
% 2.68/1.36  %Foreground operators:
% 2.68/1.36  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.68/1.36  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.68/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.68/1.36  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.68/1.36  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.68/1.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.68/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.68/1.36  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.68/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.68/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.68/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.68/1.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.68/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.68/1.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.68/1.36  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.68/1.36  
% 2.68/1.37  tff(f_56, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (k9_relat_1(k8_relat_1(A, C), B) = k3_xboole_0(A, k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t126_funct_1)).
% 2.68/1.37  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.68/1.37  tff(f_29, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.68/1.37  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => v1_relat_1(k8_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 2.68/1.37  tff(f_33, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.68/1.37  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 2.68/1.37  tff(f_45, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k8_relat_1(A, C), B) = k8_relat_1(A, k7_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t140_relat_1)).
% 2.68/1.37  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k8_relat_1(A, B)) = k3_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t119_relat_1)).
% 2.68/1.37  tff(c_20, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.68/1.37  tff(c_2, plain, (![B_2, A_1]: (k2_tarski(B_2, A_1)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.68/1.37  tff(c_56, plain, (![A_22, B_23]: (k1_setfam_1(k2_tarski(A_22, B_23))=k3_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.68/1.37  tff(c_71, plain, (![B_24, A_25]: (k1_setfam_1(k2_tarski(B_24, A_25))=k3_xboole_0(A_25, B_24))), inference(superposition, [status(thm), theory('equality')], [c_2, c_56])).
% 2.68/1.37  tff(c_4, plain, (![A_3, B_4]: (k1_setfam_1(k2_tarski(A_3, B_4))=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.68/1.37  tff(c_77, plain, (![B_24, A_25]: (k3_xboole_0(B_24, A_25)=k3_xboole_0(A_25, B_24))), inference(superposition, [status(thm), theory('equality')], [c_71, c_4])).
% 2.68/1.37  tff(c_8, plain, (![A_7, B_8]: (v1_relat_1(k8_relat_1(A_7, B_8)) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.68/1.37  tff(c_6, plain, (![A_5, B_6]: (v1_relat_1(k7_relat_1(A_5, B_6)) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.68/1.37  tff(c_14, plain, (![B_15, A_14]: (k2_relat_1(k7_relat_1(B_15, A_14))=k9_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.68/1.37  tff(c_12, plain, (![A_11, C_13, B_12]: (k8_relat_1(A_11, k7_relat_1(C_13, B_12))=k7_relat_1(k8_relat_1(A_11, C_13), B_12) | ~v1_relat_1(C_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.68/1.37  tff(c_137, plain, (![B_30, A_31]: (k3_xboole_0(k2_relat_1(B_30), A_31)=k2_relat_1(k8_relat_1(A_31, B_30)) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.68/1.37  tff(c_296, plain, (![A_42, B_43, A_44]: (k2_relat_1(k8_relat_1(A_42, k7_relat_1(B_43, A_44)))=k3_xboole_0(k9_relat_1(B_43, A_44), A_42) | ~v1_relat_1(k7_relat_1(B_43, A_44)) | ~v1_relat_1(B_43))), inference(superposition, [status(thm), theory('equality')], [c_14, c_137])).
% 2.68/1.37  tff(c_382, plain, (![A_48, C_49, B_50]: (k2_relat_1(k7_relat_1(k8_relat_1(A_48, C_49), B_50))=k3_xboole_0(k9_relat_1(C_49, B_50), A_48) | ~v1_relat_1(k7_relat_1(C_49, B_50)) | ~v1_relat_1(C_49) | ~v1_relat_1(C_49))), inference(superposition, [status(thm), theory('equality')], [c_12, c_296])).
% 2.68/1.37  tff(c_534, plain, (![A_61, C_62, A_63]: (k9_relat_1(k8_relat_1(A_61, C_62), A_63)=k3_xboole_0(k9_relat_1(C_62, A_63), A_61) | ~v1_relat_1(k7_relat_1(C_62, A_63)) | ~v1_relat_1(C_62) | ~v1_relat_1(C_62) | ~v1_relat_1(k8_relat_1(A_61, C_62)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_382])).
% 2.68/1.37  tff(c_544, plain, (![A_64, A_65, B_66]: (k9_relat_1(k8_relat_1(A_64, A_65), B_66)=k3_xboole_0(k9_relat_1(A_65, B_66), A_64) | ~v1_relat_1(k8_relat_1(A_64, A_65)) | ~v1_relat_1(A_65))), inference(resolution, [status(thm)], [c_6, c_534])).
% 2.68/1.37  tff(c_550, plain, (![A_67, B_68, B_69]: (k9_relat_1(k8_relat_1(A_67, B_68), B_69)=k3_xboole_0(k9_relat_1(B_68, B_69), A_67) | ~v1_relat_1(B_68))), inference(resolution, [status(thm)], [c_8, c_544])).
% 2.68/1.37  tff(c_16, plain, (k9_relat_1(k8_relat_1('#skF_1', '#skF_3'), '#skF_2')!=k3_xboole_0('#skF_1', k9_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.68/1.37  tff(c_556, plain, (k3_xboole_0(k9_relat_1('#skF_3', '#skF_2'), '#skF_1')!=k3_xboole_0('#skF_1', k9_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_550, c_16])).
% 2.68/1.37  tff(c_566, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_77, c_556])).
% 2.68/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.37  
% 2.68/1.37  Inference rules
% 2.68/1.37  ----------------------
% 2.68/1.37  #Ref     : 0
% 2.68/1.37  #Sup     : 150
% 2.68/1.37  #Fact    : 0
% 2.68/1.37  #Define  : 0
% 2.68/1.37  #Split   : 0
% 2.68/1.37  #Chain   : 0
% 2.68/1.37  #Close   : 0
% 2.68/1.37  
% 2.68/1.37  Ordering : KBO
% 2.68/1.37  
% 2.68/1.37  Simplification rules
% 2.68/1.37  ----------------------
% 2.68/1.37  #Subsume      : 20
% 2.68/1.37  #Demod        : 5
% 2.68/1.37  #Tautology    : 50
% 2.68/1.37  #SimpNegUnit  : 0
% 2.68/1.37  #BackRed      : 0
% 2.68/1.37  
% 2.68/1.37  #Partial instantiations: 0
% 2.68/1.37  #Strategies tried      : 1
% 2.68/1.37  
% 2.68/1.37  Timing (in seconds)
% 2.68/1.37  ----------------------
% 2.68/1.37  Preprocessing        : 0.29
% 2.68/1.37  Parsing              : 0.15
% 2.68/1.38  CNF conversion       : 0.02
% 2.68/1.38  Main loop            : 0.33
% 2.68/1.38  Inferencing          : 0.14
% 2.68/1.38  Reduction            : 0.09
% 2.68/1.38  Demodulation         : 0.07
% 2.68/1.38  BG Simplification    : 0.02
% 2.68/1.38  Subsumption          : 0.06
% 2.68/1.38  Abstraction          : 0.02
% 2.68/1.38  MUC search           : 0.00
% 2.68/1.38  Cooper               : 0.00
% 2.68/1.38  Total                : 0.65
% 2.68/1.38  Index Insertion      : 0.00
% 2.68/1.38  Index Deletion       : 0.00
% 2.68/1.38  Index Matching       : 0.00
% 2.68/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
