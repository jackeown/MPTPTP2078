%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:30 EST 2020

% Result     : Theorem 2.33s
% Output     : CNFRefutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :   48 (  60 expanded)
%              Number of leaves         :   28 (  35 expanded)
%              Depth                    :    9
%              Number of atoms          :   51 (  72 expanded)
%              Number of equality atoms :   24 (  28 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_67,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => k9_relat_1(k8_relat_1(A,C),B) = k3_xboole_0(A,k9_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_funct_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_50,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_60,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k9_relat_1(k5_relat_1(B,C),A) = k9_relat_1(C,k9_relat_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_relat_1)).

tff(c_30,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_20,plain,(
    ! [A_19] : v1_relat_1(k6_relat_1(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_16,plain,(
    ! [A_16] : k2_relat_1(k6_relat_1(A_16)) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_96,plain,(
    ! [B_37,A_38] :
      ( k5_relat_1(B_37,k6_relat_1(A_38)) = k8_relat_1(A_38,B_37)
      | ~ v1_relat_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_18,plain,(
    ! [A_17,B_18] :
      ( k5_relat_1(k6_relat_1(A_17),B_18) = k7_relat_1(B_18,A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_103,plain,(
    ! [A_38,A_17] :
      ( k8_relat_1(A_38,k6_relat_1(A_17)) = k7_relat_1(k6_relat_1(A_38),A_17)
      | ~ v1_relat_1(k6_relat_1(A_38))
      | ~ v1_relat_1(k6_relat_1(A_17)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_18])).

tff(c_113,plain,(
    ! [A_38,A_17] : k8_relat_1(A_38,k6_relat_1(A_17)) = k7_relat_1(k6_relat_1(A_38),A_17) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_103])).

tff(c_127,plain,(
    ! [B_41,A_42] : k5_relat_1(k6_relat_1(B_41),k6_relat_1(A_42)) = k6_relat_1(k3_xboole_0(A_42,B_41)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_8,plain,(
    ! [B_9,A_8] :
      ( k5_relat_1(B_9,k6_relat_1(A_8)) = k8_relat_1(A_8,B_9)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_133,plain,(
    ! [A_42,B_41] :
      ( k8_relat_1(A_42,k6_relat_1(B_41)) = k6_relat_1(k3_xboole_0(A_42,B_41))
      | ~ v1_relat_1(k6_relat_1(B_41)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_8])).

tff(c_159,plain,(
    ! [A_43,B_44] : k7_relat_1(k6_relat_1(A_43),B_44) = k6_relat_1(k3_xboole_0(A_43,B_44)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_113,c_133])).

tff(c_10,plain,(
    ! [B_11,A_10] :
      ( k2_relat_1(k7_relat_1(B_11,A_10)) = k9_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_165,plain,(
    ! [A_43,B_44] :
      ( k2_relat_1(k6_relat_1(k3_xboole_0(A_43,B_44))) = k9_relat_1(k6_relat_1(A_43),B_44)
      | ~ v1_relat_1(k6_relat_1(A_43)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_10])).

tff(c_171,plain,(
    ! [A_43,B_44] : k9_relat_1(k6_relat_1(A_43),B_44) = k3_xboole_0(A_43,B_44) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_16,c_165])).

tff(c_183,plain,(
    ! [B_47,C_48,A_49] :
      ( k9_relat_1(k5_relat_1(B_47,C_48),A_49) = k9_relat_1(C_48,k9_relat_1(B_47,A_49))
      | ~ v1_relat_1(C_48)
      | ~ v1_relat_1(B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_195,plain,(
    ! [A_8,B_9,A_49] :
      ( k9_relat_1(k6_relat_1(A_8),k9_relat_1(B_9,A_49)) = k9_relat_1(k8_relat_1(A_8,B_9),A_49)
      | ~ v1_relat_1(k6_relat_1(A_8))
      | ~ v1_relat_1(B_9)
      | ~ v1_relat_1(B_9) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_183])).

tff(c_235,plain,(
    ! [A_55,B_56,A_57] :
      ( k9_relat_1(k8_relat_1(A_55,B_56),A_57) = k3_xboole_0(A_55,k9_relat_1(B_56,A_57))
      | ~ v1_relat_1(B_56) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_171,c_195])).

tff(c_26,plain,(
    k9_relat_1(k8_relat_1('#skF_1','#skF_3'),'#skF_2') != k3_xboole_0('#skF_1',k9_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_241,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_235,c_26])).

tff(c_252,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_241])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:28:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.33/1.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.33/1.64  
% 2.33/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.33/1.65  %$ v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.33/1.65  
% 2.33/1.65  %Foreground sorts:
% 2.33/1.65  
% 2.33/1.65  
% 2.33/1.65  %Background operators:
% 2.33/1.65  
% 2.33/1.65  
% 2.33/1.65  %Foreground operators:
% 2.33/1.65  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.33/1.65  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.33/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.33/1.65  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.33/1.65  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.33/1.65  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.33/1.65  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.33/1.65  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.33/1.65  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.33/1.65  tff('#skF_2', type, '#skF_2': $i).
% 2.33/1.65  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.33/1.65  tff('#skF_3', type, '#skF_3': $i).
% 2.33/1.65  tff('#skF_1', type, '#skF_1': $i).
% 2.33/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.33/1.65  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.33/1.65  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.33/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.33/1.65  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.33/1.65  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.33/1.65  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.33/1.65  
% 2.33/1.66  tff(f_67, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (k9_relat_1(k8_relat_1(A, C), B) = k3_xboole_0(A, k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t126_funct_1)).
% 2.33/1.66  tff(f_58, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.33/1.66  tff(f_50, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.33/1.66  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_relat_1)).
% 2.33/1.66  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 2.33/1.66  tff(f_60, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 2.33/1.66  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 2.33/1.66  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k9_relat_1(k5_relat_1(B, C), A) = k9_relat_1(C, k9_relat_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t159_relat_1)).
% 2.33/1.66  tff(c_30, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.33/1.66  tff(c_20, plain, (![A_19]: (v1_relat_1(k6_relat_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.33/1.66  tff(c_16, plain, (![A_16]: (k2_relat_1(k6_relat_1(A_16))=A_16)), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.33/1.66  tff(c_96, plain, (![B_37, A_38]: (k5_relat_1(B_37, k6_relat_1(A_38))=k8_relat_1(A_38, B_37) | ~v1_relat_1(B_37))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.33/1.66  tff(c_18, plain, (![A_17, B_18]: (k5_relat_1(k6_relat_1(A_17), B_18)=k7_relat_1(B_18, A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.33/1.66  tff(c_103, plain, (![A_38, A_17]: (k8_relat_1(A_38, k6_relat_1(A_17))=k7_relat_1(k6_relat_1(A_38), A_17) | ~v1_relat_1(k6_relat_1(A_38)) | ~v1_relat_1(k6_relat_1(A_17)))), inference(superposition, [status(thm), theory('equality')], [c_96, c_18])).
% 2.33/1.66  tff(c_113, plain, (![A_38, A_17]: (k8_relat_1(A_38, k6_relat_1(A_17))=k7_relat_1(k6_relat_1(A_38), A_17))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_103])).
% 2.33/1.66  tff(c_127, plain, (![B_41, A_42]: (k5_relat_1(k6_relat_1(B_41), k6_relat_1(A_42))=k6_relat_1(k3_xboole_0(A_42, B_41)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.33/1.66  tff(c_8, plain, (![B_9, A_8]: (k5_relat_1(B_9, k6_relat_1(A_8))=k8_relat_1(A_8, B_9) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.33/1.66  tff(c_133, plain, (![A_42, B_41]: (k8_relat_1(A_42, k6_relat_1(B_41))=k6_relat_1(k3_xboole_0(A_42, B_41)) | ~v1_relat_1(k6_relat_1(B_41)))), inference(superposition, [status(thm), theory('equality')], [c_127, c_8])).
% 2.33/1.66  tff(c_159, plain, (![A_43, B_44]: (k7_relat_1(k6_relat_1(A_43), B_44)=k6_relat_1(k3_xboole_0(A_43, B_44)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_113, c_133])).
% 2.33/1.66  tff(c_10, plain, (![B_11, A_10]: (k2_relat_1(k7_relat_1(B_11, A_10))=k9_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.33/1.66  tff(c_165, plain, (![A_43, B_44]: (k2_relat_1(k6_relat_1(k3_xboole_0(A_43, B_44)))=k9_relat_1(k6_relat_1(A_43), B_44) | ~v1_relat_1(k6_relat_1(A_43)))), inference(superposition, [status(thm), theory('equality')], [c_159, c_10])).
% 2.33/1.66  tff(c_171, plain, (![A_43, B_44]: (k9_relat_1(k6_relat_1(A_43), B_44)=k3_xboole_0(A_43, B_44))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_16, c_165])).
% 2.33/1.66  tff(c_183, plain, (![B_47, C_48, A_49]: (k9_relat_1(k5_relat_1(B_47, C_48), A_49)=k9_relat_1(C_48, k9_relat_1(B_47, A_49)) | ~v1_relat_1(C_48) | ~v1_relat_1(B_47))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.33/1.66  tff(c_195, plain, (![A_8, B_9, A_49]: (k9_relat_1(k6_relat_1(A_8), k9_relat_1(B_9, A_49))=k9_relat_1(k8_relat_1(A_8, B_9), A_49) | ~v1_relat_1(k6_relat_1(A_8)) | ~v1_relat_1(B_9) | ~v1_relat_1(B_9))), inference(superposition, [status(thm), theory('equality')], [c_8, c_183])).
% 2.33/1.66  tff(c_235, plain, (![A_55, B_56, A_57]: (k9_relat_1(k8_relat_1(A_55, B_56), A_57)=k3_xboole_0(A_55, k9_relat_1(B_56, A_57)) | ~v1_relat_1(B_56))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_171, c_195])).
% 2.33/1.66  tff(c_26, plain, (k9_relat_1(k8_relat_1('#skF_1', '#skF_3'), '#skF_2')!=k3_xboole_0('#skF_1', k9_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.33/1.66  tff(c_241, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_235, c_26])).
% 2.33/1.66  tff(c_252, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_241])).
% 2.33/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.33/1.66  
% 2.33/1.66  Inference rules
% 2.33/1.66  ----------------------
% 2.33/1.66  #Ref     : 0
% 2.33/1.66  #Sup     : 46
% 2.33/1.66  #Fact    : 0
% 2.33/1.66  #Define  : 0
% 2.33/1.66  #Split   : 0
% 2.33/1.67  #Chain   : 0
% 2.33/1.67  #Close   : 0
% 2.33/1.67  
% 2.33/1.67  Ordering : KBO
% 2.33/1.67  
% 2.33/1.67  Simplification rules
% 2.33/1.67  ----------------------
% 2.33/1.67  #Subsume      : 0
% 2.33/1.67  #Demod        : 33
% 2.33/1.67  #Tautology    : 37
% 2.33/1.67  #SimpNegUnit  : 0
% 2.33/1.67  #BackRed      : 1
% 2.33/1.67  
% 2.33/1.67  #Partial instantiations: 0
% 2.33/1.67  #Strategies tried      : 1
% 2.33/1.67  
% 2.33/1.67  Timing (in seconds)
% 2.33/1.67  ----------------------
% 2.33/1.67  Preprocessing        : 0.48
% 2.33/1.67  Parsing              : 0.27
% 2.33/1.67  CNF conversion       : 0.03
% 2.33/1.67  Main loop            : 0.23
% 2.33/1.67  Inferencing          : 0.10
% 2.33/1.67  Reduction            : 0.08
% 2.33/1.67  Demodulation         : 0.06
% 2.33/1.67  BG Simplification    : 0.02
% 2.33/1.67  Subsumption          : 0.02
% 2.33/1.67  Abstraction          : 0.01
% 2.33/1.67  MUC search           : 0.00
% 2.33/1.67  Cooper               : 0.00
% 2.33/1.67  Total                : 0.76
% 2.33/1.67  Index Insertion      : 0.00
% 2.33/1.67  Index Deletion       : 0.00
% 2.33/1.67  Index Matching       : 0.00
% 2.33/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
