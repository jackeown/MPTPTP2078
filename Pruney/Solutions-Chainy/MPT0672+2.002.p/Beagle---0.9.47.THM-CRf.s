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
% DateTime   : Thu Dec  3 10:04:21 EST 2020

% Result     : Theorem 3.48s
% Output     : CNFRefutation 3.88s
% Verified   : 
% Statistics : Number of formulae       :   56 (  89 expanded)
%              Number of leaves         :   23 (  41 expanded)
%              Depth                    :   10
%              Number of atoms          :   71 ( 150 expanded)
%              Number of equality atoms :   34 (  65 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k8_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_63,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r1_tarski(A,B)
         => ( k8_relat_1(B,k8_relat_1(A,C)) = k8_relat_1(A,C)
            & k8_relat_1(A,k8_relat_1(B,C)) = k8_relat_1(A,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_funct_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_52,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k8_relat_1(A,k5_relat_1(B,C)) = k5_relat_1(B,k8_relat_1(A,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_26,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_10,plain,(
    ! [B_10,A_9] :
      ( k5_relat_1(B_10,k6_relat_1(A_9)) = k8_relat_1(A_9,B_10)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_22,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_62,plain,(
    ! [A_22,B_23] :
      ( k3_xboole_0(A_22,B_23) = A_22
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_66,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_22,c_62])).

tff(c_14,plain,(
    ! [A_15] : v1_relat_1(k6_relat_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1555,plain,(
    ! [B_70,A_71] : k5_relat_1(k6_relat_1(B_70),k6_relat_1(A_71)) = k6_relat_1(k3_xboole_0(A_71,B_70)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1561,plain,(
    ! [A_71,B_70] :
      ( k8_relat_1(A_71,k6_relat_1(B_70)) = k6_relat_1(k3_xboole_0(A_71,B_70))
      | ~ v1_relat_1(k6_relat_1(B_70)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1555,c_10])).

tff(c_1571,plain,(
    ! [A_71,B_70] : k8_relat_1(A_71,k6_relat_1(B_70)) = k6_relat_1(k3_xboole_0(A_71,B_70)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1561])).

tff(c_1585,plain,(
    ! [A_74,B_75,C_76] :
      ( k8_relat_1(A_74,k5_relat_1(B_75,C_76)) = k5_relat_1(B_75,k8_relat_1(A_74,C_76))
      | ~ v1_relat_1(C_76)
      | ~ v1_relat_1(B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1597,plain,(
    ! [B_10,A_74,A_9] :
      ( k5_relat_1(B_10,k8_relat_1(A_74,k6_relat_1(A_9))) = k8_relat_1(A_74,k8_relat_1(A_9,B_10))
      | ~ v1_relat_1(k6_relat_1(A_9))
      | ~ v1_relat_1(B_10)
      | ~ v1_relat_1(B_10) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1585])).

tff(c_1964,plain,(
    ! [B_86,A_87,A_88] :
      ( k5_relat_1(B_86,k6_relat_1(k3_xboole_0(A_87,A_88))) = k8_relat_1(A_87,k8_relat_1(A_88,B_86))
      | ~ v1_relat_1(B_86) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1571,c_1597])).

tff(c_2233,plain,(
    ! [B_92] :
      ( k8_relat_1('#skF_1',k8_relat_1('#skF_2',B_92)) = k5_relat_1(B_92,k6_relat_1('#skF_1'))
      | ~ v1_relat_1(B_92) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_1964])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_99,plain,(
    ! [B_30,A_31] : k5_relat_1(k6_relat_1(B_30),k6_relat_1(A_31)) = k6_relat_1(k3_xboole_0(A_31,B_30)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_105,plain,(
    ! [A_31,B_30] :
      ( k8_relat_1(A_31,k6_relat_1(B_30)) = k6_relat_1(k3_xboole_0(A_31,B_30))
      | ~ v1_relat_1(k6_relat_1(B_30)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_10])).

tff(c_115,plain,(
    ! [A_31,B_30] : k8_relat_1(A_31,k6_relat_1(B_30)) = k6_relat_1(k3_xboole_0(A_31,B_30)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_105])).

tff(c_128,plain,(
    ! [A_34,B_35,C_36] :
      ( k8_relat_1(A_34,k5_relat_1(B_35,C_36)) = k5_relat_1(B_35,k8_relat_1(A_34,C_36))
      | ~ v1_relat_1(C_36)
      | ~ v1_relat_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_140,plain,(
    ! [B_10,A_34,A_9] :
      ( k5_relat_1(B_10,k8_relat_1(A_34,k6_relat_1(A_9))) = k8_relat_1(A_34,k8_relat_1(A_9,B_10))
      | ~ v1_relat_1(k6_relat_1(A_9))
      | ~ v1_relat_1(B_10)
      | ~ v1_relat_1(B_10) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_128])).

tff(c_436,plain,(
    ! [B_47,A_48,A_49] :
      ( k5_relat_1(B_47,k6_relat_1(k3_xboole_0(A_48,A_49))) = k8_relat_1(A_48,k8_relat_1(A_49,B_47))
      | ~ v1_relat_1(B_47) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_115,c_140])).

tff(c_1398,plain,(
    ! [B_62,B_63,A_64] :
      ( k5_relat_1(B_62,k6_relat_1(k3_xboole_0(B_63,A_64))) = k8_relat_1(A_64,k8_relat_1(B_63,B_62))
      | ~ v1_relat_1(B_62) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_436])).

tff(c_1494,plain,(
    ! [B_65] :
      ( k8_relat_1('#skF_2',k8_relat_1('#skF_1',B_65)) = k5_relat_1(B_65,k6_relat_1('#skF_1'))
      | ~ v1_relat_1(B_65) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_1398])).

tff(c_20,plain,
    ( k8_relat_1('#skF_1',k8_relat_1('#skF_2','#skF_3')) != k8_relat_1('#skF_1','#skF_3')
    | k8_relat_1('#skF_2',k8_relat_1('#skF_1','#skF_3')) != k8_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_80,plain,(
    k8_relat_1('#skF_2',k8_relat_1('#skF_1','#skF_3')) != k8_relat_1('#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_1503,plain,
    ( k5_relat_1('#skF_3',k6_relat_1('#skF_1')) != k8_relat_1('#skF_1','#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1494,c_80])).

tff(c_1520,plain,(
    k5_relat_1('#skF_3',k6_relat_1('#skF_1')) != k8_relat_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1503])).

tff(c_1526,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1520])).

tff(c_1530,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1526])).

tff(c_1531,plain,(
    k8_relat_1('#skF_1',k8_relat_1('#skF_2','#skF_3')) != k8_relat_1('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_2239,plain,
    ( k5_relat_1('#skF_3',k6_relat_1('#skF_1')) != k8_relat_1('#skF_1','#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2233,c_1531])).

tff(c_2256,plain,(
    k5_relat_1('#skF_3',k6_relat_1('#skF_1')) != k8_relat_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_2239])).

tff(c_2262,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_2256])).

tff(c_2266,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_2262])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:36:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.48/1.62  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.48/1.63  
% 3.48/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.88/1.63  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k8_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 3.88/1.63  
% 3.88/1.63  %Foreground sorts:
% 3.88/1.63  
% 3.88/1.63  
% 3.88/1.63  %Background operators:
% 3.88/1.63  
% 3.88/1.63  
% 3.88/1.63  %Foreground operators:
% 3.88/1.63  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 3.88/1.63  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.88/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.88/1.63  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.88/1.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.88/1.63  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.88/1.63  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.88/1.63  tff('#skF_2', type, '#skF_2': $i).
% 3.88/1.63  tff('#skF_3', type, '#skF_3': $i).
% 3.88/1.63  tff('#skF_1', type, '#skF_1': $i).
% 3.88/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.88/1.63  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.88/1.63  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.88/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.88/1.63  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.88/1.63  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.88/1.63  
% 3.88/1.64  tff(f_63, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r1_tarski(A, B) => ((k8_relat_1(B, k8_relat_1(A, C)) = k8_relat_1(A, C)) & (k8_relat_1(A, k8_relat_1(B, C)) = k8_relat_1(A, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_funct_1)).
% 3.88/1.64  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_relat_1)).
% 3.88/1.64  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.88/1.64  tff(f_50, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 3.88/1.64  tff(f_52, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 3.88/1.64  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k8_relat_1(A, k5_relat_1(B, C)) = k5_relat_1(B, k8_relat_1(A, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_relat_1)).
% 3.88/1.64  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.88/1.64  tff(c_26, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.88/1.64  tff(c_10, plain, (![B_10, A_9]: (k5_relat_1(B_10, k6_relat_1(A_9))=k8_relat_1(A_9, B_10) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.88/1.64  tff(c_22, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.88/1.64  tff(c_62, plain, (![A_22, B_23]: (k3_xboole_0(A_22, B_23)=A_22 | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.88/1.64  tff(c_66, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_22, c_62])).
% 3.88/1.64  tff(c_14, plain, (![A_15]: (v1_relat_1(k6_relat_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.88/1.64  tff(c_1555, plain, (![B_70, A_71]: (k5_relat_1(k6_relat_1(B_70), k6_relat_1(A_71))=k6_relat_1(k3_xboole_0(A_71, B_70)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.88/1.64  tff(c_1561, plain, (![A_71, B_70]: (k8_relat_1(A_71, k6_relat_1(B_70))=k6_relat_1(k3_xboole_0(A_71, B_70)) | ~v1_relat_1(k6_relat_1(B_70)))), inference(superposition, [status(thm), theory('equality')], [c_1555, c_10])).
% 3.88/1.64  tff(c_1571, plain, (![A_71, B_70]: (k8_relat_1(A_71, k6_relat_1(B_70))=k6_relat_1(k3_xboole_0(A_71, B_70)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1561])).
% 3.88/1.64  tff(c_1585, plain, (![A_74, B_75, C_76]: (k8_relat_1(A_74, k5_relat_1(B_75, C_76))=k5_relat_1(B_75, k8_relat_1(A_74, C_76)) | ~v1_relat_1(C_76) | ~v1_relat_1(B_75))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.88/1.64  tff(c_1597, plain, (![B_10, A_74, A_9]: (k5_relat_1(B_10, k8_relat_1(A_74, k6_relat_1(A_9)))=k8_relat_1(A_74, k8_relat_1(A_9, B_10)) | ~v1_relat_1(k6_relat_1(A_9)) | ~v1_relat_1(B_10) | ~v1_relat_1(B_10))), inference(superposition, [status(thm), theory('equality')], [c_10, c_1585])).
% 3.88/1.64  tff(c_1964, plain, (![B_86, A_87, A_88]: (k5_relat_1(B_86, k6_relat_1(k3_xboole_0(A_87, A_88)))=k8_relat_1(A_87, k8_relat_1(A_88, B_86)) | ~v1_relat_1(B_86))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1571, c_1597])).
% 3.88/1.64  tff(c_2233, plain, (![B_92]: (k8_relat_1('#skF_1', k8_relat_1('#skF_2', B_92))=k5_relat_1(B_92, k6_relat_1('#skF_1')) | ~v1_relat_1(B_92))), inference(superposition, [status(thm), theory('equality')], [c_66, c_1964])).
% 3.88/1.64  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.88/1.64  tff(c_99, plain, (![B_30, A_31]: (k5_relat_1(k6_relat_1(B_30), k6_relat_1(A_31))=k6_relat_1(k3_xboole_0(A_31, B_30)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.88/1.64  tff(c_105, plain, (![A_31, B_30]: (k8_relat_1(A_31, k6_relat_1(B_30))=k6_relat_1(k3_xboole_0(A_31, B_30)) | ~v1_relat_1(k6_relat_1(B_30)))), inference(superposition, [status(thm), theory('equality')], [c_99, c_10])).
% 3.88/1.64  tff(c_115, plain, (![A_31, B_30]: (k8_relat_1(A_31, k6_relat_1(B_30))=k6_relat_1(k3_xboole_0(A_31, B_30)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_105])).
% 3.88/1.64  tff(c_128, plain, (![A_34, B_35, C_36]: (k8_relat_1(A_34, k5_relat_1(B_35, C_36))=k5_relat_1(B_35, k8_relat_1(A_34, C_36)) | ~v1_relat_1(C_36) | ~v1_relat_1(B_35))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.88/1.64  tff(c_140, plain, (![B_10, A_34, A_9]: (k5_relat_1(B_10, k8_relat_1(A_34, k6_relat_1(A_9)))=k8_relat_1(A_34, k8_relat_1(A_9, B_10)) | ~v1_relat_1(k6_relat_1(A_9)) | ~v1_relat_1(B_10) | ~v1_relat_1(B_10))), inference(superposition, [status(thm), theory('equality')], [c_10, c_128])).
% 3.88/1.64  tff(c_436, plain, (![B_47, A_48, A_49]: (k5_relat_1(B_47, k6_relat_1(k3_xboole_0(A_48, A_49)))=k8_relat_1(A_48, k8_relat_1(A_49, B_47)) | ~v1_relat_1(B_47))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_115, c_140])).
% 3.88/1.64  tff(c_1398, plain, (![B_62, B_63, A_64]: (k5_relat_1(B_62, k6_relat_1(k3_xboole_0(B_63, A_64)))=k8_relat_1(A_64, k8_relat_1(B_63, B_62)) | ~v1_relat_1(B_62))), inference(superposition, [status(thm), theory('equality')], [c_2, c_436])).
% 3.88/1.64  tff(c_1494, plain, (![B_65]: (k8_relat_1('#skF_2', k8_relat_1('#skF_1', B_65))=k5_relat_1(B_65, k6_relat_1('#skF_1')) | ~v1_relat_1(B_65))), inference(superposition, [status(thm), theory('equality')], [c_66, c_1398])).
% 3.88/1.64  tff(c_20, plain, (k8_relat_1('#skF_1', k8_relat_1('#skF_2', '#skF_3'))!=k8_relat_1('#skF_1', '#skF_3') | k8_relat_1('#skF_2', k8_relat_1('#skF_1', '#skF_3'))!=k8_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.88/1.64  tff(c_80, plain, (k8_relat_1('#skF_2', k8_relat_1('#skF_1', '#skF_3'))!=k8_relat_1('#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_20])).
% 3.88/1.64  tff(c_1503, plain, (k5_relat_1('#skF_3', k6_relat_1('#skF_1'))!=k8_relat_1('#skF_1', '#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1494, c_80])).
% 3.88/1.64  tff(c_1520, plain, (k5_relat_1('#skF_3', k6_relat_1('#skF_1'))!=k8_relat_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1503])).
% 3.88/1.64  tff(c_1526, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_10, c_1520])).
% 3.88/1.64  tff(c_1530, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_1526])).
% 3.88/1.64  tff(c_1531, plain, (k8_relat_1('#skF_1', k8_relat_1('#skF_2', '#skF_3'))!=k8_relat_1('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_20])).
% 3.88/1.64  tff(c_2239, plain, (k5_relat_1('#skF_3', k6_relat_1('#skF_1'))!=k8_relat_1('#skF_1', '#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2233, c_1531])).
% 3.88/1.64  tff(c_2256, plain, (k5_relat_1('#skF_3', k6_relat_1('#skF_1'))!=k8_relat_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_2239])).
% 3.88/1.64  tff(c_2262, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_10, c_2256])).
% 3.88/1.64  tff(c_2266, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_2262])).
% 3.88/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.88/1.64  
% 3.88/1.64  Inference rules
% 3.88/1.64  ----------------------
% 3.88/1.64  #Ref     : 0
% 3.88/1.64  #Sup     : 573
% 3.88/1.64  #Fact    : 0
% 3.88/1.64  #Define  : 0
% 3.88/1.64  #Split   : 1
% 3.88/1.64  #Chain   : 0
% 3.88/1.64  #Close   : 0
% 3.88/1.64  
% 3.88/1.64  Ordering : KBO
% 3.88/1.64  
% 3.88/1.64  Simplification rules
% 3.88/1.64  ----------------------
% 3.88/1.64  #Subsume      : 60
% 3.88/1.64  #Demod        : 360
% 3.88/1.64  #Tautology    : 263
% 3.88/1.64  #SimpNegUnit  : 0
% 3.88/1.64  #BackRed      : 0
% 3.88/1.64  
% 3.88/1.64  #Partial instantiations: 0
% 3.88/1.64  #Strategies tried      : 1
% 3.88/1.64  
% 3.88/1.64  Timing (in seconds)
% 3.88/1.64  ----------------------
% 3.88/1.65  Preprocessing        : 0.28
% 3.88/1.65  Parsing              : 0.15
% 3.88/1.65  CNF conversion       : 0.02
% 3.88/1.65  Main loop            : 0.60
% 3.88/1.65  Inferencing          : 0.19
% 3.88/1.65  Reduction            : 0.27
% 3.88/1.65  Demodulation         : 0.23
% 3.88/1.65  BG Simplification    : 0.03
% 3.88/1.65  Subsumption          : 0.07
% 3.88/1.65  Abstraction          : 0.04
% 3.88/1.65  MUC search           : 0.00
% 3.88/1.65  Cooper               : 0.00
% 3.88/1.65  Total                : 0.91
% 3.88/1.65  Index Insertion      : 0.00
% 3.88/1.65  Index Deletion       : 0.00
% 3.88/1.65  Index Matching       : 0.00
% 3.88/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
