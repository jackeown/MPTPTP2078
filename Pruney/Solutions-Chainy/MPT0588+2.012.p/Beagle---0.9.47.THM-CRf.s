%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:04 EST 2020

% Result     : Theorem 3.44s
% Output     : CNFRefutation 3.44s
% Verified   : 
% Statistics : Number of formulae       :   51 (  82 expanded)
%              Number of leaves         :   25 (  38 expanded)
%              Depth                    :    9
%              Number of atoms          :   66 ( 127 expanded)
%              Number of equality atoms :   18 (  42 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_69,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k7_relat_1(B,A) = k7_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k3_xboole_0(B,k2_zfmisc_1(A,k2_relat_1(B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_35,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_26,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_183,plain,(
    ! [B_47,A_48] :
      ( k3_xboole_0(B_47,k2_zfmisc_1(A_48,k2_relat_1(B_47))) = k7_relat_1(B_47,A_48)
      | ~ v1_relat_1(B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_198,plain,(
    ! [B_47,A_48] :
      ( r1_tarski(k7_relat_1(B_47,A_48),B_47)
      | ~ v1_relat_1(B_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_2])).

tff(c_12,plain,(
    ! [A_12,B_13] :
      ( v1_relat_1(k3_xboole_0(A_12,B_13))
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_195,plain,(
    ! [B_47,A_48] :
      ( v1_relat_1(k7_relat_1(B_47,A_48))
      | ~ v1_relat_1(B_47)
      | ~ v1_relat_1(B_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_12])).

tff(c_205,plain,(
    ! [A_51,B_52] :
      ( r1_tarski(k1_relat_1(A_51),k1_relat_1(B_52))
      | ~ r1_tarski(A_51,B_52)
      | ~ v1_relat_1(B_52)
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_22,plain,(
    ! [B_23,A_22] :
      ( k7_relat_1(B_23,A_22) = B_23
      | ~ r1_tarski(k1_relat_1(B_23),A_22)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_238,plain,(
    ! [A_64,B_65] :
      ( k7_relat_1(A_64,k1_relat_1(B_65)) = A_64
      | ~ r1_tarski(A_64,B_65)
      | ~ v1_relat_1(B_65)
      | ~ v1_relat_1(A_64) ) ),
    inference(resolution,[status(thm)],[c_205,c_22])).

tff(c_14,plain,(
    ! [C_16,A_14,B_15] :
      ( k7_relat_1(k7_relat_1(C_16,A_14),B_15) = k7_relat_1(C_16,k3_xboole_0(A_14,B_15))
      | ~ v1_relat_1(C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_930,plain,(
    ! [C_123,A_124,B_125] :
      ( k7_relat_1(C_123,k3_xboole_0(A_124,k1_relat_1(B_125))) = k7_relat_1(C_123,A_124)
      | ~ v1_relat_1(C_123)
      | ~ r1_tarski(k7_relat_1(C_123,A_124),B_125)
      | ~ v1_relat_1(B_125)
      | ~ v1_relat_1(k7_relat_1(C_123,A_124)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_14])).

tff(c_4,plain,(
    ! [B_4,A_3] : k2_tarski(B_4,A_3) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_62,plain,(
    ! [A_30,B_31] : k1_setfam_1(k2_tarski(A_30,B_31)) = k3_xboole_0(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_86,plain,(
    ! [A_34,B_35] : k1_setfam_1(k2_tarski(A_34,B_35)) = k3_xboole_0(B_35,A_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_62])).

tff(c_10,plain,(
    ! [A_10,B_11] : k1_setfam_1(k2_tarski(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_92,plain,(
    ! [B_35,A_34] : k3_xboole_0(B_35,A_34) = k3_xboole_0(A_34,B_35) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_10])).

tff(c_24,plain,(
    k7_relat_1('#skF_2',k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1')) != k7_relat_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_163,plain,(
    k7_relat_1('#skF_2',k3_xboole_0('#skF_1',k1_relat_1('#skF_2'))) != k7_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_24])).

tff(c_1005,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_2','#skF_1'),'#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_930,c_163])).

tff(c_1036,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_2','#skF_1'),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1005])).

tff(c_1039,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_1036])).

tff(c_1042,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_195,c_1039])).

tff(c_1046,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1042])).

tff(c_1047,plain,(
    ~ r1_tarski(k7_relat_1('#skF_2','#skF_1'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_1036])).

tff(c_1051,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_198,c_1047])).

tff(c_1055,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1051])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:40:01 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.44/1.57  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.44/1.58  
% 3.44/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.44/1.58  %$ r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 3.44/1.58  
% 3.44/1.58  %Foreground sorts:
% 3.44/1.58  
% 3.44/1.58  
% 3.44/1.58  %Background operators:
% 3.44/1.58  
% 3.44/1.58  
% 3.44/1.58  %Foreground operators:
% 3.44/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.44/1.58  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.44/1.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.44/1.58  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.44/1.58  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.44/1.58  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.44/1.58  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.44/1.58  tff('#skF_2', type, '#skF_2': $i).
% 3.44/1.58  tff('#skF_1', type, '#skF_1': $i).
% 3.44/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.44/1.58  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.44/1.58  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.44/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.44/1.58  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.44/1.58  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.44/1.58  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.44/1.58  
% 3.44/1.59  tff(f_69, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k7_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t192_relat_1)).
% 3.44/1.59  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k3_xboole_0(B, k2_zfmisc_1(A, k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t96_relat_1)).
% 3.44/1.59  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.44/1.59  tff(f_39, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_relat_1)).
% 3.44/1.59  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 3.44/1.59  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 3.44/1.59  tff(f_43, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 3.44/1.59  tff(f_29, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.44/1.59  tff(f_35, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.44/1.59  tff(c_26, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.44/1.59  tff(c_183, plain, (![B_47, A_48]: (k3_xboole_0(B_47, k2_zfmisc_1(A_48, k2_relat_1(B_47)))=k7_relat_1(B_47, A_48) | ~v1_relat_1(B_47))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.44/1.59  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.44/1.59  tff(c_198, plain, (![B_47, A_48]: (r1_tarski(k7_relat_1(B_47, A_48), B_47) | ~v1_relat_1(B_47))), inference(superposition, [status(thm), theory('equality')], [c_183, c_2])).
% 3.44/1.59  tff(c_12, plain, (![A_12, B_13]: (v1_relat_1(k3_xboole_0(A_12, B_13)) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.44/1.59  tff(c_195, plain, (![B_47, A_48]: (v1_relat_1(k7_relat_1(B_47, A_48)) | ~v1_relat_1(B_47) | ~v1_relat_1(B_47))), inference(superposition, [status(thm), theory('equality')], [c_183, c_12])).
% 3.44/1.59  tff(c_205, plain, (![A_51, B_52]: (r1_tarski(k1_relat_1(A_51), k1_relat_1(B_52)) | ~r1_tarski(A_51, B_52) | ~v1_relat_1(B_52) | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.44/1.59  tff(c_22, plain, (![B_23, A_22]: (k7_relat_1(B_23, A_22)=B_23 | ~r1_tarski(k1_relat_1(B_23), A_22) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.44/1.59  tff(c_238, plain, (![A_64, B_65]: (k7_relat_1(A_64, k1_relat_1(B_65))=A_64 | ~r1_tarski(A_64, B_65) | ~v1_relat_1(B_65) | ~v1_relat_1(A_64))), inference(resolution, [status(thm)], [c_205, c_22])).
% 3.44/1.59  tff(c_14, plain, (![C_16, A_14, B_15]: (k7_relat_1(k7_relat_1(C_16, A_14), B_15)=k7_relat_1(C_16, k3_xboole_0(A_14, B_15)) | ~v1_relat_1(C_16))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.44/1.59  tff(c_930, plain, (![C_123, A_124, B_125]: (k7_relat_1(C_123, k3_xboole_0(A_124, k1_relat_1(B_125)))=k7_relat_1(C_123, A_124) | ~v1_relat_1(C_123) | ~r1_tarski(k7_relat_1(C_123, A_124), B_125) | ~v1_relat_1(B_125) | ~v1_relat_1(k7_relat_1(C_123, A_124)))), inference(superposition, [status(thm), theory('equality')], [c_238, c_14])).
% 3.44/1.59  tff(c_4, plain, (![B_4, A_3]: (k2_tarski(B_4, A_3)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.44/1.59  tff(c_62, plain, (![A_30, B_31]: (k1_setfam_1(k2_tarski(A_30, B_31))=k3_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.44/1.59  tff(c_86, plain, (![A_34, B_35]: (k1_setfam_1(k2_tarski(A_34, B_35))=k3_xboole_0(B_35, A_34))), inference(superposition, [status(thm), theory('equality')], [c_4, c_62])).
% 3.44/1.59  tff(c_10, plain, (![A_10, B_11]: (k1_setfam_1(k2_tarski(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.44/1.59  tff(c_92, plain, (![B_35, A_34]: (k3_xboole_0(B_35, A_34)=k3_xboole_0(A_34, B_35))), inference(superposition, [status(thm), theory('equality')], [c_86, c_10])).
% 3.44/1.59  tff(c_24, plain, (k7_relat_1('#skF_2', k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1'))!=k7_relat_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.44/1.59  tff(c_163, plain, (k7_relat_1('#skF_2', k3_xboole_0('#skF_1', k1_relat_1('#skF_2')))!=k7_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_24])).
% 3.44/1.59  tff(c_1005, plain, (~r1_tarski(k7_relat_1('#skF_2', '#skF_1'), '#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_930, c_163])).
% 3.44/1.59  tff(c_1036, plain, (~r1_tarski(k7_relat_1('#skF_2', '#skF_1'), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1005])).
% 3.44/1.59  tff(c_1039, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_1036])).
% 3.44/1.59  tff(c_1042, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_195, c_1039])).
% 3.44/1.59  tff(c_1046, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_1042])).
% 3.44/1.59  tff(c_1047, plain, (~r1_tarski(k7_relat_1('#skF_2', '#skF_1'), '#skF_2')), inference(splitRight, [status(thm)], [c_1036])).
% 3.44/1.59  tff(c_1051, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_198, c_1047])).
% 3.44/1.59  tff(c_1055, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_1051])).
% 3.44/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.44/1.59  
% 3.44/1.59  Inference rules
% 3.44/1.59  ----------------------
% 3.44/1.59  #Ref     : 0
% 3.44/1.59  #Sup     : 287
% 3.44/1.59  #Fact    : 0
% 3.44/1.59  #Define  : 0
% 3.44/1.59  #Split   : 1
% 3.44/1.59  #Chain   : 0
% 3.44/1.59  #Close   : 0
% 3.44/1.59  
% 3.44/1.59  Ordering : KBO
% 3.44/1.59  
% 3.44/1.59  Simplification rules
% 3.44/1.59  ----------------------
% 3.44/1.59  #Subsume      : 84
% 3.44/1.59  #Demod        : 27
% 3.44/1.59  #Tautology    : 48
% 3.44/1.59  #SimpNegUnit  : 0
% 3.44/1.59  #BackRed      : 0
% 3.44/1.59  
% 3.44/1.59  #Partial instantiations: 0
% 3.44/1.59  #Strategies tried      : 1
% 3.44/1.59  
% 3.44/1.59  Timing (in seconds)
% 3.44/1.59  ----------------------
% 3.44/1.59  Preprocessing        : 0.31
% 3.44/1.59  Parsing              : 0.18
% 3.44/1.59  CNF conversion       : 0.02
% 3.44/1.59  Main loop            : 0.47
% 3.44/1.59  Inferencing          : 0.18
% 3.44/1.59  Reduction            : 0.14
% 3.44/1.59  Demodulation         : 0.11
% 3.44/1.59  BG Simplification    : 0.02
% 3.44/1.59  Subsumption          : 0.10
% 3.44/1.59  Abstraction          : 0.02
% 3.44/1.59  MUC search           : 0.00
% 3.44/1.59  Cooper               : 0.00
% 3.44/1.59  Total                : 0.81
% 3.44/1.59  Index Insertion      : 0.00
% 3.44/1.59  Index Deletion       : 0.00
% 3.44/1.59  Index Matching       : 0.00
% 3.44/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
