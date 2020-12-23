%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:21 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   45 (  61 expanded)
%              Number of leaves         :   22 (  31 expanded)
%              Depth                    :    9
%              Number of atoms          :   56 ( 102 expanded)
%              Number of equality atoms :   24 (  42 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k8_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

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

tff(f_65,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r1_tarski(A,B)
         => ( k8_relat_1(B,k8_relat_1(A,C)) = k8_relat_1(A,C)
            & k8_relat_1(A,k8_relat_1(B,C)) = k8_relat_1(A,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_funct_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_54,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k8_relat_1(A,k5_relat_1(B,C)) = k5_relat_1(B,k8_relat_1(A,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_relat_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k8_relat_1(B,k8_relat_1(A,C)) = k8_relat_1(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_relat_1)).

tff(c_24,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_6,plain,(
    ! [B_6,A_5] :
      ( k5_relat_1(B_6,k6_relat_1(A_5)) = k8_relat_1(A_5,B_6)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_20,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_27,plain,(
    ! [A_19,B_20] :
      ( k3_xboole_0(A_19,B_20) = A_19
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_31,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_20,c_27])).

tff(c_12,plain,(
    ! [A_14] : v1_relat_1(k6_relat_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_115,plain,(
    ! [B_32,A_33] : k5_relat_1(k6_relat_1(B_32),k6_relat_1(A_33)) = k6_relat_1(k3_xboole_0(A_33,B_32)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_121,plain,(
    ! [A_33,B_32] :
      ( k8_relat_1(A_33,k6_relat_1(B_32)) = k6_relat_1(k3_xboole_0(A_33,B_32))
      | ~ v1_relat_1(k6_relat_1(B_32)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_6])).

tff(c_131,plain,(
    ! [A_33,B_32] : k8_relat_1(A_33,k6_relat_1(B_32)) = k6_relat_1(k3_xboole_0(A_33,B_32)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_121])).

tff(c_251,plain,(
    ! [A_43,B_44,C_45] :
      ( k8_relat_1(A_43,k5_relat_1(B_44,C_45)) = k5_relat_1(B_44,k8_relat_1(A_43,C_45))
      | ~ v1_relat_1(C_45)
      | ~ v1_relat_1(B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_266,plain,(
    ! [B_6,A_43,A_5] :
      ( k5_relat_1(B_6,k8_relat_1(A_43,k6_relat_1(A_5))) = k8_relat_1(A_43,k8_relat_1(A_5,B_6))
      | ~ v1_relat_1(k6_relat_1(A_5))
      | ~ v1_relat_1(B_6)
      | ~ v1_relat_1(B_6) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_251])).

tff(c_359,plain,(
    ! [B_50,A_51,A_52] :
      ( k5_relat_1(B_50,k6_relat_1(k3_xboole_0(A_51,A_52))) = k8_relat_1(A_51,k8_relat_1(A_52,B_50))
      | ~ v1_relat_1(B_50) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_131,c_266])).

tff(c_407,plain,(
    ! [B_53] :
      ( k8_relat_1('#skF_1',k8_relat_1('#skF_2',B_53)) = k5_relat_1(B_53,k6_relat_1('#skF_1'))
      | ~ v1_relat_1(B_53) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_31,c_359])).

tff(c_85,plain,(
    ! [B_29,A_30,C_31] :
      ( k8_relat_1(B_29,k8_relat_1(A_30,C_31)) = k8_relat_1(A_30,C_31)
      | ~ r1_tarski(A_30,B_29)
      | ~ v1_relat_1(C_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,
    ( k8_relat_1('#skF_1',k8_relat_1('#skF_2','#skF_3')) != k8_relat_1('#skF_1','#skF_3')
    | k8_relat_1('#skF_2',k8_relat_1('#skF_1','#skF_3')) != k8_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_54,plain,(
    k8_relat_1('#skF_2',k8_relat_1('#skF_1','#skF_3')) != k8_relat_1('#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_94,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_54])).

tff(c_108,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_20,c_94])).

tff(c_109,plain,(
    k8_relat_1('#skF_1',k8_relat_1('#skF_2','#skF_3')) != k8_relat_1('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_419,plain,
    ( k5_relat_1('#skF_3',k6_relat_1('#skF_1')) != k8_relat_1('#skF_1','#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_407,c_109])).

tff(c_444,plain,(
    k5_relat_1('#skF_3',k6_relat_1('#skF_1')) != k8_relat_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_419])).

tff(c_450,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_444])).

tff(c_454,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_450])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:25:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.13/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.26  
% 2.13/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.26  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k8_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 2.13/1.26  
% 2.13/1.26  %Foreground sorts:
% 2.13/1.26  
% 2.13/1.26  
% 2.13/1.26  %Background operators:
% 2.13/1.26  
% 2.13/1.26  
% 2.13/1.26  %Foreground operators:
% 2.13/1.26  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.13/1.26  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.13/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.13/1.26  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.13/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.13/1.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.13/1.26  tff('#skF_2', type, '#skF_2': $i).
% 2.13/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.13/1.26  tff('#skF_1', type, '#skF_1': $i).
% 2.13/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.13/1.26  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.13/1.26  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.13/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.13/1.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.13/1.26  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.13/1.26  
% 2.13/1.27  tff(f_65, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r1_tarski(A, B) => ((k8_relat_1(B, k8_relat_1(A, C)) = k8_relat_1(A, C)) & (k8_relat_1(A, k8_relat_1(B, C)) = k8_relat_1(A, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_funct_1)).
% 2.13/1.27  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 2.13/1.27  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.13/1.27  tff(f_52, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.13/1.27  tff(f_54, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 2.13/1.27  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k8_relat_1(A, k5_relat_1(B, C)) = k5_relat_1(B, k8_relat_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_relat_1)).
% 2.13/1.27  tff(f_41, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k8_relat_1(B, k8_relat_1(A, C)) = k8_relat_1(A, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t129_relat_1)).
% 2.13/1.27  tff(c_24, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.13/1.27  tff(c_6, plain, (![B_6, A_5]: (k5_relat_1(B_6, k6_relat_1(A_5))=k8_relat_1(A_5, B_6) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.13/1.27  tff(c_20, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.13/1.27  tff(c_27, plain, (![A_19, B_20]: (k3_xboole_0(A_19, B_20)=A_19 | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.13/1.27  tff(c_31, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_20, c_27])).
% 2.13/1.27  tff(c_12, plain, (![A_14]: (v1_relat_1(k6_relat_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.13/1.27  tff(c_115, plain, (![B_32, A_33]: (k5_relat_1(k6_relat_1(B_32), k6_relat_1(A_33))=k6_relat_1(k3_xboole_0(A_33, B_32)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.13/1.27  tff(c_121, plain, (![A_33, B_32]: (k8_relat_1(A_33, k6_relat_1(B_32))=k6_relat_1(k3_xboole_0(A_33, B_32)) | ~v1_relat_1(k6_relat_1(B_32)))), inference(superposition, [status(thm), theory('equality')], [c_115, c_6])).
% 2.13/1.27  tff(c_131, plain, (![A_33, B_32]: (k8_relat_1(A_33, k6_relat_1(B_32))=k6_relat_1(k3_xboole_0(A_33, B_32)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_121])).
% 2.13/1.27  tff(c_251, plain, (![A_43, B_44, C_45]: (k8_relat_1(A_43, k5_relat_1(B_44, C_45))=k5_relat_1(B_44, k8_relat_1(A_43, C_45)) | ~v1_relat_1(C_45) | ~v1_relat_1(B_44))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.13/1.27  tff(c_266, plain, (![B_6, A_43, A_5]: (k5_relat_1(B_6, k8_relat_1(A_43, k6_relat_1(A_5)))=k8_relat_1(A_43, k8_relat_1(A_5, B_6)) | ~v1_relat_1(k6_relat_1(A_5)) | ~v1_relat_1(B_6) | ~v1_relat_1(B_6))), inference(superposition, [status(thm), theory('equality')], [c_6, c_251])).
% 2.13/1.27  tff(c_359, plain, (![B_50, A_51, A_52]: (k5_relat_1(B_50, k6_relat_1(k3_xboole_0(A_51, A_52)))=k8_relat_1(A_51, k8_relat_1(A_52, B_50)) | ~v1_relat_1(B_50))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_131, c_266])).
% 2.13/1.27  tff(c_407, plain, (![B_53]: (k8_relat_1('#skF_1', k8_relat_1('#skF_2', B_53))=k5_relat_1(B_53, k6_relat_1('#skF_1')) | ~v1_relat_1(B_53))), inference(superposition, [status(thm), theory('equality')], [c_31, c_359])).
% 2.13/1.27  tff(c_85, plain, (![B_29, A_30, C_31]: (k8_relat_1(B_29, k8_relat_1(A_30, C_31))=k8_relat_1(A_30, C_31) | ~r1_tarski(A_30, B_29) | ~v1_relat_1(C_31))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.13/1.27  tff(c_18, plain, (k8_relat_1('#skF_1', k8_relat_1('#skF_2', '#skF_3'))!=k8_relat_1('#skF_1', '#skF_3') | k8_relat_1('#skF_2', k8_relat_1('#skF_1', '#skF_3'))!=k8_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.13/1.27  tff(c_54, plain, (k8_relat_1('#skF_2', k8_relat_1('#skF_1', '#skF_3'))!=k8_relat_1('#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_18])).
% 2.13/1.27  tff(c_94, plain, (~r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_85, c_54])).
% 2.13/1.27  tff(c_108, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_20, c_94])).
% 2.13/1.27  tff(c_109, plain, (k8_relat_1('#skF_1', k8_relat_1('#skF_2', '#skF_3'))!=k8_relat_1('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_18])).
% 2.13/1.27  tff(c_419, plain, (k5_relat_1('#skF_3', k6_relat_1('#skF_1'))!=k8_relat_1('#skF_1', '#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_407, c_109])).
% 2.13/1.27  tff(c_444, plain, (k5_relat_1('#skF_3', k6_relat_1('#skF_1'))!=k8_relat_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_419])).
% 2.13/1.27  tff(c_450, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6, c_444])).
% 2.13/1.27  tff(c_454, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_450])).
% 2.13/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.27  
% 2.13/1.27  Inference rules
% 2.13/1.27  ----------------------
% 2.13/1.27  #Ref     : 0
% 2.13/1.27  #Sup     : 104
% 2.13/1.27  #Fact    : 0
% 2.13/1.27  #Define  : 0
% 2.13/1.27  #Split   : 2
% 2.13/1.27  #Chain   : 0
% 2.13/1.27  #Close   : 0
% 2.13/1.27  
% 2.13/1.27  Ordering : KBO
% 2.13/1.27  
% 2.13/1.27  Simplification rules
% 2.13/1.27  ----------------------
% 2.13/1.27  #Subsume      : 6
% 2.13/1.27  #Demod        : 66
% 2.13/1.27  #Tautology    : 48
% 2.13/1.27  #SimpNegUnit  : 0
% 2.13/1.27  #BackRed      : 0
% 2.13/1.27  
% 2.13/1.27  #Partial instantiations: 0
% 2.13/1.27  #Strategies tried      : 1
% 2.13/1.27  
% 2.13/1.27  Timing (in seconds)
% 2.13/1.27  ----------------------
% 2.13/1.27  Preprocessing        : 0.29
% 2.13/1.27  Parsing              : 0.15
% 2.13/1.27  CNF conversion       : 0.02
% 2.13/1.27  Main loop            : 0.23
% 2.13/1.27  Inferencing          : 0.10
% 2.13/1.27  Reduction            : 0.08
% 2.13/1.27  Demodulation         : 0.06
% 2.13/1.27  BG Simplification    : 0.02
% 2.13/1.27  Subsumption          : 0.03
% 2.13/1.27  Abstraction          : 0.02
% 2.13/1.27  MUC search           : 0.00
% 2.13/1.27  Cooper               : 0.00
% 2.13/1.27  Total                : 0.55
% 2.13/1.27  Index Insertion      : 0.00
% 2.13/1.27  Index Deletion       : 0.00
% 2.13/1.27  Index Matching       : 0.00
% 2.13/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
