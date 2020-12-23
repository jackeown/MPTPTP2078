%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:21 EST 2020

% Result     : Theorem 5.70s
% Output     : CNFRefutation 5.92s
% Verified   : 
% Statistics : Number of formulae       :   61 (  94 expanded)
%              Number of leaves         :   23 (  42 expanded)
%              Depth                    :   10
%              Number of atoms          :   78 ( 156 expanded)
%              Number of equality atoms :   40 (  71 expanded)
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

tff(f_61,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r1_tarski(A,B)
         => ( k8_relat_1(B,k8_relat_1(A,C)) = k8_relat_1(A,C)
            & k8_relat_1(A,k8_relat_1(B,C)) = k8_relat_1(A,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_funct_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_50,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k8_relat_1(A,k5_relat_1(B,C)) = k5_relat_1(B,k8_relat_1(A,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_relat_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_33,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_24,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_8,plain,(
    ! [B_8,A_7] :
      ( k5_relat_1(B_8,k6_relat_1(A_7)) = k8_relat_1(A_7,B_8)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_20,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_75,plain,(
    ! [A_22,B_23] :
      ( k3_xboole_0(A_22,B_23) = A_22
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_79,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_20,c_75])).

tff(c_12,plain,(
    ! [A_13] : v1_relat_1(k6_relat_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_4865,plain,(
    ! [B_122,A_123] :
      ( k5_relat_1(B_122,k6_relat_1(A_123)) = k8_relat_1(A_123,B_122)
      | ~ v1_relat_1(B_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,(
    ! [B_15,A_14] : k5_relat_1(k6_relat_1(B_15),k6_relat_1(A_14)) = k6_relat_1(k3_xboole_0(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_4872,plain,(
    ! [A_123,B_15] :
      ( k8_relat_1(A_123,k6_relat_1(B_15)) = k6_relat_1(k3_xboole_0(A_123,B_15))
      | ~ v1_relat_1(k6_relat_1(B_15)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4865,c_16])).

tff(c_4881,plain,(
    ! [A_123,B_15] : k8_relat_1(A_123,k6_relat_1(B_15)) = k6_relat_1(k3_xboole_0(A_123,B_15)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_4872])).

tff(c_4894,plain,(
    ! [A_126,B_127,C_128] :
      ( k8_relat_1(A_126,k5_relat_1(B_127,C_128)) = k5_relat_1(B_127,k8_relat_1(A_126,C_128))
      | ~ v1_relat_1(C_128)
      | ~ v1_relat_1(B_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_4903,plain,(
    ! [B_8,A_126,A_7] :
      ( k5_relat_1(B_8,k8_relat_1(A_126,k6_relat_1(A_7))) = k8_relat_1(A_126,k8_relat_1(A_7,B_8))
      | ~ v1_relat_1(k6_relat_1(A_7))
      | ~ v1_relat_1(B_8)
      | ~ v1_relat_1(B_8) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_4894])).

tff(c_5054,plain,(
    ! [B_134,A_135,A_136] :
      ( k5_relat_1(B_134,k6_relat_1(k3_xboole_0(A_135,A_136))) = k8_relat_1(A_135,k8_relat_1(A_136,B_134))
      | ~ v1_relat_1(B_134) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_4881,c_4903])).

tff(c_5105,plain,(
    ! [B_137] :
      ( k8_relat_1('#skF_1',k8_relat_1('#skF_2',B_137)) = k5_relat_1(B_137,k6_relat_1('#skF_1'))
      | ~ v1_relat_1(B_137) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_5054])).

tff(c_4,plain,(
    ! [B_4,A_3] : k2_tarski(B_4,A_3) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_60,plain,(
    ! [A_20,B_21] : k1_setfam_1(k2_tarski(A_20,B_21)) = k3_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_85,plain,(
    ! [B_24,A_25] : k1_setfam_1(k2_tarski(B_24,A_25)) = k3_xboole_0(A_25,B_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_60])).

tff(c_6,plain,(
    ! [A_5,B_6] : k1_setfam_1(k2_tarski(A_5,B_6)) = k3_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_91,plain,(
    ! [B_24,A_25] : k3_xboole_0(B_24,A_25) = k3_xboole_0(A_25,B_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_6])).

tff(c_151,plain,(
    ! [B_30,A_31] : k5_relat_1(k6_relat_1(B_30),k6_relat_1(A_31)) = k6_relat_1(k3_xboole_0(A_31,B_30)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_157,plain,(
    ! [A_31,B_30] :
      ( k8_relat_1(A_31,k6_relat_1(B_30)) = k6_relat_1(k3_xboole_0(A_31,B_30))
      | ~ v1_relat_1(k6_relat_1(B_30)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_8])).

tff(c_167,plain,(
    ! [A_31,B_30] : k8_relat_1(A_31,k6_relat_1(B_30)) = k6_relat_1(k3_xboole_0(A_31,B_30)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_157])).

tff(c_181,plain,(
    ! [A_34,B_35,C_36] :
      ( k8_relat_1(A_34,k5_relat_1(B_35,C_36)) = k5_relat_1(B_35,k8_relat_1(A_34,C_36))
      | ~ v1_relat_1(C_36)
      | ~ v1_relat_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_193,plain,(
    ! [B_8,A_34,A_7] :
      ( k5_relat_1(B_8,k8_relat_1(A_34,k6_relat_1(A_7))) = k8_relat_1(A_34,k8_relat_1(A_7,B_8))
      | ~ v1_relat_1(k6_relat_1(A_7))
      | ~ v1_relat_1(B_8)
      | ~ v1_relat_1(B_8) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_181])).

tff(c_477,plain,(
    ! [B_45,A_46,A_47] :
      ( k5_relat_1(B_45,k6_relat_1(k3_xboole_0(A_46,A_47))) = k8_relat_1(A_46,k8_relat_1(A_47,B_45))
      | ~ v1_relat_1(B_45) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_167,c_193])).

tff(c_4578,plain,(
    ! [B_112,B_113,A_114] :
      ( k5_relat_1(B_112,k6_relat_1(k3_xboole_0(B_113,A_114))) = k8_relat_1(A_114,k8_relat_1(B_113,B_112))
      | ~ v1_relat_1(B_112) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_477])).

tff(c_4732,plain,(
    ! [B_115] :
      ( k8_relat_1('#skF_2',k8_relat_1('#skF_1',B_115)) = k5_relat_1(B_115,k6_relat_1('#skF_1'))
      | ~ v1_relat_1(B_115) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_4578])).

tff(c_18,plain,
    ( k8_relat_1('#skF_1',k8_relat_1('#skF_2','#skF_3')) != k8_relat_1('#skF_1','#skF_3')
    | k8_relat_1('#skF_2',k8_relat_1('#skF_1','#skF_3')) != k8_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_84,plain,(
    k8_relat_1('#skF_2',k8_relat_1('#skF_1','#skF_3')) != k8_relat_1('#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_4747,plain,
    ( k5_relat_1('#skF_3',k6_relat_1('#skF_1')) != k8_relat_1('#skF_1','#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4732,c_84])).

tff(c_4778,plain,(
    k5_relat_1('#skF_3',k6_relat_1('#skF_1')) != k8_relat_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_4747])).

tff(c_4788,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_4778])).

tff(c_4792,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_4788])).

tff(c_4793,plain,(
    k8_relat_1('#skF_1',k8_relat_1('#skF_2','#skF_3')) != k8_relat_1('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_5111,plain,
    ( k5_relat_1('#skF_3',k6_relat_1('#skF_1')) != k8_relat_1('#skF_1','#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5105,c_4793])).

tff(c_5128,plain,(
    k5_relat_1('#skF_3',k6_relat_1('#skF_1')) != k8_relat_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_5111])).

tff(c_5134,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_5128])).

tff(c_5138,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_5134])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:19:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.70/2.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.70/2.29  
% 5.70/2.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.70/2.29  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k8_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 5.70/2.29  
% 5.70/2.29  %Foreground sorts:
% 5.70/2.29  
% 5.70/2.29  
% 5.70/2.29  %Background operators:
% 5.70/2.29  
% 5.70/2.29  
% 5.70/2.29  %Foreground operators:
% 5.70/2.29  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 5.70/2.29  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.70/2.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.70/2.29  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.70/2.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.70/2.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.70/2.29  tff('#skF_2', type, '#skF_2': $i).
% 5.70/2.29  tff('#skF_3', type, '#skF_3': $i).
% 5.70/2.29  tff('#skF_1', type, '#skF_1': $i).
% 5.70/2.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.70/2.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.70/2.29  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.70/2.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.70/2.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.70/2.29  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.70/2.29  
% 5.92/2.30  tff(f_61, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r1_tarski(A, B) => ((k8_relat_1(B, k8_relat_1(A, C)) = k8_relat_1(A, C)) & (k8_relat_1(A, k8_relat_1(B, C)) = k8_relat_1(A, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_funct_1)).
% 5.92/2.30  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 5.92/2.30  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 5.92/2.30  tff(f_48, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 5.92/2.30  tff(f_50, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 5.92/2.30  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k8_relat_1(A, k5_relat_1(B, C)) = k5_relat_1(B, k8_relat_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_relat_1)).
% 5.92/2.30  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 5.92/2.30  tff(f_33, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 5.92/2.30  tff(c_24, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.92/2.30  tff(c_8, plain, (![B_8, A_7]: (k5_relat_1(B_8, k6_relat_1(A_7))=k8_relat_1(A_7, B_8) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.92/2.30  tff(c_20, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.92/2.30  tff(c_75, plain, (![A_22, B_23]: (k3_xboole_0(A_22, B_23)=A_22 | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.92/2.30  tff(c_79, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_20, c_75])).
% 5.92/2.30  tff(c_12, plain, (![A_13]: (v1_relat_1(k6_relat_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.92/2.30  tff(c_4865, plain, (![B_122, A_123]: (k5_relat_1(B_122, k6_relat_1(A_123))=k8_relat_1(A_123, B_122) | ~v1_relat_1(B_122))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.92/2.30  tff(c_16, plain, (![B_15, A_14]: (k5_relat_1(k6_relat_1(B_15), k6_relat_1(A_14))=k6_relat_1(k3_xboole_0(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.92/2.30  tff(c_4872, plain, (![A_123, B_15]: (k8_relat_1(A_123, k6_relat_1(B_15))=k6_relat_1(k3_xboole_0(A_123, B_15)) | ~v1_relat_1(k6_relat_1(B_15)))), inference(superposition, [status(thm), theory('equality')], [c_4865, c_16])).
% 5.92/2.30  tff(c_4881, plain, (![A_123, B_15]: (k8_relat_1(A_123, k6_relat_1(B_15))=k6_relat_1(k3_xboole_0(A_123, B_15)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_4872])).
% 5.92/2.30  tff(c_4894, plain, (![A_126, B_127, C_128]: (k8_relat_1(A_126, k5_relat_1(B_127, C_128))=k5_relat_1(B_127, k8_relat_1(A_126, C_128)) | ~v1_relat_1(C_128) | ~v1_relat_1(B_127))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.92/2.30  tff(c_4903, plain, (![B_8, A_126, A_7]: (k5_relat_1(B_8, k8_relat_1(A_126, k6_relat_1(A_7)))=k8_relat_1(A_126, k8_relat_1(A_7, B_8)) | ~v1_relat_1(k6_relat_1(A_7)) | ~v1_relat_1(B_8) | ~v1_relat_1(B_8))), inference(superposition, [status(thm), theory('equality')], [c_8, c_4894])).
% 5.92/2.30  tff(c_5054, plain, (![B_134, A_135, A_136]: (k5_relat_1(B_134, k6_relat_1(k3_xboole_0(A_135, A_136)))=k8_relat_1(A_135, k8_relat_1(A_136, B_134)) | ~v1_relat_1(B_134))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_4881, c_4903])).
% 5.92/2.30  tff(c_5105, plain, (![B_137]: (k8_relat_1('#skF_1', k8_relat_1('#skF_2', B_137))=k5_relat_1(B_137, k6_relat_1('#skF_1')) | ~v1_relat_1(B_137))), inference(superposition, [status(thm), theory('equality')], [c_79, c_5054])).
% 5.92/2.30  tff(c_4, plain, (![B_4, A_3]: (k2_tarski(B_4, A_3)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.92/2.30  tff(c_60, plain, (![A_20, B_21]: (k1_setfam_1(k2_tarski(A_20, B_21))=k3_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.92/2.30  tff(c_85, plain, (![B_24, A_25]: (k1_setfam_1(k2_tarski(B_24, A_25))=k3_xboole_0(A_25, B_24))), inference(superposition, [status(thm), theory('equality')], [c_4, c_60])).
% 5.92/2.30  tff(c_6, plain, (![A_5, B_6]: (k1_setfam_1(k2_tarski(A_5, B_6))=k3_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.92/2.30  tff(c_91, plain, (![B_24, A_25]: (k3_xboole_0(B_24, A_25)=k3_xboole_0(A_25, B_24))), inference(superposition, [status(thm), theory('equality')], [c_85, c_6])).
% 5.92/2.30  tff(c_151, plain, (![B_30, A_31]: (k5_relat_1(k6_relat_1(B_30), k6_relat_1(A_31))=k6_relat_1(k3_xboole_0(A_31, B_30)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.92/2.30  tff(c_157, plain, (![A_31, B_30]: (k8_relat_1(A_31, k6_relat_1(B_30))=k6_relat_1(k3_xboole_0(A_31, B_30)) | ~v1_relat_1(k6_relat_1(B_30)))), inference(superposition, [status(thm), theory('equality')], [c_151, c_8])).
% 5.92/2.30  tff(c_167, plain, (![A_31, B_30]: (k8_relat_1(A_31, k6_relat_1(B_30))=k6_relat_1(k3_xboole_0(A_31, B_30)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_157])).
% 5.92/2.30  tff(c_181, plain, (![A_34, B_35, C_36]: (k8_relat_1(A_34, k5_relat_1(B_35, C_36))=k5_relat_1(B_35, k8_relat_1(A_34, C_36)) | ~v1_relat_1(C_36) | ~v1_relat_1(B_35))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.92/2.30  tff(c_193, plain, (![B_8, A_34, A_7]: (k5_relat_1(B_8, k8_relat_1(A_34, k6_relat_1(A_7)))=k8_relat_1(A_34, k8_relat_1(A_7, B_8)) | ~v1_relat_1(k6_relat_1(A_7)) | ~v1_relat_1(B_8) | ~v1_relat_1(B_8))), inference(superposition, [status(thm), theory('equality')], [c_8, c_181])).
% 5.92/2.30  tff(c_477, plain, (![B_45, A_46, A_47]: (k5_relat_1(B_45, k6_relat_1(k3_xboole_0(A_46, A_47)))=k8_relat_1(A_46, k8_relat_1(A_47, B_45)) | ~v1_relat_1(B_45))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_167, c_193])).
% 5.92/2.30  tff(c_4578, plain, (![B_112, B_113, A_114]: (k5_relat_1(B_112, k6_relat_1(k3_xboole_0(B_113, A_114)))=k8_relat_1(A_114, k8_relat_1(B_113, B_112)) | ~v1_relat_1(B_112))), inference(superposition, [status(thm), theory('equality')], [c_91, c_477])).
% 5.92/2.30  tff(c_4732, plain, (![B_115]: (k8_relat_1('#skF_2', k8_relat_1('#skF_1', B_115))=k5_relat_1(B_115, k6_relat_1('#skF_1')) | ~v1_relat_1(B_115))), inference(superposition, [status(thm), theory('equality')], [c_79, c_4578])).
% 5.92/2.30  tff(c_18, plain, (k8_relat_1('#skF_1', k8_relat_1('#skF_2', '#skF_3'))!=k8_relat_1('#skF_1', '#skF_3') | k8_relat_1('#skF_2', k8_relat_1('#skF_1', '#skF_3'))!=k8_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.92/2.30  tff(c_84, plain, (k8_relat_1('#skF_2', k8_relat_1('#skF_1', '#skF_3'))!=k8_relat_1('#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_18])).
% 5.92/2.30  tff(c_4747, plain, (k5_relat_1('#skF_3', k6_relat_1('#skF_1'))!=k8_relat_1('#skF_1', '#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4732, c_84])).
% 5.92/2.30  tff(c_4778, plain, (k5_relat_1('#skF_3', k6_relat_1('#skF_1'))!=k8_relat_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_4747])).
% 5.92/2.30  tff(c_4788, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_8, c_4778])).
% 5.92/2.30  tff(c_4792, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_4788])).
% 5.92/2.30  tff(c_4793, plain, (k8_relat_1('#skF_1', k8_relat_1('#skF_2', '#skF_3'))!=k8_relat_1('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_18])).
% 5.92/2.30  tff(c_5111, plain, (k5_relat_1('#skF_3', k6_relat_1('#skF_1'))!=k8_relat_1('#skF_1', '#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5105, c_4793])).
% 5.92/2.30  tff(c_5128, plain, (k5_relat_1('#skF_3', k6_relat_1('#skF_1'))!=k8_relat_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_5111])).
% 5.92/2.30  tff(c_5134, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_8, c_5128])).
% 5.92/2.30  tff(c_5138, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_5134])).
% 5.92/2.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.92/2.30  
% 5.92/2.30  Inference rules
% 5.92/2.30  ----------------------
% 5.92/2.30  #Ref     : 0
% 5.92/2.30  #Sup     : 1287
% 5.92/2.30  #Fact    : 0
% 5.92/2.30  #Define  : 0
% 5.92/2.30  #Split   : 1
% 5.92/2.30  #Chain   : 0
% 5.92/2.30  #Close   : 0
% 5.92/2.30  
% 5.92/2.30  Ordering : KBO
% 5.92/2.30  
% 5.92/2.30  Simplification rules
% 5.92/2.30  ----------------------
% 5.92/2.30  #Subsume      : 234
% 5.92/2.30  #Demod        : 940
% 5.92/2.30  #Tautology    : 455
% 5.92/2.30  #SimpNegUnit  : 0
% 5.92/2.30  #BackRed      : 0
% 5.92/2.30  
% 5.92/2.30  #Partial instantiations: 0
% 5.92/2.30  #Strategies tried      : 1
% 5.92/2.30  
% 5.92/2.30  Timing (in seconds)
% 5.92/2.30  ----------------------
% 5.92/2.31  Preprocessing        : 0.28
% 5.92/2.31  Parsing              : 0.15
% 5.92/2.31  CNF conversion       : 0.02
% 5.92/2.31  Main loop            : 1.31
% 5.92/2.31  Inferencing          : 0.34
% 5.92/2.31  Reduction            : 0.74
% 5.92/2.31  Demodulation         : 0.67
% 5.92/2.31  BG Simplification    : 0.05
% 5.92/2.31  Subsumption          : 0.13
% 5.92/2.31  Abstraction          : 0.08
% 5.92/2.31  MUC search           : 0.00
% 5.92/2.31  Cooper               : 0.00
% 5.92/2.31  Total                : 1.61
% 5.92/2.31  Index Insertion      : 0.00
% 5.92/2.31  Index Deletion       : 0.00
% 5.92/2.31  Index Matching       : 0.00
% 5.92/2.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
