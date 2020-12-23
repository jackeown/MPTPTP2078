%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:12 EST 2020

% Result     : Theorem 15.09s
% Output     : CNFRefutation 15.09s
% Verified   : 
% Statistics : Number of formulae       :   46 (  49 expanded)
%              Number of leaves         :   23 (  26 expanded)
%              Depth                    :    9
%              Number of atoms          :   53 (  60 expanded)
%              Number of equality atoms :   18 (  21 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k8_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k8_relat_1(B,k8_relat_1(A,C)) = k8_relat_1(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => v1_relat_1(k8_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k8_relat_1(A,B)) = k3_xboole_0(k2_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_relat_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_45,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

tff(c_28,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_18,plain,(
    ! [A_14,B_15] :
      ( v1_relat_1(k8_relat_1(A_14,B_15))
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_310,plain,(
    ! [B_57,A_58] :
      ( k3_xboole_0(k2_relat_1(B_57),A_58) = k2_relat_1(k8_relat_1(A_58,B_57))
      | ~ v1_relat_1(B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_14,plain,(
    ! [B_11,A_10] : k2_tarski(B_11,A_10) = k2_tarski(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_66,plain,(
    ! [A_27,B_28] : k1_setfam_1(k2_tarski(A_27,B_28)) = k3_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_81,plain,(
    ! [B_29,A_30] : k1_setfam_1(k2_tarski(B_29,A_30)) = k3_xboole_0(A_30,B_29) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_66])).

tff(c_16,plain,(
    ! [A_12,B_13] : k1_setfam_1(k2_tarski(A_12,B_13)) = k3_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_87,plain,(
    ! [B_29,A_30] : k3_xboole_0(B_29,A_30) = k3_xboole_0(A_30,B_29) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_16])).

tff(c_152,plain,(
    ! [A_35,B_36] : k4_xboole_0(A_35,k4_xboole_0(A_35,B_36)) = k3_xboole_0(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10,plain,(
    ! [A_6,B_7] : r1_tarski(k4_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_170,plain,(
    ! [A_37,B_38] : r1_tarski(k3_xboole_0(A_37,B_38),A_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_10])).

tff(c_175,plain,(
    ! [B_29,A_30] : r1_tarski(k3_xboole_0(B_29,A_30),A_30) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_170])).

tff(c_812,plain,(
    ! [A_96,B_97] :
      ( r1_tarski(k2_relat_1(k8_relat_1(A_96,B_97)),A_96)
      | ~ v1_relat_1(B_97) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_310,c_175])).

tff(c_26,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_193,plain,(
    ! [A_41,C_42,B_43] :
      ( r1_tarski(A_41,C_42)
      | ~ r1_tarski(B_43,C_42)
      | ~ r1_tarski(A_41,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_208,plain,(
    ! [A_41] :
      ( r1_tarski(A_41,'#skF_2')
      | ~ r1_tarski(A_41,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_26,c_193])).

tff(c_503,plain,(
    ! [A_75,B_76] :
      ( k8_relat_1(A_75,B_76) = B_76
      | ~ r1_tarski(k2_relat_1(B_76),A_75)
      | ~ v1_relat_1(B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_512,plain,(
    ! [B_76] :
      ( k8_relat_1('#skF_2',B_76) = B_76
      | ~ v1_relat_1(B_76)
      | ~ r1_tarski(k2_relat_1(B_76),'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_208,c_503])).

tff(c_35945,plain,(
    ! [B_962] :
      ( k8_relat_1('#skF_2',k8_relat_1('#skF_1',B_962)) = k8_relat_1('#skF_1',B_962)
      | ~ v1_relat_1(k8_relat_1('#skF_1',B_962))
      | ~ v1_relat_1(B_962) ) ),
    inference(resolution,[status(thm)],[c_812,c_512])).

tff(c_35951,plain,(
    ! [B_963] :
      ( k8_relat_1('#skF_2',k8_relat_1('#skF_1',B_963)) = k8_relat_1('#skF_1',B_963)
      | ~ v1_relat_1(B_963) ) ),
    inference(resolution,[status(thm)],[c_18,c_35945])).

tff(c_24,plain,(
    k8_relat_1('#skF_2',k8_relat_1('#skF_1','#skF_3')) != k8_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_36020,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_35951,c_24])).

tff(c_36039,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_36020])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n011.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:22:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.09/7.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.09/7.15  
% 15.09/7.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.09/7.15  %$ r1_tarski > v1_relat_1 > k8_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 15.09/7.15  
% 15.09/7.15  %Foreground sorts:
% 15.09/7.15  
% 15.09/7.15  
% 15.09/7.15  %Background operators:
% 15.09/7.15  
% 15.09/7.15  
% 15.09/7.15  %Foreground operators:
% 15.09/7.15  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 15.09/7.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.09/7.15  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 15.09/7.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 15.09/7.15  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 15.09/7.15  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 15.09/7.15  tff('#skF_2', type, '#skF_2': $i).
% 15.09/7.15  tff('#skF_3', type, '#skF_3': $i).
% 15.09/7.15  tff('#skF_1', type, '#skF_1': $i).
% 15.09/7.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.09/7.15  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 15.09/7.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.09/7.15  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 15.09/7.15  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 15.09/7.15  
% 15.09/7.17  tff(f_66, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k8_relat_1(B, k8_relat_1(A, C)) = k8_relat_1(A, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t129_relat_1)).
% 15.09/7.17  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => v1_relat_1(k8_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 15.09/7.17  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k8_relat_1(A, B)) = k3_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t119_relat_1)).
% 15.09/7.17  tff(f_43, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 15.09/7.17  tff(f_45, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 15.09/7.17  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 15.09/7.17  tff(f_39, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 15.09/7.17  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 15.09/7.17  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_relat_1)).
% 15.09/7.17  tff(c_28, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_66])).
% 15.09/7.17  tff(c_18, plain, (![A_14, B_15]: (v1_relat_1(k8_relat_1(A_14, B_15)) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_49])).
% 15.09/7.17  tff(c_310, plain, (![B_57, A_58]: (k3_xboole_0(k2_relat_1(B_57), A_58)=k2_relat_1(k8_relat_1(A_58, B_57)) | ~v1_relat_1(B_57))), inference(cnfTransformation, [status(thm)], [f_53])).
% 15.09/7.17  tff(c_14, plain, (![B_11, A_10]: (k2_tarski(B_11, A_10)=k2_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 15.09/7.17  tff(c_66, plain, (![A_27, B_28]: (k1_setfam_1(k2_tarski(A_27, B_28))=k3_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_45])).
% 15.09/7.17  tff(c_81, plain, (![B_29, A_30]: (k1_setfam_1(k2_tarski(B_29, A_30))=k3_xboole_0(A_30, B_29))), inference(superposition, [status(thm), theory('equality')], [c_14, c_66])).
% 15.09/7.17  tff(c_16, plain, (![A_12, B_13]: (k1_setfam_1(k2_tarski(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 15.09/7.17  tff(c_87, plain, (![B_29, A_30]: (k3_xboole_0(B_29, A_30)=k3_xboole_0(A_30, B_29))), inference(superposition, [status(thm), theory('equality')], [c_81, c_16])).
% 15.09/7.17  tff(c_152, plain, (![A_35, B_36]: (k4_xboole_0(A_35, k4_xboole_0(A_35, B_36))=k3_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_41])).
% 15.09/7.17  tff(c_10, plain, (![A_6, B_7]: (r1_tarski(k4_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 15.09/7.17  tff(c_170, plain, (![A_37, B_38]: (r1_tarski(k3_xboole_0(A_37, B_38), A_37))), inference(superposition, [status(thm), theory('equality')], [c_152, c_10])).
% 15.09/7.17  tff(c_175, plain, (![B_29, A_30]: (r1_tarski(k3_xboole_0(B_29, A_30), A_30))), inference(superposition, [status(thm), theory('equality')], [c_87, c_170])).
% 15.09/7.17  tff(c_812, plain, (![A_96, B_97]: (r1_tarski(k2_relat_1(k8_relat_1(A_96, B_97)), A_96) | ~v1_relat_1(B_97))), inference(superposition, [status(thm), theory('equality')], [c_310, c_175])).
% 15.09/7.17  tff(c_26, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_66])).
% 15.09/7.17  tff(c_193, plain, (![A_41, C_42, B_43]: (r1_tarski(A_41, C_42) | ~r1_tarski(B_43, C_42) | ~r1_tarski(A_41, B_43))), inference(cnfTransformation, [status(thm)], [f_37])).
% 15.09/7.17  tff(c_208, plain, (![A_41]: (r1_tarski(A_41, '#skF_2') | ~r1_tarski(A_41, '#skF_1'))), inference(resolution, [status(thm)], [c_26, c_193])).
% 15.09/7.17  tff(c_503, plain, (![A_75, B_76]: (k8_relat_1(A_75, B_76)=B_76 | ~r1_tarski(k2_relat_1(B_76), A_75) | ~v1_relat_1(B_76))), inference(cnfTransformation, [status(thm)], [f_59])).
% 15.09/7.17  tff(c_512, plain, (![B_76]: (k8_relat_1('#skF_2', B_76)=B_76 | ~v1_relat_1(B_76) | ~r1_tarski(k2_relat_1(B_76), '#skF_1'))), inference(resolution, [status(thm)], [c_208, c_503])).
% 15.09/7.17  tff(c_35945, plain, (![B_962]: (k8_relat_1('#skF_2', k8_relat_1('#skF_1', B_962))=k8_relat_1('#skF_1', B_962) | ~v1_relat_1(k8_relat_1('#skF_1', B_962)) | ~v1_relat_1(B_962))), inference(resolution, [status(thm)], [c_812, c_512])).
% 15.09/7.17  tff(c_35951, plain, (![B_963]: (k8_relat_1('#skF_2', k8_relat_1('#skF_1', B_963))=k8_relat_1('#skF_1', B_963) | ~v1_relat_1(B_963))), inference(resolution, [status(thm)], [c_18, c_35945])).
% 15.09/7.17  tff(c_24, plain, (k8_relat_1('#skF_2', k8_relat_1('#skF_1', '#skF_3'))!=k8_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_66])).
% 15.09/7.17  tff(c_36020, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_35951, c_24])).
% 15.09/7.17  tff(c_36039, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_36020])).
% 15.09/7.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.09/7.17  
% 15.09/7.17  Inference rules
% 15.09/7.17  ----------------------
% 15.09/7.17  #Ref     : 0
% 15.09/7.17  #Sup     : 8491
% 15.09/7.17  #Fact    : 0
% 15.09/7.17  #Define  : 0
% 15.09/7.17  #Split   : 1
% 15.09/7.17  #Chain   : 0
% 15.09/7.17  #Close   : 0
% 15.09/7.17  
% 15.09/7.17  Ordering : KBO
% 15.09/7.17  
% 15.09/7.17  Simplification rules
% 15.09/7.17  ----------------------
% 15.09/7.17  #Subsume      : 952
% 15.09/7.17  #Demod        : 2180
% 15.09/7.17  #Tautology    : 1972
% 15.09/7.17  #SimpNegUnit  : 0
% 15.09/7.17  #BackRed      : 0
% 15.09/7.17  
% 15.09/7.17  #Partial instantiations: 0
% 15.09/7.17  #Strategies tried      : 1
% 15.09/7.17  
% 15.09/7.17  Timing (in seconds)
% 15.09/7.17  ----------------------
% 15.09/7.17  Preprocessing        : 0.29
% 15.09/7.17  Parsing              : 0.16
% 15.09/7.17  CNF conversion       : 0.02
% 15.09/7.17  Main loop            : 6.12
% 15.09/7.17  Inferencing          : 0.99
% 15.09/7.17  Reduction            : 2.55
% 15.09/7.17  Demodulation         : 2.26
% 15.09/7.17  BG Simplification    : 0.11
% 15.09/7.17  Subsumption          : 2.14
% 15.09/7.17  Abstraction          : 0.13
% 15.09/7.17  MUC search           : 0.00
% 15.09/7.17  Cooper               : 0.00
% 15.09/7.17  Total                : 6.44
% 15.09/7.17  Index Insertion      : 0.00
% 15.09/7.17  Index Deletion       : 0.00
% 15.09/7.17  Index Matching       : 0.00
% 15.09/7.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
