%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:47 EST 2020

% Result     : Theorem 1.94s
% Output     : CNFRefutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 118 expanded)
%              Number of leaves         :   20 (  50 expanded)
%              Depth                    :   10
%              Number of atoms          :   65 ( 167 expanded)
%              Number of equality atoms :    8 (  56 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_66,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ! [C] :
                ( v1_relat_1(C)
               => r1_tarski(k5_relat_1(A,k3_xboole_0(B,C)),k3_xboole_0(k5_relat_1(A,B),k5_relat_1(A,C))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relat_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_39,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( r1_tarski(A,B)
               => r1_tarski(k5_relat_1(C,A),k5_relat_1(C,B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_relat_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_20,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_6,plain,(
    ! [B_7,A_6] : k2_tarski(B_7,A_6) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_58,plain,(
    ! [A_31,B_32] : k1_setfam_1(k2_tarski(A_31,B_32)) = k3_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_82,plain,(
    ! [B_35,A_36] : k1_setfam_1(k2_tarski(B_35,A_36)) = k3_xboole_0(A_36,B_35) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_58])).

tff(c_10,plain,(
    ! [A_10,B_11] : k1_setfam_1(k2_tarski(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_106,plain,(
    ! [B_37,A_38] : k3_xboole_0(B_37,A_38) = k3_xboole_0(A_38,B_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_10])).

tff(c_12,plain,(
    ! [A_12,B_13] :
      ( v1_relat_1(k3_xboole_0(A_12,B_13))
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_124,plain,(
    ! [A_38,B_37] :
      ( v1_relat_1(k3_xboole_0(A_38,B_37))
      | ~ v1_relat_1(B_37) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_12])).

tff(c_22,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_127,plain,(
    ! [B_37,A_38] : r1_tarski(k3_xboole_0(B_37,A_38),A_38) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_2])).

tff(c_200,plain,(
    ! [C_49,A_50,B_51] :
      ( r1_tarski(k5_relat_1(C_49,A_50),k5_relat_1(C_49,B_51))
      | ~ r1_tarski(A_50,B_51)
      | ~ v1_relat_1(C_49)
      | ~ v1_relat_1(B_51)
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_18,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_181,plain,(
    ! [C_46,A_47,B_48] :
      ( r1_tarski(k5_relat_1(C_46,A_47),k5_relat_1(C_46,B_48))
      | ~ r1_tarski(A_47,B_48)
      | ~ v1_relat_1(C_46)
      | ~ v1_relat_1(B_48)
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] :
      ( r1_tarski(A_3,k3_xboole_0(B_4,C_5))
      | ~ r1_tarski(A_3,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_88,plain,(
    ! [B_35,A_36] : k3_xboole_0(B_35,A_36) = k3_xboole_0(A_36,B_35) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_10])).

tff(c_16,plain,(
    ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k3_xboole_0(k5_relat_1('#skF_1','#skF_2'),k5_relat_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_105,plain,(
    ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k3_xboole_0(k5_relat_1('#skF_1','#skF_3'),k5_relat_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_88,c_16])).

tff(c_179,plain,
    ( ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k5_relat_1('#skF_1','#skF_2'))
    | ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k5_relat_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_4,c_105])).

tff(c_180,plain,(
    ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k5_relat_1('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_179])).

tff(c_184,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_2'),'#skF_3')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_181,c_180])).

tff(c_187,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_22,c_2,c_184])).

tff(c_190,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_124,c_187])).

tff(c_197,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_190])).

tff(c_198,plain,(
    ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k5_relat_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_179])).

tff(c_203,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_2'),'#skF_2')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_200,c_198])).

tff(c_206,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_22,c_127,c_203])).

tff(c_209,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_124,c_206])).

tff(c_216,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_209])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n012.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:15:07 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.94/1.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.20  
% 1.94/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.20  %$ r1_tarski > v1_relat_1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 1.94/1.20  
% 1.94/1.20  %Foreground sorts:
% 1.94/1.20  
% 1.94/1.20  
% 1.94/1.20  %Background operators:
% 1.94/1.20  
% 1.94/1.20  
% 1.94/1.20  %Foreground operators:
% 1.94/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.94/1.20  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.94/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.94/1.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.94/1.20  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.94/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.94/1.20  tff('#skF_3', type, '#skF_3': $i).
% 1.94/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.94/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.94/1.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.94/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.94/1.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.94/1.20  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.94/1.20  
% 1.94/1.21  tff(f_66, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => r1_tarski(k5_relat_1(A, k3_xboole_0(B, C)), k3_xboole_0(k5_relat_1(A, B), k5_relat_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_relat_1)).
% 1.94/1.21  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 1.94/1.21  tff(f_39, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 1.94/1.21  tff(f_43, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_relat_1)).
% 1.94/1.21  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.94/1.21  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k5_relat_1(C, A), k5_relat_1(C, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_relat_1)).
% 1.94/1.21  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 1.94/1.21  tff(c_20, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.94/1.21  tff(c_6, plain, (![B_7, A_6]: (k2_tarski(B_7, A_6)=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.94/1.21  tff(c_58, plain, (![A_31, B_32]: (k1_setfam_1(k2_tarski(A_31, B_32))=k3_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.94/1.21  tff(c_82, plain, (![B_35, A_36]: (k1_setfam_1(k2_tarski(B_35, A_36))=k3_xboole_0(A_36, B_35))), inference(superposition, [status(thm), theory('equality')], [c_6, c_58])).
% 1.94/1.21  tff(c_10, plain, (![A_10, B_11]: (k1_setfam_1(k2_tarski(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.94/1.21  tff(c_106, plain, (![B_37, A_38]: (k3_xboole_0(B_37, A_38)=k3_xboole_0(A_38, B_37))), inference(superposition, [status(thm), theory('equality')], [c_82, c_10])).
% 1.94/1.21  tff(c_12, plain, (![A_12, B_13]: (v1_relat_1(k3_xboole_0(A_12, B_13)) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.94/1.21  tff(c_124, plain, (![A_38, B_37]: (v1_relat_1(k3_xboole_0(A_38, B_37)) | ~v1_relat_1(B_37))), inference(superposition, [status(thm), theory('equality')], [c_106, c_12])).
% 1.94/1.21  tff(c_22, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.94/1.21  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.94/1.21  tff(c_127, plain, (![B_37, A_38]: (r1_tarski(k3_xboole_0(B_37, A_38), A_38))), inference(superposition, [status(thm), theory('equality')], [c_106, c_2])).
% 1.94/1.21  tff(c_200, plain, (![C_49, A_50, B_51]: (r1_tarski(k5_relat_1(C_49, A_50), k5_relat_1(C_49, B_51)) | ~r1_tarski(A_50, B_51) | ~v1_relat_1(C_49) | ~v1_relat_1(B_51) | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.94/1.21  tff(c_18, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.94/1.21  tff(c_181, plain, (![C_46, A_47, B_48]: (r1_tarski(k5_relat_1(C_46, A_47), k5_relat_1(C_46, B_48)) | ~r1_tarski(A_47, B_48) | ~v1_relat_1(C_46) | ~v1_relat_1(B_48) | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.94/1.21  tff(c_4, plain, (![A_3, B_4, C_5]: (r1_tarski(A_3, k3_xboole_0(B_4, C_5)) | ~r1_tarski(A_3, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.94/1.21  tff(c_88, plain, (![B_35, A_36]: (k3_xboole_0(B_35, A_36)=k3_xboole_0(A_36, B_35))), inference(superposition, [status(thm), theory('equality')], [c_82, c_10])).
% 1.94/1.21  tff(c_16, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k3_xboole_0(k5_relat_1('#skF_1', '#skF_2'), k5_relat_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.94/1.21  tff(c_105, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k3_xboole_0(k5_relat_1('#skF_1', '#skF_3'), k5_relat_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_88, c_16])).
% 1.94/1.21  tff(c_179, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k5_relat_1('#skF_1', '#skF_2')) | ~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k5_relat_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_4, c_105])).
% 1.94/1.21  tff(c_180, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k5_relat_1('#skF_1', '#skF_3'))), inference(splitLeft, [status(thm)], [c_179])).
% 1.94/1.21  tff(c_184, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), '#skF_3') | ~v1_relat_1('#skF_1') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_181, c_180])).
% 1.94/1.21  tff(c_187, plain, (~v1_relat_1(k3_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_22, c_2, c_184])).
% 1.94/1.21  tff(c_190, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_124, c_187])).
% 1.94/1.21  tff(c_197, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_190])).
% 1.94/1.21  tff(c_198, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k5_relat_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_179])).
% 1.94/1.21  tff(c_203, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), '#skF_2') | ~v1_relat_1('#skF_1') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_200, c_198])).
% 1.94/1.21  tff(c_206, plain, (~v1_relat_1(k3_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_22, c_127, c_203])).
% 1.94/1.21  tff(c_209, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_124, c_206])).
% 1.94/1.21  tff(c_216, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_209])).
% 1.94/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.21  
% 1.94/1.21  Inference rules
% 1.94/1.21  ----------------------
% 1.94/1.21  #Ref     : 0
% 1.94/1.21  #Sup     : 45
% 1.94/1.21  #Fact    : 0
% 1.94/1.21  #Define  : 0
% 1.94/1.21  #Split   : 1
% 1.94/1.21  #Chain   : 0
% 1.94/1.21  #Close   : 0
% 1.94/1.21  
% 1.94/1.21  Ordering : KBO
% 1.94/1.21  
% 1.94/1.21  Simplification rules
% 1.94/1.21  ----------------------
% 1.94/1.21  #Subsume      : 6
% 1.94/1.21  #Demod        : 16
% 1.94/1.21  #Tautology    : 28
% 1.94/1.21  #SimpNegUnit  : 0
% 1.94/1.21  #BackRed      : 1
% 1.94/1.21  
% 1.94/1.21  #Partial instantiations: 0
% 1.94/1.21  #Strategies tried      : 1
% 1.94/1.21  
% 1.94/1.21  Timing (in seconds)
% 1.94/1.21  ----------------------
% 1.94/1.21  Preprocessing        : 0.28
% 1.94/1.21  Parsing              : 0.15
% 1.94/1.21  CNF conversion       : 0.02
% 1.94/1.21  Main loop            : 0.16
% 1.94/1.21  Inferencing          : 0.06
% 1.94/1.21  Reduction            : 0.06
% 1.94/1.21  Demodulation         : 0.05
% 1.94/1.21  BG Simplification    : 0.01
% 1.94/1.21  Subsumption          : 0.03
% 1.94/1.21  Abstraction          : 0.01
% 1.94/1.21  MUC search           : 0.00
% 1.94/1.22  Cooper               : 0.00
% 1.94/1.22  Total                : 0.48
% 1.94/1.22  Index Insertion      : 0.00
% 1.94/1.22  Index Deletion       : 0.00
% 1.94/1.22  Index Matching       : 0.00
% 1.94/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
