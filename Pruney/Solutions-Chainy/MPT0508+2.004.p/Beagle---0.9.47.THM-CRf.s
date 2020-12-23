%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:54 EST 2020

% Result     : Theorem 4.08s
% Output     : CNFRefutation 4.44s
% Verified   : 
% Statistics : Number of formulae       :   49 (  68 expanded)
%              Number of leaves         :   22 (  33 expanded)
%              Depth                    :    8
%              Number of atoms          :   73 ( 132 expanded)
%              Number of equality atoms :   12 (  13 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_74,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ! [D] :
            ( v1_relat_1(D)
           => ( ( r1_tarski(C,D)
                & r1_tarski(A,B) )
             => r1_tarski(k7_relat_1(C,A),k7_relat_1(D,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_37,axiom,(
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

tff(f_49,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( r1_tarski(B,C)
           => r1_tarski(k7_relat_1(B,A),k7_relat_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_relat_1)).

tff(c_26,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_20,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_24,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_16,plain,(
    ! [B_20,A_19] :
      ( r1_tarski(k7_relat_1(B_20,A_19),B_20)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_22,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_189,plain,(
    ! [A_36,C_37,B_38] :
      ( r1_tarski(A_36,C_37)
      | ~ r1_tarski(B_38,C_37)
      | ~ r1_tarski(A_36,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_202,plain,(
    ! [A_39] :
      ( r1_tarski(A_39,'#skF_4')
      | ~ r1_tarski(A_39,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_22,c_189])).

tff(c_206,plain,(
    ! [A_19] :
      ( r1_tarski(k7_relat_1('#skF_3',A_19),'#skF_4')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_16,c_202])).

tff(c_210,plain,(
    ! [A_40] : r1_tarski(k7_relat_1('#skF_3',A_40),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_206])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( k3_xboole_0(A_4,B_5) = A_4
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_273,plain,(
    ! [A_48] : k3_xboole_0(k7_relat_1('#skF_3',A_48),'#skF_4') = k7_relat_1('#skF_3',A_48) ),
    inference(resolution,[status(thm)],[c_210,c_4])).

tff(c_6,plain,(
    ! [B_7,A_6] : k2_tarski(B_7,A_6) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_91,plain,(
    ! [A_30,B_31] : k1_setfam_1(k2_tarski(A_30,B_31)) = k3_xboole_0(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_106,plain,(
    ! [B_32,A_33] : k1_setfam_1(k2_tarski(B_32,A_33)) = k3_xboole_0(A_33,B_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_91])).

tff(c_8,plain,(
    ! [A_8,B_9] : k1_setfam_1(k2_tarski(A_8,B_9)) = k3_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_129,plain,(
    ! [B_34,A_35] : k3_xboole_0(B_34,A_35) = k3_xboole_0(A_35,B_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_8])).

tff(c_10,plain,(
    ! [A_10,B_11] :
      ( v1_relat_1(k3_xboole_0(A_10,B_11))
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_150,plain,(
    ! [B_34,A_35] :
      ( v1_relat_1(k3_xboole_0(B_34,A_35))
      | ~ v1_relat_1(A_35) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_10])).

tff(c_279,plain,(
    ! [A_48] :
      ( v1_relat_1(k7_relat_1('#skF_3',A_48))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_273,c_150])).

tff(c_300,plain,(
    ! [A_48] : v1_relat_1(k7_relat_1('#skF_3',A_48)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_279])).

tff(c_209,plain,(
    ! [A_19] : r1_tarski(k7_relat_1('#skF_3',A_19),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_206])).

tff(c_12,plain,(
    ! [C_14,A_12,B_13] :
      ( k7_relat_1(k7_relat_1(C_14,A_12),B_13) = k7_relat_1(C_14,A_12)
      | ~ r1_tarski(A_12,B_13)
      | ~ v1_relat_1(C_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_344,plain,(
    ! [B_55,A_56,C_57] :
      ( r1_tarski(k7_relat_1(B_55,A_56),k7_relat_1(C_57,A_56))
      | ~ r1_tarski(B_55,C_57)
      | ~ v1_relat_1(C_57)
      | ~ v1_relat_1(B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2323,plain,(
    ! [C_137,A_138,C_139,B_140] :
      ( r1_tarski(k7_relat_1(C_137,A_138),k7_relat_1(C_139,B_140))
      | ~ r1_tarski(k7_relat_1(C_137,A_138),C_139)
      | ~ v1_relat_1(C_139)
      | ~ v1_relat_1(k7_relat_1(C_137,A_138))
      | ~ r1_tarski(A_138,B_140)
      | ~ v1_relat_1(C_137) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_344])).

tff(c_18,plain,(
    ~ r1_tarski(k7_relat_1('#skF_3','#skF_1'),k7_relat_1('#skF_4','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2375,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3','#skF_1'),'#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2323,c_18])).

tff(c_2435,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_20,c_300,c_24,c_209,c_2375])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:40:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.08/1.75  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.08/1.76  
% 4.08/1.76  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.08/1.76  %$ r1_tarski > v1_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.08/1.76  
% 4.08/1.76  %Foreground sorts:
% 4.08/1.76  
% 4.08/1.76  
% 4.08/1.76  %Background operators:
% 4.08/1.76  
% 4.08/1.76  
% 4.08/1.76  %Foreground operators:
% 4.08/1.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.08/1.76  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.08/1.76  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.08/1.76  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.08/1.76  tff('#skF_2', type, '#skF_2': $i).
% 4.08/1.76  tff('#skF_3', type, '#skF_3': $i).
% 4.08/1.76  tff('#skF_1', type, '#skF_1': $i).
% 4.08/1.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.08/1.76  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.08/1.76  tff('#skF_4', type, '#skF_4': $i).
% 4.08/1.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.08/1.76  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.08/1.76  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.08/1.76  
% 4.44/1.77  tff(f_74, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(C, D) & r1_tarski(A, B)) => r1_tarski(k7_relat_1(C, A), k7_relat_1(D, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_relat_1)).
% 4.44/1.77  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 4.44/1.77  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 4.44/1.77  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.44/1.77  tff(f_37, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 4.44/1.77  tff(f_39, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 4.44/1.77  tff(f_43, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_relat_1)).
% 4.44/1.77  tff(f_49, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t102_relat_1)).
% 4.44/1.77  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(B, C) => r1_tarski(k7_relat_1(B, A), k7_relat_1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t105_relat_1)).
% 4.44/1.77  tff(c_26, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.44/1.77  tff(c_20, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.44/1.77  tff(c_24, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.44/1.77  tff(c_16, plain, (![B_20, A_19]: (r1_tarski(k7_relat_1(B_20, A_19), B_20) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.44/1.77  tff(c_22, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.44/1.77  tff(c_189, plain, (![A_36, C_37, B_38]: (r1_tarski(A_36, C_37) | ~r1_tarski(B_38, C_37) | ~r1_tarski(A_36, B_38))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.44/1.77  tff(c_202, plain, (![A_39]: (r1_tarski(A_39, '#skF_4') | ~r1_tarski(A_39, '#skF_3'))), inference(resolution, [status(thm)], [c_22, c_189])).
% 4.44/1.77  tff(c_206, plain, (![A_19]: (r1_tarski(k7_relat_1('#skF_3', A_19), '#skF_4') | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_16, c_202])).
% 4.44/1.77  tff(c_210, plain, (![A_40]: (r1_tarski(k7_relat_1('#skF_3', A_40), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_206])).
% 4.44/1.77  tff(c_4, plain, (![A_4, B_5]: (k3_xboole_0(A_4, B_5)=A_4 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.44/1.77  tff(c_273, plain, (![A_48]: (k3_xboole_0(k7_relat_1('#skF_3', A_48), '#skF_4')=k7_relat_1('#skF_3', A_48))), inference(resolution, [status(thm)], [c_210, c_4])).
% 4.44/1.77  tff(c_6, plain, (![B_7, A_6]: (k2_tarski(B_7, A_6)=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.44/1.77  tff(c_91, plain, (![A_30, B_31]: (k1_setfam_1(k2_tarski(A_30, B_31))=k3_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.44/1.77  tff(c_106, plain, (![B_32, A_33]: (k1_setfam_1(k2_tarski(B_32, A_33))=k3_xboole_0(A_33, B_32))), inference(superposition, [status(thm), theory('equality')], [c_6, c_91])).
% 4.44/1.77  tff(c_8, plain, (![A_8, B_9]: (k1_setfam_1(k2_tarski(A_8, B_9))=k3_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.44/1.77  tff(c_129, plain, (![B_34, A_35]: (k3_xboole_0(B_34, A_35)=k3_xboole_0(A_35, B_34))), inference(superposition, [status(thm), theory('equality')], [c_106, c_8])).
% 4.44/1.77  tff(c_10, plain, (![A_10, B_11]: (v1_relat_1(k3_xboole_0(A_10, B_11)) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.44/1.77  tff(c_150, plain, (![B_34, A_35]: (v1_relat_1(k3_xboole_0(B_34, A_35)) | ~v1_relat_1(A_35))), inference(superposition, [status(thm), theory('equality')], [c_129, c_10])).
% 4.44/1.77  tff(c_279, plain, (![A_48]: (v1_relat_1(k7_relat_1('#skF_3', A_48)) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_273, c_150])).
% 4.44/1.77  tff(c_300, plain, (![A_48]: (v1_relat_1(k7_relat_1('#skF_3', A_48)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_279])).
% 4.44/1.77  tff(c_209, plain, (![A_19]: (r1_tarski(k7_relat_1('#skF_3', A_19), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_206])).
% 4.44/1.77  tff(c_12, plain, (![C_14, A_12, B_13]: (k7_relat_1(k7_relat_1(C_14, A_12), B_13)=k7_relat_1(C_14, A_12) | ~r1_tarski(A_12, B_13) | ~v1_relat_1(C_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.44/1.77  tff(c_344, plain, (![B_55, A_56, C_57]: (r1_tarski(k7_relat_1(B_55, A_56), k7_relat_1(C_57, A_56)) | ~r1_tarski(B_55, C_57) | ~v1_relat_1(C_57) | ~v1_relat_1(B_55))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.44/1.77  tff(c_2323, plain, (![C_137, A_138, C_139, B_140]: (r1_tarski(k7_relat_1(C_137, A_138), k7_relat_1(C_139, B_140)) | ~r1_tarski(k7_relat_1(C_137, A_138), C_139) | ~v1_relat_1(C_139) | ~v1_relat_1(k7_relat_1(C_137, A_138)) | ~r1_tarski(A_138, B_140) | ~v1_relat_1(C_137))), inference(superposition, [status(thm), theory('equality')], [c_12, c_344])).
% 4.44/1.77  tff(c_18, plain, (~r1_tarski(k7_relat_1('#skF_3', '#skF_1'), k7_relat_1('#skF_4', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.44/1.77  tff(c_2375, plain, (~r1_tarski(k7_relat_1('#skF_3', '#skF_1'), '#skF_4') | ~v1_relat_1('#skF_4') | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2323, c_18])).
% 4.44/1.77  tff(c_2435, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_20, c_300, c_24, c_209, c_2375])).
% 4.44/1.77  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.44/1.77  
% 4.44/1.77  Inference rules
% 4.44/1.77  ----------------------
% 4.44/1.77  #Ref     : 0
% 4.44/1.77  #Sup     : 557
% 4.44/1.77  #Fact    : 0
% 4.44/1.77  #Define  : 0
% 4.44/1.77  #Split   : 5
% 4.44/1.77  #Chain   : 0
% 4.44/1.77  #Close   : 0
% 4.44/1.77  
% 4.44/1.77  Ordering : KBO
% 4.44/1.77  
% 4.44/1.77  Simplification rules
% 4.44/1.77  ----------------------
% 4.44/1.77  #Subsume      : 78
% 4.44/1.77  #Demod        : 331
% 4.44/1.77  #Tautology    : 219
% 4.44/1.77  #SimpNegUnit  : 0
% 4.44/1.77  #BackRed      : 0
% 4.44/1.77  
% 4.44/1.77  #Partial instantiations: 0
% 4.44/1.77  #Strategies tried      : 1
% 4.44/1.77  
% 4.44/1.77  Timing (in seconds)
% 4.44/1.77  ----------------------
% 4.44/1.78  Preprocessing        : 0.30
% 4.44/1.78  Parsing              : 0.17
% 4.44/1.78  CNF conversion       : 0.02
% 4.44/1.78  Main loop            : 0.68
% 4.44/1.78  Inferencing          : 0.23
% 4.44/1.78  Reduction            : 0.22
% 4.44/1.78  Demodulation         : 0.17
% 4.44/1.78  BG Simplification    : 0.03
% 4.44/1.78  Subsumption          : 0.15
% 4.44/1.78  Abstraction          : 0.04
% 4.44/1.78  MUC search           : 0.00
% 4.44/1.78  Cooper               : 0.00
% 4.44/1.78  Total                : 1.00
% 4.44/1.78  Index Insertion      : 0.00
% 4.44/1.78  Index Deletion       : 0.00
% 4.44/1.78  Index Matching       : 0.00
% 4.44/1.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
