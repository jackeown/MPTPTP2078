%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:12 EST 2020

% Result     : Theorem 2.84s
% Output     : CNFRefutation 2.84s
% Verified   : 
% Statistics : Number of formulae       :   45 (  52 expanded)
%              Number of leaves         :   22 (  27 expanded)
%              Depth                    :   10
%              Number of atoms          :   71 (  93 expanded)
%              Number of equality atoms :   17 (  22 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_71,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ! [C] :
            ( v1_relat_1(C)
           => ( r1_tarski(k2_relat_1(B),k1_relat_1(k7_relat_1(C,A)))
             => k5_relat_1(B,k7_relat_1(C,A)) = k5_relat_1(B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t200_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_33,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

tff(c_20,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_22,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_18,plain,(
    r1_tarski(k2_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_12,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_17,A_16)),A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_64,plain,(
    ! [A_30,C_31,B_32] :
      ( r1_tarski(A_30,C_31)
      | ~ r1_tarski(B_32,C_31)
      | ~ r1_tarski(A_30,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_92,plain,(
    ! [A_36,A_37,B_38] :
      ( r1_tarski(A_36,A_37)
      | ~ r1_tarski(A_36,k1_relat_1(k7_relat_1(B_38,A_37)))
      | ~ v1_relat_1(B_38) ) ),
    inference(resolution,[status(thm)],[c_12,c_64])).

tff(c_102,plain,
    ( r1_tarski(k2_relat_1('#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_92])).

tff(c_109,plain,(
    r1_tarski(k2_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_102])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( k8_relat_1(A_7,B_8) = B_8
      | ~ r1_tarski(k2_relat_1(B_8),A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_149,plain,
    ( k8_relat_1('#skF_1','#skF_2') = '#skF_2'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_109,c_8])).

tff(c_154,plain,(
    k8_relat_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_149])).

tff(c_14,plain,(
    ! [A_18,B_19] :
      ( k5_relat_1(k6_relat_1(A_18),B_19) = k7_relat_1(B_19,A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_4,plain,(
    ! [A_4] : v1_relat_1(k6_relat_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [B_6,A_5] :
      ( k5_relat_1(B_6,k6_relat_1(A_5)) = k8_relat_1(A_5,B_6)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_110,plain,(
    ! [A_39,B_40,C_41] :
      ( k5_relat_1(k5_relat_1(A_39,B_40),C_41) = k5_relat_1(A_39,k5_relat_1(B_40,C_41))
      | ~ v1_relat_1(C_41)
      | ~ v1_relat_1(B_40)
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_132,plain,(
    ! [B_6,A_5,C_41] :
      ( k5_relat_1(B_6,k5_relat_1(k6_relat_1(A_5),C_41)) = k5_relat_1(k8_relat_1(A_5,B_6),C_41)
      | ~ v1_relat_1(C_41)
      | ~ v1_relat_1(k6_relat_1(A_5))
      | ~ v1_relat_1(B_6)
      | ~ v1_relat_1(B_6) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_110])).

tff(c_217,plain,(
    ! [B_52,A_53,C_54] :
      ( k5_relat_1(B_52,k5_relat_1(k6_relat_1(A_53),C_54)) = k5_relat_1(k8_relat_1(A_53,B_52),C_54)
      | ~ v1_relat_1(C_54)
      | ~ v1_relat_1(B_52) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_132])).

tff(c_694,plain,(
    ! [A_84,B_85,B_86] :
      ( k5_relat_1(k8_relat_1(A_84,B_85),B_86) = k5_relat_1(B_85,k7_relat_1(B_86,A_84))
      | ~ v1_relat_1(B_86)
      | ~ v1_relat_1(B_85)
      | ~ v1_relat_1(B_86) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_217])).

tff(c_740,plain,(
    ! [B_86] :
      ( k5_relat_1('#skF_2',k7_relat_1(B_86,'#skF_1')) = k5_relat_1('#skF_2',B_86)
      | ~ v1_relat_1(B_86)
      | ~ v1_relat_1('#skF_2')
      | ~ v1_relat_1(B_86) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_694])).

tff(c_771,plain,(
    ! [B_87] :
      ( k5_relat_1('#skF_2',k7_relat_1(B_87,'#skF_1')) = k5_relat_1('#skF_2',B_87)
      | ~ v1_relat_1(B_87) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_740])).

tff(c_16,plain,(
    k5_relat_1('#skF_2',k7_relat_1('#skF_3','#skF_1')) != k5_relat_1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_786,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_771,c_16])).

tff(c_804,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_786])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:26:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.84/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.84/1.39  
% 2.84/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.84/1.40  %$ r1_tarski > v1_relat_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.84/1.40  
% 2.84/1.40  %Foreground sorts:
% 2.84/1.40  
% 2.84/1.40  
% 2.84/1.40  %Background operators:
% 2.84/1.40  
% 2.84/1.40  
% 2.84/1.40  %Foreground operators:
% 2.84/1.40  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.84/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.84/1.40  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.84/1.40  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.84/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.84/1.40  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.84/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.84/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.84/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.84/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.84/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.84/1.40  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.84/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.84/1.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.84/1.40  
% 2.84/1.41  tff(f_71, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(k2_relat_1(B), k1_relat_1(k7_relat_1(C, A))) => (k5_relat_1(B, k7_relat_1(C, A)) = k5_relat_1(B, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t200_relat_1)).
% 2.84/1.41  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 2.84/1.41  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.84/1.41  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_relat_1)).
% 2.84/1.41  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 2.84/1.41  tff(f_33, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.84/1.41  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 2.84/1.41  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 2.84/1.41  tff(c_20, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.84/1.41  tff(c_22, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.84/1.41  tff(c_18, plain, (r1_tarski(k2_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.84/1.41  tff(c_12, plain, (![B_17, A_16]: (r1_tarski(k1_relat_1(k7_relat_1(B_17, A_16)), A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.84/1.41  tff(c_64, plain, (![A_30, C_31, B_32]: (r1_tarski(A_30, C_31) | ~r1_tarski(B_32, C_31) | ~r1_tarski(A_30, B_32))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.84/1.41  tff(c_92, plain, (![A_36, A_37, B_38]: (r1_tarski(A_36, A_37) | ~r1_tarski(A_36, k1_relat_1(k7_relat_1(B_38, A_37))) | ~v1_relat_1(B_38))), inference(resolution, [status(thm)], [c_12, c_64])).
% 2.84/1.41  tff(c_102, plain, (r1_tarski(k2_relat_1('#skF_2'), '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_18, c_92])).
% 2.84/1.41  tff(c_109, plain, (r1_tarski(k2_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_102])).
% 2.84/1.41  tff(c_8, plain, (![A_7, B_8]: (k8_relat_1(A_7, B_8)=B_8 | ~r1_tarski(k2_relat_1(B_8), A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.84/1.41  tff(c_149, plain, (k8_relat_1('#skF_1', '#skF_2')='#skF_2' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_109, c_8])).
% 2.84/1.41  tff(c_154, plain, (k8_relat_1('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_149])).
% 2.84/1.41  tff(c_14, plain, (![A_18, B_19]: (k5_relat_1(k6_relat_1(A_18), B_19)=k7_relat_1(B_19, A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.84/1.41  tff(c_4, plain, (![A_4]: (v1_relat_1(k6_relat_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.84/1.41  tff(c_6, plain, (![B_6, A_5]: (k5_relat_1(B_6, k6_relat_1(A_5))=k8_relat_1(A_5, B_6) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.84/1.41  tff(c_110, plain, (![A_39, B_40, C_41]: (k5_relat_1(k5_relat_1(A_39, B_40), C_41)=k5_relat_1(A_39, k5_relat_1(B_40, C_41)) | ~v1_relat_1(C_41) | ~v1_relat_1(B_40) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.84/1.41  tff(c_132, plain, (![B_6, A_5, C_41]: (k5_relat_1(B_6, k5_relat_1(k6_relat_1(A_5), C_41))=k5_relat_1(k8_relat_1(A_5, B_6), C_41) | ~v1_relat_1(C_41) | ~v1_relat_1(k6_relat_1(A_5)) | ~v1_relat_1(B_6) | ~v1_relat_1(B_6))), inference(superposition, [status(thm), theory('equality')], [c_6, c_110])).
% 2.84/1.41  tff(c_217, plain, (![B_52, A_53, C_54]: (k5_relat_1(B_52, k5_relat_1(k6_relat_1(A_53), C_54))=k5_relat_1(k8_relat_1(A_53, B_52), C_54) | ~v1_relat_1(C_54) | ~v1_relat_1(B_52))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_132])).
% 2.84/1.41  tff(c_694, plain, (![A_84, B_85, B_86]: (k5_relat_1(k8_relat_1(A_84, B_85), B_86)=k5_relat_1(B_85, k7_relat_1(B_86, A_84)) | ~v1_relat_1(B_86) | ~v1_relat_1(B_85) | ~v1_relat_1(B_86))), inference(superposition, [status(thm), theory('equality')], [c_14, c_217])).
% 2.84/1.41  tff(c_740, plain, (![B_86]: (k5_relat_1('#skF_2', k7_relat_1(B_86, '#skF_1'))=k5_relat_1('#skF_2', B_86) | ~v1_relat_1(B_86) | ~v1_relat_1('#skF_2') | ~v1_relat_1(B_86))), inference(superposition, [status(thm), theory('equality')], [c_154, c_694])).
% 2.84/1.41  tff(c_771, plain, (![B_87]: (k5_relat_1('#skF_2', k7_relat_1(B_87, '#skF_1'))=k5_relat_1('#skF_2', B_87) | ~v1_relat_1(B_87))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_740])).
% 2.84/1.41  tff(c_16, plain, (k5_relat_1('#skF_2', k7_relat_1('#skF_3', '#skF_1'))!=k5_relat_1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.84/1.41  tff(c_786, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_771, c_16])).
% 2.84/1.41  tff(c_804, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_786])).
% 2.84/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.84/1.41  
% 2.84/1.41  Inference rules
% 2.84/1.41  ----------------------
% 2.84/1.41  #Ref     : 0
% 2.84/1.41  #Sup     : 168
% 2.84/1.41  #Fact    : 0
% 2.84/1.41  #Define  : 0
% 2.84/1.41  #Split   : 1
% 2.84/1.41  #Chain   : 0
% 2.84/1.41  #Close   : 0
% 2.84/1.41  
% 2.84/1.41  Ordering : KBO
% 2.84/1.41  
% 2.84/1.41  Simplification rules
% 2.84/1.41  ----------------------
% 2.84/1.41  #Subsume      : 8
% 2.84/1.41  #Demod        : 101
% 2.84/1.41  #Tautology    : 48
% 2.84/1.41  #SimpNegUnit  : 0
% 2.84/1.41  #BackRed      : 0
% 2.84/1.41  
% 2.84/1.41  #Partial instantiations: 0
% 2.84/1.41  #Strategies tried      : 1
% 2.84/1.41  
% 2.84/1.41  Timing (in seconds)
% 2.84/1.41  ----------------------
% 2.84/1.41  Preprocessing        : 0.27
% 2.84/1.41  Parsing              : 0.15
% 2.84/1.41  CNF conversion       : 0.02
% 2.84/1.41  Main loop            : 0.38
% 2.84/1.41  Inferencing          : 0.16
% 2.84/1.41  Reduction            : 0.11
% 2.84/1.41  Demodulation         : 0.08
% 2.84/1.41  BG Simplification    : 0.02
% 2.84/1.41  Subsumption          : 0.07
% 2.84/1.41  Abstraction          : 0.02
% 2.84/1.41  MUC search           : 0.00
% 2.84/1.41  Cooper               : 0.00
% 2.84/1.41  Total                : 0.68
% 2.84/1.41  Index Insertion      : 0.00
% 2.84/1.41  Index Deletion       : 0.00
% 2.84/1.41  Index Matching       : 0.00
% 2.84/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
