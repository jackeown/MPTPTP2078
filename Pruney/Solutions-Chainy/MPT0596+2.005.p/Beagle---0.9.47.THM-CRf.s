%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:11 EST 2020

% Result     : Theorem 7.19s
% Output     : CNFRefutation 7.19s
% Verified   : 
% Statistics : Number of formulae       :   49 (  60 expanded)
%              Number of leaves         :   23 (  30 expanded)
%              Depth                    :   12
%              Number of atoms          :   82 ( 110 expanded)
%              Number of equality atoms :   20 (  27 expanded)
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

tff(f_78,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ! [C] :
            ( v1_relat_1(C)
           => ( r1_tarski(k2_relat_1(B),k1_relat_1(k7_relat_1(C,A)))
             => k5_relat_1(B,k7_relat_1(C,A)) = k5_relat_1(B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t200_relat_1)).

tff(f_33,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_64,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

tff(c_24,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_26,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_22,plain,(
    r1_tarski(k2_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_4,plain,(
    ! [A_4] : v1_relat_1(k6_relat_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_14,plain,(
    ! [A_19] : k1_relat_1(k6_relat_1(A_19)) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_18,plain,(
    ! [A_20,B_21] :
      ( k5_relat_1(k6_relat_1(A_20),B_21) = k7_relat_1(B_21,A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_115,plain,(
    ! [A_38,B_39] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_38,B_39)),k1_relat_1(A_38))
      | ~ v1_relat_1(B_39)
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_123,plain,(
    ! [B_21,A_20] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_21,A_20)),k1_relat_1(k6_relat_1(A_20)))
      | ~ v1_relat_1(B_21)
      | ~ v1_relat_1(k6_relat_1(A_20))
      | ~ v1_relat_1(B_21) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_115])).

tff(c_134,plain,(
    ! [B_40,A_41] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_40,A_41)),A_41)
      | ~ v1_relat_1(B_40) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_14,c_123])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_357,plain,(
    ! [A_61,A_62,B_63] :
      ( r1_tarski(A_61,A_62)
      | ~ r1_tarski(A_61,k1_relat_1(k7_relat_1(B_63,A_62)))
      | ~ v1_relat_1(B_63) ) ),
    inference(resolution,[status(thm)],[c_134,c_2])).

tff(c_386,plain,
    ( r1_tarski(k2_relat_1('#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_357])).

tff(c_399,plain,(
    r1_tarski(k2_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_386])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( k8_relat_1(A_7,B_8) = B_8
      | ~ r1_tarski(k2_relat_1(B_8),A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_406,plain,
    ( k8_relat_1('#skF_1','#skF_2') = '#skF_2'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_399,c_8])).

tff(c_415,plain,(
    k8_relat_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_406])).

tff(c_6,plain,(
    ! [B_6,A_5] :
      ( k5_relat_1(B_6,k6_relat_1(A_5)) = k8_relat_1(A_5,B_6)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_234,plain,(
    ! [A_52,B_53,C_54] :
      ( k5_relat_1(k5_relat_1(A_52,B_53),C_54) = k5_relat_1(A_52,k5_relat_1(B_53,C_54))
      | ~ v1_relat_1(C_54)
      | ~ v1_relat_1(B_53)
      | ~ v1_relat_1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_256,plain,(
    ! [B_6,A_5,C_54] :
      ( k5_relat_1(B_6,k5_relat_1(k6_relat_1(A_5),C_54)) = k5_relat_1(k8_relat_1(A_5,B_6),C_54)
      | ~ v1_relat_1(C_54)
      | ~ v1_relat_1(k6_relat_1(A_5))
      | ~ v1_relat_1(B_6)
      | ~ v1_relat_1(B_6) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_234])).

tff(c_697,plain,(
    ! [B_81,A_82,C_83] :
      ( k5_relat_1(B_81,k5_relat_1(k6_relat_1(A_82),C_83)) = k5_relat_1(k8_relat_1(A_82,B_81),C_83)
      | ~ v1_relat_1(C_83)
      | ~ v1_relat_1(B_81) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_256])).

tff(c_7022,plain,(
    ! [A_249,B_250,B_251] :
      ( k5_relat_1(k8_relat_1(A_249,B_250),B_251) = k5_relat_1(B_250,k7_relat_1(B_251,A_249))
      | ~ v1_relat_1(B_251)
      | ~ v1_relat_1(B_250)
      | ~ v1_relat_1(B_251) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_697])).

tff(c_7119,plain,(
    ! [B_251] :
      ( k5_relat_1('#skF_2',k7_relat_1(B_251,'#skF_1')) = k5_relat_1('#skF_2',B_251)
      | ~ v1_relat_1(B_251)
      | ~ v1_relat_1('#skF_2')
      | ~ v1_relat_1(B_251) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_415,c_7022])).

tff(c_7165,plain,(
    ! [B_252] :
      ( k5_relat_1('#skF_2',k7_relat_1(B_252,'#skF_1')) = k5_relat_1('#skF_2',B_252)
      | ~ v1_relat_1(B_252) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_7119])).

tff(c_20,plain,(
    k5_relat_1('#skF_2',k7_relat_1('#skF_3','#skF_1')) != k5_relat_1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_7204,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_7165,c_20])).

tff(c_7246,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_7204])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:34:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.19/2.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.19/2.48  
% 7.19/2.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.19/2.48  %$ r1_tarski > v1_relat_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 7.19/2.48  
% 7.19/2.48  %Foreground sorts:
% 7.19/2.48  
% 7.19/2.48  
% 7.19/2.48  %Background operators:
% 7.19/2.48  
% 7.19/2.48  
% 7.19/2.48  %Foreground operators:
% 7.19/2.48  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 7.19/2.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.19/2.48  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 7.19/2.48  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 7.19/2.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.19/2.48  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.19/2.48  tff('#skF_2', type, '#skF_2': $i).
% 7.19/2.48  tff('#skF_3', type, '#skF_3': $i).
% 7.19/2.48  tff('#skF_1', type, '#skF_1': $i).
% 7.19/2.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.19/2.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.19/2.48  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.19/2.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.19/2.48  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.19/2.48  
% 7.19/2.49  tff(f_78, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(k2_relat_1(B), k1_relat_1(k7_relat_1(C, A))) => (k5_relat_1(B, k7_relat_1(C, A)) = k5_relat_1(B, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t200_relat_1)).
% 7.19/2.49  tff(f_33, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 7.19/2.49  tff(f_64, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 7.19/2.49  tff(f_68, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 7.19/2.49  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_relat_1)).
% 7.19/2.49  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 7.19/2.49  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_relat_1)).
% 7.19/2.49  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_relat_1)).
% 7.19/2.49  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 7.19/2.49  tff(c_24, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.19/2.49  tff(c_26, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.19/2.49  tff(c_22, plain, (r1_tarski(k2_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.19/2.49  tff(c_4, plain, (![A_4]: (v1_relat_1(k6_relat_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.19/2.49  tff(c_14, plain, (![A_19]: (k1_relat_1(k6_relat_1(A_19))=A_19)), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.19/2.49  tff(c_18, plain, (![A_20, B_21]: (k5_relat_1(k6_relat_1(A_20), B_21)=k7_relat_1(B_21, A_20) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.19/2.49  tff(c_115, plain, (![A_38, B_39]: (r1_tarski(k1_relat_1(k5_relat_1(A_38, B_39)), k1_relat_1(A_38)) | ~v1_relat_1(B_39) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.19/2.49  tff(c_123, plain, (![B_21, A_20]: (r1_tarski(k1_relat_1(k7_relat_1(B_21, A_20)), k1_relat_1(k6_relat_1(A_20))) | ~v1_relat_1(B_21) | ~v1_relat_1(k6_relat_1(A_20)) | ~v1_relat_1(B_21))), inference(superposition, [status(thm), theory('equality')], [c_18, c_115])).
% 7.19/2.49  tff(c_134, plain, (![B_40, A_41]: (r1_tarski(k1_relat_1(k7_relat_1(B_40, A_41)), A_41) | ~v1_relat_1(B_40))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_14, c_123])).
% 7.19/2.49  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.19/2.49  tff(c_357, plain, (![A_61, A_62, B_63]: (r1_tarski(A_61, A_62) | ~r1_tarski(A_61, k1_relat_1(k7_relat_1(B_63, A_62))) | ~v1_relat_1(B_63))), inference(resolution, [status(thm)], [c_134, c_2])).
% 7.19/2.49  tff(c_386, plain, (r1_tarski(k2_relat_1('#skF_2'), '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_22, c_357])).
% 7.19/2.49  tff(c_399, plain, (r1_tarski(k2_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_386])).
% 7.19/2.49  tff(c_8, plain, (![A_7, B_8]: (k8_relat_1(A_7, B_8)=B_8 | ~r1_tarski(k2_relat_1(B_8), A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.19/2.49  tff(c_406, plain, (k8_relat_1('#skF_1', '#skF_2')='#skF_2' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_399, c_8])).
% 7.19/2.49  tff(c_415, plain, (k8_relat_1('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_406])).
% 7.19/2.49  tff(c_6, plain, (![B_6, A_5]: (k5_relat_1(B_6, k6_relat_1(A_5))=k8_relat_1(A_5, B_6) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.19/2.49  tff(c_234, plain, (![A_52, B_53, C_54]: (k5_relat_1(k5_relat_1(A_52, B_53), C_54)=k5_relat_1(A_52, k5_relat_1(B_53, C_54)) | ~v1_relat_1(C_54) | ~v1_relat_1(B_53) | ~v1_relat_1(A_52))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.19/2.49  tff(c_256, plain, (![B_6, A_5, C_54]: (k5_relat_1(B_6, k5_relat_1(k6_relat_1(A_5), C_54))=k5_relat_1(k8_relat_1(A_5, B_6), C_54) | ~v1_relat_1(C_54) | ~v1_relat_1(k6_relat_1(A_5)) | ~v1_relat_1(B_6) | ~v1_relat_1(B_6))), inference(superposition, [status(thm), theory('equality')], [c_6, c_234])).
% 7.19/2.49  tff(c_697, plain, (![B_81, A_82, C_83]: (k5_relat_1(B_81, k5_relat_1(k6_relat_1(A_82), C_83))=k5_relat_1(k8_relat_1(A_82, B_81), C_83) | ~v1_relat_1(C_83) | ~v1_relat_1(B_81))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_256])).
% 7.19/2.49  tff(c_7022, plain, (![A_249, B_250, B_251]: (k5_relat_1(k8_relat_1(A_249, B_250), B_251)=k5_relat_1(B_250, k7_relat_1(B_251, A_249)) | ~v1_relat_1(B_251) | ~v1_relat_1(B_250) | ~v1_relat_1(B_251))), inference(superposition, [status(thm), theory('equality')], [c_18, c_697])).
% 7.19/2.49  tff(c_7119, plain, (![B_251]: (k5_relat_1('#skF_2', k7_relat_1(B_251, '#skF_1'))=k5_relat_1('#skF_2', B_251) | ~v1_relat_1(B_251) | ~v1_relat_1('#skF_2') | ~v1_relat_1(B_251))), inference(superposition, [status(thm), theory('equality')], [c_415, c_7022])).
% 7.19/2.49  tff(c_7165, plain, (![B_252]: (k5_relat_1('#skF_2', k7_relat_1(B_252, '#skF_1'))=k5_relat_1('#skF_2', B_252) | ~v1_relat_1(B_252))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_7119])).
% 7.19/2.49  tff(c_20, plain, (k5_relat_1('#skF_2', k7_relat_1('#skF_3', '#skF_1'))!=k5_relat_1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.19/2.49  tff(c_7204, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_7165, c_20])).
% 7.19/2.49  tff(c_7246, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_7204])).
% 7.19/2.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.19/2.49  
% 7.19/2.49  Inference rules
% 7.19/2.49  ----------------------
% 7.19/2.49  #Ref     : 0
% 7.19/2.49  #Sup     : 1566
% 7.19/2.49  #Fact    : 0
% 7.19/2.49  #Define  : 0
% 7.19/2.49  #Split   : 6
% 7.19/2.49  #Chain   : 0
% 7.19/2.49  #Close   : 0
% 7.19/2.49  
% 7.19/2.49  Ordering : KBO
% 7.19/2.49  
% 7.19/2.49  Simplification rules
% 7.19/2.49  ----------------------
% 7.19/2.49  #Subsume      : 250
% 7.19/2.49  #Demod        : 1159
% 7.19/2.49  #Tautology    : 339
% 7.19/2.49  #SimpNegUnit  : 0
% 7.19/2.49  #BackRed      : 6
% 7.19/2.49  
% 7.19/2.49  #Partial instantiations: 0
% 7.19/2.49  #Strategies tried      : 1
% 7.19/2.49  
% 7.19/2.49  Timing (in seconds)
% 7.19/2.49  ----------------------
% 7.36/2.49  Preprocessing        : 0.30
% 7.36/2.49  Parsing              : 0.18
% 7.36/2.49  CNF conversion       : 0.02
% 7.36/2.49  Main loop            : 1.39
% 7.36/2.49  Inferencing          : 0.45
% 7.36/2.49  Reduction            : 0.49
% 7.36/2.49  Demodulation         : 0.37
% 7.36/2.50  BG Simplification    : 0.05
% 7.36/2.50  Subsumption          : 0.31
% 7.36/2.50  Abstraction          : 0.06
% 7.36/2.50  MUC search           : 0.00
% 7.36/2.50  Cooper               : 0.00
% 7.36/2.50  Total                : 1.72
% 7.36/2.50  Index Insertion      : 0.00
% 7.36/2.50  Index Deletion       : 0.00
% 7.36/2.50  Index Matching       : 0.00
% 7.36/2.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
