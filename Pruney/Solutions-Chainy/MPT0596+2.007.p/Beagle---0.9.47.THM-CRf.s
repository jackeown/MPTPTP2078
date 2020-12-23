%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:12 EST 2020

% Result     : Theorem 2.86s
% Output     : CNFRefutation 3.19s
% Verified   : 
% Statistics : Number of formulae       :   40 (  51 expanded)
%              Number of leaves         :   21 (  28 expanded)
%              Depth                    :    9
%              Number of atoms          :   58 (  90 expanded)
%              Number of equality atoms :   20 (  27 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_65,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ! [C] :
            ( v1_relat_1(C)
           => ( r1_tarski(k2_relat_1(B),k1_relat_1(k7_relat_1(C,A)))
             => k5_relat_1(B,k7_relat_1(C,A)) = k5_relat_1(B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t200_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k7_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_27,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

tff(c_14,plain,(
    k5_relat_1('#skF_2',k7_relat_1('#skF_3','#skF_1')) != k5_relat_1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_18,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_10,plain,(
    ! [B_14,A_13] :
      ( k3_xboole_0(k1_relat_1(B_14),A_13) = k1_relat_1(k7_relat_1(B_14,A_13))
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_51,plain,(
    ! [B_25,A_26] :
      ( k7_relat_1(B_25,k3_xboole_0(k1_relat_1(B_25),A_26)) = k7_relat_1(B_25,A_26)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_60,plain,(
    ! [B_14,A_13] :
      ( k7_relat_1(B_14,k1_relat_1(k7_relat_1(B_14,A_13))) = k7_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14)
      | ~ v1_relat_1(B_14) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_51])).

tff(c_12,plain,(
    ! [A_15,B_16] :
      ( k5_relat_1(k6_relat_1(A_15),B_16) = k7_relat_1(B_16,A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_20,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2,plain,(
    ! [A_1] : v1_relat_1(k6_relat_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_16,plain,(
    r1_tarski(k2_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_40,plain,(
    ! [B_23,A_24] :
      ( k5_relat_1(B_23,k6_relat_1(A_24)) = B_23
      | ~ r1_tarski(k2_relat_1(B_23),A_24)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_43,plain,
    ( k5_relat_1('#skF_2',k6_relat_1(k1_relat_1(k7_relat_1('#skF_3','#skF_1')))) = '#skF_2'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_40])).

tff(c_46,plain,(
    k5_relat_1('#skF_2',k6_relat_1(k1_relat_1(k7_relat_1('#skF_3','#skF_1')))) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_43])).

tff(c_83,plain,(
    ! [A_29,B_30,C_31] :
      ( k5_relat_1(k5_relat_1(A_29,B_30),C_31) = k5_relat_1(A_29,k5_relat_1(B_30,C_31))
      | ~ v1_relat_1(C_31)
      | ~ v1_relat_1(B_30)
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_98,plain,(
    ! [C_31] :
      ( k5_relat_1('#skF_2',k5_relat_1(k6_relat_1(k1_relat_1(k7_relat_1('#skF_3','#skF_1'))),C_31)) = k5_relat_1('#skF_2',C_31)
      | ~ v1_relat_1(C_31)
      | ~ v1_relat_1(k6_relat_1(k1_relat_1(k7_relat_1('#skF_3','#skF_1'))))
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_83])).

tff(c_108,plain,(
    ! [C_32] :
      ( k5_relat_1('#skF_2',k5_relat_1(k6_relat_1(k1_relat_1(k7_relat_1('#skF_3','#skF_1'))),C_32)) = k5_relat_1('#skF_2',C_32)
      | ~ v1_relat_1(C_32) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_2,c_98])).

tff(c_1023,plain,(
    ! [B_60] :
      ( k5_relat_1('#skF_2',k7_relat_1(B_60,k1_relat_1(k7_relat_1('#skF_3','#skF_1')))) = k5_relat_1('#skF_2',B_60)
      | ~ v1_relat_1(B_60)
      | ~ v1_relat_1(B_60) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_108])).

tff(c_1054,plain,
    ( k5_relat_1('#skF_2',k7_relat_1('#skF_3','#skF_1')) = k5_relat_1('#skF_2','#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_1023])).

tff(c_1070,plain,(
    k5_relat_1('#skF_2',k7_relat_1('#skF_3','#skF_1')) = k5_relat_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_18,c_18,c_1054])).

tff(c_1072,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_1070])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:02:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.86/1.60  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.61  
% 2.86/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.61  %$ r1_tarski > v1_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.86/1.61  
% 2.86/1.61  %Foreground sorts:
% 2.86/1.61  
% 2.86/1.61  
% 2.86/1.61  %Background operators:
% 2.86/1.61  
% 2.86/1.61  
% 2.86/1.61  %Foreground operators:
% 2.86/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.86/1.61  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.86/1.61  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.86/1.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.86/1.61  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.86/1.61  tff('#skF_2', type, '#skF_2': $i).
% 2.86/1.61  tff('#skF_3', type, '#skF_3': $i).
% 2.86/1.61  tff('#skF_1', type, '#skF_1': $i).
% 2.86/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.86/1.61  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.86/1.61  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.86/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.86/1.61  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.86/1.61  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.86/1.61  
% 3.19/1.62  tff(f_65, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(k2_relat_1(B), k1_relat_1(k7_relat_1(C, A))) => (k5_relat_1(B, k7_relat_1(C, A)) = k5_relat_1(B, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t200_relat_1)).
% 3.19/1.62  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 3.19/1.62  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k7_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t192_relat_1)).
% 3.19/1.62  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 3.19/1.62  tff(f_27, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 3.19/1.62  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 3.19/1.62  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 3.19/1.62  tff(c_14, plain, (k5_relat_1('#skF_2', k7_relat_1('#skF_3', '#skF_1'))!=k5_relat_1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.19/1.62  tff(c_18, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.19/1.62  tff(c_10, plain, (![B_14, A_13]: (k3_xboole_0(k1_relat_1(B_14), A_13)=k1_relat_1(k7_relat_1(B_14, A_13)) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.19/1.62  tff(c_51, plain, (![B_25, A_26]: (k7_relat_1(B_25, k3_xboole_0(k1_relat_1(B_25), A_26))=k7_relat_1(B_25, A_26) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.19/1.62  tff(c_60, plain, (![B_14, A_13]: (k7_relat_1(B_14, k1_relat_1(k7_relat_1(B_14, A_13)))=k7_relat_1(B_14, A_13) | ~v1_relat_1(B_14) | ~v1_relat_1(B_14))), inference(superposition, [status(thm), theory('equality')], [c_10, c_51])).
% 3.19/1.62  tff(c_12, plain, (![A_15, B_16]: (k5_relat_1(k6_relat_1(A_15), B_16)=k7_relat_1(B_16, A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.19/1.62  tff(c_20, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.19/1.62  tff(c_2, plain, (![A_1]: (v1_relat_1(k6_relat_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.19/1.62  tff(c_16, plain, (r1_tarski(k2_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.19/1.62  tff(c_40, plain, (![B_23, A_24]: (k5_relat_1(B_23, k6_relat_1(A_24))=B_23 | ~r1_tarski(k2_relat_1(B_23), A_24) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.19/1.62  tff(c_43, plain, (k5_relat_1('#skF_2', k6_relat_1(k1_relat_1(k7_relat_1('#skF_3', '#skF_1'))))='#skF_2' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_16, c_40])).
% 3.19/1.62  tff(c_46, plain, (k5_relat_1('#skF_2', k6_relat_1(k1_relat_1(k7_relat_1('#skF_3', '#skF_1'))))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_43])).
% 3.19/1.62  tff(c_83, plain, (![A_29, B_30, C_31]: (k5_relat_1(k5_relat_1(A_29, B_30), C_31)=k5_relat_1(A_29, k5_relat_1(B_30, C_31)) | ~v1_relat_1(C_31) | ~v1_relat_1(B_30) | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.19/1.62  tff(c_98, plain, (![C_31]: (k5_relat_1('#skF_2', k5_relat_1(k6_relat_1(k1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), C_31))=k5_relat_1('#skF_2', C_31) | ~v1_relat_1(C_31) | ~v1_relat_1(k6_relat_1(k1_relat_1(k7_relat_1('#skF_3', '#skF_1')))) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_46, c_83])).
% 3.19/1.62  tff(c_108, plain, (![C_32]: (k5_relat_1('#skF_2', k5_relat_1(k6_relat_1(k1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), C_32))=k5_relat_1('#skF_2', C_32) | ~v1_relat_1(C_32))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_2, c_98])).
% 3.19/1.62  tff(c_1023, plain, (![B_60]: (k5_relat_1('#skF_2', k7_relat_1(B_60, k1_relat_1(k7_relat_1('#skF_3', '#skF_1'))))=k5_relat_1('#skF_2', B_60) | ~v1_relat_1(B_60) | ~v1_relat_1(B_60))), inference(superposition, [status(thm), theory('equality')], [c_12, c_108])).
% 3.19/1.62  tff(c_1054, plain, (k5_relat_1('#skF_2', k7_relat_1('#skF_3', '#skF_1'))=k5_relat_1('#skF_2', '#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_60, c_1023])).
% 3.19/1.62  tff(c_1070, plain, (k5_relat_1('#skF_2', k7_relat_1('#skF_3', '#skF_1'))=k5_relat_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_18, c_18, c_1054])).
% 3.19/1.62  tff(c_1072, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14, c_1070])).
% 3.19/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.19/1.62  
% 3.19/1.62  Inference rules
% 3.19/1.62  ----------------------
% 3.19/1.62  #Ref     : 0
% 3.19/1.62  #Sup     : 221
% 3.19/1.62  #Fact    : 0
% 3.19/1.62  #Define  : 0
% 3.19/1.62  #Split   : 0
% 3.19/1.62  #Chain   : 0
% 3.19/1.62  #Close   : 0
% 3.19/1.62  
% 3.19/1.62  Ordering : KBO
% 3.19/1.62  
% 3.19/1.62  Simplification rules
% 3.19/1.62  ----------------------
% 3.19/1.62  #Subsume      : 3
% 3.19/1.62  #Demod        : 259
% 3.19/1.62  #Tautology    : 101
% 3.19/1.62  #SimpNegUnit  : 1
% 3.19/1.62  #BackRed      : 3
% 3.19/1.62  
% 3.19/1.62  #Partial instantiations: 0
% 3.19/1.62  #Strategies tried      : 1
% 3.19/1.62  
% 3.19/1.62  Timing (in seconds)
% 3.19/1.62  ----------------------
% 3.19/1.62  Preprocessing        : 0.36
% 3.19/1.62  Parsing              : 0.19
% 3.19/1.62  CNF conversion       : 0.02
% 3.19/1.62  Main loop            : 0.41
% 3.19/1.62  Inferencing          : 0.16
% 3.19/1.62  Reduction            : 0.15
% 3.19/1.62  Demodulation         : 0.11
% 3.19/1.62  BG Simplification    : 0.03
% 3.19/1.62  Subsumption          : 0.05
% 3.19/1.62  Abstraction          : 0.04
% 3.19/1.62  MUC search           : 0.00
% 3.19/1.62  Cooper               : 0.00
% 3.19/1.62  Total                : 0.79
% 3.19/1.62  Index Insertion      : 0.00
% 3.19/1.62  Index Deletion       : 0.00
% 3.19/1.62  Index Matching       : 0.00
% 3.19/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
