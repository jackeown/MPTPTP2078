%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:12 EST 2020

% Result     : Theorem 2.62s
% Output     : CNFRefutation 2.87s
% Verified   : 
% Statistics : Number of formulae       :   46 (  72 expanded)
%              Number of leaves         :   20 (  34 expanded)
%              Depth                    :   14
%              Number of atoms          :   72 ( 134 expanded)
%              Number of equality atoms :   25 (  40 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_27,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_41,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

tff(c_20,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_14,plain,(
    ! [A_14,B_15] :
      ( k5_relat_1(k6_relat_1(A_14),B_15) = k7_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_22,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2,plain,(
    ! [A_1] : v1_relat_1(k6_relat_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [B_13,A_12] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_13,A_12)),A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_18,plain,(
    r1_tarski(k2_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_52,plain,(
    ! [B_24,A_25] :
      ( k5_relat_1(B_24,k6_relat_1(A_25)) = B_24
      | ~ r1_tarski(k2_relat_1(B_24),A_25)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_55,plain,
    ( k5_relat_1('#skF_2',k6_relat_1(k1_relat_1(k7_relat_1('#skF_3','#skF_1')))) = '#skF_2'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_52])).

tff(c_61,plain,(
    k5_relat_1('#skF_2',k6_relat_1(k1_relat_1(k7_relat_1('#skF_3','#skF_1')))) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_55])).

tff(c_8,plain,(
    ! [A_9] : k2_relat_1(k6_relat_1(A_9)) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_58,plain,(
    ! [A_9,A_25] :
      ( k5_relat_1(k6_relat_1(A_9),k6_relat_1(A_25)) = k6_relat_1(A_9)
      | ~ r1_tarski(A_9,A_25)
      | ~ v1_relat_1(k6_relat_1(A_9)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_52])).

tff(c_63,plain,(
    ! [A_9,A_25] :
      ( k5_relat_1(k6_relat_1(A_9),k6_relat_1(A_25)) = k6_relat_1(A_9)
      | ~ r1_tarski(A_9,A_25) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_58])).

tff(c_119,plain,(
    ! [A_32,B_33,C_34] :
      ( k5_relat_1(k5_relat_1(A_32,B_33),C_34) = k5_relat_1(A_32,k5_relat_1(B_33,C_34))
      | ~ v1_relat_1(C_34)
      | ~ v1_relat_1(B_33)
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_137,plain,(
    ! [C_34] :
      ( k5_relat_1('#skF_2',k5_relat_1(k6_relat_1(k1_relat_1(k7_relat_1('#skF_3','#skF_1'))),C_34)) = k5_relat_1('#skF_2',C_34)
      | ~ v1_relat_1(C_34)
      | ~ v1_relat_1(k6_relat_1(k1_relat_1(k7_relat_1('#skF_3','#skF_1'))))
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_119])).

tff(c_172,plain,(
    ! [C_37] :
      ( k5_relat_1('#skF_2',k5_relat_1(k6_relat_1(k1_relat_1(k7_relat_1('#skF_3','#skF_1'))),C_37)) = k5_relat_1('#skF_2',C_37)
      | ~ v1_relat_1(C_37) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_2,c_137])).

tff(c_185,plain,(
    ! [A_25] :
      ( k5_relat_1('#skF_2',k6_relat_1(k1_relat_1(k7_relat_1('#skF_3','#skF_1')))) = k5_relat_1('#skF_2',k6_relat_1(A_25))
      | ~ v1_relat_1(k6_relat_1(A_25))
      | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_3','#skF_1')),A_25) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_172])).

tff(c_217,plain,(
    ! [A_42] :
      ( k5_relat_1('#skF_2',k6_relat_1(A_42)) = '#skF_2'
      | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_3','#skF_1')),A_42) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_61,c_185])).

tff(c_229,plain,
    ( k5_relat_1('#skF_2',k6_relat_1('#skF_1')) = '#skF_2'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_217])).

tff(c_236,plain,(
    k5_relat_1('#skF_2',k6_relat_1('#skF_1')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_229])).

tff(c_4,plain,(
    ! [A_2,B_6,C_8] :
      ( k5_relat_1(k5_relat_1(A_2,B_6),C_8) = k5_relat_1(A_2,k5_relat_1(B_6,C_8))
      | ~ v1_relat_1(C_8)
      | ~ v1_relat_1(B_6)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_240,plain,(
    ! [C_8] :
      ( k5_relat_1('#skF_2',k5_relat_1(k6_relat_1('#skF_1'),C_8)) = k5_relat_1('#skF_2',C_8)
      | ~ v1_relat_1(C_8)
      | ~ v1_relat_1(k6_relat_1('#skF_1'))
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_236,c_4])).

tff(c_246,plain,(
    ! [C_43] :
      ( k5_relat_1('#skF_2',k5_relat_1(k6_relat_1('#skF_1'),C_43)) = k5_relat_1('#skF_2',C_43)
      | ~ v1_relat_1(C_43) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_2,c_240])).

tff(c_496,plain,(
    ! [B_53] :
      ( k5_relat_1('#skF_2',k7_relat_1(B_53,'#skF_1')) = k5_relat_1('#skF_2',B_53)
      | ~ v1_relat_1(B_53)
      | ~ v1_relat_1(B_53) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_246])).

tff(c_16,plain,(
    k5_relat_1('#skF_2',k7_relat_1('#skF_3','#skF_1')) != k5_relat_1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_508,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_496,c_16])).

tff(c_524,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_508])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:04:45 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.62/1.67  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.62/1.68  
% 2.62/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.62/1.68  %$ r1_tarski > v1_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.62/1.68  
% 2.62/1.68  %Foreground sorts:
% 2.62/1.68  
% 2.62/1.68  
% 2.62/1.68  %Background operators:
% 2.62/1.68  
% 2.62/1.68  
% 2.62/1.68  %Foreground operators:
% 2.62/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.62/1.68  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.62/1.68  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.62/1.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.62/1.68  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.62/1.68  tff('#skF_2', type, '#skF_2': $i).
% 2.62/1.68  tff('#skF_3', type, '#skF_3': $i).
% 2.62/1.68  tff('#skF_1', type, '#skF_1': $i).
% 2.62/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.62/1.68  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.62/1.68  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.62/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.62/1.68  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.62/1.68  
% 2.87/1.69  tff(f_65, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(k2_relat_1(B), k1_relat_1(k7_relat_1(C, A))) => (k5_relat_1(B, k7_relat_1(C, A)) = k5_relat_1(B, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t200_relat_1)).
% 2.87/1.69  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 2.87/1.69  tff(f_27, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.87/1.69  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 2.87/1.69  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 2.87/1.69  tff(f_41, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.87/1.69  tff(f_37, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 2.87/1.69  tff(c_20, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.87/1.69  tff(c_14, plain, (![A_14, B_15]: (k5_relat_1(k6_relat_1(A_14), B_15)=k7_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.87/1.69  tff(c_22, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.87/1.69  tff(c_2, plain, (![A_1]: (v1_relat_1(k6_relat_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.87/1.69  tff(c_12, plain, (![B_13, A_12]: (r1_tarski(k1_relat_1(k7_relat_1(B_13, A_12)), A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.87/1.69  tff(c_18, plain, (r1_tarski(k2_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.87/1.69  tff(c_52, plain, (![B_24, A_25]: (k5_relat_1(B_24, k6_relat_1(A_25))=B_24 | ~r1_tarski(k2_relat_1(B_24), A_25) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.87/1.69  tff(c_55, plain, (k5_relat_1('#skF_2', k6_relat_1(k1_relat_1(k7_relat_1('#skF_3', '#skF_1'))))='#skF_2' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_18, c_52])).
% 2.87/1.69  tff(c_61, plain, (k5_relat_1('#skF_2', k6_relat_1(k1_relat_1(k7_relat_1('#skF_3', '#skF_1'))))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_55])).
% 2.87/1.69  tff(c_8, plain, (![A_9]: (k2_relat_1(k6_relat_1(A_9))=A_9)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.87/1.69  tff(c_58, plain, (![A_9, A_25]: (k5_relat_1(k6_relat_1(A_9), k6_relat_1(A_25))=k6_relat_1(A_9) | ~r1_tarski(A_9, A_25) | ~v1_relat_1(k6_relat_1(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_52])).
% 2.87/1.69  tff(c_63, plain, (![A_9, A_25]: (k5_relat_1(k6_relat_1(A_9), k6_relat_1(A_25))=k6_relat_1(A_9) | ~r1_tarski(A_9, A_25))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_58])).
% 2.87/1.69  tff(c_119, plain, (![A_32, B_33, C_34]: (k5_relat_1(k5_relat_1(A_32, B_33), C_34)=k5_relat_1(A_32, k5_relat_1(B_33, C_34)) | ~v1_relat_1(C_34) | ~v1_relat_1(B_33) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.87/1.69  tff(c_137, plain, (![C_34]: (k5_relat_1('#skF_2', k5_relat_1(k6_relat_1(k1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), C_34))=k5_relat_1('#skF_2', C_34) | ~v1_relat_1(C_34) | ~v1_relat_1(k6_relat_1(k1_relat_1(k7_relat_1('#skF_3', '#skF_1')))) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_61, c_119])).
% 2.87/1.69  tff(c_172, plain, (![C_37]: (k5_relat_1('#skF_2', k5_relat_1(k6_relat_1(k1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), C_37))=k5_relat_1('#skF_2', C_37) | ~v1_relat_1(C_37))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_2, c_137])).
% 2.87/1.69  tff(c_185, plain, (![A_25]: (k5_relat_1('#skF_2', k6_relat_1(k1_relat_1(k7_relat_1('#skF_3', '#skF_1'))))=k5_relat_1('#skF_2', k6_relat_1(A_25)) | ~v1_relat_1(k6_relat_1(A_25)) | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_3', '#skF_1')), A_25))), inference(superposition, [status(thm), theory('equality')], [c_63, c_172])).
% 2.87/1.69  tff(c_217, plain, (![A_42]: (k5_relat_1('#skF_2', k6_relat_1(A_42))='#skF_2' | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_3', '#skF_1')), A_42))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_61, c_185])).
% 2.87/1.69  tff(c_229, plain, (k5_relat_1('#skF_2', k6_relat_1('#skF_1'))='#skF_2' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_12, c_217])).
% 2.87/1.69  tff(c_236, plain, (k5_relat_1('#skF_2', k6_relat_1('#skF_1'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_229])).
% 2.87/1.69  tff(c_4, plain, (![A_2, B_6, C_8]: (k5_relat_1(k5_relat_1(A_2, B_6), C_8)=k5_relat_1(A_2, k5_relat_1(B_6, C_8)) | ~v1_relat_1(C_8) | ~v1_relat_1(B_6) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.87/1.69  tff(c_240, plain, (![C_8]: (k5_relat_1('#skF_2', k5_relat_1(k6_relat_1('#skF_1'), C_8))=k5_relat_1('#skF_2', C_8) | ~v1_relat_1(C_8) | ~v1_relat_1(k6_relat_1('#skF_1')) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_236, c_4])).
% 2.87/1.69  tff(c_246, plain, (![C_43]: (k5_relat_1('#skF_2', k5_relat_1(k6_relat_1('#skF_1'), C_43))=k5_relat_1('#skF_2', C_43) | ~v1_relat_1(C_43))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_2, c_240])).
% 2.87/1.69  tff(c_496, plain, (![B_53]: (k5_relat_1('#skF_2', k7_relat_1(B_53, '#skF_1'))=k5_relat_1('#skF_2', B_53) | ~v1_relat_1(B_53) | ~v1_relat_1(B_53))), inference(superposition, [status(thm), theory('equality')], [c_14, c_246])).
% 2.87/1.69  tff(c_16, plain, (k5_relat_1('#skF_2', k7_relat_1('#skF_3', '#skF_1'))!=k5_relat_1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.87/1.69  tff(c_508, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_496, c_16])).
% 2.87/1.69  tff(c_524, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_508])).
% 2.87/1.69  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.87/1.69  
% 2.87/1.69  Inference rules
% 2.87/1.69  ----------------------
% 2.87/1.69  #Ref     : 0
% 2.87/1.69  #Sup     : 110
% 2.87/1.69  #Fact    : 0
% 2.87/1.69  #Define  : 0
% 2.87/1.69  #Split   : 0
% 2.87/1.69  #Chain   : 0
% 2.87/1.69  #Close   : 0
% 2.87/1.69  
% 2.87/1.69  Ordering : KBO
% 2.87/1.69  
% 2.87/1.69  Simplification rules
% 2.87/1.69  ----------------------
% 2.87/1.69  #Subsume      : 5
% 2.87/1.69  #Demod        : 65
% 2.87/1.69  #Tautology    : 45
% 2.87/1.69  #SimpNegUnit  : 0
% 2.87/1.69  #BackRed      : 0
% 2.87/1.69  
% 2.87/1.69  #Partial instantiations: 0
% 2.87/1.69  #Strategies tried      : 1
% 2.87/1.69  
% 2.87/1.69  Timing (in seconds)
% 2.87/1.69  ----------------------
% 2.87/1.70  Preprocessing        : 0.45
% 2.87/1.70  Parsing              : 0.25
% 2.87/1.70  CNF conversion       : 0.03
% 2.87/1.70  Main loop            : 0.43
% 2.87/1.70  Inferencing          : 0.18
% 2.87/1.70  Reduction            : 0.13
% 2.87/1.70  Demodulation         : 0.10
% 2.87/1.70  BG Simplification    : 0.02
% 2.87/1.70  Subsumption          : 0.06
% 2.87/1.70  Abstraction          : 0.02
% 2.87/1.70  MUC search           : 0.00
% 2.87/1.70  Cooper               : 0.00
% 2.87/1.70  Total                : 0.92
% 2.87/1.70  Index Insertion      : 0.00
% 2.87/1.70  Index Deletion       : 0.00
% 2.87/1.70  Index Matching       : 0.00
% 2.87/1.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
