%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:52 EST 2020

% Result     : Theorem 2.29s
% Output     : CNFRefutation 2.29s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 107 expanded)
%              Number of leaves         :   20 (  47 expanded)
%              Depth                    :    9
%              Number of atoms          :  112 ( 295 expanded)
%              Number of equality atoms :   21 (  79 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_80,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v2_funct_1(A)
         => ( k1_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A)
            & k2_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).

tff(f_69,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_59,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

tff(c_24,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_22,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_20,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_14,plain,(
    ! [A_11] :
      ( k2_relat_1(k2_funct_1(A_11)) = k1_relat_1(A_11)
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_12,plain,(
    ! [A_10] :
      ( v1_relat_1(k2_funct_1(A_10))
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_4,plain,(
    ! [A_3] :
      ( k10_relat_1(A_3,k2_relat_1(A_3)) = k1_relat_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_41,plain,(
    ! [A_18] :
      ( k1_relat_1(k2_funct_1(A_18)) = k2_relat_1(A_18)
      | ~ v2_funct_1(A_18)
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k10_relat_1(B_2,A_1),k1_relat_1(B_2))
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_251,plain,(
    ! [A_36,A_37] :
      ( r1_tarski(k10_relat_1(k2_funct_1(A_36),A_37),k2_relat_1(A_36))
      | ~ v1_relat_1(k2_funct_1(A_36))
      | ~ v2_funct_1(A_36)
      | ~ v1_funct_1(A_36)
      | ~ v1_relat_1(A_36) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_41,c_2])).

tff(c_280,plain,(
    ! [A_39] :
      ( r1_tarski(k1_relat_1(k2_funct_1(A_39)),k2_relat_1(A_39))
      | ~ v1_relat_1(k2_funct_1(A_39))
      | ~ v2_funct_1(A_39)
      | ~ v1_funct_1(A_39)
      | ~ v1_relat_1(A_39)
      | ~ v1_relat_1(k2_funct_1(A_39)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_251])).

tff(c_8,plain,(
    ! [B_9,A_7] :
      ( k2_relat_1(k5_relat_1(B_9,A_7)) = k2_relat_1(A_7)
      | ~ r1_tarski(k1_relat_1(A_7),k2_relat_1(B_9))
      | ~ v1_relat_1(B_9)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_291,plain,(
    ! [A_40] :
      ( k2_relat_1(k5_relat_1(A_40,k2_funct_1(A_40))) = k2_relat_1(k2_funct_1(A_40))
      | ~ v2_funct_1(A_40)
      | ~ v1_funct_1(A_40)
      | ~ v1_relat_1(A_40)
      | ~ v1_relat_1(k2_funct_1(A_40)) ) ),
    inference(resolution,[status(thm)],[c_280,c_8])).

tff(c_36,plain,(
    ! [B_15,A_16] :
      ( r1_tarski(k10_relat_1(B_15,A_16),k1_relat_1(B_15))
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_39,plain,(
    ! [A_3] :
      ( r1_tarski(k1_relat_1(A_3),k1_relat_1(A_3))
      | ~ v1_relat_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_36])).

tff(c_147,plain,(
    ! [A_29] :
      ( r1_tarski(k2_relat_1(A_29),k1_relat_1(k2_funct_1(A_29)))
      | ~ v1_relat_1(k2_funct_1(A_29))
      | ~ v1_relat_1(k2_funct_1(A_29))
      | ~ v2_funct_1(A_29)
      | ~ v1_funct_1(A_29)
      | ~ v1_relat_1(A_29) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_41,c_39])).

tff(c_6,plain,(
    ! [A_4,B_6] :
      ( k1_relat_1(k5_relat_1(A_4,B_6)) = k1_relat_1(A_4)
      | ~ r1_tarski(k2_relat_1(A_4),k1_relat_1(B_6))
      | ~ v1_relat_1(B_6)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_161,plain,(
    ! [A_30] :
      ( k1_relat_1(k5_relat_1(A_30,k2_funct_1(A_30))) = k1_relat_1(A_30)
      | ~ v1_relat_1(k2_funct_1(A_30))
      | ~ v2_funct_1(A_30)
      | ~ v1_funct_1(A_30)
      | ~ v1_relat_1(A_30) ) ),
    inference(resolution,[status(thm)],[c_147,c_6])).

tff(c_18,plain,
    ( k2_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1')
    | k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_59,plain,(
    k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_176,plain,
    ( ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_59])).

tff(c_192,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_20,c_176])).

tff(c_196,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_192])).

tff(c_200,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_196])).

tff(c_201,plain,(
    k2_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_309,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1')
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_291,c_201])).

tff(c_318,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_20,c_309])).

tff(c_333,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_318])).

tff(c_336,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_333])).

tff(c_340,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_336])).

tff(c_341,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_318])).

tff(c_345,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_341])).

tff(c_349,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_20,c_345])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:55:16 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.29/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.29/1.31  
% 2.29/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.29/1.31  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1
% 2.29/1.31  
% 2.29/1.31  %Foreground sorts:
% 2.29/1.31  
% 2.29/1.31  
% 2.29/1.31  %Background operators:
% 2.29/1.31  
% 2.29/1.31  
% 2.29/1.31  %Foreground operators:
% 2.29/1.31  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.29/1.31  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.29/1.31  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.29/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.29/1.31  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.29/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.29/1.31  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.29/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.29/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.29/1.31  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.29/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.29/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.29/1.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.29/1.31  
% 2.29/1.33  tff(f_80, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)) & (k2_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_funct_1)).
% 2.29/1.33  tff(f_69, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 2.29/1.33  tff(f_59, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 2.29/1.33  tff(f_33, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 2.29/1.33  tff(f_29, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 2.29/1.33  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_relat_1)).
% 2.29/1.33  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_relat_1)).
% 2.29/1.33  tff(c_24, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.29/1.33  tff(c_22, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.29/1.33  tff(c_20, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.29/1.33  tff(c_14, plain, (![A_11]: (k2_relat_1(k2_funct_1(A_11))=k1_relat_1(A_11) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.29/1.33  tff(c_12, plain, (![A_10]: (v1_relat_1(k2_funct_1(A_10)) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.29/1.33  tff(c_4, plain, (![A_3]: (k10_relat_1(A_3, k2_relat_1(A_3))=k1_relat_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.29/1.33  tff(c_41, plain, (![A_18]: (k1_relat_1(k2_funct_1(A_18))=k2_relat_1(A_18) | ~v2_funct_1(A_18) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.29/1.33  tff(c_2, plain, (![B_2, A_1]: (r1_tarski(k10_relat_1(B_2, A_1), k1_relat_1(B_2)) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.29/1.33  tff(c_251, plain, (![A_36, A_37]: (r1_tarski(k10_relat_1(k2_funct_1(A_36), A_37), k2_relat_1(A_36)) | ~v1_relat_1(k2_funct_1(A_36)) | ~v2_funct_1(A_36) | ~v1_funct_1(A_36) | ~v1_relat_1(A_36))), inference(superposition, [status(thm), theory('equality')], [c_41, c_2])).
% 2.29/1.33  tff(c_280, plain, (![A_39]: (r1_tarski(k1_relat_1(k2_funct_1(A_39)), k2_relat_1(A_39)) | ~v1_relat_1(k2_funct_1(A_39)) | ~v2_funct_1(A_39) | ~v1_funct_1(A_39) | ~v1_relat_1(A_39) | ~v1_relat_1(k2_funct_1(A_39)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_251])).
% 2.29/1.33  tff(c_8, plain, (![B_9, A_7]: (k2_relat_1(k5_relat_1(B_9, A_7))=k2_relat_1(A_7) | ~r1_tarski(k1_relat_1(A_7), k2_relat_1(B_9)) | ~v1_relat_1(B_9) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.29/1.33  tff(c_291, plain, (![A_40]: (k2_relat_1(k5_relat_1(A_40, k2_funct_1(A_40)))=k2_relat_1(k2_funct_1(A_40)) | ~v2_funct_1(A_40) | ~v1_funct_1(A_40) | ~v1_relat_1(A_40) | ~v1_relat_1(k2_funct_1(A_40)))), inference(resolution, [status(thm)], [c_280, c_8])).
% 2.29/1.33  tff(c_36, plain, (![B_15, A_16]: (r1_tarski(k10_relat_1(B_15, A_16), k1_relat_1(B_15)) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.29/1.33  tff(c_39, plain, (![A_3]: (r1_tarski(k1_relat_1(A_3), k1_relat_1(A_3)) | ~v1_relat_1(A_3) | ~v1_relat_1(A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_36])).
% 2.29/1.33  tff(c_147, plain, (![A_29]: (r1_tarski(k2_relat_1(A_29), k1_relat_1(k2_funct_1(A_29))) | ~v1_relat_1(k2_funct_1(A_29)) | ~v1_relat_1(k2_funct_1(A_29)) | ~v2_funct_1(A_29) | ~v1_funct_1(A_29) | ~v1_relat_1(A_29))), inference(superposition, [status(thm), theory('equality')], [c_41, c_39])).
% 2.29/1.33  tff(c_6, plain, (![A_4, B_6]: (k1_relat_1(k5_relat_1(A_4, B_6))=k1_relat_1(A_4) | ~r1_tarski(k2_relat_1(A_4), k1_relat_1(B_6)) | ~v1_relat_1(B_6) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.29/1.33  tff(c_161, plain, (![A_30]: (k1_relat_1(k5_relat_1(A_30, k2_funct_1(A_30)))=k1_relat_1(A_30) | ~v1_relat_1(k2_funct_1(A_30)) | ~v2_funct_1(A_30) | ~v1_funct_1(A_30) | ~v1_relat_1(A_30))), inference(resolution, [status(thm)], [c_147, c_6])).
% 2.29/1.33  tff(c_18, plain, (k2_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1') | k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.29/1.33  tff(c_59, plain, (k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_18])).
% 2.29/1.33  tff(c_176, plain, (~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_161, c_59])).
% 2.29/1.33  tff(c_192, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_20, c_176])).
% 2.29/1.33  tff(c_196, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_12, c_192])).
% 2.29/1.33  tff(c_200, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_196])).
% 2.29/1.33  tff(c_201, plain, (k2_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_18])).
% 2.29/1.33  tff(c_309, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1') | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_291, c_201])).
% 2.29/1.33  tff(c_318, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_20, c_309])).
% 2.29/1.33  tff(c_333, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_318])).
% 2.29/1.33  tff(c_336, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_12, c_333])).
% 2.29/1.33  tff(c_340, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_336])).
% 2.29/1.33  tff(c_341, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_318])).
% 2.29/1.33  tff(c_345, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_14, c_341])).
% 2.29/1.33  tff(c_349, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_20, c_345])).
% 2.29/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.29/1.33  
% 2.29/1.33  Inference rules
% 2.29/1.33  ----------------------
% 2.29/1.33  #Ref     : 0
% 2.29/1.33  #Sup     : 85
% 2.29/1.33  #Fact    : 0
% 2.29/1.33  #Define  : 0
% 2.29/1.33  #Split   : 3
% 2.29/1.33  #Chain   : 0
% 2.29/1.33  #Close   : 0
% 2.29/1.33  
% 2.29/1.33  Ordering : KBO
% 2.29/1.33  
% 2.29/1.33  Simplification rules
% 2.29/1.33  ----------------------
% 2.29/1.33  #Subsume      : 7
% 2.29/1.33  #Demod        : 15
% 2.29/1.33  #Tautology    : 20
% 2.29/1.33  #SimpNegUnit  : 0
% 2.29/1.33  #BackRed      : 0
% 2.29/1.33  
% 2.29/1.33  #Partial instantiations: 0
% 2.29/1.33  #Strategies tried      : 1
% 2.29/1.33  
% 2.29/1.33  Timing (in seconds)
% 2.29/1.33  ----------------------
% 2.59/1.33  Preprocessing        : 0.29
% 2.59/1.33  Parsing              : 0.16
% 2.59/1.33  CNF conversion       : 0.02
% 2.59/1.33  Main loop            : 0.27
% 2.59/1.33  Inferencing          : 0.11
% 2.59/1.33  Reduction            : 0.07
% 2.59/1.33  Demodulation         : 0.05
% 2.59/1.33  BG Simplification    : 0.02
% 2.59/1.33  Subsumption          : 0.06
% 2.59/1.33  Abstraction          : 0.01
% 2.59/1.33  MUC search           : 0.00
% 2.59/1.33  Cooper               : 0.00
% 2.59/1.33  Total                : 0.60
% 2.59/1.34  Index Insertion      : 0.00
% 2.59/1.34  Index Deletion       : 0.00
% 2.59/1.34  Index Matching       : 0.00
% 2.59/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
