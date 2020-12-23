%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:49 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.45s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 102 expanded)
%              Number of leaves         :   20 (  46 expanded)
%              Depth                    :    8
%              Number of atoms          :  108 ( 285 expanded)
%              Number of equality atoms :   25 (  85 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1

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

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

tff(c_28,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_26,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_24,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_18,plain,(
    ! [A_11] :
      ( k2_relat_1(k2_funct_1(A_11)) = k1_relat_1(A_11)
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_16,plain,(
    ! [A_10] :
      ( v1_relat_1(k2_funct_1(A_10))
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_10,plain,(
    ! [B_6,A_4] :
      ( k9_relat_1(B_6,k2_relat_1(A_4)) = k2_relat_1(k5_relat_1(A_4,B_6))
      | ~ v1_relat_1(B_6)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_49,plain,(
    ! [A_18] :
      ( k1_relat_1(k2_funct_1(A_18)) = k2_relat_1(A_18)
      | ~ v2_funct_1(A_18)
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_8,plain,(
    ! [A_3] :
      ( k9_relat_1(A_3,k1_relat_1(A_3)) = k2_relat_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_245,plain,(
    ! [A_36] :
      ( k9_relat_1(k2_funct_1(A_36),k2_relat_1(A_36)) = k2_relat_1(k2_funct_1(A_36))
      | ~ v1_relat_1(k2_funct_1(A_36))
      | ~ v2_funct_1(A_36)
      | ~ v1_funct_1(A_36)
      | ~ v1_relat_1(A_36) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_8])).

tff(c_283,plain,(
    ! [A_39] :
      ( k2_relat_1(k5_relat_1(A_39,k2_funct_1(A_39))) = k2_relat_1(k2_funct_1(A_39))
      | ~ v1_relat_1(k2_funct_1(A_39))
      | ~ v2_funct_1(A_39)
      | ~ v1_funct_1(A_39)
      | ~ v1_relat_1(A_39)
      | ~ v1_relat_1(k2_funct_1(A_39))
      | ~ v1_relat_1(A_39) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_245])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,(
    ! [A_11] :
      ( k1_relat_1(k2_funct_1(A_11)) = k2_relat_1(A_11)
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_83,plain,(
    ! [A_22,B_23] :
      ( k1_relat_1(k5_relat_1(A_22,B_23)) = k1_relat_1(A_22)
      | ~ r1_tarski(k2_relat_1(A_22),k1_relat_1(B_23))
      | ~ v1_relat_1(B_23)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_153,plain,(
    ! [A_28,A_29] :
      ( k1_relat_1(k5_relat_1(A_28,k2_funct_1(A_29))) = k1_relat_1(A_28)
      | ~ r1_tarski(k2_relat_1(A_28),k2_relat_1(A_29))
      | ~ v1_relat_1(k2_funct_1(A_29))
      | ~ v1_relat_1(A_28)
      | ~ v2_funct_1(A_29)
      | ~ v1_funct_1(A_29)
      | ~ v1_relat_1(A_29) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_83])).

tff(c_177,plain,(
    ! [A_30] :
      ( k1_relat_1(k5_relat_1(A_30,k2_funct_1(A_30))) = k1_relat_1(A_30)
      | ~ v1_relat_1(k2_funct_1(A_30))
      | ~ v2_funct_1(A_30)
      | ~ v1_funct_1(A_30)
      | ~ v1_relat_1(A_30) ) ),
    inference(resolution,[status(thm)],[c_6,c_153])).

tff(c_22,plain,
    ( k2_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1')
    | k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_61,plain,(
    k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_186,plain,
    ( ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_177,c_61])).

tff(c_196,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_186])).

tff(c_200,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_196])).

tff(c_204,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_200])).

tff(c_205,plain,(
    k2_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_302,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_283,c_205])).

tff(c_312,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_28,c_26,c_24,c_302])).

tff(c_314,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_312])).

tff(c_317,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_314])).

tff(c_321,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_317])).

tff(c_322,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_312])).

tff(c_350,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_322])).

tff(c_354,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_350])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:21:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.13/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.30  
% 2.13/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.31  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1
% 2.13/1.31  
% 2.13/1.31  %Foreground sorts:
% 2.13/1.31  
% 2.13/1.31  
% 2.13/1.31  %Background operators:
% 2.13/1.31  
% 2.13/1.31  
% 2.13/1.31  %Foreground operators:
% 2.13/1.31  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.13/1.31  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.13/1.31  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.13/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.13/1.31  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.13/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.13/1.31  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.13/1.31  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.13/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.13/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.13/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.13/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.13/1.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.13/1.31  
% 2.45/1.32  tff(f_80, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)) & (k2_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_funct_1)).
% 2.45/1.32  tff(f_69, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 2.45/1.32  tff(f_59, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 2.45/1.32  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t160_relat_1)).
% 2.45/1.32  tff(f_35, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 2.45/1.32  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.45/1.32  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_relat_1)).
% 2.45/1.32  tff(c_28, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.45/1.32  tff(c_26, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.45/1.32  tff(c_24, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.45/1.32  tff(c_18, plain, (![A_11]: (k2_relat_1(k2_funct_1(A_11))=k1_relat_1(A_11) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.45/1.32  tff(c_16, plain, (![A_10]: (v1_relat_1(k2_funct_1(A_10)) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.45/1.32  tff(c_10, plain, (![B_6, A_4]: (k9_relat_1(B_6, k2_relat_1(A_4))=k2_relat_1(k5_relat_1(A_4, B_6)) | ~v1_relat_1(B_6) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.45/1.32  tff(c_49, plain, (![A_18]: (k1_relat_1(k2_funct_1(A_18))=k2_relat_1(A_18) | ~v2_funct_1(A_18) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.45/1.32  tff(c_8, plain, (![A_3]: (k9_relat_1(A_3, k1_relat_1(A_3))=k2_relat_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.45/1.32  tff(c_245, plain, (![A_36]: (k9_relat_1(k2_funct_1(A_36), k2_relat_1(A_36))=k2_relat_1(k2_funct_1(A_36)) | ~v1_relat_1(k2_funct_1(A_36)) | ~v2_funct_1(A_36) | ~v1_funct_1(A_36) | ~v1_relat_1(A_36))), inference(superposition, [status(thm), theory('equality')], [c_49, c_8])).
% 2.45/1.32  tff(c_283, plain, (![A_39]: (k2_relat_1(k5_relat_1(A_39, k2_funct_1(A_39)))=k2_relat_1(k2_funct_1(A_39)) | ~v1_relat_1(k2_funct_1(A_39)) | ~v2_funct_1(A_39) | ~v1_funct_1(A_39) | ~v1_relat_1(A_39) | ~v1_relat_1(k2_funct_1(A_39)) | ~v1_relat_1(A_39))), inference(superposition, [status(thm), theory('equality')], [c_10, c_245])).
% 2.45/1.32  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.45/1.32  tff(c_20, plain, (![A_11]: (k1_relat_1(k2_funct_1(A_11))=k2_relat_1(A_11) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.45/1.32  tff(c_83, plain, (![A_22, B_23]: (k1_relat_1(k5_relat_1(A_22, B_23))=k1_relat_1(A_22) | ~r1_tarski(k2_relat_1(A_22), k1_relat_1(B_23)) | ~v1_relat_1(B_23) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.45/1.32  tff(c_153, plain, (![A_28, A_29]: (k1_relat_1(k5_relat_1(A_28, k2_funct_1(A_29)))=k1_relat_1(A_28) | ~r1_tarski(k2_relat_1(A_28), k2_relat_1(A_29)) | ~v1_relat_1(k2_funct_1(A_29)) | ~v1_relat_1(A_28) | ~v2_funct_1(A_29) | ~v1_funct_1(A_29) | ~v1_relat_1(A_29))), inference(superposition, [status(thm), theory('equality')], [c_20, c_83])).
% 2.45/1.32  tff(c_177, plain, (![A_30]: (k1_relat_1(k5_relat_1(A_30, k2_funct_1(A_30)))=k1_relat_1(A_30) | ~v1_relat_1(k2_funct_1(A_30)) | ~v2_funct_1(A_30) | ~v1_funct_1(A_30) | ~v1_relat_1(A_30))), inference(resolution, [status(thm)], [c_6, c_153])).
% 2.45/1.32  tff(c_22, plain, (k2_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1') | k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.45/1.32  tff(c_61, plain, (k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_22])).
% 2.45/1.32  tff(c_186, plain, (~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_177, c_61])).
% 2.45/1.32  tff(c_196, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_24, c_186])).
% 2.45/1.32  tff(c_200, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_16, c_196])).
% 2.45/1.32  tff(c_204, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_200])).
% 2.45/1.32  tff(c_205, plain, (k2_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_22])).
% 2.45/1.32  tff(c_302, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_283, c_205])).
% 2.45/1.32  tff(c_312, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_28, c_26, c_24, c_302])).
% 2.45/1.32  tff(c_314, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_312])).
% 2.45/1.32  tff(c_317, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_16, c_314])).
% 2.45/1.32  tff(c_321, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_317])).
% 2.45/1.32  tff(c_322, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_312])).
% 2.45/1.32  tff(c_350, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_18, c_322])).
% 2.45/1.32  tff(c_354, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_24, c_350])).
% 2.45/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.45/1.32  
% 2.45/1.32  Inference rules
% 2.45/1.32  ----------------------
% 2.45/1.32  #Ref     : 0
% 2.45/1.32  #Sup     : 81
% 2.45/1.32  #Fact    : 0
% 2.45/1.32  #Define  : 0
% 2.45/1.32  #Split   : 3
% 2.45/1.32  #Chain   : 0
% 2.45/1.32  #Close   : 0
% 2.45/1.32  
% 2.45/1.32  Ordering : KBO
% 2.45/1.32  
% 2.45/1.32  Simplification rules
% 2.45/1.32  ----------------------
% 2.45/1.32  #Subsume      : 2
% 2.45/1.32  #Demod        : 16
% 2.45/1.32  #Tautology    : 30
% 2.45/1.32  #SimpNegUnit  : 0
% 2.45/1.32  #BackRed      : 0
% 2.45/1.32  
% 2.45/1.32  #Partial instantiations: 0
% 2.45/1.32  #Strategies tried      : 1
% 2.45/1.32  
% 2.45/1.32  Timing (in seconds)
% 2.45/1.32  ----------------------
% 2.45/1.32  Preprocessing        : 0.30
% 2.45/1.32  Parsing              : 0.16
% 2.45/1.32  CNF conversion       : 0.02
% 2.45/1.32  Main loop            : 0.25
% 2.45/1.32  Inferencing          : 0.09
% 2.45/1.32  Reduction            : 0.07
% 2.45/1.32  Demodulation         : 0.05
% 2.45/1.32  BG Simplification    : 0.02
% 2.45/1.32  Subsumption          : 0.06
% 2.45/1.32  Abstraction          : 0.02
% 2.45/1.32  MUC search           : 0.00
% 2.45/1.32  Cooper               : 0.00
% 2.45/1.32  Total                : 0.58
% 2.45/1.32  Index Insertion      : 0.00
% 2.45/1.33  Index Deletion       : 0.00
% 2.45/1.33  Index Matching       : 0.00
% 2.45/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
