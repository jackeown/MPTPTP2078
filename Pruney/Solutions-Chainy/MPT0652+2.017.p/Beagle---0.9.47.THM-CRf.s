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
% DateTime   : Thu Dec  3 10:03:54 EST 2020

% Result     : Theorem 2.38s
% Output     : CNFRefutation 2.38s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 123 expanded)
%              Number of leaves         :   20 (  53 expanded)
%              Depth                    :    8
%              Number of atoms          :  103 ( 345 expanded)
%              Number of equality atoms :   26 ( 107 expanded)
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
         => ( k1_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A)
            & k2_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_funct_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_69,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

tff(c_28,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_8,plain,(
    ! [A_3] :
      ( k9_relat_1(A_3,k1_relat_1(A_3)) = k2_relat_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_26,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_16,plain,(
    ! [A_10] :
      ( v1_relat_1(k2_funct_1(A_10))
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

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

tff(c_290,plain,(
    ! [B_36,A_37] :
      ( k9_relat_1(B_36,k2_relat_1(A_37)) = k2_relat_1(k5_relat_1(A_37,B_36))
      | ~ v1_relat_1(B_36)
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_331,plain,(
    ! [A_41,B_42] :
      ( k2_relat_1(k5_relat_1(k2_funct_1(A_41),B_42)) = k9_relat_1(B_42,k1_relat_1(A_41))
      | ~ v1_relat_1(B_42)
      | ~ v1_relat_1(k2_funct_1(A_41))
      | ~ v2_funct_1(A_41)
      | ~ v1_funct_1(A_41)
      | ~ v1_relat_1(A_41) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_290])).

tff(c_20,plain,(
    ! [A_11] :
      ( k1_relat_1(k2_funct_1(A_11)) = k2_relat_1(A_11)
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_83,plain,(
    ! [A_22,B_23] :
      ( k1_relat_1(k5_relat_1(A_22,B_23)) = k1_relat_1(A_22)
      | ~ r1_tarski(k2_relat_1(A_22),k1_relat_1(B_23))
      | ~ v1_relat_1(B_23)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_192,plain,(
    ! [A_31,B_32] :
      ( k1_relat_1(k5_relat_1(k2_funct_1(A_31),B_32)) = k1_relat_1(k2_funct_1(A_31))
      | ~ r1_tarski(k1_relat_1(A_31),k1_relat_1(B_32))
      | ~ v1_relat_1(B_32)
      | ~ v1_relat_1(k2_funct_1(A_31))
      | ~ v2_funct_1(A_31)
      | ~ v1_funct_1(A_31)
      | ~ v1_relat_1(A_31) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_83])).

tff(c_210,plain,(
    ! [A_33] :
      ( k1_relat_1(k5_relat_1(k2_funct_1(A_33),A_33)) = k1_relat_1(k2_funct_1(A_33))
      | ~ v1_relat_1(k2_funct_1(A_33))
      | ~ v2_funct_1(A_33)
      | ~ v1_funct_1(A_33)
      | ~ v1_relat_1(A_33) ) ),
    inference(resolution,[status(thm)],[c_6,c_192])).

tff(c_22,plain,
    ( k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1')
    | k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_61,plain,(
    k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_225,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_210,c_61])).

tff(c_234,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_225])).

tff(c_236,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_234])).

tff(c_239,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_236])).

tff(c_243,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_239])).

tff(c_244,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_234])).

tff(c_266,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_244])).

tff(c_270,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_266])).

tff(c_271,plain,(
    k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_346,plain,
    ( k9_relat_1('#skF_1',k1_relat_1('#skF_1')) != k2_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_331,c_271])).

tff(c_352,plain,
    ( k9_relat_1('#skF_1',k1_relat_1('#skF_1')) != k2_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_28,c_346])).

tff(c_354,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_352])).

tff(c_357,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_354])).

tff(c_361,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_357])).

tff(c_362,plain,(
    k9_relat_1('#skF_1',k1_relat_1('#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_352])).

tff(c_366,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_362])).

tff(c_370,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_366])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:09:44 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.38/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.38/1.30  
% 2.38/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.38/1.30  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1
% 2.38/1.30  
% 2.38/1.30  %Foreground sorts:
% 2.38/1.30  
% 2.38/1.30  
% 2.38/1.30  %Background operators:
% 2.38/1.30  
% 2.38/1.30  
% 2.38/1.30  %Foreground operators:
% 2.38/1.30  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.38/1.30  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.38/1.30  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.38/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.38/1.30  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.38/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.38/1.30  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.38/1.30  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.38/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.38/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.38/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.38/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.38/1.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.38/1.30  
% 2.38/1.31  tff(f_80, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)) & (k2_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_funct_1)).
% 2.38/1.31  tff(f_35, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 2.38/1.31  tff(f_59, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 2.38/1.31  tff(f_69, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 2.38/1.31  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t160_relat_1)).
% 2.38/1.31  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.38/1.31  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_relat_1)).
% 2.38/1.31  tff(c_28, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.38/1.31  tff(c_8, plain, (![A_3]: (k9_relat_1(A_3, k1_relat_1(A_3))=k2_relat_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.38/1.31  tff(c_26, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.38/1.31  tff(c_16, plain, (![A_10]: (v1_relat_1(k2_funct_1(A_10)) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.38/1.31  tff(c_24, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.38/1.31  tff(c_18, plain, (![A_11]: (k2_relat_1(k2_funct_1(A_11))=k1_relat_1(A_11) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.38/1.31  tff(c_290, plain, (![B_36, A_37]: (k9_relat_1(B_36, k2_relat_1(A_37))=k2_relat_1(k5_relat_1(A_37, B_36)) | ~v1_relat_1(B_36) | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.38/1.31  tff(c_331, plain, (![A_41, B_42]: (k2_relat_1(k5_relat_1(k2_funct_1(A_41), B_42))=k9_relat_1(B_42, k1_relat_1(A_41)) | ~v1_relat_1(B_42) | ~v1_relat_1(k2_funct_1(A_41)) | ~v2_funct_1(A_41) | ~v1_funct_1(A_41) | ~v1_relat_1(A_41))), inference(superposition, [status(thm), theory('equality')], [c_18, c_290])).
% 2.38/1.31  tff(c_20, plain, (![A_11]: (k1_relat_1(k2_funct_1(A_11))=k2_relat_1(A_11) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.38/1.31  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.38/1.31  tff(c_83, plain, (![A_22, B_23]: (k1_relat_1(k5_relat_1(A_22, B_23))=k1_relat_1(A_22) | ~r1_tarski(k2_relat_1(A_22), k1_relat_1(B_23)) | ~v1_relat_1(B_23) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.38/1.31  tff(c_192, plain, (![A_31, B_32]: (k1_relat_1(k5_relat_1(k2_funct_1(A_31), B_32))=k1_relat_1(k2_funct_1(A_31)) | ~r1_tarski(k1_relat_1(A_31), k1_relat_1(B_32)) | ~v1_relat_1(B_32) | ~v1_relat_1(k2_funct_1(A_31)) | ~v2_funct_1(A_31) | ~v1_funct_1(A_31) | ~v1_relat_1(A_31))), inference(superposition, [status(thm), theory('equality')], [c_18, c_83])).
% 2.38/1.31  tff(c_210, plain, (![A_33]: (k1_relat_1(k5_relat_1(k2_funct_1(A_33), A_33))=k1_relat_1(k2_funct_1(A_33)) | ~v1_relat_1(k2_funct_1(A_33)) | ~v2_funct_1(A_33) | ~v1_funct_1(A_33) | ~v1_relat_1(A_33))), inference(resolution, [status(thm)], [c_6, c_192])).
% 2.38/1.31  tff(c_22, plain, (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1') | k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.38/1.31  tff(c_61, plain, (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_22])).
% 2.38/1.31  tff(c_225, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_210, c_61])).
% 2.38/1.31  tff(c_234, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_24, c_225])).
% 2.38/1.31  tff(c_236, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_234])).
% 2.38/1.31  tff(c_239, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_16, c_236])).
% 2.38/1.31  tff(c_243, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_239])).
% 2.38/1.31  tff(c_244, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_234])).
% 2.38/1.31  tff(c_266, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_20, c_244])).
% 2.38/1.31  tff(c_270, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_24, c_266])).
% 2.38/1.31  tff(c_271, plain, (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_22])).
% 2.38/1.31  tff(c_346, plain, (k9_relat_1('#skF_1', k1_relat_1('#skF_1'))!=k2_relat_1('#skF_1') | ~v1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_331, c_271])).
% 2.38/1.31  tff(c_352, plain, (k9_relat_1('#skF_1', k1_relat_1('#skF_1'))!=k2_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_24, c_28, c_346])).
% 2.38/1.31  tff(c_354, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_352])).
% 2.38/1.31  tff(c_357, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_16, c_354])).
% 2.38/1.31  tff(c_361, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_357])).
% 2.38/1.31  tff(c_362, plain, (k9_relat_1('#skF_1', k1_relat_1('#skF_1'))!=k2_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_352])).
% 2.38/1.31  tff(c_366, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_8, c_362])).
% 2.38/1.31  tff(c_370, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_366])).
% 2.38/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.38/1.31  
% 2.38/1.31  Inference rules
% 2.38/1.31  ----------------------
% 2.38/1.31  #Ref     : 0
% 2.38/1.31  #Sup     : 84
% 2.38/1.31  #Fact    : 0
% 2.38/1.31  #Define  : 0
% 2.38/1.31  #Split   : 4
% 2.38/1.31  #Chain   : 0
% 2.38/1.31  #Close   : 0
% 2.38/1.31  
% 2.38/1.31  Ordering : KBO
% 2.38/1.31  
% 2.38/1.31  Simplification rules
% 2.38/1.31  ----------------------
% 2.38/1.31  #Subsume      : 2
% 2.38/1.31  #Demod        : 17
% 2.38/1.31  #Tautology    : 32
% 2.38/1.31  #SimpNegUnit  : 0
% 2.38/1.31  #BackRed      : 0
% 2.38/1.31  
% 2.38/1.31  #Partial instantiations: 0
% 2.38/1.31  #Strategies tried      : 1
% 2.38/1.31  
% 2.38/1.31  Timing (in seconds)
% 2.38/1.31  ----------------------
% 2.38/1.31  Preprocessing        : 0.30
% 2.38/1.31  Parsing              : 0.16
% 2.38/1.31  CNF conversion       : 0.02
% 2.38/1.31  Main loop            : 0.26
% 2.38/1.31  Inferencing          : 0.10
% 2.38/1.31  Reduction            : 0.07
% 2.38/1.31  Demodulation         : 0.05
% 2.38/1.31  BG Simplification    : 0.02
% 2.38/1.31  Subsumption          : 0.06
% 2.38/1.32  Abstraction          : 0.02
% 2.38/1.32  MUC search           : 0.00
% 2.38/1.32  Cooper               : 0.00
% 2.38/1.32  Total                : 0.59
% 2.38/1.32  Index Insertion      : 0.00
% 2.38/1.32  Index Deletion       : 0.00
% 2.38/1.32  Index Matching       : 0.00
% 2.38/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
