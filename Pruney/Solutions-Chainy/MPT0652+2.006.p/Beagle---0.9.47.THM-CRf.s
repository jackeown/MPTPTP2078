%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:53 EST 2020

% Result     : Theorem 2.22s
% Output     : CNFRefutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :   47 (  93 expanded)
%              Number of leaves         :   20 (  43 expanded)
%              Depth                    :    8
%              Number of atoms          :  103 ( 246 expanded)
%              Number of equality atoms :   25 (  73 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1

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

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(f_82,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v2_funct_1(A)
         => ( k1_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A)
            & k2_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_funct_1)).

tff(f_61,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_71,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

tff(c_26,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_24,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_22,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_37,plain,(
    ! [A_16] :
      ( k4_relat_1(A_16) = k2_funct_1(A_16)
      | ~ v2_funct_1(A_16)
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_40,plain,
    ( k4_relat_1('#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_37])).

tff(c_43,plain,(
    k4_relat_1('#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_40])).

tff(c_8,plain,(
    ! [A_3] :
      ( v1_relat_1(k4_relat_1(A_3))
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_47,plain,
    ( v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_43,c_8])).

tff(c_51,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_47])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    ! [A_11] :
      ( k2_relat_1(k2_funct_1(A_11)) = k1_relat_1(A_11)
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_278,plain,(
    ! [B_37,A_38] :
      ( k2_relat_1(k5_relat_1(B_37,A_38)) = k2_relat_1(A_38)
      | ~ r1_tarski(k1_relat_1(A_38),k2_relat_1(B_37))
      | ~ v1_relat_1(B_37)
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_299,plain,(
    ! [A_41,A_42] :
      ( k2_relat_1(k5_relat_1(k2_funct_1(A_41),A_42)) = k2_relat_1(A_42)
      | ~ r1_tarski(k1_relat_1(A_42),k1_relat_1(A_41))
      | ~ v1_relat_1(k2_funct_1(A_41))
      | ~ v1_relat_1(A_42)
      | ~ v2_funct_1(A_41)
      | ~ v1_funct_1(A_41)
      | ~ v1_relat_1(A_41) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_278])).

tff(c_317,plain,(
    ! [A_43] :
      ( k2_relat_1(k5_relat_1(k2_funct_1(A_43),A_43)) = k2_relat_1(A_43)
      | ~ v1_relat_1(k2_funct_1(A_43))
      | ~ v2_funct_1(A_43)
      | ~ v1_funct_1(A_43)
      | ~ v1_relat_1(A_43) ) ),
    inference(resolution,[status(thm)],[c_6,c_299])).

tff(c_18,plain,(
    ! [A_11] :
      ( k1_relat_1(k2_funct_1(A_11)) = k2_relat_1(A_11)
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_72,plain,(
    ! [A_19,B_20] :
      ( k1_relat_1(k5_relat_1(A_19,B_20)) = k1_relat_1(A_19)
      | ~ r1_tarski(k2_relat_1(A_19),k1_relat_1(B_20))
      | ~ v1_relat_1(B_20)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_197,plain,(
    ! [A_32,B_33] :
      ( k1_relat_1(k5_relat_1(k2_funct_1(A_32),B_33)) = k1_relat_1(k2_funct_1(A_32))
      | ~ r1_tarski(k1_relat_1(A_32),k1_relat_1(B_33))
      | ~ v1_relat_1(B_33)
      | ~ v1_relat_1(k2_funct_1(A_32))
      | ~ v2_funct_1(A_32)
      | ~ v1_funct_1(A_32)
      | ~ v1_relat_1(A_32) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_72])).

tff(c_215,plain,(
    ! [A_34] :
      ( k1_relat_1(k5_relat_1(k2_funct_1(A_34),A_34)) = k1_relat_1(k2_funct_1(A_34))
      | ~ v1_relat_1(k2_funct_1(A_34))
      | ~ v2_funct_1(A_34)
      | ~ v1_funct_1(A_34)
      | ~ v1_relat_1(A_34) ) ),
    inference(resolution,[status(thm)],[c_6,c_197])).

tff(c_20,plain,
    ( k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1')
    | k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_53,plain,(
    k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_239,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_53])).

tff(c_245,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_22,c_51,c_239])).

tff(c_249,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_245])).

tff(c_253,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_22,c_249])).

tff(c_254,plain,(
    k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_329,plain,
    ( ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_317,c_254])).

tff(c_337,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_22,c_51,c_329])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:28:54 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.22/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.31  
% 2.22/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.31  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1
% 2.22/1.31  
% 2.22/1.31  %Foreground sorts:
% 2.22/1.31  
% 2.22/1.31  
% 2.22/1.31  %Background operators:
% 2.22/1.31  
% 2.22/1.31  
% 2.22/1.31  %Foreground operators:
% 2.22/1.31  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.22/1.31  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.22/1.31  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.22/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.22/1.31  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.22/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.22/1.31  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.22/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.22/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.22/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.22/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.22/1.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.22/1.31  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 2.22/1.31  
% 2.22/1.32  tff(f_82, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)) & (k2_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_funct_1)).
% 2.22/1.32  tff(f_61, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 2.22/1.32  tff(f_35, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 2.22/1.32  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.22/1.32  tff(f_71, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 2.22/1.32  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_relat_1)).
% 2.22/1.32  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_relat_1)).
% 2.22/1.32  tff(c_26, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.22/1.32  tff(c_24, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.22/1.32  tff(c_22, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.22/1.32  tff(c_37, plain, (![A_16]: (k4_relat_1(A_16)=k2_funct_1(A_16) | ~v2_funct_1(A_16) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.22/1.32  tff(c_40, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_22, c_37])).
% 2.22/1.32  tff(c_43, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_40])).
% 2.22/1.32  tff(c_8, plain, (![A_3]: (v1_relat_1(k4_relat_1(A_3)) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.22/1.32  tff(c_47, plain, (v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_43, c_8])).
% 2.22/1.32  tff(c_51, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_47])).
% 2.22/1.32  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.22/1.32  tff(c_16, plain, (![A_11]: (k2_relat_1(k2_funct_1(A_11))=k1_relat_1(A_11) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.22/1.32  tff(c_278, plain, (![B_37, A_38]: (k2_relat_1(k5_relat_1(B_37, A_38))=k2_relat_1(A_38) | ~r1_tarski(k1_relat_1(A_38), k2_relat_1(B_37)) | ~v1_relat_1(B_37) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.22/1.32  tff(c_299, plain, (![A_41, A_42]: (k2_relat_1(k5_relat_1(k2_funct_1(A_41), A_42))=k2_relat_1(A_42) | ~r1_tarski(k1_relat_1(A_42), k1_relat_1(A_41)) | ~v1_relat_1(k2_funct_1(A_41)) | ~v1_relat_1(A_42) | ~v2_funct_1(A_41) | ~v1_funct_1(A_41) | ~v1_relat_1(A_41))), inference(superposition, [status(thm), theory('equality')], [c_16, c_278])).
% 2.22/1.32  tff(c_317, plain, (![A_43]: (k2_relat_1(k5_relat_1(k2_funct_1(A_43), A_43))=k2_relat_1(A_43) | ~v1_relat_1(k2_funct_1(A_43)) | ~v2_funct_1(A_43) | ~v1_funct_1(A_43) | ~v1_relat_1(A_43))), inference(resolution, [status(thm)], [c_6, c_299])).
% 2.22/1.32  tff(c_18, plain, (![A_11]: (k1_relat_1(k2_funct_1(A_11))=k2_relat_1(A_11) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.22/1.32  tff(c_72, plain, (![A_19, B_20]: (k1_relat_1(k5_relat_1(A_19, B_20))=k1_relat_1(A_19) | ~r1_tarski(k2_relat_1(A_19), k1_relat_1(B_20)) | ~v1_relat_1(B_20) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.22/1.32  tff(c_197, plain, (![A_32, B_33]: (k1_relat_1(k5_relat_1(k2_funct_1(A_32), B_33))=k1_relat_1(k2_funct_1(A_32)) | ~r1_tarski(k1_relat_1(A_32), k1_relat_1(B_33)) | ~v1_relat_1(B_33) | ~v1_relat_1(k2_funct_1(A_32)) | ~v2_funct_1(A_32) | ~v1_funct_1(A_32) | ~v1_relat_1(A_32))), inference(superposition, [status(thm), theory('equality')], [c_16, c_72])).
% 2.22/1.32  tff(c_215, plain, (![A_34]: (k1_relat_1(k5_relat_1(k2_funct_1(A_34), A_34))=k1_relat_1(k2_funct_1(A_34)) | ~v1_relat_1(k2_funct_1(A_34)) | ~v2_funct_1(A_34) | ~v1_funct_1(A_34) | ~v1_relat_1(A_34))), inference(resolution, [status(thm)], [c_6, c_197])).
% 2.22/1.32  tff(c_20, plain, (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1') | k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.22/1.32  tff(c_53, plain, (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_20])).
% 2.22/1.32  tff(c_239, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_215, c_53])).
% 2.22/1.32  tff(c_245, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_22, c_51, c_239])).
% 2.22/1.32  tff(c_249, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_18, c_245])).
% 2.22/1.32  tff(c_253, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_22, c_249])).
% 2.22/1.32  tff(c_254, plain, (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_20])).
% 2.22/1.32  tff(c_329, plain, (~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_317, c_254])).
% 2.22/1.32  tff(c_337, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_22, c_51, c_329])).
% 2.22/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.32  
% 2.22/1.32  Inference rules
% 2.22/1.32  ----------------------
% 2.22/1.32  #Ref     : 0
% 2.22/1.32  #Sup     : 81
% 2.22/1.32  #Fact    : 0
% 2.22/1.32  #Define  : 0
% 2.22/1.32  #Split   : 2
% 2.22/1.32  #Chain   : 0
% 2.22/1.32  #Close   : 0
% 2.22/1.32  
% 2.22/1.32  Ordering : KBO
% 2.22/1.32  
% 2.22/1.32  Simplification rules
% 2.22/1.32  ----------------------
% 2.22/1.32  #Subsume      : 3
% 2.22/1.32  #Demod        : 16
% 2.22/1.32  #Tautology    : 23
% 2.22/1.32  #SimpNegUnit  : 0
% 2.22/1.32  #BackRed      : 0
% 2.22/1.32  
% 2.22/1.32  #Partial instantiations: 0
% 2.22/1.32  #Strategies tried      : 1
% 2.22/1.32  
% 2.22/1.32  Timing (in seconds)
% 2.22/1.32  ----------------------
% 2.22/1.33  Preprocessing        : 0.30
% 2.22/1.33  Parsing              : 0.16
% 2.22/1.33  CNF conversion       : 0.02
% 2.22/1.33  Main loop            : 0.26
% 2.22/1.33  Inferencing          : 0.09
% 2.22/1.33  Reduction            : 0.07
% 2.22/1.33  Demodulation         : 0.05
% 2.22/1.33  BG Simplification    : 0.02
% 2.22/1.33  Subsumption          : 0.06
% 2.22/1.33  Abstraction          : 0.02
% 2.22/1.33  MUC search           : 0.00
% 2.22/1.33  Cooper               : 0.00
% 2.22/1.33  Total                : 0.59
% 2.22/1.33  Index Insertion      : 0.00
% 2.22/1.33  Index Deletion       : 0.00
% 2.22/1.33  Index Matching       : 0.00
% 2.22/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
