%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:59 EST 2020

% Result     : Theorem 2.00s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   45 (  99 expanded)
%              Number of leaves         :   20 (  45 expanded)
%              Depth                    :    9
%              Number of atoms          :   98 ( 266 expanded)
%              Number of equality atoms :   17 (  34 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(f_87,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v2_funct_1(A)
         => v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_1)).

tff(f_47,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_39,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_78,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_68,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(k5_relat_1(B,A))
              & k2_relat_1(B) = k1_relat_1(A) )
           => ( v2_funct_1(B)
              & v2_funct_1(A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).

tff(c_30,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_28,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_8,plain,(
    ! [A_3] :
      ( v1_funct_1(k2_funct_1(A_3))
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_10,plain,(
    ! [A_3] :
      ( v1_relat_1(k2_funct_1(A_3))
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_26,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_53,plain,(
    ! [A_15] :
      ( k4_relat_1(A_15) = k2_funct_1(A_15)
      | ~ v2_funct_1(A_15)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_59,plain,
    ( k4_relat_1('#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_53])).

tff(c_65,plain,(
    k4_relat_1('#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_59])).

tff(c_2,plain,(
    ! [A_1] :
      ( k2_relat_1(k4_relat_1(A_1)) = k1_relat_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_69,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_2])).

tff(c_76,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_69])).

tff(c_14,plain,(
    ! [A_4] : v2_funct_1(k6_relat_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_20,plain,(
    ! [A_8] :
      ( k5_relat_1(k2_funct_1(A_8),A_8) = k6_relat_1(k2_relat_1(A_8))
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_107,plain,(
    ! [B_19,A_20] :
      ( v2_funct_1(B_19)
      | k2_relat_1(B_19) != k1_relat_1(A_20)
      | ~ v2_funct_1(k5_relat_1(B_19,A_20))
      | ~ v1_funct_1(B_19)
      | ~ v1_relat_1(B_19)
      | ~ v1_funct_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_113,plain,(
    ! [A_8] :
      ( v2_funct_1(k2_funct_1(A_8))
      | k2_relat_1(k2_funct_1(A_8)) != k1_relat_1(A_8)
      | ~ v2_funct_1(k6_relat_1(k2_relat_1(A_8)))
      | ~ v1_funct_1(k2_funct_1(A_8))
      | ~ v1_relat_1(k2_funct_1(A_8))
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8)
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_107])).

tff(c_129,plain,(
    ! [A_23] :
      ( v2_funct_1(k2_funct_1(A_23))
      | k2_relat_1(k2_funct_1(A_23)) != k1_relat_1(A_23)
      | ~ v1_funct_1(k2_funct_1(A_23))
      | ~ v1_relat_1(k2_funct_1(A_23))
      | ~ v2_funct_1(A_23)
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_113])).

tff(c_24,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_135,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_129,c_24])).

tff(c_139,plain,
    ( ~ v1_funct_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_76,c_135])).

tff(c_140,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_139])).

tff(c_143,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_140])).

tff(c_147,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_143])).

tff(c_148,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_139])).

tff(c_152,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_148])).

tff(c_156,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_152])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:52:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.00/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.22  
% 2.00/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.23  %$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1
% 2.00/1.23  
% 2.00/1.23  %Foreground sorts:
% 2.00/1.23  
% 2.00/1.23  
% 2.00/1.23  %Background operators:
% 2.00/1.23  
% 2.00/1.23  
% 2.00/1.23  %Foreground operators:
% 2.00/1.23  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.00/1.23  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.00/1.23  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.00/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.00/1.23  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.00/1.23  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.00/1.23  tff('#skF_1', type, '#skF_1': $i).
% 2.00/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.00/1.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.00/1.23  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.00/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.00/1.23  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.00/1.23  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 2.00/1.23  
% 2.10/1.24  tff(f_87, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_funct_1)).
% 2.10/1.24  tff(f_47, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 2.10/1.24  tff(f_39, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 2.10/1.24  tff(f_31, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_relat_1)).
% 2.10/1.24  tff(f_51, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 2.10/1.24  tff(f_78, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 2.10/1.24  tff(f_68, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & (k2_relat_1(B) = k1_relat_1(A))) => (v2_funct_1(B) & v2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_funct_1)).
% 2.10/1.24  tff(c_30, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.10/1.24  tff(c_28, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.10/1.24  tff(c_8, plain, (![A_3]: (v1_funct_1(k2_funct_1(A_3)) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.10/1.24  tff(c_10, plain, (![A_3]: (v1_relat_1(k2_funct_1(A_3)) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.10/1.24  tff(c_26, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.10/1.24  tff(c_53, plain, (![A_15]: (k4_relat_1(A_15)=k2_funct_1(A_15) | ~v2_funct_1(A_15) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.10/1.24  tff(c_59, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_26, c_53])).
% 2.10/1.24  tff(c_65, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_59])).
% 2.10/1.24  tff(c_2, plain, (![A_1]: (k2_relat_1(k4_relat_1(A_1))=k1_relat_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.10/1.24  tff(c_69, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_65, c_2])).
% 2.10/1.24  tff(c_76, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_69])).
% 2.10/1.24  tff(c_14, plain, (![A_4]: (v2_funct_1(k6_relat_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.10/1.24  tff(c_20, plain, (![A_8]: (k5_relat_1(k2_funct_1(A_8), A_8)=k6_relat_1(k2_relat_1(A_8)) | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.10/1.24  tff(c_107, plain, (![B_19, A_20]: (v2_funct_1(B_19) | k2_relat_1(B_19)!=k1_relat_1(A_20) | ~v2_funct_1(k5_relat_1(B_19, A_20)) | ~v1_funct_1(B_19) | ~v1_relat_1(B_19) | ~v1_funct_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.10/1.24  tff(c_113, plain, (![A_8]: (v2_funct_1(k2_funct_1(A_8)) | k2_relat_1(k2_funct_1(A_8))!=k1_relat_1(A_8) | ~v2_funct_1(k6_relat_1(k2_relat_1(A_8))) | ~v1_funct_1(k2_funct_1(A_8)) | ~v1_relat_1(k2_funct_1(A_8)) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8) | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(superposition, [status(thm), theory('equality')], [c_20, c_107])).
% 2.10/1.24  tff(c_129, plain, (![A_23]: (v2_funct_1(k2_funct_1(A_23)) | k2_relat_1(k2_funct_1(A_23))!=k1_relat_1(A_23) | ~v1_funct_1(k2_funct_1(A_23)) | ~v1_relat_1(k2_funct_1(A_23)) | ~v2_funct_1(A_23) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_113])).
% 2.10/1.24  tff(c_24, plain, (~v2_funct_1(k2_funct_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.10/1.24  tff(c_135, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1') | ~v1_funct_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_129, c_24])).
% 2.10/1.24  tff(c_139, plain, (~v1_funct_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_76, c_135])).
% 2.10/1.24  tff(c_140, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_139])).
% 2.10/1.24  tff(c_143, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_10, c_140])).
% 2.10/1.24  tff(c_147, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_143])).
% 2.10/1.24  tff(c_148, plain, (~v1_funct_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_139])).
% 2.10/1.24  tff(c_152, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_8, c_148])).
% 2.10/1.24  tff(c_156, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_152])).
% 2.10/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.24  
% 2.10/1.24  Inference rules
% 2.10/1.24  ----------------------
% 2.10/1.24  #Ref     : 0
% 2.10/1.24  #Sup     : 26
% 2.10/1.24  #Fact    : 0
% 2.10/1.24  #Define  : 0
% 2.10/1.24  #Split   : 1
% 2.10/1.24  #Chain   : 0
% 2.10/1.24  #Close   : 0
% 2.10/1.24  
% 2.10/1.24  Ordering : KBO
% 2.10/1.24  
% 2.10/1.24  Simplification rules
% 2.10/1.24  ----------------------
% 2.10/1.24  #Subsume      : 0
% 2.10/1.24  #Demod        : 17
% 2.10/1.24  #Tautology    : 16
% 2.10/1.24  #SimpNegUnit  : 0
% 2.10/1.24  #BackRed      : 0
% 2.10/1.24  
% 2.10/1.24  #Partial instantiations: 0
% 2.10/1.24  #Strategies tried      : 1
% 2.10/1.24  
% 2.10/1.24  Timing (in seconds)
% 2.10/1.24  ----------------------
% 2.10/1.24  Preprocessing        : 0.29
% 2.10/1.24  Parsing              : 0.15
% 2.10/1.24  CNF conversion       : 0.02
% 2.10/1.24  Main loop            : 0.15
% 2.10/1.24  Inferencing          : 0.06
% 2.10/1.24  Reduction            : 0.04
% 2.10/1.24  Demodulation         : 0.03
% 2.10/1.24  BG Simplification    : 0.01
% 2.10/1.24  Subsumption          : 0.02
% 2.10/1.24  Abstraction          : 0.01
% 2.10/1.24  MUC search           : 0.00
% 2.10/1.24  Cooper               : 0.00
% 2.10/1.24  Total                : 0.47
% 2.10/1.24  Index Insertion      : 0.00
% 2.10/1.24  Index Deletion       : 0.00
% 2.10/1.24  Index Matching       : 0.00
% 2.10/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
