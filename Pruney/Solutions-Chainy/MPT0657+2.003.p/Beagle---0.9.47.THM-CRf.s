%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:04 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.39s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 102 expanded)
%              Number of leaves         :   22 (  47 expanded)
%              Depth                    :   10
%              Number of atoms          :   96 ( 329 expanded)
%              Number of equality atoms :   30 ( 111 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(f_97,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ( ( v2_funct_1(A)
                & k2_relat_1(B) = k1_relat_1(A)
                & k5_relat_1(B,A) = k6_relat_1(k2_relat_1(A)) )
             => B = k2_funct_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_79,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_59,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_69,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

tff(c_26,plain,(
    k2_funct_1('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_40,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_38,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_32,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_36,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_30,plain,(
    k2_relat_1('#skF_2') = k1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_69,plain,(
    ! [B_23,A_24] :
      ( k5_relat_1(B_23,k6_relat_1(A_24)) = B_23
      | ~ r1_tarski(k2_relat_1(B_23),A_24)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_80,plain,(
    ! [B_25] :
      ( k5_relat_1(B_25,k6_relat_1(k2_relat_1(B_25))) = B_25
      | ~ v1_relat_1(B_25) ) ),
    inference(resolution,[status(thm)],[c_6,c_69])).

tff(c_92,plain,
    ( k5_relat_1('#skF_2',k6_relat_1(k1_relat_1('#skF_1'))) = '#skF_2'
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_80])).

tff(c_98,plain,(
    k5_relat_1('#skF_2',k6_relat_1(k1_relat_1('#skF_1'))) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_92])).

tff(c_24,plain,(
    ! [A_15] :
      ( k5_relat_1(A_15,k2_funct_1(A_15)) = k6_relat_1(k1_relat_1(A_15))
      | ~ v2_funct_1(A_15)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_16,plain,(
    ! [A_13] :
      ( v1_relat_1(k2_funct_1(A_13))
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_28,plain,(
    k6_relat_1(k2_relat_1('#skF_1')) = k5_relat_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_129,plain,(
    ! [A_28] :
      ( k1_relat_1(k2_funct_1(A_28)) = k2_relat_1(A_28)
      | ~ v2_funct_1(A_28)
      | ~ v1_funct_1(A_28)
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_10,plain,(
    ! [A_10] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_10)),A_10) = A_10
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_213,plain,(
    ! [A_34] :
      ( k5_relat_1(k6_relat_1(k2_relat_1(A_34)),k2_funct_1(A_34)) = k2_funct_1(A_34)
      | ~ v1_relat_1(k2_funct_1(A_34))
      | ~ v2_funct_1(A_34)
      | ~ v1_funct_1(A_34)
      | ~ v1_relat_1(A_34) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_10])).

tff(c_228,plain,
    ( k5_relat_1(k5_relat_1('#skF_2','#skF_1'),k2_funct_1('#skF_1')) = k2_funct_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_213])).

tff(c_235,plain,
    ( k5_relat_1(k5_relat_1('#skF_2','#skF_1'),k2_funct_1('#skF_1')) = k2_funct_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_32,c_228])).

tff(c_238,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_235])).

tff(c_241,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_238])).

tff(c_245,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_241])).

tff(c_247,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_235])).

tff(c_246,plain,(
    k5_relat_1(k5_relat_1('#skF_2','#skF_1'),k2_funct_1('#skF_1')) = k2_funct_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_235])).

tff(c_8,plain,(
    ! [A_3,B_7,C_9] :
      ( k5_relat_1(k5_relat_1(A_3,B_7),C_9) = k5_relat_1(A_3,k5_relat_1(B_7,C_9))
      | ~ v1_relat_1(C_9)
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_255,plain,
    ( k5_relat_1('#skF_2',k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k2_funct_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_246,c_8])).

tff(c_264,plain,(
    k5_relat_1('#skF_2',k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_40,c_247,c_255])).

tff(c_275,plain,
    ( k5_relat_1('#skF_2',k6_relat_1(k1_relat_1('#skF_1'))) = k2_funct_1('#skF_1')
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_264])).

tff(c_281,plain,(
    k2_funct_1('#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_32,c_98,c_275])).

tff(c_283,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_281])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:21:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.17/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.39/1.30  
% 2.39/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.39/1.30  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.39/1.30  
% 2.39/1.30  %Foreground sorts:
% 2.39/1.30  
% 2.39/1.30  
% 2.39/1.30  %Background operators:
% 2.39/1.30  
% 2.39/1.30  
% 2.39/1.30  %Foreground operators:
% 2.39/1.30  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.39/1.30  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.39/1.30  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.39/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.39/1.30  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.39/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.39/1.30  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.39/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.39/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.39/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.39/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.39/1.30  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.39/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.39/1.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.39/1.30  
% 2.39/1.32  tff(f_97, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_1)).
% 2.39/1.32  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.39/1.32  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 2.39/1.32  tff(f_79, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 2.39/1.32  tff(f_59, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 2.39/1.32  tff(f_69, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 2.39/1.32  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_relat_1)).
% 2.39/1.32  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 2.39/1.32  tff(c_26, plain, (k2_funct_1('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.39/1.32  tff(c_40, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.39/1.32  tff(c_38, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.39/1.32  tff(c_32, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.39/1.32  tff(c_36, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.39/1.32  tff(c_30, plain, (k2_relat_1('#skF_2')=k1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.39/1.32  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.39/1.32  tff(c_69, plain, (![B_23, A_24]: (k5_relat_1(B_23, k6_relat_1(A_24))=B_23 | ~r1_tarski(k2_relat_1(B_23), A_24) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.39/1.32  tff(c_80, plain, (![B_25]: (k5_relat_1(B_25, k6_relat_1(k2_relat_1(B_25)))=B_25 | ~v1_relat_1(B_25))), inference(resolution, [status(thm)], [c_6, c_69])).
% 2.39/1.32  tff(c_92, plain, (k5_relat_1('#skF_2', k6_relat_1(k1_relat_1('#skF_1')))='#skF_2' | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_30, c_80])).
% 2.39/1.32  tff(c_98, plain, (k5_relat_1('#skF_2', k6_relat_1(k1_relat_1('#skF_1')))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_92])).
% 2.39/1.32  tff(c_24, plain, (![A_15]: (k5_relat_1(A_15, k2_funct_1(A_15))=k6_relat_1(k1_relat_1(A_15)) | ~v2_funct_1(A_15) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.39/1.32  tff(c_16, plain, (![A_13]: (v1_relat_1(k2_funct_1(A_13)) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.39/1.32  tff(c_28, plain, (k6_relat_1(k2_relat_1('#skF_1'))=k5_relat_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.39/1.32  tff(c_129, plain, (![A_28]: (k1_relat_1(k2_funct_1(A_28))=k2_relat_1(A_28) | ~v2_funct_1(A_28) | ~v1_funct_1(A_28) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.39/1.32  tff(c_10, plain, (![A_10]: (k5_relat_1(k6_relat_1(k1_relat_1(A_10)), A_10)=A_10 | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.39/1.32  tff(c_213, plain, (![A_34]: (k5_relat_1(k6_relat_1(k2_relat_1(A_34)), k2_funct_1(A_34))=k2_funct_1(A_34) | ~v1_relat_1(k2_funct_1(A_34)) | ~v2_funct_1(A_34) | ~v1_funct_1(A_34) | ~v1_relat_1(A_34))), inference(superposition, [status(thm), theory('equality')], [c_129, c_10])).
% 2.39/1.32  tff(c_228, plain, (k5_relat_1(k5_relat_1('#skF_2', '#skF_1'), k2_funct_1('#skF_1'))=k2_funct_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_28, c_213])).
% 2.39/1.32  tff(c_235, plain, (k5_relat_1(k5_relat_1('#skF_2', '#skF_1'), k2_funct_1('#skF_1'))=k2_funct_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_32, c_228])).
% 2.39/1.32  tff(c_238, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_235])).
% 2.39/1.32  tff(c_241, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_16, c_238])).
% 2.39/1.32  tff(c_245, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_241])).
% 2.39/1.32  tff(c_247, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_235])).
% 2.39/1.32  tff(c_246, plain, (k5_relat_1(k5_relat_1('#skF_2', '#skF_1'), k2_funct_1('#skF_1'))=k2_funct_1('#skF_1')), inference(splitRight, [status(thm)], [c_235])).
% 2.39/1.32  tff(c_8, plain, (![A_3, B_7, C_9]: (k5_relat_1(k5_relat_1(A_3, B_7), C_9)=k5_relat_1(A_3, k5_relat_1(B_7, C_9)) | ~v1_relat_1(C_9) | ~v1_relat_1(B_7) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.39/1.32  tff(c_255, plain, (k5_relat_1('#skF_2', k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k2_funct_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_246, c_8])).
% 2.39/1.32  tff(c_264, plain, (k5_relat_1('#skF_2', k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_40, c_247, c_255])).
% 2.39/1.32  tff(c_275, plain, (k5_relat_1('#skF_2', k6_relat_1(k1_relat_1('#skF_1')))=k2_funct_1('#skF_1') | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_24, c_264])).
% 2.39/1.32  tff(c_281, plain, (k2_funct_1('#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_32, c_98, c_275])).
% 2.39/1.32  tff(c_283, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_281])).
% 2.39/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.39/1.32  
% 2.39/1.32  Inference rules
% 2.39/1.32  ----------------------
% 2.39/1.32  #Ref     : 0
% 2.39/1.32  #Sup     : 59
% 2.39/1.32  #Fact    : 0
% 2.39/1.32  #Define  : 0
% 2.39/1.32  #Split   : 3
% 2.39/1.32  #Chain   : 0
% 2.39/1.32  #Close   : 0
% 2.39/1.32  
% 2.39/1.32  Ordering : KBO
% 2.39/1.32  
% 2.39/1.32  Simplification rules
% 2.39/1.32  ----------------------
% 2.39/1.32  #Subsume      : 0
% 2.39/1.32  #Demod        : 27
% 2.39/1.32  #Tautology    : 31
% 2.39/1.32  #SimpNegUnit  : 1
% 2.39/1.32  #BackRed      : 0
% 2.39/1.32  
% 2.39/1.32  #Partial instantiations: 0
% 2.39/1.32  #Strategies tried      : 1
% 2.39/1.32  
% 2.39/1.32  Timing (in seconds)
% 2.39/1.32  ----------------------
% 2.39/1.32  Preprocessing        : 0.32
% 2.39/1.32  Parsing              : 0.16
% 2.39/1.32  CNF conversion       : 0.02
% 2.39/1.32  Main loop            : 0.22
% 2.39/1.32  Inferencing          : 0.08
% 2.39/1.32  Reduction            : 0.07
% 2.39/1.32  Demodulation         : 0.05
% 2.39/1.32  BG Simplification    : 0.02
% 2.39/1.32  Subsumption          : 0.04
% 2.39/1.32  Abstraction          : 0.01
% 2.39/1.32  MUC search           : 0.00
% 2.39/1.32  Cooper               : 0.00
% 2.39/1.32  Total                : 0.57
% 2.39/1.32  Index Insertion      : 0.00
% 2.39/1.32  Index Deletion       : 0.00
% 2.39/1.32  Index Matching       : 0.00
% 2.39/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
