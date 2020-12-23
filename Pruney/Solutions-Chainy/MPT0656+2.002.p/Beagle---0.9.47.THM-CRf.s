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
% DateTime   : Thu Dec  3 10:04:00 EST 2020

% Result     : Theorem 3.10s
% Output     : CNFRefutation 3.10s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 101 expanded)
%              Number of leaves         :   22 (  47 expanded)
%              Depth                    :    9
%              Number of atoms          :  103 ( 336 expanded)
%              Number of equality atoms :   29 ( 110 expanded)
%              Maximal formula depth    :   10 (   4 average)
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
                & k2_relat_1(A) = k1_relat_1(B)
                & k5_relat_1(A,B) = k6_relat_1(k1_relat_1(A)) )
             => B = k2_funct_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_funct_1)).

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

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_79,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

tff(c_26,plain,(
    k2_funct_1('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_36,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_40,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_38,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_16,plain,(
    ! [A_13] :
      ( v1_relat_1(k2_funct_1(A_13))
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_32,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_28,plain,(
    k6_relat_1(k1_relat_1('#skF_1')) = k5_relat_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_78,plain,(
    ! [A_23] :
      ( k2_relat_1(k2_funct_1(A_23)) = k1_relat_1(A_23)
      | ~ v2_funct_1(A_23)
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_12,plain,(
    ! [A_12] :
      ( k5_relat_1(A_12,k6_relat_1(k2_relat_1(A_12))) = A_12
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_221,plain,(
    ! [A_33] :
      ( k5_relat_1(k2_funct_1(A_33),k6_relat_1(k1_relat_1(A_33))) = k2_funct_1(A_33)
      | ~ v1_relat_1(k2_funct_1(A_33))
      | ~ v2_funct_1(A_33)
      | ~ v1_funct_1(A_33)
      | ~ v1_relat_1(A_33) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_12])).

tff(c_236,plain,
    ( k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1','#skF_2')) = k2_funct_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_221])).

tff(c_240,plain,
    ( k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1','#skF_2')) = k2_funct_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_32,c_236])).

tff(c_241,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_240])).

tff(c_244,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_241])).

tff(c_248,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_244])).

tff(c_249,plain,(
    k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1','#skF_2')) = k2_funct_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_240])).

tff(c_250,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_240])).

tff(c_30,plain,(
    k2_relat_1('#skF_1') = k1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_22,plain,(
    ! [A_15] :
      ( k5_relat_1(k2_funct_1(A_15),A_15) = k6_relat_1(k2_relat_1(A_15))
      | ~ v2_funct_1(A_15)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_147,plain,(
    ! [A_30,B_31,C_32] :
      ( k5_relat_1(k5_relat_1(A_30,B_31),C_32) = k5_relat_1(A_30,k5_relat_1(B_31,C_32))
      | ~ v1_relat_1(C_32)
      | ~ v1_relat_1(B_31)
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_634,plain,(
    ! [A_44,C_45] :
      ( k5_relat_1(k6_relat_1(k2_relat_1(A_44)),C_45) = k5_relat_1(k2_funct_1(A_44),k5_relat_1(A_44,C_45))
      | ~ v1_relat_1(C_45)
      | ~ v1_relat_1(A_44)
      | ~ v1_relat_1(k2_funct_1(A_44))
      | ~ v2_funct_1(A_44)
      | ~ v1_funct_1(A_44)
      | ~ v1_relat_1(A_44) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_147])).

tff(c_771,plain,(
    ! [C_45] :
      ( k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')),C_45) = k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1',C_45))
      | ~ v1_relat_1(C_45)
      | ~ v1_relat_1('#skF_1')
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v2_funct_1('#skF_1')
      | ~ v1_funct_1('#skF_1')
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_634])).

tff(c_842,plain,(
    ! [C_47] :
      ( k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')),C_47) = k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1',C_47))
      | ~ v1_relat_1(C_47) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_32,c_250,c_40,c_771])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_99,plain,(
    ! [A_25,B_26] :
      ( k5_relat_1(k6_relat_1(A_25),B_26) = B_26
      | ~ r1_tarski(k1_relat_1(B_26),A_25)
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_107,plain,(
    ! [B_26] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(B_26)),B_26) = B_26
      | ~ v1_relat_1(B_26) ) ),
    inference(resolution,[status(thm)],[c_6,c_99])).

tff(c_884,plain,
    ( k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1','#skF_2')) = '#skF_2'
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_842,c_107])).

tff(c_935,plain,(
    k2_funct_1('#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_36,c_249,c_884])).

tff(c_937,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_935])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:51:39 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.10/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.10/1.50  
% 3.10/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.10/1.51  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1
% 3.10/1.51  
% 3.10/1.51  %Foreground sorts:
% 3.10/1.51  
% 3.10/1.51  
% 3.10/1.51  %Background operators:
% 3.10/1.51  
% 3.10/1.51  
% 3.10/1.51  %Foreground operators:
% 3.10/1.51  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.10/1.51  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.10/1.51  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.10/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.10/1.51  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.10/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.10/1.51  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.10/1.51  tff('#skF_2', type, '#skF_2': $i).
% 3.10/1.51  tff('#skF_1', type, '#skF_1': $i).
% 3.10/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.10/1.51  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.10/1.51  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.10/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.10/1.51  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.10/1.51  
% 3.10/1.52  tff(f_97, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(A) = k1_relat_1(B))) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_funct_1)).
% 3.10/1.52  tff(f_59, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 3.10/1.52  tff(f_69, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 3.10/1.52  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 3.10/1.52  tff(f_79, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 3.10/1.52  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 3.10/1.52  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.10/1.52  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_relat_1)).
% 3.10/1.52  tff(c_26, plain, (k2_funct_1('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.10/1.52  tff(c_36, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.10/1.52  tff(c_40, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.10/1.52  tff(c_38, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.10/1.52  tff(c_16, plain, (![A_13]: (v1_relat_1(k2_funct_1(A_13)) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.10/1.52  tff(c_32, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.10/1.52  tff(c_28, plain, (k6_relat_1(k1_relat_1('#skF_1'))=k5_relat_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.10/1.52  tff(c_78, plain, (![A_23]: (k2_relat_1(k2_funct_1(A_23))=k1_relat_1(A_23) | ~v2_funct_1(A_23) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.10/1.52  tff(c_12, plain, (![A_12]: (k5_relat_1(A_12, k6_relat_1(k2_relat_1(A_12)))=A_12 | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.10/1.52  tff(c_221, plain, (![A_33]: (k5_relat_1(k2_funct_1(A_33), k6_relat_1(k1_relat_1(A_33)))=k2_funct_1(A_33) | ~v1_relat_1(k2_funct_1(A_33)) | ~v2_funct_1(A_33) | ~v1_funct_1(A_33) | ~v1_relat_1(A_33))), inference(superposition, [status(thm), theory('equality')], [c_78, c_12])).
% 3.10/1.52  tff(c_236, plain, (k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', '#skF_2'))=k2_funct_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_28, c_221])).
% 3.10/1.52  tff(c_240, plain, (k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', '#skF_2'))=k2_funct_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_32, c_236])).
% 3.10/1.52  tff(c_241, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_240])).
% 3.10/1.52  tff(c_244, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_16, c_241])).
% 3.10/1.52  tff(c_248, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_244])).
% 3.10/1.52  tff(c_249, plain, (k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', '#skF_2'))=k2_funct_1('#skF_1')), inference(splitRight, [status(thm)], [c_240])).
% 3.10/1.52  tff(c_250, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_240])).
% 3.10/1.52  tff(c_30, plain, (k2_relat_1('#skF_1')=k1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.10/1.52  tff(c_22, plain, (![A_15]: (k5_relat_1(k2_funct_1(A_15), A_15)=k6_relat_1(k2_relat_1(A_15)) | ~v2_funct_1(A_15) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.10/1.52  tff(c_147, plain, (![A_30, B_31, C_32]: (k5_relat_1(k5_relat_1(A_30, B_31), C_32)=k5_relat_1(A_30, k5_relat_1(B_31, C_32)) | ~v1_relat_1(C_32) | ~v1_relat_1(B_31) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.10/1.52  tff(c_634, plain, (![A_44, C_45]: (k5_relat_1(k6_relat_1(k2_relat_1(A_44)), C_45)=k5_relat_1(k2_funct_1(A_44), k5_relat_1(A_44, C_45)) | ~v1_relat_1(C_45) | ~v1_relat_1(A_44) | ~v1_relat_1(k2_funct_1(A_44)) | ~v2_funct_1(A_44) | ~v1_funct_1(A_44) | ~v1_relat_1(A_44))), inference(superposition, [status(thm), theory('equality')], [c_22, c_147])).
% 3.10/1.52  tff(c_771, plain, (![C_45]: (k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')), C_45)=k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', C_45)) | ~v1_relat_1(C_45) | ~v1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_30, c_634])).
% 3.10/1.52  tff(c_842, plain, (![C_47]: (k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')), C_47)=k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', C_47)) | ~v1_relat_1(C_47))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_32, c_250, c_40, c_771])).
% 3.10/1.52  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.10/1.52  tff(c_99, plain, (![A_25, B_26]: (k5_relat_1(k6_relat_1(A_25), B_26)=B_26 | ~r1_tarski(k1_relat_1(B_26), A_25) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.10/1.52  tff(c_107, plain, (![B_26]: (k5_relat_1(k6_relat_1(k1_relat_1(B_26)), B_26)=B_26 | ~v1_relat_1(B_26))), inference(resolution, [status(thm)], [c_6, c_99])).
% 3.10/1.52  tff(c_884, plain, (k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', '#skF_2'))='#skF_2' | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_842, c_107])).
% 3.10/1.52  tff(c_935, plain, (k2_funct_1('#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_36, c_249, c_884])).
% 3.10/1.52  tff(c_937, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_935])).
% 3.10/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.10/1.52  
% 3.10/1.52  Inference rules
% 3.10/1.52  ----------------------
% 3.10/1.52  #Ref     : 0
% 3.10/1.52  #Sup     : 224
% 3.10/1.52  #Fact    : 0
% 3.10/1.52  #Define  : 0
% 3.10/1.52  #Split   : 5
% 3.10/1.52  #Chain   : 0
% 3.10/1.52  #Close   : 0
% 3.10/1.52  
% 3.10/1.52  Ordering : KBO
% 3.10/1.52  
% 3.10/1.52  Simplification rules
% 3.10/1.52  ----------------------
% 3.10/1.52  #Subsume      : 22
% 3.10/1.52  #Demod        : 123
% 3.10/1.52  #Tautology    : 61
% 3.10/1.52  #SimpNegUnit  : 1
% 3.10/1.52  #BackRed      : 0
% 3.10/1.52  
% 3.10/1.52  #Partial instantiations: 0
% 3.10/1.52  #Strategies tried      : 1
% 3.10/1.52  
% 3.10/1.52  Timing (in seconds)
% 3.10/1.52  ----------------------
% 3.10/1.52  Preprocessing        : 0.31
% 3.10/1.52  Parsing              : 0.17
% 3.10/1.52  CNF conversion       : 0.02
% 3.10/1.52  Main loop            : 0.44
% 3.10/1.52  Inferencing          : 0.17
% 3.10/1.52  Reduction            : 0.13
% 3.10/1.52  Demodulation         : 0.10
% 3.10/1.52  BG Simplification    : 0.03
% 3.10/1.52  Subsumption          : 0.09
% 3.10/1.52  Abstraction          : 0.02
% 3.10/1.52  MUC search           : 0.00
% 3.10/1.52  Cooper               : 0.00
% 3.10/1.52  Total                : 0.79
% 3.10/1.52  Index Insertion      : 0.00
% 3.10/1.52  Index Deletion       : 0.00
% 3.10/1.52  Index Matching       : 0.00
% 3.10/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
