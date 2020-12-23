%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:02 EST 2020

% Result     : Theorem 2.46s
% Output     : CNFRefutation 2.46s
% Verified   : 
% Statistics : Number of formulae       :   48 (  94 expanded)
%              Number of leaves         :   20 (  46 expanded)
%              Depth                    :   11
%              Number of atoms          :  133 ( 359 expanded)
%              Number of equality atoms :   38 ( 114 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(f_103,negated_conjecture,(
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

tff(f_85,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_33,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_43,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k4_relat_1(A))
        & v1_funct_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_funct_1)).

tff(f_75,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ! [D] :
              ( ( v1_relat_1(D)
                & v1_funct_1(D) )
             => ( ( k2_relat_1(B) = A
                  & k5_relat_1(B,C) = k6_relat_1(k1_relat_1(D))
                  & k5_relat_1(C,D) = k6_relat_1(A) )
               => D = B ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l72_funct_1)).

tff(c_32,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_30,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_24,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_22,plain,(
    k2_relat_1('#skF_1') = k1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_14,plain,(
    ! [A_12] :
      ( k5_relat_1(k2_funct_1(A_12),A_12) = k6_relat_1(k2_relat_1(A_12))
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_18,plain,(
    k2_funct_1('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_28,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_26,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_43,plain,(
    ! [A_16] :
      ( k4_relat_1(A_16) = k2_funct_1(A_16)
      | ~ v2_funct_1(A_16)
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_46,plain,
    ( k4_relat_1('#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_43])).

tff(c_49,plain,(
    k4_relat_1('#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_46])).

tff(c_6,plain,(
    ! [A_2] :
      ( v1_relat_1(k4_relat_1(A_2))
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_56,plain,
    ( v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_6])).

tff(c_62,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_24,c_56])).

tff(c_4,plain,(
    ! [A_2] :
      ( v1_funct_1(k4_relat_1(A_2))
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_53,plain,
    ( v1_funct_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_4])).

tff(c_60,plain,(
    v1_funct_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_24,c_53])).

tff(c_20,plain,(
    k6_relat_1(k1_relat_1('#skF_1')) = k5_relat_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_10,plain,(
    ! [A_11] :
      ( k2_relat_1(k2_funct_1(A_11)) = k1_relat_1(A_11)
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_100,plain,(
    ! [D_21,B_22,C_23] :
      ( D_21 = B_22
      | k6_relat_1(k2_relat_1(B_22)) != k5_relat_1(C_23,D_21)
      | k6_relat_1(k1_relat_1(D_21)) != k5_relat_1(B_22,C_23)
      | ~ v1_funct_1(D_21)
      | ~ v1_relat_1(D_21)
      | ~ v1_funct_1(C_23)
      | ~ v1_relat_1(C_23)
      | ~ v1_funct_1(B_22)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_136,plain,(
    ! [A_30,D_31,C_32] :
      ( k2_funct_1(A_30) = D_31
      | k6_relat_1(k1_relat_1(A_30)) != k5_relat_1(C_32,D_31)
      | k6_relat_1(k1_relat_1(D_31)) != k5_relat_1(k2_funct_1(A_30),C_32)
      | ~ v1_funct_1(D_31)
      | ~ v1_relat_1(D_31)
      | ~ v1_funct_1(C_32)
      | ~ v1_relat_1(C_32)
      | ~ v1_funct_1(k2_funct_1(A_30))
      | ~ v1_relat_1(k2_funct_1(A_30))
      | ~ v2_funct_1(A_30)
      | ~ v1_funct_1(A_30)
      | ~ v1_relat_1(A_30) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_100])).

tff(c_144,plain,(
    ! [D_31,C_32] :
      ( k2_funct_1('#skF_1') = D_31
      | k5_relat_1(C_32,D_31) != k5_relat_1('#skF_1','#skF_2')
      | k6_relat_1(k1_relat_1(D_31)) != k5_relat_1(k2_funct_1('#skF_1'),C_32)
      | ~ v1_funct_1(D_31)
      | ~ v1_relat_1(D_31)
      | ~ v1_funct_1(C_32)
      | ~ v1_relat_1(C_32)
      | ~ v1_funct_1(k2_funct_1('#skF_1'))
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v2_funct_1('#skF_1')
      | ~ v1_funct_1('#skF_1')
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_136])).

tff(c_146,plain,(
    ! [D_31,C_32] :
      ( k2_funct_1('#skF_1') = D_31
      | k5_relat_1(C_32,D_31) != k5_relat_1('#skF_1','#skF_2')
      | k6_relat_1(k1_relat_1(D_31)) != k5_relat_1(k2_funct_1('#skF_1'),C_32)
      | ~ v1_funct_1(D_31)
      | ~ v1_relat_1(D_31)
      | ~ v1_funct_1(C_32)
      | ~ v1_relat_1(C_32) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_24,c_62,c_60,c_144])).

tff(c_149,plain,
    ( k2_funct_1('#skF_1') = '#skF_2'
    | k5_relat_1(k2_funct_1('#skF_1'),'#skF_1') != k6_relat_1(k1_relat_1('#skF_2'))
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_146])).

tff(c_151,plain,
    ( k2_funct_1('#skF_1') = '#skF_2'
    | k5_relat_1(k2_funct_1('#skF_1'),'#skF_1') != k6_relat_1(k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_26,c_149])).

tff(c_152,plain,(
    k5_relat_1(k2_funct_1('#skF_1'),'#skF_1') != k6_relat_1(k1_relat_1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_151])).

tff(c_169,plain,
    ( k6_relat_1(k2_relat_1('#skF_1')) != k6_relat_1(k1_relat_1('#skF_2'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_152])).

tff(c_172,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_24,c_22,c_169])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:35:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.46/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.46/1.38  
% 2.46/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.46/1.38  %$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.46/1.38  
% 2.46/1.38  %Foreground sorts:
% 2.46/1.38  
% 2.46/1.38  
% 2.46/1.38  %Background operators:
% 2.46/1.38  
% 2.46/1.38  
% 2.46/1.38  %Foreground operators:
% 2.46/1.38  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.46/1.38  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.46/1.38  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.46/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.46/1.38  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.46/1.38  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.46/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.46/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.46/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.46/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.46/1.38  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.46/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.46/1.38  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.46/1.38  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 2.46/1.38  
% 2.46/1.40  tff(f_103, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(A) = k1_relat_1(B))) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_funct_1)).
% 2.46/1.40  tff(f_85, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 2.46/1.40  tff(f_33, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 2.46/1.40  tff(f_43, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => (v1_relat_1(k4_relat_1(A)) & v1_funct_1(k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_funct_1)).
% 2.46/1.40  tff(f_75, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 2.46/1.40  tff(f_65, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (![D]: ((v1_relat_1(D) & v1_funct_1(D)) => ((((k2_relat_1(B) = A) & (k5_relat_1(B, C) = k6_relat_1(k1_relat_1(D)))) & (k5_relat_1(C, D) = k6_relat_1(A))) => (D = B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l72_funct_1)).
% 2.46/1.40  tff(c_32, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.46/1.40  tff(c_30, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.46/1.40  tff(c_24, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.46/1.40  tff(c_22, plain, (k2_relat_1('#skF_1')=k1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.46/1.40  tff(c_14, plain, (![A_12]: (k5_relat_1(k2_funct_1(A_12), A_12)=k6_relat_1(k2_relat_1(A_12)) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.46/1.40  tff(c_18, plain, (k2_funct_1('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.46/1.40  tff(c_28, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.46/1.40  tff(c_26, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.46/1.40  tff(c_43, plain, (![A_16]: (k4_relat_1(A_16)=k2_funct_1(A_16) | ~v2_funct_1(A_16) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.46/1.40  tff(c_46, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_24, c_43])).
% 2.46/1.40  tff(c_49, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_46])).
% 2.46/1.40  tff(c_6, plain, (![A_2]: (v1_relat_1(k4_relat_1(A_2)) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.46/1.40  tff(c_56, plain, (v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_49, c_6])).
% 2.46/1.40  tff(c_62, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_24, c_56])).
% 2.46/1.40  tff(c_4, plain, (![A_2]: (v1_funct_1(k4_relat_1(A_2)) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.46/1.40  tff(c_53, plain, (v1_funct_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_49, c_4])).
% 2.46/1.40  tff(c_60, plain, (v1_funct_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_24, c_53])).
% 2.46/1.40  tff(c_20, plain, (k6_relat_1(k1_relat_1('#skF_1'))=k5_relat_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.46/1.40  tff(c_10, plain, (![A_11]: (k2_relat_1(k2_funct_1(A_11))=k1_relat_1(A_11) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.46/1.40  tff(c_100, plain, (![D_21, B_22, C_23]: (D_21=B_22 | k6_relat_1(k2_relat_1(B_22))!=k5_relat_1(C_23, D_21) | k6_relat_1(k1_relat_1(D_21))!=k5_relat_1(B_22, C_23) | ~v1_funct_1(D_21) | ~v1_relat_1(D_21) | ~v1_funct_1(C_23) | ~v1_relat_1(C_23) | ~v1_funct_1(B_22) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.46/1.40  tff(c_136, plain, (![A_30, D_31, C_32]: (k2_funct_1(A_30)=D_31 | k6_relat_1(k1_relat_1(A_30))!=k5_relat_1(C_32, D_31) | k6_relat_1(k1_relat_1(D_31))!=k5_relat_1(k2_funct_1(A_30), C_32) | ~v1_funct_1(D_31) | ~v1_relat_1(D_31) | ~v1_funct_1(C_32) | ~v1_relat_1(C_32) | ~v1_funct_1(k2_funct_1(A_30)) | ~v1_relat_1(k2_funct_1(A_30)) | ~v2_funct_1(A_30) | ~v1_funct_1(A_30) | ~v1_relat_1(A_30))), inference(superposition, [status(thm), theory('equality')], [c_10, c_100])).
% 2.46/1.40  tff(c_144, plain, (![D_31, C_32]: (k2_funct_1('#skF_1')=D_31 | k5_relat_1(C_32, D_31)!=k5_relat_1('#skF_1', '#skF_2') | k6_relat_1(k1_relat_1(D_31))!=k5_relat_1(k2_funct_1('#skF_1'), C_32) | ~v1_funct_1(D_31) | ~v1_relat_1(D_31) | ~v1_funct_1(C_32) | ~v1_relat_1(C_32) | ~v1_funct_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_20, c_136])).
% 2.46/1.40  tff(c_146, plain, (![D_31, C_32]: (k2_funct_1('#skF_1')=D_31 | k5_relat_1(C_32, D_31)!=k5_relat_1('#skF_1', '#skF_2') | k6_relat_1(k1_relat_1(D_31))!=k5_relat_1(k2_funct_1('#skF_1'), C_32) | ~v1_funct_1(D_31) | ~v1_relat_1(D_31) | ~v1_funct_1(C_32) | ~v1_relat_1(C_32))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_24, c_62, c_60, c_144])).
% 2.46/1.40  tff(c_149, plain, (k2_funct_1('#skF_1')='#skF_2' | k5_relat_1(k2_funct_1('#skF_1'), '#skF_1')!=k6_relat_1(k1_relat_1('#skF_2')) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(reflexivity, [status(thm), theory('equality')], [c_146])).
% 2.46/1.40  tff(c_151, plain, (k2_funct_1('#skF_1')='#skF_2' | k5_relat_1(k2_funct_1('#skF_1'), '#skF_1')!=k6_relat_1(k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_26, c_149])).
% 2.46/1.40  tff(c_152, plain, (k5_relat_1(k2_funct_1('#skF_1'), '#skF_1')!=k6_relat_1(k1_relat_1('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_18, c_151])).
% 2.46/1.40  tff(c_169, plain, (k6_relat_1(k2_relat_1('#skF_1'))!=k6_relat_1(k1_relat_1('#skF_2')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_14, c_152])).
% 2.46/1.40  tff(c_172, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_24, c_22, c_169])).
% 2.46/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.46/1.40  
% 2.46/1.40  Inference rules
% 2.46/1.40  ----------------------
% 2.46/1.40  #Ref     : 1
% 2.46/1.40  #Sup     : 37
% 2.46/1.40  #Fact    : 0
% 2.46/1.40  #Define  : 0
% 2.46/1.40  #Split   : 0
% 2.46/1.40  #Chain   : 0
% 2.46/1.40  #Close   : 0
% 2.46/1.40  
% 2.46/1.40  Ordering : KBO
% 2.46/1.40  
% 2.46/1.40  Simplification rules
% 2.46/1.40  ----------------------
% 2.46/1.40  #Subsume      : 0
% 2.46/1.40  #Demod        : 31
% 2.46/1.40  #Tautology    : 16
% 2.46/1.40  #SimpNegUnit  : 1
% 2.46/1.40  #BackRed      : 0
% 2.46/1.40  
% 2.46/1.40  #Partial instantiations: 0
% 2.46/1.40  #Strategies tried      : 1
% 2.46/1.40  
% 2.46/1.40  Timing (in seconds)
% 2.46/1.40  ----------------------
% 2.46/1.40  Preprocessing        : 0.37
% 2.46/1.40  Parsing              : 0.20
% 2.46/1.40  CNF conversion       : 0.02
% 2.46/1.40  Main loop            : 0.22
% 2.46/1.40  Inferencing          : 0.08
% 2.46/1.40  Reduction            : 0.06
% 2.46/1.40  Demodulation         : 0.04
% 2.46/1.40  BG Simplification    : 0.02
% 2.46/1.40  Subsumption          : 0.04
% 2.46/1.40  Abstraction          : 0.01
% 2.46/1.40  MUC search           : 0.00
% 2.46/1.40  Cooper               : 0.00
% 2.46/1.40  Total                : 0.62
% 2.46/1.40  Index Insertion      : 0.00
% 2.46/1.40  Index Deletion       : 0.00
% 2.46/1.40  Index Matching       : 0.00
% 2.46/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
