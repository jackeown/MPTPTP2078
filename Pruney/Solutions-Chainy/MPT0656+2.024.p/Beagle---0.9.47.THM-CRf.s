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
% DateTime   : Thu Dec  3 10:04:04 EST 2020

% Result     : Theorem 2.30s
% Output     : CNFRefutation 2.47s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 108 expanded)
%              Number of leaves         :   18 (  49 expanded)
%              Depth                    :   11
%              Number of atoms          :  139 ( 502 expanded)
%              Number of equality atoms :   40 ( 161 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(f_79,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_37,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A))
        & v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).

tff(f_69,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_59,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_30,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_24,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_22,plain,(
    k2_relat_1('#skF_1') = k1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_14,plain,(
    ! [A_11] :
      ( k5_relat_1(k2_funct_1(A_11),A_11) = k6_relat_1(k2_relat_1(A_11))
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_18,plain,(
    k2_funct_1('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_28,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_26,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_funct_1(k2_funct_1(A_1))
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6,plain,(
    ! [A_1] :
      ( v1_relat_1(k2_funct_1(A_1))
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_20,plain,(
    k6_relat_1(k1_relat_1('#skF_1')) = k5_relat_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_10,plain,(
    ! [A_10] :
      ( k2_relat_1(k2_funct_1(A_10)) = k1_relat_1(A_10)
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_80,plain,(
    ! [D_20,B_21,C_22] :
      ( D_20 = B_21
      | k6_relat_1(k2_relat_1(B_21)) != k5_relat_1(C_22,D_20)
      | k6_relat_1(k1_relat_1(D_20)) != k5_relat_1(B_21,C_22)
      | ~ v1_funct_1(D_20)
      | ~ v1_relat_1(D_20)
      | ~ v1_funct_1(C_22)
      | ~ v1_relat_1(C_22)
      | ~ v1_funct_1(B_21)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_127,plain,(
    ! [A_31,D_32,C_33] :
      ( k2_funct_1(A_31) = D_32
      | k6_relat_1(k1_relat_1(A_31)) != k5_relat_1(C_33,D_32)
      | k6_relat_1(k1_relat_1(D_32)) != k5_relat_1(k2_funct_1(A_31),C_33)
      | ~ v1_funct_1(D_32)
      | ~ v1_relat_1(D_32)
      | ~ v1_funct_1(C_33)
      | ~ v1_relat_1(C_33)
      | ~ v1_funct_1(k2_funct_1(A_31))
      | ~ v1_relat_1(k2_funct_1(A_31))
      | ~ v2_funct_1(A_31)
      | ~ v1_funct_1(A_31)
      | ~ v1_relat_1(A_31) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_80])).

tff(c_135,plain,(
    ! [D_32,C_33] :
      ( k2_funct_1('#skF_1') = D_32
      | k5_relat_1(C_33,D_32) != k5_relat_1('#skF_1','#skF_2')
      | k6_relat_1(k1_relat_1(D_32)) != k5_relat_1(k2_funct_1('#skF_1'),C_33)
      | ~ v1_funct_1(D_32)
      | ~ v1_relat_1(D_32)
      | ~ v1_funct_1(C_33)
      | ~ v1_relat_1(C_33)
      | ~ v1_funct_1(k2_funct_1('#skF_1'))
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v2_funct_1('#skF_1')
      | ~ v1_funct_1('#skF_1')
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_127])).

tff(c_137,plain,(
    ! [D_32,C_33] :
      ( k2_funct_1('#skF_1') = D_32
      | k5_relat_1(C_33,D_32) != k5_relat_1('#skF_1','#skF_2')
      | k6_relat_1(k1_relat_1(D_32)) != k5_relat_1(k2_funct_1('#skF_1'),C_33)
      | ~ v1_funct_1(D_32)
      | ~ v1_relat_1(D_32)
      | ~ v1_funct_1(C_33)
      | ~ v1_relat_1(C_33)
      | ~ v1_funct_1(k2_funct_1('#skF_1'))
      | ~ v1_relat_1(k2_funct_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_24,c_135])).

tff(c_138,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_137])).

tff(c_141,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_138])).

tff(c_145,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_24,c_141])).

tff(c_146,plain,(
    ! [D_32,C_33] :
      ( ~ v1_funct_1(k2_funct_1('#skF_1'))
      | k2_funct_1('#skF_1') = D_32
      | k5_relat_1(C_33,D_32) != k5_relat_1('#skF_1','#skF_2')
      | k6_relat_1(k1_relat_1(D_32)) != k5_relat_1(k2_funct_1('#skF_1'),C_33)
      | ~ v1_funct_1(D_32)
      | ~ v1_relat_1(D_32)
      | ~ v1_funct_1(C_33)
      | ~ v1_relat_1(C_33) ) ),
    inference(splitRight,[status(thm)],[c_137])).

tff(c_157,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_146])).

tff(c_160,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_157])).

tff(c_164,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_24,c_160])).

tff(c_165,plain,(
    ! [D_32,C_33] :
      ( k2_funct_1('#skF_1') = D_32
      | k5_relat_1(C_33,D_32) != k5_relat_1('#skF_1','#skF_2')
      | k6_relat_1(k1_relat_1(D_32)) != k5_relat_1(k2_funct_1('#skF_1'),C_33)
      | ~ v1_funct_1(D_32)
      | ~ v1_relat_1(D_32)
      | ~ v1_funct_1(C_33)
      | ~ v1_relat_1(C_33) ) ),
    inference(splitRight,[status(thm)],[c_146])).

tff(c_173,plain,
    ( k2_funct_1('#skF_1') = '#skF_2'
    | k5_relat_1(k2_funct_1('#skF_1'),'#skF_1') != k6_relat_1(k1_relat_1('#skF_2'))
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_165])).

tff(c_175,plain,
    ( k2_funct_1('#skF_1') = '#skF_2'
    | k5_relat_1(k2_funct_1('#skF_1'),'#skF_1') != k6_relat_1(k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_26,c_173])).

tff(c_176,plain,(
    k5_relat_1(k2_funct_1('#skF_1'),'#skF_1') != k6_relat_1(k1_relat_1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_175])).

tff(c_184,plain,
    ( k6_relat_1(k2_relat_1('#skF_1')) != k6_relat_1(k1_relat_1('#skF_2'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_176])).

tff(c_187,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_24,c_22,c_184])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:33:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.30/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.30/1.31  
% 2.30/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.30/1.31  %$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.30/1.31  
% 2.30/1.31  %Foreground sorts:
% 2.30/1.31  
% 2.30/1.31  
% 2.30/1.31  %Background operators:
% 2.30/1.31  
% 2.30/1.31  
% 2.30/1.31  %Foreground operators:
% 2.30/1.31  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.30/1.31  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.30/1.31  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.30/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.30/1.31  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.30/1.31  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.30/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.30/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.30/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.30/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.30/1.31  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.30/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.30/1.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.30/1.31  
% 2.47/1.32  tff(f_97, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(A) = k1_relat_1(B))) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_funct_1)).
% 2.47/1.32  tff(f_79, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 2.47/1.32  tff(f_37, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => ((v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))) & v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_funct_1)).
% 2.47/1.32  tff(f_69, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 2.47/1.32  tff(f_59, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (![D]: ((v1_relat_1(D) & v1_funct_1(D)) => ((((k2_relat_1(B) = A) & (k5_relat_1(B, C) = k6_relat_1(k1_relat_1(D)))) & (k5_relat_1(C, D) = k6_relat_1(A))) => (D = B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l72_funct_1)).
% 2.47/1.32  tff(c_32, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.47/1.32  tff(c_30, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.47/1.32  tff(c_24, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.47/1.32  tff(c_22, plain, (k2_relat_1('#skF_1')=k1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.47/1.32  tff(c_14, plain, (![A_11]: (k5_relat_1(k2_funct_1(A_11), A_11)=k6_relat_1(k2_relat_1(A_11)) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.47/1.32  tff(c_18, plain, (k2_funct_1('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.47/1.32  tff(c_28, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.47/1.32  tff(c_26, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.47/1.32  tff(c_4, plain, (![A_1]: (v1_funct_1(k2_funct_1(A_1)) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.47/1.32  tff(c_6, plain, (![A_1]: (v1_relat_1(k2_funct_1(A_1)) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.47/1.32  tff(c_20, plain, (k6_relat_1(k1_relat_1('#skF_1'))=k5_relat_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.47/1.32  tff(c_10, plain, (![A_10]: (k2_relat_1(k2_funct_1(A_10))=k1_relat_1(A_10) | ~v2_funct_1(A_10) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.47/1.32  tff(c_80, plain, (![D_20, B_21, C_22]: (D_20=B_21 | k6_relat_1(k2_relat_1(B_21))!=k5_relat_1(C_22, D_20) | k6_relat_1(k1_relat_1(D_20))!=k5_relat_1(B_21, C_22) | ~v1_funct_1(D_20) | ~v1_relat_1(D_20) | ~v1_funct_1(C_22) | ~v1_relat_1(C_22) | ~v1_funct_1(B_21) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.47/1.32  tff(c_127, plain, (![A_31, D_32, C_33]: (k2_funct_1(A_31)=D_32 | k6_relat_1(k1_relat_1(A_31))!=k5_relat_1(C_33, D_32) | k6_relat_1(k1_relat_1(D_32))!=k5_relat_1(k2_funct_1(A_31), C_33) | ~v1_funct_1(D_32) | ~v1_relat_1(D_32) | ~v1_funct_1(C_33) | ~v1_relat_1(C_33) | ~v1_funct_1(k2_funct_1(A_31)) | ~v1_relat_1(k2_funct_1(A_31)) | ~v2_funct_1(A_31) | ~v1_funct_1(A_31) | ~v1_relat_1(A_31))), inference(superposition, [status(thm), theory('equality')], [c_10, c_80])).
% 2.47/1.32  tff(c_135, plain, (![D_32, C_33]: (k2_funct_1('#skF_1')=D_32 | k5_relat_1(C_33, D_32)!=k5_relat_1('#skF_1', '#skF_2') | k6_relat_1(k1_relat_1(D_32))!=k5_relat_1(k2_funct_1('#skF_1'), C_33) | ~v1_funct_1(D_32) | ~v1_relat_1(D_32) | ~v1_funct_1(C_33) | ~v1_relat_1(C_33) | ~v1_funct_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_20, c_127])).
% 2.47/1.32  tff(c_137, plain, (![D_32, C_33]: (k2_funct_1('#skF_1')=D_32 | k5_relat_1(C_33, D_32)!=k5_relat_1('#skF_1', '#skF_2') | k6_relat_1(k1_relat_1(D_32))!=k5_relat_1(k2_funct_1('#skF_1'), C_33) | ~v1_funct_1(D_32) | ~v1_relat_1(D_32) | ~v1_funct_1(C_33) | ~v1_relat_1(C_33) | ~v1_funct_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_24, c_135])).
% 2.47/1.32  tff(c_138, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_137])).
% 2.47/1.32  tff(c_141, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_6, c_138])).
% 2.47/1.32  tff(c_145, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_24, c_141])).
% 2.47/1.32  tff(c_146, plain, (![D_32, C_33]: (~v1_funct_1(k2_funct_1('#skF_1')) | k2_funct_1('#skF_1')=D_32 | k5_relat_1(C_33, D_32)!=k5_relat_1('#skF_1', '#skF_2') | k6_relat_1(k1_relat_1(D_32))!=k5_relat_1(k2_funct_1('#skF_1'), C_33) | ~v1_funct_1(D_32) | ~v1_relat_1(D_32) | ~v1_funct_1(C_33) | ~v1_relat_1(C_33))), inference(splitRight, [status(thm)], [c_137])).
% 2.47/1.32  tff(c_157, plain, (~v1_funct_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_146])).
% 2.47/1.32  tff(c_160, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_4, c_157])).
% 2.47/1.32  tff(c_164, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_24, c_160])).
% 2.47/1.32  tff(c_165, plain, (![D_32, C_33]: (k2_funct_1('#skF_1')=D_32 | k5_relat_1(C_33, D_32)!=k5_relat_1('#skF_1', '#skF_2') | k6_relat_1(k1_relat_1(D_32))!=k5_relat_1(k2_funct_1('#skF_1'), C_33) | ~v1_funct_1(D_32) | ~v1_relat_1(D_32) | ~v1_funct_1(C_33) | ~v1_relat_1(C_33))), inference(splitRight, [status(thm)], [c_146])).
% 2.47/1.32  tff(c_173, plain, (k2_funct_1('#skF_1')='#skF_2' | k5_relat_1(k2_funct_1('#skF_1'), '#skF_1')!=k6_relat_1(k1_relat_1('#skF_2')) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(reflexivity, [status(thm), theory('equality')], [c_165])).
% 2.47/1.32  tff(c_175, plain, (k2_funct_1('#skF_1')='#skF_2' | k5_relat_1(k2_funct_1('#skF_1'), '#skF_1')!=k6_relat_1(k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_26, c_173])).
% 2.47/1.32  tff(c_176, plain, (k5_relat_1(k2_funct_1('#skF_1'), '#skF_1')!=k6_relat_1(k1_relat_1('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_18, c_175])).
% 2.47/1.32  tff(c_184, plain, (k6_relat_1(k2_relat_1('#skF_1'))!=k6_relat_1(k1_relat_1('#skF_2')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_14, c_176])).
% 2.47/1.32  tff(c_187, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_24, c_22, c_184])).
% 2.47/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.32  
% 2.47/1.32  Inference rules
% 2.47/1.32  ----------------------
% 2.47/1.32  #Ref     : 1
% 2.47/1.32  #Sup     : 37
% 2.47/1.32  #Fact    : 0
% 2.47/1.32  #Define  : 0
% 2.47/1.32  #Split   : 2
% 2.47/1.32  #Chain   : 0
% 2.47/1.32  #Close   : 0
% 2.47/1.32  
% 2.47/1.32  Ordering : KBO
% 2.47/1.32  
% 2.47/1.32  Simplification rules
% 2.47/1.32  ----------------------
% 2.47/1.32  #Subsume      : 3
% 2.47/1.32  #Demod        : 25
% 2.47/1.32  #Tautology    : 14
% 2.47/1.32  #SimpNegUnit  : 1
% 2.47/1.32  #BackRed      : 0
% 2.47/1.32  
% 2.47/1.32  #Partial instantiations: 0
% 2.47/1.32  #Strategies tried      : 1
% 2.47/1.32  
% 2.47/1.32  Timing (in seconds)
% 2.47/1.32  ----------------------
% 2.47/1.33  Preprocessing        : 0.28
% 2.47/1.33  Parsing              : 0.15
% 2.47/1.33  CNF conversion       : 0.02
% 2.47/1.33  Main loop            : 0.22
% 2.47/1.33  Inferencing          : 0.08
% 2.47/1.33  Reduction            : 0.06
% 2.47/1.33  Demodulation         : 0.04
% 2.47/1.33  BG Simplification    : 0.02
% 2.47/1.33  Subsumption          : 0.06
% 2.47/1.33  Abstraction          : 0.01
% 2.47/1.33  MUC search           : 0.00
% 2.47/1.33  Cooper               : 0.00
% 2.47/1.33  Total                : 0.54
% 2.47/1.33  Index Insertion      : 0.00
% 2.47/1.33  Index Deletion       : 0.00
% 2.47/1.33  Index Matching       : 0.00
% 2.47/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
