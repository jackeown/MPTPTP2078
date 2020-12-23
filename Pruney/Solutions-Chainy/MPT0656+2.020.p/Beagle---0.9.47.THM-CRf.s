%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:03 EST 2020

% Result     : Theorem 2.51s
% Output     : CNFRefutation 2.51s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 104 expanded)
%              Number of leaves         :   18 (  47 expanded)
%              Depth                    :   11
%              Number of atoms          :  133 ( 476 expanded)
%              Number of equality atoms :   40 ( 155 expanded)
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

tff(f_93,negated_conjecture,(
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

tff(f_75,axiom,(
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
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_65,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_55,axiom,(
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

tff(c_30,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_28,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_22,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_20,plain,(
    k2_relat_1('#skF_1') = k1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_12,plain,(
    ! [A_11] :
      ( k5_relat_1(k2_funct_1(A_11),A_11) = k6_relat_1(k2_relat_1(A_11))
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_16,plain,(
    k2_funct_1('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_26,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_24,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2,plain,(
    ! [A_1] :
      ( v1_funct_1(k2_funct_1(A_1))
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_relat_1(k2_funct_1(A_1))
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_18,plain,(
    k6_relat_1(k1_relat_1('#skF_1')) = k5_relat_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_8,plain,(
    ! [A_10] :
      ( k2_relat_1(k2_funct_1(A_10)) = k1_relat_1(A_10)
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_77,plain,(
    ! [D_19,B_20,C_21] :
      ( D_19 = B_20
      | k6_relat_1(k2_relat_1(B_20)) != k5_relat_1(C_21,D_19)
      | k6_relat_1(k1_relat_1(D_19)) != k5_relat_1(B_20,C_21)
      | ~ v1_funct_1(D_19)
      | ~ v1_relat_1(D_19)
      | ~ v1_funct_1(C_21)
      | ~ v1_relat_1(C_21)
      | ~ v1_funct_1(B_20)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_147,plain,(
    ! [A_35,D_36,C_37] :
      ( k2_funct_1(A_35) = D_36
      | k6_relat_1(k1_relat_1(A_35)) != k5_relat_1(C_37,D_36)
      | k6_relat_1(k1_relat_1(D_36)) != k5_relat_1(k2_funct_1(A_35),C_37)
      | ~ v1_funct_1(D_36)
      | ~ v1_relat_1(D_36)
      | ~ v1_funct_1(C_37)
      | ~ v1_relat_1(C_37)
      | ~ v1_funct_1(k2_funct_1(A_35))
      | ~ v1_relat_1(k2_funct_1(A_35))
      | ~ v2_funct_1(A_35)
      | ~ v1_funct_1(A_35)
      | ~ v1_relat_1(A_35) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_77])).

tff(c_155,plain,(
    ! [D_36,C_37] :
      ( k2_funct_1('#skF_1') = D_36
      | k5_relat_1(C_37,D_36) != k5_relat_1('#skF_1','#skF_2')
      | k6_relat_1(k1_relat_1(D_36)) != k5_relat_1(k2_funct_1('#skF_1'),C_37)
      | ~ v1_funct_1(D_36)
      | ~ v1_relat_1(D_36)
      | ~ v1_funct_1(C_37)
      | ~ v1_relat_1(C_37)
      | ~ v1_funct_1(k2_funct_1('#skF_1'))
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v2_funct_1('#skF_1')
      | ~ v1_funct_1('#skF_1')
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_147])).

tff(c_157,plain,(
    ! [D_36,C_37] :
      ( k2_funct_1('#skF_1') = D_36
      | k5_relat_1(C_37,D_36) != k5_relat_1('#skF_1','#skF_2')
      | k6_relat_1(k1_relat_1(D_36)) != k5_relat_1(k2_funct_1('#skF_1'),C_37)
      | ~ v1_funct_1(D_36)
      | ~ v1_relat_1(D_36)
      | ~ v1_funct_1(C_37)
      | ~ v1_relat_1(C_37)
      | ~ v1_funct_1(k2_funct_1('#skF_1'))
      | ~ v1_relat_1(k2_funct_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_22,c_155])).

tff(c_168,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_157])).

tff(c_171,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_168])).

tff(c_175,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_171])).

tff(c_176,plain,(
    ! [D_36,C_37] :
      ( ~ v1_funct_1(k2_funct_1('#skF_1'))
      | k2_funct_1('#skF_1') = D_36
      | k5_relat_1(C_37,D_36) != k5_relat_1('#skF_1','#skF_2')
      | k6_relat_1(k1_relat_1(D_36)) != k5_relat_1(k2_funct_1('#skF_1'),C_37)
      | ~ v1_funct_1(D_36)
      | ~ v1_relat_1(D_36)
      | ~ v1_funct_1(C_37)
      | ~ v1_relat_1(C_37) ) ),
    inference(splitRight,[status(thm)],[c_157])).

tff(c_178,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_176])).

tff(c_181,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_178])).

tff(c_185,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_181])).

tff(c_186,plain,(
    ! [D_36,C_37] :
      ( k2_funct_1('#skF_1') = D_36
      | k5_relat_1(C_37,D_36) != k5_relat_1('#skF_1','#skF_2')
      | k6_relat_1(k1_relat_1(D_36)) != k5_relat_1(k2_funct_1('#skF_1'),C_37)
      | ~ v1_funct_1(D_36)
      | ~ v1_relat_1(D_36)
      | ~ v1_funct_1(C_37)
      | ~ v1_relat_1(C_37) ) ),
    inference(splitRight,[status(thm)],[c_176])).

tff(c_190,plain,
    ( k2_funct_1('#skF_1') = '#skF_2'
    | k5_relat_1(k2_funct_1('#skF_1'),'#skF_1') != k6_relat_1(k1_relat_1('#skF_2'))
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_186])).

tff(c_192,plain,
    ( k2_funct_1('#skF_1') = '#skF_2'
    | k5_relat_1(k2_funct_1('#skF_1'),'#skF_1') != k6_relat_1(k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_24,c_190])).

tff(c_193,plain,(
    k5_relat_1(k2_funct_1('#skF_1'),'#skF_1') != k6_relat_1(k1_relat_1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_192])).

tff(c_201,plain,
    ( k6_relat_1(k2_relat_1('#skF_1')) != k6_relat_1(k1_relat_1('#skF_2'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_193])).

tff(c_204,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_22,c_20,c_201])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:29:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.51/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.34  
% 2.51/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.34  %$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.51/1.34  
% 2.51/1.34  %Foreground sorts:
% 2.51/1.34  
% 2.51/1.34  
% 2.51/1.34  %Background operators:
% 2.51/1.34  
% 2.51/1.34  
% 2.51/1.34  %Foreground operators:
% 2.51/1.34  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.51/1.34  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.51/1.34  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.51/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.51/1.34  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.51/1.34  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.51/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.51/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.51/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.51/1.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.51/1.34  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.51/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.51/1.34  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.51/1.34  
% 2.51/1.35  tff(f_93, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(A) = k1_relat_1(B))) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_funct_1)).
% 2.51/1.35  tff(f_75, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 2.51/1.35  tff(f_33, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 2.51/1.35  tff(f_65, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 2.51/1.35  tff(f_55, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (![D]: ((v1_relat_1(D) & v1_funct_1(D)) => ((((k2_relat_1(B) = A) & (k5_relat_1(B, C) = k6_relat_1(k1_relat_1(D)))) & (k5_relat_1(C, D) = k6_relat_1(A))) => (D = B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l72_funct_1)).
% 2.51/1.35  tff(c_30, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.51/1.35  tff(c_28, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.51/1.35  tff(c_22, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.51/1.35  tff(c_20, plain, (k2_relat_1('#skF_1')=k1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.51/1.35  tff(c_12, plain, (![A_11]: (k5_relat_1(k2_funct_1(A_11), A_11)=k6_relat_1(k2_relat_1(A_11)) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.51/1.35  tff(c_16, plain, (k2_funct_1('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.51/1.35  tff(c_26, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.51/1.35  tff(c_24, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.51/1.35  tff(c_2, plain, (![A_1]: (v1_funct_1(k2_funct_1(A_1)) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.51/1.35  tff(c_4, plain, (![A_1]: (v1_relat_1(k2_funct_1(A_1)) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.51/1.35  tff(c_18, plain, (k6_relat_1(k1_relat_1('#skF_1'))=k5_relat_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.51/1.35  tff(c_8, plain, (![A_10]: (k2_relat_1(k2_funct_1(A_10))=k1_relat_1(A_10) | ~v2_funct_1(A_10) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.51/1.35  tff(c_77, plain, (![D_19, B_20, C_21]: (D_19=B_20 | k6_relat_1(k2_relat_1(B_20))!=k5_relat_1(C_21, D_19) | k6_relat_1(k1_relat_1(D_19))!=k5_relat_1(B_20, C_21) | ~v1_funct_1(D_19) | ~v1_relat_1(D_19) | ~v1_funct_1(C_21) | ~v1_relat_1(C_21) | ~v1_funct_1(B_20) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.51/1.35  tff(c_147, plain, (![A_35, D_36, C_37]: (k2_funct_1(A_35)=D_36 | k6_relat_1(k1_relat_1(A_35))!=k5_relat_1(C_37, D_36) | k6_relat_1(k1_relat_1(D_36))!=k5_relat_1(k2_funct_1(A_35), C_37) | ~v1_funct_1(D_36) | ~v1_relat_1(D_36) | ~v1_funct_1(C_37) | ~v1_relat_1(C_37) | ~v1_funct_1(k2_funct_1(A_35)) | ~v1_relat_1(k2_funct_1(A_35)) | ~v2_funct_1(A_35) | ~v1_funct_1(A_35) | ~v1_relat_1(A_35))), inference(superposition, [status(thm), theory('equality')], [c_8, c_77])).
% 2.51/1.35  tff(c_155, plain, (![D_36, C_37]: (k2_funct_1('#skF_1')=D_36 | k5_relat_1(C_37, D_36)!=k5_relat_1('#skF_1', '#skF_2') | k6_relat_1(k1_relat_1(D_36))!=k5_relat_1(k2_funct_1('#skF_1'), C_37) | ~v1_funct_1(D_36) | ~v1_relat_1(D_36) | ~v1_funct_1(C_37) | ~v1_relat_1(C_37) | ~v1_funct_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_18, c_147])).
% 2.51/1.35  tff(c_157, plain, (![D_36, C_37]: (k2_funct_1('#skF_1')=D_36 | k5_relat_1(C_37, D_36)!=k5_relat_1('#skF_1', '#skF_2') | k6_relat_1(k1_relat_1(D_36))!=k5_relat_1(k2_funct_1('#skF_1'), C_37) | ~v1_funct_1(D_36) | ~v1_relat_1(D_36) | ~v1_funct_1(C_37) | ~v1_relat_1(C_37) | ~v1_funct_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_22, c_155])).
% 2.51/1.35  tff(c_168, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_157])).
% 2.51/1.35  tff(c_171, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_4, c_168])).
% 2.51/1.35  tff(c_175, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_171])).
% 2.51/1.35  tff(c_176, plain, (![D_36, C_37]: (~v1_funct_1(k2_funct_1('#skF_1')) | k2_funct_1('#skF_1')=D_36 | k5_relat_1(C_37, D_36)!=k5_relat_1('#skF_1', '#skF_2') | k6_relat_1(k1_relat_1(D_36))!=k5_relat_1(k2_funct_1('#skF_1'), C_37) | ~v1_funct_1(D_36) | ~v1_relat_1(D_36) | ~v1_funct_1(C_37) | ~v1_relat_1(C_37))), inference(splitRight, [status(thm)], [c_157])).
% 2.51/1.35  tff(c_178, plain, (~v1_funct_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_176])).
% 2.51/1.35  tff(c_181, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_2, c_178])).
% 2.51/1.35  tff(c_185, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_181])).
% 2.51/1.35  tff(c_186, plain, (![D_36, C_37]: (k2_funct_1('#skF_1')=D_36 | k5_relat_1(C_37, D_36)!=k5_relat_1('#skF_1', '#skF_2') | k6_relat_1(k1_relat_1(D_36))!=k5_relat_1(k2_funct_1('#skF_1'), C_37) | ~v1_funct_1(D_36) | ~v1_relat_1(D_36) | ~v1_funct_1(C_37) | ~v1_relat_1(C_37))), inference(splitRight, [status(thm)], [c_176])).
% 2.51/1.35  tff(c_190, plain, (k2_funct_1('#skF_1')='#skF_2' | k5_relat_1(k2_funct_1('#skF_1'), '#skF_1')!=k6_relat_1(k1_relat_1('#skF_2')) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(reflexivity, [status(thm), theory('equality')], [c_186])).
% 2.51/1.35  tff(c_192, plain, (k2_funct_1('#skF_1')='#skF_2' | k5_relat_1(k2_funct_1('#skF_1'), '#skF_1')!=k6_relat_1(k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_24, c_190])).
% 2.51/1.35  tff(c_193, plain, (k5_relat_1(k2_funct_1('#skF_1'), '#skF_1')!=k6_relat_1(k1_relat_1('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_16, c_192])).
% 2.51/1.35  tff(c_201, plain, (k6_relat_1(k2_relat_1('#skF_1'))!=k6_relat_1(k1_relat_1('#skF_2')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_12, c_193])).
% 2.51/1.35  tff(c_204, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_22, c_20, c_201])).
% 2.51/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.35  
% 2.51/1.35  Inference rules
% 2.51/1.35  ----------------------
% 2.51/1.35  #Ref     : 1
% 2.51/1.35  #Sup     : 41
% 2.51/1.35  #Fact    : 0
% 2.51/1.35  #Define  : 0
% 2.51/1.35  #Split   : 3
% 2.51/1.35  #Chain   : 0
% 2.51/1.35  #Close   : 0
% 2.51/1.35  
% 2.51/1.35  Ordering : KBO
% 2.51/1.35  
% 2.51/1.35  Simplification rules
% 2.51/1.35  ----------------------
% 2.51/1.35  #Subsume      : 5
% 2.51/1.35  #Demod        : 27
% 2.51/1.35  #Tautology    : 14
% 2.51/1.35  #SimpNegUnit  : 1
% 2.51/1.35  #BackRed      : 0
% 2.51/1.35  
% 2.51/1.35  #Partial instantiations: 0
% 2.51/1.35  #Strategies tried      : 1
% 2.51/1.35  
% 2.51/1.35  Timing (in seconds)
% 2.51/1.35  ----------------------
% 2.51/1.36  Preprocessing        : 0.31
% 2.51/1.36  Parsing              : 0.17
% 2.51/1.36  CNF conversion       : 0.02
% 2.51/1.36  Main loop            : 0.24
% 2.51/1.36  Inferencing          : 0.09
% 2.51/1.36  Reduction            : 0.06
% 2.51/1.36  Demodulation         : 0.04
% 2.51/1.36  BG Simplification    : 0.02
% 2.51/1.36  Subsumption          : 0.06
% 2.51/1.36  Abstraction          : 0.01
% 2.51/1.36  MUC search           : 0.00
% 2.51/1.36  Cooper               : 0.00
% 2.51/1.36  Total                : 0.57
% 2.51/1.36  Index Insertion      : 0.00
% 2.51/1.36  Index Deletion       : 0.00
% 2.51/1.36  Index Matching       : 0.00
% 2.51/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
