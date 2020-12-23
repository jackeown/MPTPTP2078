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
% DateTime   : Thu Dec  3 10:04:07 EST 2020

% Result     : Theorem 2.32s
% Output     : CNFRefutation 2.62s
% Verified   : 
% Statistics : Number of formulae       :   40 (  48 expanded)
%              Number of leaves         :   18 (  26 expanded)
%              Depth                    :   10
%              Number of atoms          :  125 ( 185 expanded)
%              Number of equality atoms :   39 (  60 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

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
                & k2_relat_1(B) = k1_relat_1(A)
                & k5_relat_1(B,A) = k6_relat_1(k2_relat_1(A)) )
             => B = k2_funct_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).

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

tff(f_75,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

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

tff(c_16,plain,(
    k2_funct_1('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_30,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_28,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_22,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_18,plain,(
    k6_relat_1(k2_relat_1('#skF_1')) = k5_relat_1('#skF_2','#skF_1') ),
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

tff(c_10,plain,(
    ! [A_10] :
      ( k1_relat_1(k2_funct_1(A_10)) = k2_relat_1(A_10)
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_26,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_24,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_20,plain,(
    k2_relat_1('#skF_2') = k1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_14,plain,(
    ! [A_11] :
      ( k5_relat_1(A_11,k2_funct_1(A_11)) = k6_relat_1(k1_relat_1(A_11))
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

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

tff(c_169,plain,(
    ! [A_39,B_40] :
      ( k2_funct_1(A_39) = B_40
      | k6_relat_1(k2_relat_1(B_40)) != k6_relat_1(k1_relat_1(A_39))
      | k6_relat_1(k1_relat_1(k2_funct_1(A_39))) != k5_relat_1(B_40,A_39)
      | ~ v1_funct_1(k2_funct_1(A_39))
      | ~ v1_relat_1(k2_funct_1(A_39))
      | ~ v1_funct_1(A_39)
      | ~ v1_relat_1(A_39)
      | ~ v1_funct_1(B_40)
      | ~ v1_relat_1(B_40)
      | ~ v2_funct_1(A_39)
      | ~ v1_funct_1(A_39)
      | ~ v1_relat_1(A_39) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_77])).

tff(c_177,plain,(
    ! [A_39] :
      ( k2_funct_1(A_39) = '#skF_2'
      | k6_relat_1(k1_relat_1(A_39)) != k6_relat_1(k1_relat_1('#skF_1'))
      | k6_relat_1(k1_relat_1(k2_funct_1(A_39))) != k5_relat_1('#skF_2',A_39)
      | ~ v1_funct_1(k2_funct_1(A_39))
      | ~ v1_relat_1(k2_funct_1(A_39))
      | ~ v1_funct_1(A_39)
      | ~ v1_relat_1(A_39)
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2')
      | ~ v2_funct_1(A_39)
      | ~ v1_funct_1(A_39)
      | ~ v1_relat_1(A_39) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_169])).

tff(c_186,plain,(
    ! [A_42] :
      ( k2_funct_1(A_42) = '#skF_2'
      | k6_relat_1(k1_relat_1(A_42)) != k6_relat_1(k1_relat_1('#skF_1'))
      | k6_relat_1(k1_relat_1(k2_funct_1(A_42))) != k5_relat_1('#skF_2',A_42)
      | ~ v1_funct_1(k2_funct_1(A_42))
      | ~ v1_relat_1(k2_funct_1(A_42))
      | ~ v2_funct_1(A_42)
      | ~ v1_funct_1(A_42)
      | ~ v1_relat_1(A_42) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_177])).

tff(c_227,plain,(
    ! [A_48] :
      ( k2_funct_1(A_48) = '#skF_2'
      | k6_relat_1(k1_relat_1(A_48)) != k6_relat_1(k1_relat_1('#skF_1'))
      | k6_relat_1(k2_relat_1(A_48)) != k5_relat_1('#skF_2',A_48)
      | ~ v1_funct_1(k2_funct_1(A_48))
      | ~ v1_relat_1(k2_funct_1(A_48))
      | ~ v2_funct_1(A_48)
      | ~ v1_funct_1(A_48)
      | ~ v1_relat_1(A_48)
      | ~ v2_funct_1(A_48)
      | ~ v1_funct_1(A_48)
      | ~ v1_relat_1(A_48) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_186])).

tff(c_232,plain,(
    ! [A_49] :
      ( k2_funct_1(A_49) = '#skF_2'
      | k6_relat_1(k1_relat_1(A_49)) != k6_relat_1(k1_relat_1('#skF_1'))
      | k6_relat_1(k2_relat_1(A_49)) != k5_relat_1('#skF_2',A_49)
      | ~ v1_funct_1(k2_funct_1(A_49))
      | ~ v2_funct_1(A_49)
      | ~ v1_funct_1(A_49)
      | ~ v1_relat_1(A_49) ) ),
    inference(resolution,[status(thm)],[c_4,c_227])).

tff(c_237,plain,(
    ! [A_50] :
      ( k2_funct_1(A_50) = '#skF_2'
      | k6_relat_1(k1_relat_1(A_50)) != k6_relat_1(k1_relat_1('#skF_1'))
      | k6_relat_1(k2_relat_1(A_50)) != k5_relat_1('#skF_2',A_50)
      | ~ v2_funct_1(A_50)
      | ~ v1_funct_1(A_50)
      | ~ v1_relat_1(A_50) ) ),
    inference(resolution,[status(thm)],[c_2,c_232])).

tff(c_243,plain,
    ( k2_funct_1('#skF_1') = '#skF_2'
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_237])).

tff(c_249,plain,(
    k2_funct_1('#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_22,c_243])).

tff(c_251,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_249])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:48:44 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.32/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.62/1.32  
% 2.62/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.62/1.33  %$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.62/1.33  
% 2.62/1.33  %Foreground sorts:
% 2.62/1.33  
% 2.62/1.33  
% 2.62/1.33  %Background operators:
% 2.62/1.33  
% 2.62/1.33  
% 2.62/1.33  %Foreground operators:
% 2.62/1.33  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.62/1.33  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.62/1.33  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.62/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.62/1.33  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.62/1.33  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.62/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.62/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.62/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.62/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.62/1.33  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.62/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.62/1.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.62/1.33  
% 2.62/1.34  tff(f_93, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_1)).
% 2.62/1.34  tff(f_33, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 2.62/1.34  tff(f_65, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 2.62/1.34  tff(f_75, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 2.62/1.34  tff(f_55, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (![D]: ((v1_relat_1(D) & v1_funct_1(D)) => ((((k2_relat_1(B) = A) & (k5_relat_1(B, C) = k6_relat_1(k1_relat_1(D)))) & (k5_relat_1(C, D) = k6_relat_1(A))) => (D = B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l72_funct_1)).
% 2.62/1.34  tff(c_16, plain, (k2_funct_1('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.62/1.34  tff(c_30, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.62/1.34  tff(c_28, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.62/1.34  tff(c_22, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.62/1.34  tff(c_18, plain, (k6_relat_1(k2_relat_1('#skF_1'))=k5_relat_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.62/1.34  tff(c_2, plain, (![A_1]: (v1_funct_1(k2_funct_1(A_1)) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.62/1.34  tff(c_4, plain, (![A_1]: (v1_relat_1(k2_funct_1(A_1)) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.62/1.34  tff(c_10, plain, (![A_10]: (k1_relat_1(k2_funct_1(A_10))=k2_relat_1(A_10) | ~v2_funct_1(A_10) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.62/1.34  tff(c_26, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.62/1.34  tff(c_24, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.62/1.34  tff(c_20, plain, (k2_relat_1('#skF_2')=k1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.62/1.34  tff(c_14, plain, (![A_11]: (k5_relat_1(A_11, k2_funct_1(A_11))=k6_relat_1(k1_relat_1(A_11)) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.62/1.34  tff(c_77, plain, (![D_19, B_20, C_21]: (D_19=B_20 | k6_relat_1(k2_relat_1(B_20))!=k5_relat_1(C_21, D_19) | k6_relat_1(k1_relat_1(D_19))!=k5_relat_1(B_20, C_21) | ~v1_funct_1(D_19) | ~v1_relat_1(D_19) | ~v1_funct_1(C_21) | ~v1_relat_1(C_21) | ~v1_funct_1(B_20) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.62/1.34  tff(c_169, plain, (![A_39, B_40]: (k2_funct_1(A_39)=B_40 | k6_relat_1(k2_relat_1(B_40))!=k6_relat_1(k1_relat_1(A_39)) | k6_relat_1(k1_relat_1(k2_funct_1(A_39)))!=k5_relat_1(B_40, A_39) | ~v1_funct_1(k2_funct_1(A_39)) | ~v1_relat_1(k2_funct_1(A_39)) | ~v1_funct_1(A_39) | ~v1_relat_1(A_39) | ~v1_funct_1(B_40) | ~v1_relat_1(B_40) | ~v2_funct_1(A_39) | ~v1_funct_1(A_39) | ~v1_relat_1(A_39))), inference(superposition, [status(thm), theory('equality')], [c_14, c_77])).
% 2.62/1.34  tff(c_177, plain, (![A_39]: (k2_funct_1(A_39)='#skF_2' | k6_relat_1(k1_relat_1(A_39))!=k6_relat_1(k1_relat_1('#skF_1')) | k6_relat_1(k1_relat_1(k2_funct_1(A_39)))!=k5_relat_1('#skF_2', A_39) | ~v1_funct_1(k2_funct_1(A_39)) | ~v1_relat_1(k2_funct_1(A_39)) | ~v1_funct_1(A_39) | ~v1_relat_1(A_39) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v2_funct_1(A_39) | ~v1_funct_1(A_39) | ~v1_relat_1(A_39))), inference(superposition, [status(thm), theory('equality')], [c_20, c_169])).
% 2.62/1.34  tff(c_186, plain, (![A_42]: (k2_funct_1(A_42)='#skF_2' | k6_relat_1(k1_relat_1(A_42))!=k6_relat_1(k1_relat_1('#skF_1')) | k6_relat_1(k1_relat_1(k2_funct_1(A_42)))!=k5_relat_1('#skF_2', A_42) | ~v1_funct_1(k2_funct_1(A_42)) | ~v1_relat_1(k2_funct_1(A_42)) | ~v2_funct_1(A_42) | ~v1_funct_1(A_42) | ~v1_relat_1(A_42))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_177])).
% 2.62/1.34  tff(c_227, plain, (![A_48]: (k2_funct_1(A_48)='#skF_2' | k6_relat_1(k1_relat_1(A_48))!=k6_relat_1(k1_relat_1('#skF_1')) | k6_relat_1(k2_relat_1(A_48))!=k5_relat_1('#skF_2', A_48) | ~v1_funct_1(k2_funct_1(A_48)) | ~v1_relat_1(k2_funct_1(A_48)) | ~v2_funct_1(A_48) | ~v1_funct_1(A_48) | ~v1_relat_1(A_48) | ~v2_funct_1(A_48) | ~v1_funct_1(A_48) | ~v1_relat_1(A_48))), inference(superposition, [status(thm), theory('equality')], [c_10, c_186])).
% 2.62/1.34  tff(c_232, plain, (![A_49]: (k2_funct_1(A_49)='#skF_2' | k6_relat_1(k1_relat_1(A_49))!=k6_relat_1(k1_relat_1('#skF_1')) | k6_relat_1(k2_relat_1(A_49))!=k5_relat_1('#skF_2', A_49) | ~v1_funct_1(k2_funct_1(A_49)) | ~v2_funct_1(A_49) | ~v1_funct_1(A_49) | ~v1_relat_1(A_49))), inference(resolution, [status(thm)], [c_4, c_227])).
% 2.62/1.34  tff(c_237, plain, (![A_50]: (k2_funct_1(A_50)='#skF_2' | k6_relat_1(k1_relat_1(A_50))!=k6_relat_1(k1_relat_1('#skF_1')) | k6_relat_1(k2_relat_1(A_50))!=k5_relat_1('#skF_2', A_50) | ~v2_funct_1(A_50) | ~v1_funct_1(A_50) | ~v1_relat_1(A_50))), inference(resolution, [status(thm)], [c_2, c_232])).
% 2.62/1.34  tff(c_243, plain, (k2_funct_1('#skF_1')='#skF_2' | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_18, c_237])).
% 2.62/1.34  tff(c_249, plain, (k2_funct_1('#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_22, c_243])).
% 2.62/1.34  tff(c_251, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_249])).
% 2.62/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.62/1.34  
% 2.62/1.34  Inference rules
% 2.62/1.34  ----------------------
% 2.62/1.34  #Ref     : 1
% 2.62/1.34  #Sup     : 52
% 2.62/1.34  #Fact    : 0
% 2.62/1.34  #Define  : 0
% 2.62/1.34  #Split   : 2
% 2.62/1.34  #Chain   : 0
% 2.62/1.34  #Close   : 0
% 2.62/1.34  
% 2.62/1.34  Ordering : KBO
% 2.62/1.34  
% 2.62/1.34  Simplification rules
% 2.62/1.34  ----------------------
% 2.62/1.34  #Subsume      : 10
% 2.62/1.34  #Demod        : 27
% 2.62/1.34  #Tautology    : 17
% 2.62/1.34  #SimpNegUnit  : 1
% 2.62/1.34  #BackRed      : 0
% 2.62/1.34  
% 2.62/1.34  #Partial instantiations: 0
% 2.62/1.34  #Strategies tried      : 1
% 2.62/1.34  
% 2.62/1.34  Timing (in seconds)
% 2.62/1.34  ----------------------
% 2.62/1.34  Preprocessing        : 0.30
% 2.62/1.34  Parsing              : 0.16
% 2.62/1.34  CNF conversion       : 0.02
% 2.62/1.34  Main loop            : 0.28
% 2.62/1.34  Inferencing          : 0.10
% 2.62/1.34  Reduction            : 0.07
% 2.62/1.34  Demodulation         : 0.05
% 2.62/1.34  BG Simplification    : 0.02
% 2.62/1.34  Subsumption          : 0.08
% 2.62/1.34  Abstraction          : 0.01
% 2.62/1.34  MUC search           : 0.00
% 2.62/1.34  Cooper               : 0.00
% 2.62/1.34  Total                : 0.61
% 2.62/1.34  Index Insertion      : 0.00
% 2.62/1.34  Index Deletion       : 0.00
% 2.62/1.34  Index Matching       : 0.00
% 2.62/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
