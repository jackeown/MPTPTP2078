%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:05 EST 2020

% Result     : Theorem 2.47s
% Output     : CNFRefutation 2.47s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 154 expanded)
%              Number of leaves         :   21 (  65 expanded)
%              Depth                    :   10
%              Number of atoms          :  140 ( 570 expanded)
%              Number of equality atoms :   46 ( 192 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

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

tff(f_101,negated_conjecture,(
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

tff(f_43,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_73,axiom,(
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

tff(f_83,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(c_20,plain,(
    k2_funct_1('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_34,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_32,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_26,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_64,plain,(
    ! [A_20] :
      ( k4_relat_1(A_20) = k2_funct_1(A_20)
      | ~ v2_funct_1(A_20)
      | ~ v1_funct_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_67,plain,
    ( k4_relat_1('#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_64])).

tff(c_70,plain,(
    k4_relat_1('#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_67])).

tff(c_2,plain,(
    ! [A_1] :
      ( v1_relat_1(k4_relat_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_80,plain,
    ( v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_2])).

tff(c_88,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_80])).

tff(c_10,plain,(
    ! [A_4] :
      ( v1_funct_1(k2_funct_1(A_4))
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4,plain,(
    ! [A_2] :
      ( k2_relat_1(k4_relat_1(A_2)) = k1_relat_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_77,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_4])).

tff(c_86,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_77])).

tff(c_116,plain,(
    ! [D_23,B_24,C_25] :
      ( D_23 = B_24
      | k6_relat_1(k2_relat_1(B_24)) != k5_relat_1(C_25,D_23)
      | k6_relat_1(k1_relat_1(D_23)) != k5_relat_1(B_24,C_25)
      | ~ v1_funct_1(D_23)
      | ~ v1_relat_1(D_23)
      | ~ v1_funct_1(C_25)
      | ~ v1_relat_1(C_25)
      | ~ v1_funct_1(B_24)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_120,plain,(
    ! [D_23,C_25] :
      ( k2_funct_1('#skF_1') = D_23
      | k6_relat_1(k1_relat_1('#skF_1')) != k5_relat_1(C_25,D_23)
      | k6_relat_1(k1_relat_1(D_23)) != k5_relat_1(k2_funct_1('#skF_1'),C_25)
      | ~ v1_funct_1(D_23)
      | ~ v1_relat_1(D_23)
      | ~ v1_funct_1(C_25)
      | ~ v1_relat_1(C_25)
      | ~ v1_funct_1(k2_funct_1('#skF_1'))
      | ~ v1_relat_1(k2_funct_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_116])).

tff(c_130,plain,(
    ! [D_23,C_25] :
      ( k2_funct_1('#skF_1') = D_23
      | k6_relat_1(k1_relat_1('#skF_1')) != k5_relat_1(C_25,D_23)
      | k6_relat_1(k1_relat_1(D_23)) != k5_relat_1(k2_funct_1('#skF_1'),C_25)
      | ~ v1_funct_1(D_23)
      | ~ v1_relat_1(D_23)
      | ~ v1_funct_1(C_25)
      | ~ v1_relat_1(C_25)
      | ~ v1_funct_1(k2_funct_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_120])).

tff(c_151,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_130])).

tff(c_154,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_151])).

tff(c_158,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_154])).

tff(c_160,plain,(
    v1_funct_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_130])).

tff(c_22,plain,(
    k6_relat_1(k2_relat_1('#skF_1')) = k5_relat_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_6,plain,(
    ! [A_2] :
      ( k1_relat_1(k4_relat_1(A_2)) = k2_relat_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_74,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_6])).

tff(c_84,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_74])).

tff(c_18,plain,(
    ! [A_13] :
      ( k5_relat_1(A_13,k2_funct_1(A_13)) = k6_relat_1(k1_relat_1(A_13))
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_30,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_28,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_24,plain,(
    k2_relat_1('#skF_2') = k1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_128,plain,(
    ! [D_23,C_25] :
      ( D_23 = '#skF_2'
      | k6_relat_1(k1_relat_1('#skF_1')) != k5_relat_1(C_25,D_23)
      | k6_relat_1(k1_relat_1(D_23)) != k5_relat_1('#skF_2',C_25)
      | ~ v1_funct_1(D_23)
      | ~ v1_relat_1(D_23)
      | ~ v1_funct_1(C_25)
      | ~ v1_relat_1(C_25)
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_116])).

tff(c_146,plain,(
    ! [D_28,C_29] :
      ( D_28 = '#skF_2'
      | k6_relat_1(k1_relat_1('#skF_1')) != k5_relat_1(C_29,D_28)
      | k6_relat_1(k1_relat_1(D_28)) != k5_relat_1('#skF_2',C_29)
      | ~ v1_funct_1(D_28)
      | ~ v1_relat_1(D_28)
      | ~ v1_funct_1(C_29)
      | ~ v1_relat_1(C_29) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_128])).

tff(c_257,plain,(
    ! [A_44] :
      ( k2_funct_1(A_44) = '#skF_2'
      | k6_relat_1(k1_relat_1(A_44)) != k6_relat_1(k1_relat_1('#skF_1'))
      | k6_relat_1(k1_relat_1(k2_funct_1(A_44))) != k5_relat_1('#skF_2',A_44)
      | ~ v1_funct_1(k2_funct_1(A_44))
      | ~ v1_relat_1(k2_funct_1(A_44))
      | ~ v1_funct_1(A_44)
      | ~ v1_relat_1(A_44)
      | ~ v2_funct_1(A_44)
      | ~ v1_funct_1(A_44)
      | ~ v1_relat_1(A_44) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_146])).

tff(c_260,plain,
    ( k2_funct_1('#skF_1') = '#skF_2'
    | k6_relat_1(k2_relat_1('#skF_1')) != k5_relat_1('#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_257])).

tff(c_263,plain,(
    k2_funct_1('#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_26,c_88,c_160,c_22,c_260])).

tff(c_265,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_263])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:34:22 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.47/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.37  
% 2.47/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.37  %$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.47/1.37  
% 2.47/1.37  %Foreground sorts:
% 2.47/1.37  
% 2.47/1.37  
% 2.47/1.37  %Background operators:
% 2.47/1.37  
% 2.47/1.37  
% 2.47/1.37  %Foreground operators:
% 2.47/1.37  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.47/1.37  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.47/1.37  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.47/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.47/1.37  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.47/1.37  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.47/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.47/1.37  tff('#skF_1', type, '#skF_1': $i).
% 2.47/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.47/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.47/1.37  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.47/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.47/1.37  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.47/1.37  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 2.47/1.37  
% 2.47/1.39  tff(f_101, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_1)).
% 2.47/1.39  tff(f_43, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 2.47/1.39  tff(f_29, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 2.47/1.39  tff(f_51, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 2.47/1.39  tff(f_35, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_relat_1)).
% 2.47/1.39  tff(f_73, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (![D]: ((v1_relat_1(D) & v1_funct_1(D)) => ((((k2_relat_1(B) = A) & (k5_relat_1(B, C) = k6_relat_1(k1_relat_1(D)))) & (k5_relat_1(C, D) = k6_relat_1(A))) => (D = B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l72_funct_1)).
% 2.47/1.39  tff(f_83, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 2.47/1.39  tff(c_20, plain, (k2_funct_1('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.47/1.39  tff(c_34, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.47/1.39  tff(c_32, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.47/1.39  tff(c_26, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.47/1.39  tff(c_64, plain, (![A_20]: (k4_relat_1(A_20)=k2_funct_1(A_20) | ~v2_funct_1(A_20) | ~v1_funct_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.47/1.39  tff(c_67, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_26, c_64])).
% 2.47/1.39  tff(c_70, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_67])).
% 2.47/1.39  tff(c_2, plain, (![A_1]: (v1_relat_1(k4_relat_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.47/1.39  tff(c_80, plain, (v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_70, c_2])).
% 2.47/1.39  tff(c_88, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_80])).
% 2.47/1.39  tff(c_10, plain, (![A_4]: (v1_funct_1(k2_funct_1(A_4)) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.47/1.39  tff(c_4, plain, (![A_2]: (k2_relat_1(k4_relat_1(A_2))=k1_relat_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.47/1.39  tff(c_77, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_70, c_4])).
% 2.47/1.39  tff(c_86, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_77])).
% 2.47/1.39  tff(c_116, plain, (![D_23, B_24, C_25]: (D_23=B_24 | k6_relat_1(k2_relat_1(B_24))!=k5_relat_1(C_25, D_23) | k6_relat_1(k1_relat_1(D_23))!=k5_relat_1(B_24, C_25) | ~v1_funct_1(D_23) | ~v1_relat_1(D_23) | ~v1_funct_1(C_25) | ~v1_relat_1(C_25) | ~v1_funct_1(B_24) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.47/1.39  tff(c_120, plain, (![D_23, C_25]: (k2_funct_1('#skF_1')=D_23 | k6_relat_1(k1_relat_1('#skF_1'))!=k5_relat_1(C_25, D_23) | k6_relat_1(k1_relat_1(D_23))!=k5_relat_1(k2_funct_1('#skF_1'), C_25) | ~v1_funct_1(D_23) | ~v1_relat_1(D_23) | ~v1_funct_1(C_25) | ~v1_relat_1(C_25) | ~v1_funct_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_86, c_116])).
% 2.47/1.39  tff(c_130, plain, (![D_23, C_25]: (k2_funct_1('#skF_1')=D_23 | k6_relat_1(k1_relat_1('#skF_1'))!=k5_relat_1(C_25, D_23) | k6_relat_1(k1_relat_1(D_23))!=k5_relat_1(k2_funct_1('#skF_1'), C_25) | ~v1_funct_1(D_23) | ~v1_relat_1(D_23) | ~v1_funct_1(C_25) | ~v1_relat_1(C_25) | ~v1_funct_1(k2_funct_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_120])).
% 2.47/1.39  tff(c_151, plain, (~v1_funct_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_130])).
% 2.47/1.39  tff(c_154, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_10, c_151])).
% 2.47/1.39  tff(c_158, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_154])).
% 2.47/1.39  tff(c_160, plain, (v1_funct_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_130])).
% 2.47/1.39  tff(c_22, plain, (k6_relat_1(k2_relat_1('#skF_1'))=k5_relat_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.47/1.39  tff(c_6, plain, (![A_2]: (k1_relat_1(k4_relat_1(A_2))=k2_relat_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.47/1.39  tff(c_74, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_70, c_6])).
% 2.47/1.39  tff(c_84, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_74])).
% 2.47/1.39  tff(c_18, plain, (![A_13]: (k5_relat_1(A_13, k2_funct_1(A_13))=k6_relat_1(k1_relat_1(A_13)) | ~v2_funct_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.47/1.39  tff(c_30, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.47/1.39  tff(c_28, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.47/1.39  tff(c_24, plain, (k2_relat_1('#skF_2')=k1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.47/1.39  tff(c_128, plain, (![D_23, C_25]: (D_23='#skF_2' | k6_relat_1(k1_relat_1('#skF_1'))!=k5_relat_1(C_25, D_23) | k6_relat_1(k1_relat_1(D_23))!=k5_relat_1('#skF_2', C_25) | ~v1_funct_1(D_23) | ~v1_relat_1(D_23) | ~v1_funct_1(C_25) | ~v1_relat_1(C_25) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_24, c_116])).
% 2.47/1.39  tff(c_146, plain, (![D_28, C_29]: (D_28='#skF_2' | k6_relat_1(k1_relat_1('#skF_1'))!=k5_relat_1(C_29, D_28) | k6_relat_1(k1_relat_1(D_28))!=k5_relat_1('#skF_2', C_29) | ~v1_funct_1(D_28) | ~v1_relat_1(D_28) | ~v1_funct_1(C_29) | ~v1_relat_1(C_29))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_128])).
% 2.47/1.39  tff(c_257, plain, (![A_44]: (k2_funct_1(A_44)='#skF_2' | k6_relat_1(k1_relat_1(A_44))!=k6_relat_1(k1_relat_1('#skF_1')) | k6_relat_1(k1_relat_1(k2_funct_1(A_44)))!=k5_relat_1('#skF_2', A_44) | ~v1_funct_1(k2_funct_1(A_44)) | ~v1_relat_1(k2_funct_1(A_44)) | ~v1_funct_1(A_44) | ~v1_relat_1(A_44) | ~v2_funct_1(A_44) | ~v1_funct_1(A_44) | ~v1_relat_1(A_44))), inference(superposition, [status(thm), theory('equality')], [c_18, c_146])).
% 2.47/1.39  tff(c_260, plain, (k2_funct_1('#skF_1')='#skF_2' | k6_relat_1(k2_relat_1('#skF_1'))!=k5_relat_1('#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_84, c_257])).
% 2.47/1.39  tff(c_263, plain, (k2_funct_1('#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_26, c_88, c_160, c_22, c_260])).
% 2.47/1.39  tff(c_265, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_263])).
% 2.47/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.39  
% 2.47/1.39  Inference rules
% 2.47/1.39  ----------------------
% 2.47/1.39  #Ref     : 1
% 2.47/1.39  #Sup     : 53
% 2.47/1.39  #Fact    : 0
% 2.47/1.39  #Define  : 0
% 2.47/1.39  #Split   : 3
% 2.47/1.39  #Chain   : 0
% 2.47/1.39  #Close   : 0
% 2.47/1.39  
% 2.47/1.39  Ordering : KBO
% 2.47/1.39  
% 2.47/1.39  Simplification rules
% 2.47/1.39  ----------------------
% 2.47/1.39  #Subsume      : 5
% 2.47/1.39  #Demod        : 57
% 2.47/1.39  #Tautology    : 24
% 2.47/1.39  #SimpNegUnit  : 1
% 2.47/1.39  #BackRed      : 0
% 2.47/1.39  
% 2.47/1.39  #Partial instantiations: 0
% 2.47/1.39  #Strategies tried      : 1
% 2.47/1.39  
% 2.47/1.39  Timing (in seconds)
% 2.47/1.39  ----------------------
% 2.47/1.39  Preprocessing        : 0.33
% 2.47/1.39  Parsing              : 0.17
% 2.47/1.39  CNF conversion       : 0.02
% 2.47/1.39  Main loop            : 0.27
% 2.47/1.39  Inferencing          : 0.10
% 2.47/1.39  Reduction            : 0.07
% 2.47/1.39  Demodulation         : 0.05
% 2.47/1.39  BG Simplification    : 0.02
% 2.47/1.39  Subsumption          : 0.06
% 2.47/1.39  Abstraction          : 0.01
% 2.47/1.39  MUC search           : 0.00
% 2.47/1.39  Cooper               : 0.00
% 2.47/1.39  Total                : 0.63
% 2.47/1.39  Index Insertion      : 0.00
% 2.47/1.39  Index Deletion       : 0.00
% 2.47/1.39  Index Matching       : 0.00
% 2.47/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
