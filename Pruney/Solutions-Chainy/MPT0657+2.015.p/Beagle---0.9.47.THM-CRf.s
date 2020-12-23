%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:06 EST 2020

% Result     : Theorem 2.46s
% Output     : CNFRefutation 2.46s
% Verified   : 
% Statistics : Number of formulae       :   47 (  83 expanded)
%              Number of leaves         :   20 (  41 expanded)
%              Depth                    :    8
%              Number of atoms          :  139 ( 320 expanded)
%              Number of equality atoms :   38 (  99 expanded)
%              Maximal formula depth    :   15 (   5 average)
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

tff(f_103,negated_conjecture,(
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

tff(f_33,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_43,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k4_relat_1(A))
        & v1_funct_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_funct_1)).

tff(f_75,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_85,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l72_funct_1)).

tff(c_18,plain,(
    k2_funct_1('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_32,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_30,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_24,plain,(
    v2_funct_1('#skF_1') ),
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
    k6_relat_1(k2_relat_1('#skF_1')) = k5_relat_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

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

tff(c_12,plain,(
    ! [A_11] :
      ( k1_relat_1(k2_funct_1(A_11)) = k2_relat_1(A_11)
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_28,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_26,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_22,plain,(
    k2_relat_1('#skF_2') = k1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_16,plain,(
    ! [A_12] :
      ( k5_relat_1(A_12,k2_funct_1(A_12)) = k6_relat_1(k1_relat_1(A_12))
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

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

tff(c_163,plain,(
    ! [A_34,B_35] :
      ( k2_funct_1(A_34) = B_35
      | k6_relat_1(k2_relat_1(B_35)) != k6_relat_1(k1_relat_1(A_34))
      | k6_relat_1(k1_relat_1(k2_funct_1(A_34))) != k5_relat_1(B_35,A_34)
      | ~ v1_funct_1(k2_funct_1(A_34))
      | ~ v1_relat_1(k2_funct_1(A_34))
      | ~ v1_funct_1(A_34)
      | ~ v1_relat_1(A_34)
      | ~ v1_funct_1(B_35)
      | ~ v1_relat_1(B_35)
      | ~ v2_funct_1(A_34)
      | ~ v1_funct_1(A_34)
      | ~ v1_relat_1(A_34) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_100])).

tff(c_171,plain,(
    ! [A_34] :
      ( k2_funct_1(A_34) = '#skF_2'
      | k6_relat_1(k1_relat_1(A_34)) != k6_relat_1(k1_relat_1('#skF_1'))
      | k6_relat_1(k1_relat_1(k2_funct_1(A_34))) != k5_relat_1('#skF_2',A_34)
      | ~ v1_funct_1(k2_funct_1(A_34))
      | ~ v1_relat_1(k2_funct_1(A_34))
      | ~ v1_funct_1(A_34)
      | ~ v1_relat_1(A_34)
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2')
      | ~ v2_funct_1(A_34)
      | ~ v1_funct_1(A_34)
      | ~ v1_relat_1(A_34) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_163])).

tff(c_180,plain,(
    ! [A_37] :
      ( k2_funct_1(A_37) = '#skF_2'
      | k6_relat_1(k1_relat_1(A_37)) != k6_relat_1(k1_relat_1('#skF_1'))
      | k6_relat_1(k1_relat_1(k2_funct_1(A_37))) != k5_relat_1('#skF_2',A_37)
      | ~ v1_funct_1(k2_funct_1(A_37))
      | ~ v1_relat_1(k2_funct_1(A_37))
      | ~ v2_funct_1(A_37)
      | ~ v1_funct_1(A_37)
      | ~ v1_relat_1(A_37) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_171])).

tff(c_192,plain,(
    ! [A_39] :
      ( k2_funct_1(A_39) = '#skF_2'
      | k6_relat_1(k1_relat_1(A_39)) != k6_relat_1(k1_relat_1('#skF_1'))
      | k6_relat_1(k2_relat_1(A_39)) != k5_relat_1('#skF_2',A_39)
      | ~ v1_funct_1(k2_funct_1(A_39))
      | ~ v1_relat_1(k2_funct_1(A_39))
      | ~ v2_funct_1(A_39)
      | ~ v1_funct_1(A_39)
      | ~ v1_relat_1(A_39)
      | ~ v2_funct_1(A_39)
      | ~ v1_funct_1(A_39)
      | ~ v1_relat_1(A_39) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_180])).

tff(c_195,plain,
    ( k2_funct_1('#skF_1') = '#skF_2'
    | k6_relat_1(k2_relat_1('#skF_1')) != k5_relat_1('#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_192])).

tff(c_198,plain,(
    k2_funct_1('#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_24,c_60,c_20,c_195])).

tff(c_200,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_198])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:18:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.46/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.46/1.34  
% 2.46/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.46/1.34  %$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.46/1.34  
% 2.46/1.34  %Foreground sorts:
% 2.46/1.34  
% 2.46/1.34  
% 2.46/1.34  %Background operators:
% 2.46/1.34  
% 2.46/1.34  
% 2.46/1.34  %Foreground operators:
% 2.46/1.34  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.46/1.34  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.46/1.34  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.46/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.46/1.34  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.46/1.34  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.46/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.46/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.46/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.46/1.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.46/1.34  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.46/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.46/1.34  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.46/1.34  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 2.46/1.34  
% 2.46/1.35  tff(f_103, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_1)).
% 2.46/1.35  tff(f_33, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 2.46/1.35  tff(f_43, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => (v1_relat_1(k4_relat_1(A)) & v1_funct_1(k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_funct_1)).
% 2.46/1.35  tff(f_75, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 2.46/1.35  tff(f_85, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 2.46/1.35  tff(f_65, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (![D]: ((v1_relat_1(D) & v1_funct_1(D)) => ((((k2_relat_1(B) = A) & (k5_relat_1(B, C) = k6_relat_1(k1_relat_1(D)))) & (k5_relat_1(C, D) = k6_relat_1(A))) => (D = B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l72_funct_1)).
% 2.46/1.35  tff(c_18, plain, (k2_funct_1('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.46/1.35  tff(c_32, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.46/1.35  tff(c_30, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.46/1.35  tff(c_24, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.46/1.35  tff(c_43, plain, (![A_16]: (k4_relat_1(A_16)=k2_funct_1(A_16) | ~v2_funct_1(A_16) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.46/1.35  tff(c_46, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_24, c_43])).
% 2.46/1.35  tff(c_49, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_46])).
% 2.46/1.35  tff(c_4, plain, (![A_2]: (v1_funct_1(k4_relat_1(A_2)) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.46/1.35  tff(c_53, plain, (v1_funct_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_49, c_4])).
% 2.46/1.35  tff(c_60, plain, (v1_funct_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_24, c_53])).
% 2.46/1.35  tff(c_20, plain, (k6_relat_1(k2_relat_1('#skF_1'))=k5_relat_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.46/1.35  tff(c_6, plain, (![A_2]: (v1_relat_1(k4_relat_1(A_2)) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.46/1.35  tff(c_56, plain, (v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_49, c_6])).
% 2.46/1.35  tff(c_62, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_24, c_56])).
% 2.46/1.35  tff(c_12, plain, (![A_11]: (k1_relat_1(k2_funct_1(A_11))=k2_relat_1(A_11) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.46/1.35  tff(c_28, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.46/1.35  tff(c_26, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.46/1.35  tff(c_22, plain, (k2_relat_1('#skF_2')=k1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.46/1.35  tff(c_16, plain, (![A_12]: (k5_relat_1(A_12, k2_funct_1(A_12))=k6_relat_1(k1_relat_1(A_12)) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.46/1.35  tff(c_100, plain, (![D_21, B_22, C_23]: (D_21=B_22 | k6_relat_1(k2_relat_1(B_22))!=k5_relat_1(C_23, D_21) | k6_relat_1(k1_relat_1(D_21))!=k5_relat_1(B_22, C_23) | ~v1_funct_1(D_21) | ~v1_relat_1(D_21) | ~v1_funct_1(C_23) | ~v1_relat_1(C_23) | ~v1_funct_1(B_22) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.46/1.35  tff(c_163, plain, (![A_34, B_35]: (k2_funct_1(A_34)=B_35 | k6_relat_1(k2_relat_1(B_35))!=k6_relat_1(k1_relat_1(A_34)) | k6_relat_1(k1_relat_1(k2_funct_1(A_34)))!=k5_relat_1(B_35, A_34) | ~v1_funct_1(k2_funct_1(A_34)) | ~v1_relat_1(k2_funct_1(A_34)) | ~v1_funct_1(A_34) | ~v1_relat_1(A_34) | ~v1_funct_1(B_35) | ~v1_relat_1(B_35) | ~v2_funct_1(A_34) | ~v1_funct_1(A_34) | ~v1_relat_1(A_34))), inference(superposition, [status(thm), theory('equality')], [c_16, c_100])).
% 2.46/1.35  tff(c_171, plain, (![A_34]: (k2_funct_1(A_34)='#skF_2' | k6_relat_1(k1_relat_1(A_34))!=k6_relat_1(k1_relat_1('#skF_1')) | k6_relat_1(k1_relat_1(k2_funct_1(A_34)))!=k5_relat_1('#skF_2', A_34) | ~v1_funct_1(k2_funct_1(A_34)) | ~v1_relat_1(k2_funct_1(A_34)) | ~v1_funct_1(A_34) | ~v1_relat_1(A_34) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v2_funct_1(A_34) | ~v1_funct_1(A_34) | ~v1_relat_1(A_34))), inference(superposition, [status(thm), theory('equality')], [c_22, c_163])).
% 2.46/1.35  tff(c_180, plain, (![A_37]: (k2_funct_1(A_37)='#skF_2' | k6_relat_1(k1_relat_1(A_37))!=k6_relat_1(k1_relat_1('#skF_1')) | k6_relat_1(k1_relat_1(k2_funct_1(A_37)))!=k5_relat_1('#skF_2', A_37) | ~v1_funct_1(k2_funct_1(A_37)) | ~v1_relat_1(k2_funct_1(A_37)) | ~v2_funct_1(A_37) | ~v1_funct_1(A_37) | ~v1_relat_1(A_37))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_171])).
% 2.46/1.35  tff(c_192, plain, (![A_39]: (k2_funct_1(A_39)='#skF_2' | k6_relat_1(k1_relat_1(A_39))!=k6_relat_1(k1_relat_1('#skF_1')) | k6_relat_1(k2_relat_1(A_39))!=k5_relat_1('#skF_2', A_39) | ~v1_funct_1(k2_funct_1(A_39)) | ~v1_relat_1(k2_funct_1(A_39)) | ~v2_funct_1(A_39) | ~v1_funct_1(A_39) | ~v1_relat_1(A_39) | ~v2_funct_1(A_39) | ~v1_funct_1(A_39) | ~v1_relat_1(A_39))), inference(superposition, [status(thm), theory('equality')], [c_12, c_180])).
% 2.46/1.35  tff(c_195, plain, (k2_funct_1('#skF_1')='#skF_2' | k6_relat_1(k2_relat_1('#skF_1'))!=k5_relat_1('#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_62, c_192])).
% 2.46/1.35  tff(c_198, plain, (k2_funct_1('#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_24, c_60, c_20, c_195])).
% 2.46/1.35  tff(c_200, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_198])).
% 2.46/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.46/1.35  
% 2.46/1.35  Inference rules
% 2.46/1.35  ----------------------
% 2.46/1.35  #Ref     : 1
% 2.46/1.35  #Sup     : 40
% 2.46/1.35  #Fact    : 0
% 2.46/1.35  #Define  : 0
% 2.46/1.35  #Split   : 2
% 2.46/1.35  #Chain   : 0
% 2.46/1.35  #Close   : 0
% 2.46/1.35  
% 2.46/1.35  Ordering : KBO
% 2.46/1.35  
% 2.46/1.35  Simplification rules
% 2.46/1.35  ----------------------
% 2.46/1.35  #Subsume      : 2
% 2.46/1.35  #Demod        : 40
% 2.46/1.35  #Tautology    : 17
% 2.46/1.35  #SimpNegUnit  : 1
% 2.46/1.35  #BackRed      : 0
% 2.46/1.35  
% 2.46/1.35  #Partial instantiations: 0
% 2.46/1.35  #Strategies tried      : 1
% 2.46/1.35  
% 2.46/1.35  Timing (in seconds)
% 2.46/1.35  ----------------------
% 2.46/1.35  Preprocessing        : 0.33
% 2.46/1.35  Parsing              : 0.17
% 2.46/1.35  CNF conversion       : 0.02
% 2.46/1.35  Main loop            : 0.24
% 2.46/1.35  Inferencing          : 0.09
% 2.46/1.35  Reduction            : 0.06
% 2.46/1.36  Demodulation         : 0.04
% 2.46/1.36  BG Simplification    : 0.02
% 2.46/1.36  Subsumption          : 0.05
% 2.46/1.36  Abstraction          : 0.01
% 2.46/1.36  MUC search           : 0.00
% 2.46/1.36  Cooper               : 0.00
% 2.46/1.36  Total                : 0.59
% 2.46/1.36  Index Insertion      : 0.00
% 2.46/1.36  Index Deletion       : 0.00
% 2.46/1.36  Index Matching       : 0.00
% 2.46/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
