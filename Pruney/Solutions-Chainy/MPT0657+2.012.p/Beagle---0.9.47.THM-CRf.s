%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:05 EST 2020

% Result     : Theorem 2.37s
% Output     : CNFRefutation 2.49s
% Verified   : 
% Statistics : Number of formulae       :   49 (  92 expanded)
%              Number of leaves         :   21 (  44 expanded)
%              Depth                    :    8
%              Number of atoms          :  120 ( 326 expanded)
%              Number of equality atoms :   37 ( 108 expanded)
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

tff(f_43,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_53,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k4_relat_1(A))
        & v1_funct_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_funct_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_85,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_75,axiom,(
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

tff(c_20,plain,(
    k2_funct_1('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_34,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_32,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_26,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_63,plain,(
    ! [A_19] :
      ( k4_relat_1(A_19) = k2_funct_1(A_19)
      | ~ v2_funct_1(A_19)
      | ~ v1_funct_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_66,plain,
    ( k4_relat_1('#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_63])).

tff(c_69,plain,(
    k4_relat_1('#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_66])).

tff(c_2,plain,(
    ! [A_1] :
      ( v1_relat_1(k4_relat_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_82,plain,
    ( v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_2])).

tff(c_92,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_82])).

tff(c_10,plain,(
    ! [A_4] :
      ( v1_funct_1(k4_relat_1(A_4))
      | ~ v2_funct_1(A_4)
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_73,plain,
    ( v1_funct_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_10])).

tff(c_86,plain,(
    v1_funct_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_26,c_73])).

tff(c_22,plain,(
    k6_relat_1(k2_relat_1('#skF_1')) = k5_relat_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_6,plain,(
    ! [A_2] :
      ( k1_relat_1(k4_relat_1(A_2)) = k2_relat_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_76,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_6])).

tff(c_88,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_76])).

tff(c_18,plain,(
    ! [A_13] :
      ( k5_relat_1(A_13,k2_funct_1(A_13)) = k6_relat_1(k1_relat_1(A_13))
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_30,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_28,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_24,plain,(
    k2_relat_1('#skF_2') = k1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_120,plain,(
    ! [D_22,B_23,C_24] :
      ( D_22 = B_23
      | k6_relat_1(k2_relat_1(B_23)) != k5_relat_1(C_24,D_22)
      | k6_relat_1(k1_relat_1(D_22)) != k5_relat_1(B_23,C_24)
      | ~ v1_funct_1(D_22)
      | ~ v1_relat_1(D_22)
      | ~ v1_funct_1(C_24)
      | ~ v1_relat_1(C_24)
      | ~ v1_funct_1(B_23)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_132,plain,(
    ! [D_22,C_24] :
      ( D_22 = '#skF_2'
      | k6_relat_1(k1_relat_1('#skF_1')) != k5_relat_1(C_24,D_22)
      | k6_relat_1(k1_relat_1(D_22)) != k5_relat_1('#skF_2',C_24)
      | ~ v1_funct_1(D_22)
      | ~ v1_relat_1(D_22)
      | ~ v1_funct_1(C_24)
      | ~ v1_relat_1(C_24)
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_120])).

tff(c_150,plain,(
    ! [D_27,C_28] :
      ( D_27 = '#skF_2'
      | k6_relat_1(k1_relat_1('#skF_1')) != k5_relat_1(C_28,D_27)
      | k6_relat_1(k1_relat_1(D_27)) != k5_relat_1('#skF_2',C_28)
      | ~ v1_funct_1(D_27)
      | ~ v1_relat_1(D_27)
      | ~ v1_funct_1(C_28)
      | ~ v1_relat_1(C_28) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_132])).

tff(c_194,plain,(
    ! [A_37] :
      ( k2_funct_1(A_37) = '#skF_2'
      | k6_relat_1(k1_relat_1(A_37)) != k6_relat_1(k1_relat_1('#skF_1'))
      | k6_relat_1(k1_relat_1(k2_funct_1(A_37))) != k5_relat_1('#skF_2',A_37)
      | ~ v1_funct_1(k2_funct_1(A_37))
      | ~ v1_relat_1(k2_funct_1(A_37))
      | ~ v1_funct_1(A_37)
      | ~ v1_relat_1(A_37)
      | ~ v2_funct_1(A_37)
      | ~ v1_funct_1(A_37)
      | ~ v1_relat_1(A_37) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_150])).

tff(c_197,plain,
    ( k2_funct_1('#skF_1') = '#skF_2'
    | k6_relat_1(k2_relat_1('#skF_1')) != k5_relat_1('#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_194])).

tff(c_200,plain,(
    k2_funct_1('#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_26,c_92,c_86,c_22,c_197])).

tff(c_202,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_200])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:44:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.37/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.37/1.35  
% 2.37/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.37/1.36  %$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.37/1.36  
% 2.37/1.36  %Foreground sorts:
% 2.37/1.36  
% 2.37/1.36  
% 2.37/1.36  %Background operators:
% 2.37/1.36  
% 2.37/1.36  
% 2.37/1.36  %Foreground operators:
% 2.37/1.36  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.37/1.36  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.37/1.36  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.37/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.37/1.36  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.37/1.36  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.37/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.37/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.37/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.37/1.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.37/1.36  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.37/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.37/1.36  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.37/1.36  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 2.37/1.36  
% 2.49/1.37  tff(f_103, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_1)).
% 2.49/1.37  tff(f_43, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 2.49/1.37  tff(f_29, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 2.49/1.37  tff(f_53, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => (v1_relat_1(k4_relat_1(A)) & v1_funct_1(k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_funct_1)).
% 2.49/1.37  tff(f_35, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_relat_1)).
% 2.49/1.37  tff(f_85, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 2.49/1.37  tff(f_75, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (![D]: ((v1_relat_1(D) & v1_funct_1(D)) => ((((k2_relat_1(B) = A) & (k5_relat_1(B, C) = k6_relat_1(k1_relat_1(D)))) & (k5_relat_1(C, D) = k6_relat_1(A))) => (D = B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l72_funct_1)).
% 2.49/1.37  tff(c_20, plain, (k2_funct_1('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.49/1.37  tff(c_34, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.49/1.37  tff(c_32, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.49/1.37  tff(c_26, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.49/1.37  tff(c_63, plain, (![A_19]: (k4_relat_1(A_19)=k2_funct_1(A_19) | ~v2_funct_1(A_19) | ~v1_funct_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.49/1.37  tff(c_66, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_26, c_63])).
% 2.49/1.37  tff(c_69, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_66])).
% 2.49/1.37  tff(c_2, plain, (![A_1]: (v1_relat_1(k4_relat_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.49/1.37  tff(c_82, plain, (v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_69, c_2])).
% 2.49/1.37  tff(c_92, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_82])).
% 2.49/1.37  tff(c_10, plain, (![A_4]: (v1_funct_1(k4_relat_1(A_4)) | ~v2_funct_1(A_4) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.49/1.37  tff(c_73, plain, (v1_funct_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_69, c_10])).
% 2.49/1.37  tff(c_86, plain, (v1_funct_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_26, c_73])).
% 2.49/1.37  tff(c_22, plain, (k6_relat_1(k2_relat_1('#skF_1'))=k5_relat_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.49/1.37  tff(c_6, plain, (![A_2]: (k1_relat_1(k4_relat_1(A_2))=k2_relat_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.49/1.37  tff(c_76, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_69, c_6])).
% 2.49/1.37  tff(c_88, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_76])).
% 2.49/1.37  tff(c_18, plain, (![A_13]: (k5_relat_1(A_13, k2_funct_1(A_13))=k6_relat_1(k1_relat_1(A_13)) | ~v2_funct_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.49/1.37  tff(c_30, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.49/1.37  tff(c_28, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.49/1.37  tff(c_24, plain, (k2_relat_1('#skF_2')=k1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.49/1.37  tff(c_120, plain, (![D_22, B_23, C_24]: (D_22=B_23 | k6_relat_1(k2_relat_1(B_23))!=k5_relat_1(C_24, D_22) | k6_relat_1(k1_relat_1(D_22))!=k5_relat_1(B_23, C_24) | ~v1_funct_1(D_22) | ~v1_relat_1(D_22) | ~v1_funct_1(C_24) | ~v1_relat_1(C_24) | ~v1_funct_1(B_23) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.49/1.37  tff(c_132, plain, (![D_22, C_24]: (D_22='#skF_2' | k6_relat_1(k1_relat_1('#skF_1'))!=k5_relat_1(C_24, D_22) | k6_relat_1(k1_relat_1(D_22))!=k5_relat_1('#skF_2', C_24) | ~v1_funct_1(D_22) | ~v1_relat_1(D_22) | ~v1_funct_1(C_24) | ~v1_relat_1(C_24) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_24, c_120])).
% 2.49/1.37  tff(c_150, plain, (![D_27, C_28]: (D_27='#skF_2' | k6_relat_1(k1_relat_1('#skF_1'))!=k5_relat_1(C_28, D_27) | k6_relat_1(k1_relat_1(D_27))!=k5_relat_1('#skF_2', C_28) | ~v1_funct_1(D_27) | ~v1_relat_1(D_27) | ~v1_funct_1(C_28) | ~v1_relat_1(C_28))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_132])).
% 2.49/1.37  tff(c_194, plain, (![A_37]: (k2_funct_1(A_37)='#skF_2' | k6_relat_1(k1_relat_1(A_37))!=k6_relat_1(k1_relat_1('#skF_1')) | k6_relat_1(k1_relat_1(k2_funct_1(A_37)))!=k5_relat_1('#skF_2', A_37) | ~v1_funct_1(k2_funct_1(A_37)) | ~v1_relat_1(k2_funct_1(A_37)) | ~v1_funct_1(A_37) | ~v1_relat_1(A_37) | ~v2_funct_1(A_37) | ~v1_funct_1(A_37) | ~v1_relat_1(A_37))), inference(superposition, [status(thm), theory('equality')], [c_18, c_150])).
% 2.49/1.37  tff(c_197, plain, (k2_funct_1('#skF_1')='#skF_2' | k6_relat_1(k2_relat_1('#skF_1'))!=k5_relat_1('#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_88, c_194])).
% 2.49/1.37  tff(c_200, plain, (k2_funct_1('#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_26, c_92, c_86, c_22, c_197])).
% 2.49/1.37  tff(c_202, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_200])).
% 2.49/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.37  
% 2.49/1.37  Inference rules
% 2.49/1.37  ----------------------
% 2.49/1.37  #Ref     : 1
% 2.49/1.37  #Sup     : 43
% 2.49/1.37  #Fact    : 0
% 2.49/1.37  #Define  : 0
% 2.49/1.37  #Split   : 2
% 2.49/1.37  #Chain   : 0
% 2.49/1.37  #Close   : 0
% 2.49/1.37  
% 2.49/1.37  Ordering : KBO
% 2.49/1.37  
% 2.49/1.37  Simplification rules
% 2.49/1.37  ----------------------
% 2.49/1.37  #Subsume      : 1
% 2.49/1.37  #Demod        : 44
% 2.49/1.37  #Tautology    : 20
% 2.49/1.37  #SimpNegUnit  : 1
% 2.49/1.37  #BackRed      : 0
% 2.49/1.37  
% 2.49/1.37  #Partial instantiations: 0
% 2.49/1.37  #Strategies tried      : 1
% 2.49/1.37  
% 2.49/1.37  Timing (in seconds)
% 2.49/1.37  ----------------------
% 2.49/1.37  Preprocessing        : 0.32
% 2.49/1.37  Parsing              : 0.17
% 2.49/1.37  CNF conversion       : 0.02
% 2.49/1.38  Main loop            : 0.22
% 2.49/1.38  Inferencing          : 0.08
% 2.49/1.38  Reduction            : 0.06
% 2.49/1.38  Demodulation         : 0.05
% 2.49/1.38  BG Simplification    : 0.02
% 2.49/1.38  Subsumption          : 0.05
% 2.49/1.38  Abstraction          : 0.01
% 2.49/1.38  MUC search           : 0.00
% 2.49/1.38  Cooper               : 0.00
% 2.49/1.38  Total                : 0.57
% 2.49/1.38  Index Insertion      : 0.00
% 2.49/1.38  Index Deletion       : 0.00
% 2.49/1.38  Index Matching       : 0.00
% 2.49/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
