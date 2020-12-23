%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:06 EST 2020

% Result     : Theorem 2.32s
% Output     : CNFRefutation 2.32s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 188 expanded)
%              Number of leaves         :   23 (  78 expanded)
%              Depth                    :   16
%              Number of atoms          :  127 ( 622 expanded)
%              Number of equality atoms :   50 ( 238 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k10_relat_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

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

tff(f_100,negated_conjecture,(
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

tff(f_52,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_44,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( ? [B] :
            ( v1_relat_1(B)
            & v1_funct_1(B)
            & k5_relat_1(A,B) = k6_relat_1(k1_relat_1(A)) )
       => v2_funct_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_funct_1)).

tff(f_82,axiom,(
    ! [A] :
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

tff(f_29,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k4_relat_1(k4_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

tff(c_18,plain,(
    k2_funct_1('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_28,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_32,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_30,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_24,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_116,plain,(
    ! [A_19] :
      ( k4_relat_1(A_19) = k2_funct_1(A_19)
      | ~ v2_funct_1(A_19)
      | ~ v1_funct_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_119,plain,
    ( k4_relat_1('#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_116])).

tff(c_122,plain,(
    k4_relat_1('#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_119])).

tff(c_26,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_20,plain,(
    k6_relat_1(k2_relat_1('#skF_1')) = k5_relat_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_8,plain,(
    ! [A_6] : k1_relat_1(k6_relat_1(A_6)) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_61,plain,(
    k1_relat_1(k5_relat_1('#skF_2','#skF_1')) = k2_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_8])).

tff(c_145,plain,(
    ! [A_21,B_22] :
      ( k10_relat_1(A_21,k1_relat_1(B_22)) = k1_relat_1(k5_relat_1(A_21,B_22))
      | ~ v1_relat_1(B_22)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_22,plain,(
    k2_relat_1('#skF_2') = k1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_90,plain,(
    ! [A_18] :
      ( k10_relat_1(A_18,k2_relat_1(A_18)) = k1_relat_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_105,plain,
    ( k10_relat_1('#skF_2',k1_relat_1('#skF_1')) = k1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_90])).

tff(c_111,plain,(
    k10_relat_1('#skF_2',k1_relat_1('#skF_1')) = k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_105])).

tff(c_151,plain,
    ( k1_relat_1(k5_relat_1('#skF_2','#skF_1')) = k1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_111])).

tff(c_166,plain,(
    k2_relat_1('#skF_1') = k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_32,c_61,c_151])).

tff(c_172,plain,(
    k6_relat_1(k1_relat_1('#skF_2')) = k5_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_20])).

tff(c_196,plain,(
    ! [A_23,B_24] :
      ( v2_funct_1(A_23)
      | k6_relat_1(k1_relat_1(A_23)) != k5_relat_1(A_23,B_24)
      | ~ v1_funct_1(B_24)
      | ~ v1_relat_1(B_24)
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_198,plain,(
    ! [B_24] :
      ( v2_funct_1('#skF_2')
      | k5_relat_1('#skF_2',B_24) != k5_relat_1('#skF_2','#skF_1')
      | ~ v1_funct_1(B_24)
      | ~ v1_relat_1(B_24)
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_196])).

tff(c_202,plain,(
    ! [B_24] :
      ( v2_funct_1('#skF_2')
      | k5_relat_1('#skF_2',B_24) != k5_relat_1('#skF_2','#skF_1')
      | ~ v1_funct_1(B_24)
      | ~ v1_relat_1(B_24) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_198])).

tff(c_261,plain,(
    ! [B_27] :
      ( k5_relat_1('#skF_2',B_27) != k5_relat_1('#skF_2','#skF_1')
      | ~ v1_funct_1(B_27)
      | ~ v1_relat_1(B_27) ) ),
    inference(splitLeft,[status(thm)],[c_202])).

tff(c_267,plain,(
    ~ v1_funct_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_261])).

tff(c_274,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_267])).

tff(c_275,plain,(
    v2_funct_1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_202])).

tff(c_322,plain,(
    ! [A_32,B_33] :
      ( k2_funct_1(A_32) = B_33
      | k6_relat_1(k1_relat_1(A_32)) != k5_relat_1(A_32,B_33)
      | k2_relat_1(A_32) != k1_relat_1(B_33)
      | ~ v2_funct_1(A_32)
      | ~ v1_funct_1(B_33)
      | ~ v1_relat_1(B_33)
      | ~ v1_funct_1(A_32)
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_330,plain,(
    ! [B_33] :
      ( k2_funct_1('#skF_2') = B_33
      | k5_relat_1('#skF_2',B_33) != k5_relat_1('#skF_2','#skF_1')
      | k2_relat_1('#skF_2') != k1_relat_1(B_33)
      | ~ v2_funct_1('#skF_2')
      | ~ v1_funct_1(B_33)
      | ~ v1_relat_1(B_33)
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_322])).

tff(c_342,plain,(
    ! [B_36] :
      ( k2_funct_1('#skF_2') = B_36
      | k5_relat_1('#skF_2',B_36) != k5_relat_1('#skF_2','#skF_1')
      | k1_relat_1(B_36) != k1_relat_1('#skF_1')
      | ~ v1_funct_1(B_36)
      | ~ v1_relat_1(B_36) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_275,c_22,c_330])).

tff(c_348,plain,
    ( k2_funct_1('#skF_2') = '#skF_1'
    | ~ v1_funct_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_342])).

tff(c_354,plain,(
    k2_funct_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_348])).

tff(c_12,plain,(
    ! [A_7] :
      ( k4_relat_1(A_7) = k2_funct_1(A_7)
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_278,plain,
    ( k4_relat_1('#skF_2') = k2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_275,c_12])).

tff(c_281,plain,(
    k4_relat_1('#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_278])).

tff(c_357,plain,(
    k4_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_354,c_281])).

tff(c_2,plain,(
    ! [A_1] :
      ( k4_relat_1(k4_relat_1(A_1)) = A_1
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_365,plain,
    ( k4_relat_1('#skF_1') = '#skF_2'
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_357,c_2])).

tff(c_369,plain,(
    k2_funct_1('#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_122,c_365])).

tff(c_371,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_369])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:38:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.32/1.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.42  
% 2.32/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.42  %$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k10_relat_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.32/1.42  
% 2.32/1.42  %Foreground sorts:
% 2.32/1.42  
% 2.32/1.42  
% 2.32/1.42  %Background operators:
% 2.32/1.42  
% 2.32/1.42  
% 2.32/1.42  %Foreground operators:
% 2.32/1.42  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.32/1.42  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.32/1.42  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.32/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.32/1.42  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.32/1.42  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.32/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.32/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.32/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.32/1.42  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.32/1.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.32/1.42  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.32/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.32/1.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.32/1.42  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 2.32/1.42  
% 2.32/1.43  tff(f_100, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_1)).
% 2.32/1.43  tff(f_52, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 2.32/1.43  tff(f_44, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.32/1.43  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 2.32/1.43  tff(f_33, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 2.32/1.43  tff(f_65, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((?[B]: ((v1_relat_1(B) & v1_funct_1(B)) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A))))) => v2_funct_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_funct_1)).
% 2.32/1.43  tff(f_82, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(A) = k1_relat_1(B))) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_funct_1)).
% 2.32/1.43  tff(f_29, axiom, (![A]: (v1_relat_1(A) => (k4_relat_1(k4_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k4_relat_1)).
% 2.32/1.43  tff(c_18, plain, (k2_funct_1('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.32/1.43  tff(c_28, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.32/1.43  tff(c_32, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.32/1.43  tff(c_30, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.32/1.43  tff(c_24, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.32/1.43  tff(c_116, plain, (![A_19]: (k4_relat_1(A_19)=k2_funct_1(A_19) | ~v2_funct_1(A_19) | ~v1_funct_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.32/1.43  tff(c_119, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_24, c_116])).
% 2.32/1.43  tff(c_122, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_119])).
% 2.32/1.43  tff(c_26, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.32/1.43  tff(c_20, plain, (k6_relat_1(k2_relat_1('#skF_1'))=k5_relat_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.32/1.43  tff(c_8, plain, (![A_6]: (k1_relat_1(k6_relat_1(A_6))=A_6)), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.32/1.43  tff(c_61, plain, (k1_relat_1(k5_relat_1('#skF_2', '#skF_1'))=k2_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_20, c_8])).
% 2.32/1.43  tff(c_145, plain, (![A_21, B_22]: (k10_relat_1(A_21, k1_relat_1(B_22))=k1_relat_1(k5_relat_1(A_21, B_22)) | ~v1_relat_1(B_22) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.32/1.43  tff(c_22, plain, (k2_relat_1('#skF_2')=k1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.32/1.43  tff(c_90, plain, (![A_18]: (k10_relat_1(A_18, k2_relat_1(A_18))=k1_relat_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.32/1.43  tff(c_105, plain, (k10_relat_1('#skF_2', k1_relat_1('#skF_1'))=k1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_22, c_90])).
% 2.32/1.43  tff(c_111, plain, (k10_relat_1('#skF_2', k1_relat_1('#skF_1'))=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_105])).
% 2.32/1.43  tff(c_151, plain, (k1_relat_1(k5_relat_1('#skF_2', '#skF_1'))=k1_relat_1('#skF_2') | ~v1_relat_1('#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_145, c_111])).
% 2.32/1.43  tff(c_166, plain, (k2_relat_1('#skF_1')=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_32, c_61, c_151])).
% 2.32/1.43  tff(c_172, plain, (k6_relat_1(k1_relat_1('#skF_2'))=k5_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_166, c_20])).
% 2.32/1.43  tff(c_196, plain, (![A_23, B_24]: (v2_funct_1(A_23) | k6_relat_1(k1_relat_1(A_23))!=k5_relat_1(A_23, B_24) | ~v1_funct_1(B_24) | ~v1_relat_1(B_24) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.32/1.43  tff(c_198, plain, (![B_24]: (v2_funct_1('#skF_2') | k5_relat_1('#skF_2', B_24)!=k5_relat_1('#skF_2', '#skF_1') | ~v1_funct_1(B_24) | ~v1_relat_1(B_24) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_172, c_196])).
% 2.32/1.43  tff(c_202, plain, (![B_24]: (v2_funct_1('#skF_2') | k5_relat_1('#skF_2', B_24)!=k5_relat_1('#skF_2', '#skF_1') | ~v1_funct_1(B_24) | ~v1_relat_1(B_24))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_198])).
% 2.32/1.43  tff(c_261, plain, (![B_27]: (k5_relat_1('#skF_2', B_27)!=k5_relat_1('#skF_2', '#skF_1') | ~v1_funct_1(B_27) | ~v1_relat_1(B_27))), inference(splitLeft, [status(thm)], [c_202])).
% 2.32/1.43  tff(c_267, plain, (~v1_funct_1('#skF_1')), inference(resolution, [status(thm)], [c_32, c_261])).
% 2.32/1.43  tff(c_274, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_267])).
% 2.32/1.43  tff(c_275, plain, (v2_funct_1('#skF_2')), inference(splitRight, [status(thm)], [c_202])).
% 2.32/1.43  tff(c_322, plain, (![A_32, B_33]: (k2_funct_1(A_32)=B_33 | k6_relat_1(k1_relat_1(A_32))!=k5_relat_1(A_32, B_33) | k2_relat_1(A_32)!=k1_relat_1(B_33) | ~v2_funct_1(A_32) | ~v1_funct_1(B_33) | ~v1_relat_1(B_33) | ~v1_funct_1(A_32) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.32/1.43  tff(c_330, plain, (![B_33]: (k2_funct_1('#skF_2')=B_33 | k5_relat_1('#skF_2', B_33)!=k5_relat_1('#skF_2', '#skF_1') | k2_relat_1('#skF_2')!=k1_relat_1(B_33) | ~v2_funct_1('#skF_2') | ~v1_funct_1(B_33) | ~v1_relat_1(B_33) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_172, c_322])).
% 2.32/1.43  tff(c_342, plain, (![B_36]: (k2_funct_1('#skF_2')=B_36 | k5_relat_1('#skF_2', B_36)!=k5_relat_1('#skF_2', '#skF_1') | k1_relat_1(B_36)!=k1_relat_1('#skF_1') | ~v1_funct_1(B_36) | ~v1_relat_1(B_36))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_275, c_22, c_330])).
% 2.32/1.43  tff(c_348, plain, (k2_funct_1('#skF_2')='#skF_1' | ~v1_funct_1('#skF_1')), inference(resolution, [status(thm)], [c_32, c_342])).
% 2.32/1.43  tff(c_354, plain, (k2_funct_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_348])).
% 2.32/1.43  tff(c_12, plain, (![A_7]: (k4_relat_1(A_7)=k2_funct_1(A_7) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.32/1.43  tff(c_278, plain, (k4_relat_1('#skF_2')=k2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_275, c_12])).
% 2.32/1.43  tff(c_281, plain, (k4_relat_1('#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_278])).
% 2.32/1.43  tff(c_357, plain, (k4_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_354, c_281])).
% 2.32/1.43  tff(c_2, plain, (![A_1]: (k4_relat_1(k4_relat_1(A_1))=A_1 | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.32/1.43  tff(c_365, plain, (k4_relat_1('#skF_1')='#skF_2' | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_357, c_2])).
% 2.32/1.43  tff(c_369, plain, (k2_funct_1('#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_122, c_365])).
% 2.32/1.43  tff(c_371, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_369])).
% 2.32/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.43  
% 2.32/1.43  Inference rules
% 2.32/1.43  ----------------------
% 2.32/1.43  #Ref     : 0
% 2.32/1.43  #Sup     : 96
% 2.32/1.43  #Fact    : 0
% 2.32/1.43  #Define  : 0
% 2.32/1.43  #Split   : 3
% 2.32/1.43  #Chain   : 0
% 2.32/1.43  #Close   : 0
% 2.32/1.43  
% 2.32/1.43  Ordering : KBO
% 2.32/1.43  
% 2.32/1.43  Simplification rules
% 2.32/1.43  ----------------------
% 2.32/1.43  #Subsume      : 12
% 2.32/1.43  #Demod        : 68
% 2.32/1.43  #Tautology    : 53
% 2.32/1.43  #SimpNegUnit  : 1
% 2.32/1.43  #BackRed      : 6
% 2.32/1.43  
% 2.32/1.43  #Partial instantiations: 0
% 2.32/1.43  #Strategies tried      : 1
% 2.32/1.43  
% 2.32/1.43  Timing (in seconds)
% 2.32/1.43  ----------------------
% 2.32/1.44  Preprocessing        : 0.33
% 2.32/1.44  Parsing              : 0.17
% 2.32/1.44  CNF conversion       : 0.02
% 2.32/1.44  Main loop            : 0.25
% 2.32/1.44  Inferencing          : 0.09
% 2.32/1.44  Reduction            : 0.08
% 2.32/1.44  Demodulation         : 0.06
% 2.32/1.44  BG Simplification    : 0.02
% 2.32/1.44  Subsumption          : 0.04
% 2.32/1.44  Abstraction          : 0.01
% 2.32/1.44  MUC search           : 0.00
% 2.32/1.44  Cooper               : 0.00
% 2.32/1.44  Total                : 0.60
% 2.32/1.44  Index Insertion      : 0.00
% 2.32/1.44  Index Deletion       : 0.00
% 2.32/1.44  Index Matching       : 0.00
% 2.32/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
