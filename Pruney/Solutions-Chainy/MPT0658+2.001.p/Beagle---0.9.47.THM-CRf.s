%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:07 EST 2020

% Result     : Theorem 2.57s
% Output     : CNFRefutation 2.74s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 526 expanded)
%              Number of leaves         :   20 ( 193 expanded)
%              Depth                    :   16
%              Number of atoms          :  164 (1568 expanded)
%              Number of equality atoms :   49 ( 503 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1

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

tff(f_95,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v2_funct_1(A)
         => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_69,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_47,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_39,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_86,axiom,(
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

tff(f_59,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A))
        & v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).

tff(c_24,plain,(
    k2_funct_1(k2_funct_1('#skF_1')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_30,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_28,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_26,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_18,plain,(
    ! [A_5] :
      ( k5_relat_1(k2_funct_1(A_5),A_5) = k6_relat_1(k2_relat_1(A_5))
      | ~ v2_funct_1(A_5)
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_10,plain,(
    ! [A_3] :
      ( v1_relat_1(k2_funct_1(A_3))
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_52,plain,(
    ! [A_14] :
      ( k4_relat_1(A_14) = k2_funct_1(A_14)
      | ~ v2_funct_1(A_14)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_58,plain,
    ( k4_relat_1('#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_52])).

tff(c_62,plain,(
    k4_relat_1('#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_58])).

tff(c_2,plain,(
    ! [A_1] :
      ( k2_relat_1(k4_relat_1(A_1)) = k1_relat_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_69,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_2])).

tff(c_75,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_69])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_relat_1(k4_relat_1(A_1)) = k2_relat_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_66,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_4])).

tff(c_73,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_66])).

tff(c_103,plain,(
    ! [A_17,B_18] :
      ( k2_funct_1(A_17) = B_18
      | k6_relat_1(k1_relat_1(A_17)) != k5_relat_1(A_17,B_18)
      | k2_relat_1(A_17) != k1_relat_1(B_18)
      | ~ v2_funct_1(A_17)
      | ~ v1_funct_1(B_18)
      | ~ v1_relat_1(B_18)
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_109,plain,(
    ! [B_18] :
      ( k2_funct_1(k2_funct_1('#skF_1')) = B_18
      | k5_relat_1(k2_funct_1('#skF_1'),B_18) != k6_relat_1(k2_relat_1('#skF_1'))
      | k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1(B_18)
      | ~ v2_funct_1(k2_funct_1('#skF_1'))
      | ~ v1_funct_1(B_18)
      | ~ v1_relat_1(B_18)
      | ~ v1_funct_1(k2_funct_1('#skF_1'))
      | ~ v1_relat_1(k2_funct_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_103])).

tff(c_114,plain,(
    ! [B_18] :
      ( k2_funct_1(k2_funct_1('#skF_1')) = B_18
      | k5_relat_1(k2_funct_1('#skF_1'),B_18) != k6_relat_1(k2_relat_1('#skF_1'))
      | k1_relat_1(B_18) != k1_relat_1('#skF_1')
      | ~ v2_funct_1(k2_funct_1('#skF_1'))
      | ~ v1_funct_1(B_18)
      | ~ v1_relat_1(B_18)
      | ~ v1_funct_1(k2_funct_1('#skF_1'))
      | ~ v1_relat_1(k2_funct_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_109])).

tff(c_140,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_114])).

tff(c_143,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_140])).

tff(c_147,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_143])).

tff(c_149,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_114])).

tff(c_8,plain,(
    ! [A_3] :
      ( v1_funct_1(k2_funct_1(A_3))
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_12,plain,(
    ! [A_4] :
      ( v2_funct_1(k2_funct_1(A_4))
      | ~ v2_funct_1(A_4)
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_148,plain,(
    ! [B_18] :
      ( ~ v1_funct_1(k2_funct_1('#skF_1'))
      | ~ v2_funct_1(k2_funct_1('#skF_1'))
      | k2_funct_1(k2_funct_1('#skF_1')) = B_18
      | k5_relat_1(k2_funct_1('#skF_1'),B_18) != k6_relat_1(k2_relat_1('#skF_1'))
      | k1_relat_1(B_18) != k1_relat_1('#skF_1')
      | ~ v1_funct_1(B_18)
      | ~ v1_relat_1(B_18) ) ),
    inference(splitRight,[status(thm)],[c_114])).

tff(c_170,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_148])).

tff(c_184,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_170])).

tff(c_188,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_184])).

tff(c_189,plain,(
    ! [B_18] :
      ( ~ v1_funct_1(k2_funct_1('#skF_1'))
      | k2_funct_1(k2_funct_1('#skF_1')) = B_18
      | k5_relat_1(k2_funct_1('#skF_1'),B_18) != k6_relat_1(k2_relat_1('#skF_1'))
      | k1_relat_1(B_18) != k1_relat_1('#skF_1')
      | ~ v1_funct_1(B_18)
      | ~ v1_relat_1(B_18) ) ),
    inference(splitRight,[status(thm)],[c_148])).

tff(c_198,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_189])).

tff(c_201,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_198])).

tff(c_205,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_201])).

tff(c_207,plain,(
    v1_funct_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_189])).

tff(c_190,plain,(
    v2_funct_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_148])).

tff(c_6,plain,(
    ! [A_2] :
      ( k4_relat_1(A_2) = k2_funct_1(A_2)
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_193,plain,
    ( k4_relat_1(k2_funct_1('#skF_1')) = k2_funct_1(k2_funct_1('#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_190,c_6])).

tff(c_196,plain,
    ( k4_relat_1(k2_funct_1('#skF_1')) = k2_funct_1(k2_funct_1('#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_193])).

tff(c_197,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_196])).

tff(c_209,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_197])).

tff(c_211,plain,(
    v1_funct_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_196])).

tff(c_238,plain,(
    ! [A_26,B_27] :
      ( k2_funct_1(k4_relat_1(A_26)) = B_27
      | k5_relat_1(k4_relat_1(A_26),B_27) != k6_relat_1(k2_relat_1(A_26))
      | k2_relat_1(k4_relat_1(A_26)) != k1_relat_1(B_27)
      | ~ v2_funct_1(k4_relat_1(A_26))
      | ~ v1_funct_1(B_27)
      | ~ v1_relat_1(B_27)
      | ~ v1_funct_1(k4_relat_1(A_26))
      | ~ v1_relat_1(k4_relat_1(A_26))
      | ~ v1_relat_1(A_26) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_103])).

tff(c_247,plain,(
    ! [B_27] :
      ( k2_funct_1(k4_relat_1('#skF_1')) = B_27
      | k5_relat_1(k2_funct_1('#skF_1'),B_27) != k6_relat_1(k2_relat_1('#skF_1'))
      | k2_relat_1(k4_relat_1('#skF_1')) != k1_relat_1(B_27)
      | ~ v2_funct_1(k4_relat_1('#skF_1'))
      | ~ v1_funct_1(B_27)
      | ~ v1_relat_1(B_27)
      | ~ v1_funct_1(k4_relat_1('#skF_1'))
      | ~ v1_relat_1(k4_relat_1('#skF_1'))
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_238])).

tff(c_283,plain,(
    ! [B_28] :
      ( k2_funct_1(k2_funct_1('#skF_1')) = B_28
      | k5_relat_1(k2_funct_1('#skF_1'),B_28) != k6_relat_1(k2_relat_1('#skF_1'))
      | k1_relat_1(B_28) != k1_relat_1('#skF_1')
      | ~ v1_funct_1(B_28)
      | ~ v1_relat_1(B_28) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_149,c_62,c_211,c_62,c_190,c_62,c_75,c_62,c_62,c_247])).

tff(c_287,plain,
    ( k2_funct_1(k2_funct_1('#skF_1')) = '#skF_1'
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_283])).

tff(c_294,plain,(
    k2_funct_1(k2_funct_1('#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_287])).

tff(c_296,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_294])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:20:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.57/1.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/1.49  
% 2.57/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/1.50  %$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1
% 2.57/1.50  
% 2.57/1.50  %Foreground sorts:
% 2.57/1.50  
% 2.57/1.50  
% 2.57/1.50  %Background operators:
% 2.57/1.50  
% 2.57/1.50  
% 2.57/1.50  %Foreground operators:
% 2.57/1.50  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.57/1.50  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.57/1.50  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.57/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.57/1.50  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.57/1.50  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.57/1.50  tff('#skF_1', type, '#skF_1': $i).
% 2.57/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.57/1.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.57/1.50  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.57/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.57/1.50  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.57/1.50  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 2.57/1.50  
% 2.74/1.51  tff(f_95, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_1)).
% 2.74/1.51  tff(f_69, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 2.74/1.51  tff(f_47, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 2.74/1.51  tff(f_39, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 2.74/1.51  tff(f_31, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_relat_1)).
% 2.74/1.51  tff(f_86, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(A) = k1_relat_1(B))) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_funct_1)).
% 2.74/1.51  tff(f_59, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => ((v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))) & v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_funct_1)).
% 2.74/1.51  tff(c_24, plain, (k2_funct_1(k2_funct_1('#skF_1'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.74/1.51  tff(c_30, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.74/1.51  tff(c_28, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.74/1.51  tff(c_26, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.74/1.51  tff(c_18, plain, (![A_5]: (k5_relat_1(k2_funct_1(A_5), A_5)=k6_relat_1(k2_relat_1(A_5)) | ~v2_funct_1(A_5) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.74/1.51  tff(c_10, plain, (![A_3]: (v1_relat_1(k2_funct_1(A_3)) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.74/1.51  tff(c_52, plain, (![A_14]: (k4_relat_1(A_14)=k2_funct_1(A_14) | ~v2_funct_1(A_14) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.74/1.51  tff(c_58, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_26, c_52])).
% 2.74/1.51  tff(c_62, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_58])).
% 2.74/1.51  tff(c_2, plain, (![A_1]: (k2_relat_1(k4_relat_1(A_1))=k1_relat_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.74/1.51  tff(c_69, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_62, c_2])).
% 2.74/1.51  tff(c_75, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_69])).
% 2.74/1.51  tff(c_4, plain, (![A_1]: (k1_relat_1(k4_relat_1(A_1))=k2_relat_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.74/1.51  tff(c_66, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_62, c_4])).
% 2.74/1.51  tff(c_73, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_66])).
% 2.74/1.51  tff(c_103, plain, (![A_17, B_18]: (k2_funct_1(A_17)=B_18 | k6_relat_1(k1_relat_1(A_17))!=k5_relat_1(A_17, B_18) | k2_relat_1(A_17)!=k1_relat_1(B_18) | ~v2_funct_1(A_17) | ~v1_funct_1(B_18) | ~v1_relat_1(B_18) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.74/1.51  tff(c_109, plain, (![B_18]: (k2_funct_1(k2_funct_1('#skF_1'))=B_18 | k5_relat_1(k2_funct_1('#skF_1'), B_18)!=k6_relat_1(k2_relat_1('#skF_1')) | k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1(B_18) | ~v2_funct_1(k2_funct_1('#skF_1')) | ~v1_funct_1(B_18) | ~v1_relat_1(B_18) | ~v1_funct_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_73, c_103])).
% 2.74/1.51  tff(c_114, plain, (![B_18]: (k2_funct_1(k2_funct_1('#skF_1'))=B_18 | k5_relat_1(k2_funct_1('#skF_1'), B_18)!=k6_relat_1(k2_relat_1('#skF_1')) | k1_relat_1(B_18)!=k1_relat_1('#skF_1') | ~v2_funct_1(k2_funct_1('#skF_1')) | ~v1_funct_1(B_18) | ~v1_relat_1(B_18) | ~v1_funct_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_109])).
% 2.74/1.51  tff(c_140, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_114])).
% 2.74/1.51  tff(c_143, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_10, c_140])).
% 2.74/1.51  tff(c_147, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_143])).
% 2.74/1.51  tff(c_149, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_114])).
% 2.74/1.51  tff(c_8, plain, (![A_3]: (v1_funct_1(k2_funct_1(A_3)) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.74/1.51  tff(c_12, plain, (![A_4]: (v2_funct_1(k2_funct_1(A_4)) | ~v2_funct_1(A_4) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.74/1.51  tff(c_148, plain, (![B_18]: (~v1_funct_1(k2_funct_1('#skF_1')) | ~v2_funct_1(k2_funct_1('#skF_1')) | k2_funct_1(k2_funct_1('#skF_1'))=B_18 | k5_relat_1(k2_funct_1('#skF_1'), B_18)!=k6_relat_1(k2_relat_1('#skF_1')) | k1_relat_1(B_18)!=k1_relat_1('#skF_1') | ~v1_funct_1(B_18) | ~v1_relat_1(B_18))), inference(splitRight, [status(thm)], [c_114])).
% 2.74/1.51  tff(c_170, plain, (~v2_funct_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_148])).
% 2.74/1.51  tff(c_184, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_12, c_170])).
% 2.74/1.51  tff(c_188, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_184])).
% 2.74/1.51  tff(c_189, plain, (![B_18]: (~v1_funct_1(k2_funct_1('#skF_1')) | k2_funct_1(k2_funct_1('#skF_1'))=B_18 | k5_relat_1(k2_funct_1('#skF_1'), B_18)!=k6_relat_1(k2_relat_1('#skF_1')) | k1_relat_1(B_18)!=k1_relat_1('#skF_1') | ~v1_funct_1(B_18) | ~v1_relat_1(B_18))), inference(splitRight, [status(thm)], [c_148])).
% 2.74/1.51  tff(c_198, plain, (~v1_funct_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_189])).
% 2.74/1.51  tff(c_201, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_8, c_198])).
% 2.74/1.51  tff(c_205, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_201])).
% 2.74/1.51  tff(c_207, plain, (v1_funct_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_189])).
% 2.74/1.51  tff(c_190, plain, (v2_funct_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_148])).
% 2.74/1.51  tff(c_6, plain, (![A_2]: (k4_relat_1(A_2)=k2_funct_1(A_2) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.74/1.51  tff(c_193, plain, (k4_relat_1(k2_funct_1('#skF_1'))=k2_funct_1(k2_funct_1('#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(resolution, [status(thm)], [c_190, c_6])).
% 2.74/1.51  tff(c_196, plain, (k4_relat_1(k2_funct_1('#skF_1'))=k2_funct_1(k2_funct_1('#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_149, c_193])).
% 2.74/1.51  tff(c_197, plain, (~v1_funct_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_196])).
% 2.74/1.51  tff(c_209, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_207, c_197])).
% 2.74/1.51  tff(c_211, plain, (v1_funct_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_196])).
% 2.74/1.51  tff(c_238, plain, (![A_26, B_27]: (k2_funct_1(k4_relat_1(A_26))=B_27 | k5_relat_1(k4_relat_1(A_26), B_27)!=k6_relat_1(k2_relat_1(A_26)) | k2_relat_1(k4_relat_1(A_26))!=k1_relat_1(B_27) | ~v2_funct_1(k4_relat_1(A_26)) | ~v1_funct_1(B_27) | ~v1_relat_1(B_27) | ~v1_funct_1(k4_relat_1(A_26)) | ~v1_relat_1(k4_relat_1(A_26)) | ~v1_relat_1(A_26))), inference(superposition, [status(thm), theory('equality')], [c_4, c_103])).
% 2.74/1.51  tff(c_247, plain, (![B_27]: (k2_funct_1(k4_relat_1('#skF_1'))=B_27 | k5_relat_1(k2_funct_1('#skF_1'), B_27)!=k6_relat_1(k2_relat_1('#skF_1')) | k2_relat_1(k4_relat_1('#skF_1'))!=k1_relat_1(B_27) | ~v2_funct_1(k4_relat_1('#skF_1')) | ~v1_funct_1(B_27) | ~v1_relat_1(B_27) | ~v1_funct_1(k4_relat_1('#skF_1')) | ~v1_relat_1(k4_relat_1('#skF_1')) | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_62, c_238])).
% 2.74/1.51  tff(c_283, plain, (![B_28]: (k2_funct_1(k2_funct_1('#skF_1'))=B_28 | k5_relat_1(k2_funct_1('#skF_1'), B_28)!=k6_relat_1(k2_relat_1('#skF_1')) | k1_relat_1(B_28)!=k1_relat_1('#skF_1') | ~v1_funct_1(B_28) | ~v1_relat_1(B_28))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_149, c_62, c_211, c_62, c_190, c_62, c_75, c_62, c_62, c_247])).
% 2.74/1.51  tff(c_287, plain, (k2_funct_1(k2_funct_1('#skF_1'))='#skF_1' | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_18, c_283])).
% 2.74/1.51  tff(c_294, plain, (k2_funct_1(k2_funct_1('#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_287])).
% 2.74/1.51  tff(c_296, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_294])).
% 2.74/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.74/1.51  
% 2.74/1.51  Inference rules
% 2.74/1.51  ----------------------
% 2.74/1.51  #Ref     : 0
% 2.74/1.51  #Sup     : 61
% 2.74/1.51  #Fact    : 0
% 2.74/1.51  #Define  : 0
% 2.74/1.51  #Split   : 4
% 2.74/1.51  #Chain   : 0
% 2.74/1.51  #Close   : 0
% 2.74/1.51  
% 2.74/1.51  Ordering : KBO
% 2.74/1.51  
% 2.74/1.51  Simplification rules
% 2.74/1.51  ----------------------
% 2.74/1.51  #Subsume      : 4
% 2.74/1.51  #Demod        : 72
% 2.74/1.51  #Tautology    : 35
% 2.74/1.51  #SimpNegUnit  : 1
% 2.74/1.51  #BackRed      : 0
% 2.74/1.51  
% 2.74/1.51  #Partial instantiations: 0
% 2.74/1.51  #Strategies tried      : 1
% 2.74/1.51  
% 2.74/1.51  Timing (in seconds)
% 2.74/1.51  ----------------------
% 2.74/1.52  Preprocessing        : 0.40
% 2.74/1.52  Parsing              : 0.22
% 2.74/1.52  CNF conversion       : 0.02
% 2.74/1.52  Main loop            : 0.31
% 2.74/1.52  Inferencing          : 0.12
% 2.74/1.52  Reduction            : 0.08
% 2.74/1.52  Demodulation         : 0.06
% 2.74/1.52  BG Simplification    : 0.02
% 2.74/1.52  Subsumption          : 0.07
% 2.74/1.52  Abstraction          : 0.02
% 2.74/1.52  MUC search           : 0.00
% 2.74/1.52  Cooper               : 0.00
% 2.74/1.52  Total                : 0.74
% 2.74/1.52  Index Insertion      : 0.00
% 2.74/1.52  Index Deletion       : 0.00
% 2.74/1.52  Index Matching       : 0.00
% 2.74/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
