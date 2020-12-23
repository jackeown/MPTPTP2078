%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:04 EST 2020

% Result     : Theorem 4.56s
% Output     : CNFRefutation 4.68s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 138 expanded)
%              Number of leaves         :   22 (  62 expanded)
%              Depth                    :   17
%              Number of atoms          :  140 ( 499 expanded)
%              Number of equality atoms :   51 ( 179 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

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

tff(f_133,negated_conjecture,(
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

tff(f_44,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_65,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(k5_relat_1(B,A))
              & k2_relat_1(B) = k1_relat_1(A) )
           => ( v2_funct_1(B)
              & v2_funct_1(A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_1)).

tff(f_115,axiom,(
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

tff(f_98,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(c_34,plain,(
    k2_funct_1('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_42,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_44,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_48,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_46,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_40,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_36,plain,(
    k6_relat_1(k2_relat_1('#skF_1')) = k5_relat_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_10,plain,(
    ! [A_6] : k1_relat_1(k6_relat_1(A_6)) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_81,plain,(
    k1_relat_1(k5_relat_1('#skF_2','#skF_1')) = k2_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_10])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_38,plain,(
    k2_relat_1('#skF_2') = k1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_140,plain,(
    ! [A_31,B_32] :
      ( k1_relat_1(k5_relat_1(A_31,B_32)) = k1_relat_1(A_31)
      | ~ r1_tarski(k2_relat_1(A_31),k1_relat_1(B_32))
      | ~ v1_relat_1(B_32)
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_161,plain,(
    ! [B_32] :
      ( k1_relat_1(k5_relat_1('#skF_2',B_32)) = k1_relat_1('#skF_2')
      | ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1(B_32))
      | ~ v1_relat_1(B_32)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_140])).

tff(c_246,plain,(
    ! [B_39] :
      ( k1_relat_1(k5_relat_1('#skF_2',B_39)) = k1_relat_1('#skF_2')
      | ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1(B_39))
      | ~ v1_relat_1(B_39) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_161])).

tff(c_265,plain,
    ( k1_relat_1(k5_relat_1('#skF_2','#skF_1')) = k1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_246])).

tff(c_272,plain,(
    k2_relat_1('#skF_1') = k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_81,c_265])).

tff(c_16,plain,(
    ! [A_7] : v2_funct_1(k6_relat_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_83,plain,(
    v2_funct_1(k5_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_16])).

tff(c_398,plain,(
    ! [B_42,A_43] :
      ( v2_funct_1(B_42)
      | k2_relat_1(B_42) != k1_relat_1(A_43)
      | ~ v2_funct_1(k5_relat_1(B_42,A_43))
      | ~ v1_funct_1(B_42)
      | ~ v1_relat_1(B_42)
      | ~ v1_funct_1(A_43)
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_407,plain,
    ( v2_funct_1('#skF_2')
    | k2_relat_1('#skF_2') != k1_relat_1('#skF_1')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_83,c_398])).

tff(c_414,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_38,c_407])).

tff(c_275,plain,(
    k6_relat_1(k1_relat_1('#skF_2')) = k5_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_272,c_36])).

tff(c_913,plain,(
    ! [A_56,B_57] :
      ( k2_funct_1(A_56) = B_57
      | k6_relat_1(k1_relat_1(A_56)) != k5_relat_1(A_56,B_57)
      | k2_relat_1(A_56) != k1_relat_1(B_57)
      | ~ v2_funct_1(A_56)
      | ~ v1_funct_1(B_57)
      | ~ v1_relat_1(B_57)
      | ~ v1_funct_1(A_56)
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_933,plain,(
    ! [B_57] :
      ( k2_funct_1('#skF_2') = B_57
      | k5_relat_1('#skF_2',B_57) != k5_relat_1('#skF_2','#skF_1')
      | k2_relat_1('#skF_2') != k1_relat_1(B_57)
      | ~ v2_funct_1('#skF_2')
      | ~ v1_funct_1(B_57)
      | ~ v1_relat_1(B_57)
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_275,c_913])).

tff(c_1013,plain,(
    ! [B_60] :
      ( k2_funct_1('#skF_2') = B_60
      | k5_relat_1('#skF_2',B_60) != k5_relat_1('#skF_2','#skF_1')
      | k1_relat_1(B_60) != k1_relat_1('#skF_1')
      | ~ v1_funct_1(B_60)
      | ~ v1_relat_1(B_60) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_414,c_38,c_933])).

tff(c_1028,plain,
    ( k2_funct_1('#skF_2') = '#skF_1'
    | ~ v1_funct_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_1013])).

tff(c_1041,plain,(
    k2_funct_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1028])).

tff(c_28,plain,(
    ! [A_15] :
      ( k5_relat_1(k2_funct_1(A_15),A_15) = k6_relat_1(k2_relat_1(A_15))
      | ~ v2_funct_1(A_15)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1052,plain,
    ( k6_relat_1(k2_relat_1('#skF_2')) = k5_relat_1('#skF_1','#skF_2')
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1041,c_28])).

tff(c_1066,plain,(
    k6_relat_1(k1_relat_1('#skF_1')) = k5_relat_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_414,c_38,c_1052])).

tff(c_32,plain,(
    ! [A_16,B_18] :
      ( k2_funct_1(A_16) = B_18
      | k6_relat_1(k1_relat_1(A_16)) != k5_relat_1(A_16,B_18)
      | k2_relat_1(A_16) != k1_relat_1(B_18)
      | ~ v2_funct_1(A_16)
      | ~ v1_funct_1(B_18)
      | ~ v1_relat_1(B_18)
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1077,plain,(
    ! [B_18] :
      ( k2_funct_1('#skF_1') = B_18
      | k5_relat_1('#skF_1',B_18) != k5_relat_1('#skF_1','#skF_2')
      | k2_relat_1('#skF_1') != k1_relat_1(B_18)
      | ~ v2_funct_1('#skF_1')
      | ~ v1_funct_1(B_18)
      | ~ v1_relat_1(B_18)
      | ~ v1_funct_1('#skF_1')
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1066,c_32])).

tff(c_1966,plain,(
    ! [B_80] :
      ( k2_funct_1('#skF_1') = B_80
      | k5_relat_1('#skF_1',B_80) != k5_relat_1('#skF_1','#skF_2')
      | k1_relat_1(B_80) != k1_relat_1('#skF_2')
      | ~ v1_funct_1(B_80)
      | ~ v1_relat_1(B_80) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_40,c_272,c_1077])).

tff(c_1978,plain,
    ( k2_funct_1('#skF_1') = '#skF_2'
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_1966])).

tff(c_1991,plain,(
    k2_funct_1('#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1978])).

tff(c_1993,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_1991])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:55:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.56/1.83  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.56/1.84  
% 4.56/1.84  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.56/1.84  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1
% 4.56/1.84  
% 4.56/1.84  %Foreground sorts:
% 4.56/1.84  
% 4.56/1.84  
% 4.56/1.84  %Background operators:
% 4.56/1.84  
% 4.56/1.84  
% 4.56/1.84  %Foreground operators:
% 4.56/1.84  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.56/1.84  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.56/1.84  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.56/1.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.56/1.84  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.56/1.84  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.56/1.84  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.56/1.84  tff('#skF_2', type, '#skF_2': $i).
% 4.56/1.84  tff('#skF_1', type, '#skF_1': $i).
% 4.56/1.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.56/1.84  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.56/1.84  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.56/1.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.56/1.84  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.56/1.84  
% 4.68/1.86  tff(f_133, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_1)).
% 4.68/1.86  tff(f_44, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 4.68/1.86  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.68/1.86  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_relat_1)).
% 4.68/1.86  tff(f_48, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 4.68/1.86  tff(f_65, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & (k2_relat_1(B) = k1_relat_1(A))) => (v2_funct_1(B) & v2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_funct_1)).
% 4.68/1.86  tff(f_115, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(A) = k1_relat_1(B))) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_funct_1)).
% 4.68/1.86  tff(f_98, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 4.68/1.86  tff(c_34, plain, (k2_funct_1('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.68/1.86  tff(c_42, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.68/1.86  tff(c_44, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.68/1.86  tff(c_48, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.68/1.86  tff(c_46, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.68/1.86  tff(c_40, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.68/1.86  tff(c_36, plain, (k6_relat_1(k2_relat_1('#skF_1'))=k5_relat_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.68/1.86  tff(c_10, plain, (![A_6]: (k1_relat_1(k6_relat_1(A_6))=A_6)), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.68/1.86  tff(c_81, plain, (k1_relat_1(k5_relat_1('#skF_2', '#skF_1'))=k2_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_36, c_10])).
% 4.68/1.86  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.68/1.86  tff(c_38, plain, (k2_relat_1('#skF_2')=k1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.68/1.86  tff(c_140, plain, (![A_31, B_32]: (k1_relat_1(k5_relat_1(A_31, B_32))=k1_relat_1(A_31) | ~r1_tarski(k2_relat_1(A_31), k1_relat_1(B_32)) | ~v1_relat_1(B_32) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.68/1.86  tff(c_161, plain, (![B_32]: (k1_relat_1(k5_relat_1('#skF_2', B_32))=k1_relat_1('#skF_2') | ~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1(B_32)) | ~v1_relat_1(B_32) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_38, c_140])).
% 4.68/1.86  tff(c_246, plain, (![B_39]: (k1_relat_1(k5_relat_1('#skF_2', B_39))=k1_relat_1('#skF_2') | ~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1(B_39)) | ~v1_relat_1(B_39))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_161])).
% 4.68/1.86  tff(c_265, plain, (k1_relat_1(k5_relat_1('#skF_2', '#skF_1'))=k1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_6, c_246])).
% 4.68/1.86  tff(c_272, plain, (k2_relat_1('#skF_1')=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_81, c_265])).
% 4.68/1.86  tff(c_16, plain, (![A_7]: (v2_funct_1(k6_relat_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.68/1.86  tff(c_83, plain, (v2_funct_1(k5_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_36, c_16])).
% 4.68/1.86  tff(c_398, plain, (![B_42, A_43]: (v2_funct_1(B_42) | k2_relat_1(B_42)!=k1_relat_1(A_43) | ~v2_funct_1(k5_relat_1(B_42, A_43)) | ~v1_funct_1(B_42) | ~v1_relat_1(B_42) | ~v1_funct_1(A_43) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.68/1.86  tff(c_407, plain, (v2_funct_1('#skF_2') | k2_relat_1('#skF_2')!=k1_relat_1('#skF_1') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_83, c_398])).
% 4.68/1.86  tff(c_414, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_38, c_407])).
% 4.68/1.86  tff(c_275, plain, (k6_relat_1(k1_relat_1('#skF_2'))=k5_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_272, c_36])).
% 4.68/1.86  tff(c_913, plain, (![A_56, B_57]: (k2_funct_1(A_56)=B_57 | k6_relat_1(k1_relat_1(A_56))!=k5_relat_1(A_56, B_57) | k2_relat_1(A_56)!=k1_relat_1(B_57) | ~v2_funct_1(A_56) | ~v1_funct_1(B_57) | ~v1_relat_1(B_57) | ~v1_funct_1(A_56) | ~v1_relat_1(A_56))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.68/1.86  tff(c_933, plain, (![B_57]: (k2_funct_1('#skF_2')=B_57 | k5_relat_1('#skF_2', B_57)!=k5_relat_1('#skF_2', '#skF_1') | k2_relat_1('#skF_2')!=k1_relat_1(B_57) | ~v2_funct_1('#skF_2') | ~v1_funct_1(B_57) | ~v1_relat_1(B_57) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_275, c_913])).
% 4.68/1.86  tff(c_1013, plain, (![B_60]: (k2_funct_1('#skF_2')=B_60 | k5_relat_1('#skF_2', B_60)!=k5_relat_1('#skF_2', '#skF_1') | k1_relat_1(B_60)!=k1_relat_1('#skF_1') | ~v1_funct_1(B_60) | ~v1_relat_1(B_60))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_414, c_38, c_933])).
% 4.68/1.86  tff(c_1028, plain, (k2_funct_1('#skF_2')='#skF_1' | ~v1_funct_1('#skF_1')), inference(resolution, [status(thm)], [c_48, c_1013])).
% 4.68/1.86  tff(c_1041, plain, (k2_funct_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1028])).
% 4.68/1.86  tff(c_28, plain, (![A_15]: (k5_relat_1(k2_funct_1(A_15), A_15)=k6_relat_1(k2_relat_1(A_15)) | ~v2_funct_1(A_15) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.68/1.86  tff(c_1052, plain, (k6_relat_1(k2_relat_1('#skF_2'))=k5_relat_1('#skF_1', '#skF_2') | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1041, c_28])).
% 4.68/1.86  tff(c_1066, plain, (k6_relat_1(k1_relat_1('#skF_1'))=k5_relat_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_414, c_38, c_1052])).
% 4.68/1.86  tff(c_32, plain, (![A_16, B_18]: (k2_funct_1(A_16)=B_18 | k6_relat_1(k1_relat_1(A_16))!=k5_relat_1(A_16, B_18) | k2_relat_1(A_16)!=k1_relat_1(B_18) | ~v2_funct_1(A_16) | ~v1_funct_1(B_18) | ~v1_relat_1(B_18) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.68/1.86  tff(c_1077, plain, (![B_18]: (k2_funct_1('#skF_1')=B_18 | k5_relat_1('#skF_1', B_18)!=k5_relat_1('#skF_1', '#skF_2') | k2_relat_1('#skF_1')!=k1_relat_1(B_18) | ~v2_funct_1('#skF_1') | ~v1_funct_1(B_18) | ~v1_relat_1(B_18) | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1066, c_32])).
% 4.68/1.86  tff(c_1966, plain, (![B_80]: (k2_funct_1('#skF_1')=B_80 | k5_relat_1('#skF_1', B_80)!=k5_relat_1('#skF_1', '#skF_2') | k1_relat_1(B_80)!=k1_relat_1('#skF_2') | ~v1_funct_1(B_80) | ~v1_relat_1(B_80))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_40, c_272, c_1077])).
% 4.68/1.86  tff(c_1978, plain, (k2_funct_1('#skF_1')='#skF_2' | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_44, c_1966])).
% 4.68/1.86  tff(c_1991, plain, (k2_funct_1('#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1978])).
% 4.68/1.86  tff(c_1993, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_1991])).
% 4.68/1.86  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.68/1.86  
% 4.68/1.86  Inference rules
% 4.68/1.86  ----------------------
% 4.68/1.86  #Ref     : 0
% 4.68/1.86  #Sup     : 489
% 4.68/1.86  #Fact    : 0
% 4.68/1.86  #Define  : 0
% 4.68/1.86  #Split   : 13
% 4.68/1.86  #Chain   : 0
% 4.68/1.86  #Close   : 0
% 4.68/1.86  
% 4.68/1.86  Ordering : KBO
% 4.68/1.86  
% 4.68/1.86  Simplification rules
% 4.68/1.86  ----------------------
% 4.68/1.86  #Subsume      : 82
% 4.68/1.86  #Demod        : 473
% 4.68/1.86  #Tautology    : 150
% 4.68/1.86  #SimpNegUnit  : 2
% 4.68/1.86  #BackRed      : 5
% 4.68/1.86  
% 4.68/1.86  #Partial instantiations: 0
% 4.68/1.86  #Strategies tried      : 1
% 4.68/1.86  
% 4.68/1.86  Timing (in seconds)
% 4.68/1.86  ----------------------
% 4.68/1.87  Preprocessing        : 0.34
% 4.68/1.87  Parsing              : 0.18
% 4.68/1.87  CNF conversion       : 0.02
% 4.68/1.87  Main loop            : 0.72
% 4.68/1.87  Inferencing          : 0.21
% 4.68/1.87  Reduction            : 0.28
% 4.68/1.87  Demodulation         : 0.21
% 4.68/1.87  BG Simplification    : 0.04
% 4.68/1.87  Subsumption          : 0.16
% 4.68/1.87  Abstraction          : 0.04
% 4.68/1.87  MUC search           : 0.00
% 4.68/1.87  Cooper               : 0.00
% 4.68/1.87  Total                : 1.09
% 4.68/1.87  Index Insertion      : 0.00
% 4.68/1.87  Index Deletion       : 0.00
% 4.68/1.87  Index Matching       : 0.00
% 4.68/1.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
