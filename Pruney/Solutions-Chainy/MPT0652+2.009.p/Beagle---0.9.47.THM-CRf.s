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
% DateTime   : Thu Dec  3 10:03:53 EST 2020

% Result     : Theorem 3.31s
% Output     : CNFRefutation 3.31s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 203 expanded)
%              Number of leaves         :   22 (  77 expanded)
%              Depth                    :   12
%              Number of atoms          :  143 ( 539 expanded)
%              Number of equality atoms :   53 ( 229 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1

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

tff(f_91,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v2_funct_1(A)
         => ( k1_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A)
            & k2_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_funct_1)).

tff(f_80,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_70,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_33,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_58,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( k1_relat_1(A) = k1_relat_1(B)
               => k1_relat_1(k5_relat_1(C,A)) = k1_relat_1(k5_relat_1(C,B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t198_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).

tff(c_34,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_32,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_30,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_24,plain,(
    ! [A_17] :
      ( k2_relat_1(k2_funct_1(A_17)) = k1_relat_1(A_17)
      | ~ v2_funct_1(A_17)
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_26,plain,(
    ! [A_17] :
      ( k1_relat_1(k2_funct_1(A_17)) = k2_relat_1(A_17)
      | ~ v2_funct_1(A_17)
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_22,plain,(
    ! [A_16] :
      ( v1_relat_1(k2_funct_1(A_16))
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_8,plain,(
    ! [A_3] : v1_relat_1(k6_relat_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_14,plain,(
    ! [A_14] : k1_relat_1(k6_relat_1(A_14)) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_18,plain,(
    ! [A_15] :
      ( k5_relat_1(A_15,k6_relat_1(k2_relat_1(A_15))) = A_15
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_191,plain,(
    ! [C_36,B_37,A_38] :
      ( k1_relat_1(k5_relat_1(C_36,B_37)) = k1_relat_1(k5_relat_1(C_36,A_38))
      | k1_relat_1(B_37) != k1_relat_1(A_38)
      | ~ v1_relat_1(C_36)
      | ~ v1_relat_1(B_37)
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_236,plain,(
    ! [A_15,A_38] :
      ( k1_relat_1(k5_relat_1(A_15,A_38)) = k1_relat_1(A_15)
      | k1_relat_1(k6_relat_1(k2_relat_1(A_15))) != k1_relat_1(A_38)
      | ~ v1_relat_1(A_15)
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(A_15)))
      | ~ v1_relat_1(A_38)
      | ~ v1_relat_1(A_15) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_191])).

tff(c_298,plain,(
    ! [A_41,A_42] :
      ( k1_relat_1(k5_relat_1(A_41,A_42)) = k1_relat_1(A_41)
      | k2_relat_1(A_41) != k1_relat_1(A_42)
      | ~ v1_relat_1(A_42)
      | ~ v1_relat_1(A_41) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_14,c_236])).

tff(c_28,plain,
    ( k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1')
    | k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_58,plain,(
    k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_317,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1')
    | k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_298,c_58])).

tff(c_340,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1')
    | k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_317])).

tff(c_349,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_340])).

tff(c_352,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_349])).

tff(c_356,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_352])).

tff(c_357,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1')
    | k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_340])).

tff(c_359,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_357])).

tff(c_362,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_359])).

tff(c_366,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_362])).

tff(c_367,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_357])).

tff(c_419,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_367])).

tff(c_423,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_419])).

tff(c_424,plain,(
    k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_588,plain,(
    ! [C_57,B_58,A_59] :
      ( k1_relat_1(k5_relat_1(C_57,B_58)) = k1_relat_1(k5_relat_1(C_57,A_59))
      | k1_relat_1(B_58) != k1_relat_1(A_59)
      | ~ v1_relat_1(C_57)
      | ~ v1_relat_1(B_58)
      | ~ v1_relat_1(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_645,plain,(
    ! [A_15,A_59] :
      ( k1_relat_1(k5_relat_1(A_15,A_59)) = k1_relat_1(A_15)
      | k1_relat_1(k6_relat_1(k2_relat_1(A_15))) != k1_relat_1(A_59)
      | ~ v1_relat_1(A_15)
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(A_15)))
      | ~ v1_relat_1(A_59)
      | ~ v1_relat_1(A_15) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_588])).

tff(c_724,plain,(
    ! [A_62,A_63] :
      ( k1_relat_1(k5_relat_1(A_62,A_63)) = k1_relat_1(A_62)
      | k2_relat_1(A_62) != k1_relat_1(A_63)
      | ~ v1_relat_1(A_63)
      | ~ v1_relat_1(A_62) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_14,c_645])).

tff(c_425,plain,(
    k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) = k2_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_746,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1')
    | k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_724,c_425])).

tff(c_775,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1')
    | k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_746])).

tff(c_789,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_775])).

tff(c_792,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_789])).

tff(c_796,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_792])).

tff(c_798,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_775])).

tff(c_797,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1')
    | k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_775])).

tff(c_800,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_797])).

tff(c_803,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_800])).

tff(c_807,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_803])).

tff(c_809,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_797])).

tff(c_12,plain,(
    ! [B_13,A_11] :
      ( k2_relat_1(k5_relat_1(B_13,A_11)) = k2_relat_1(A_11)
      | ~ r1_tarski(k1_relat_1(A_11),k2_relat_1(B_13))
      | ~ v1_relat_1(B_13)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_839,plain,(
    ! [A_11] :
      ( k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),A_11)) = k2_relat_1(A_11)
      | ~ r1_tarski(k1_relat_1(A_11),k1_relat_1('#skF_1'))
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v1_relat_1(A_11) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_809,c_12])).

tff(c_979,plain,(
    ! [A_65] :
      ( k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),A_65)) = k2_relat_1(A_65)
      | ~ r1_tarski(k1_relat_1(A_65),k1_relat_1('#skF_1'))
      | ~ v1_relat_1(A_65) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_798,c_839])).

tff(c_1010,plain,
    ( k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) = k2_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_979])).

tff(c_1017,plain,(
    k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) = k2_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1010])).

tff(c_1019,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_424,c_1017])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:29:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.31/1.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.31/1.64  
% 3.31/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.31/1.64  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1
% 3.31/1.64  
% 3.31/1.64  %Foreground sorts:
% 3.31/1.64  
% 3.31/1.64  
% 3.31/1.64  %Background operators:
% 3.31/1.64  
% 3.31/1.64  
% 3.31/1.64  %Foreground operators:
% 3.31/1.64  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.31/1.64  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.31/1.64  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.31/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.31/1.64  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.31/1.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.31/1.64  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.31/1.64  tff('#skF_1', type, '#skF_1': $i).
% 3.31/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.31/1.64  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.31/1.64  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.31/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.31/1.64  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.31/1.64  
% 3.31/1.66  tff(f_91, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)) & (k2_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_funct_1)).
% 3.31/1.66  tff(f_80, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 3.31/1.66  tff(f_70, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 3.31/1.66  tff(f_33, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 3.31/1.66  tff(f_58, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 3.31/1.66  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 3.31/1.66  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((k1_relat_1(A) = k1_relat_1(B)) => (k1_relat_1(k5_relat_1(C, A)) = k1_relat_1(k5_relat_1(C, B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t198_relat_1)).
% 3.31/1.66  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.31/1.66  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_relat_1)).
% 3.31/1.66  tff(c_34, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.31/1.66  tff(c_32, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.31/1.66  tff(c_30, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.31/1.66  tff(c_24, plain, (![A_17]: (k2_relat_1(k2_funct_1(A_17))=k1_relat_1(A_17) | ~v2_funct_1(A_17) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.31/1.66  tff(c_26, plain, (![A_17]: (k1_relat_1(k2_funct_1(A_17))=k2_relat_1(A_17) | ~v2_funct_1(A_17) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.31/1.66  tff(c_22, plain, (![A_16]: (v1_relat_1(k2_funct_1(A_16)) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.31/1.66  tff(c_8, plain, (![A_3]: (v1_relat_1(k6_relat_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.31/1.66  tff(c_14, plain, (![A_14]: (k1_relat_1(k6_relat_1(A_14))=A_14)), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.31/1.66  tff(c_18, plain, (![A_15]: (k5_relat_1(A_15, k6_relat_1(k2_relat_1(A_15)))=A_15 | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.31/1.66  tff(c_191, plain, (![C_36, B_37, A_38]: (k1_relat_1(k5_relat_1(C_36, B_37))=k1_relat_1(k5_relat_1(C_36, A_38)) | k1_relat_1(B_37)!=k1_relat_1(A_38) | ~v1_relat_1(C_36) | ~v1_relat_1(B_37) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.31/1.66  tff(c_236, plain, (![A_15, A_38]: (k1_relat_1(k5_relat_1(A_15, A_38))=k1_relat_1(A_15) | k1_relat_1(k6_relat_1(k2_relat_1(A_15)))!=k1_relat_1(A_38) | ~v1_relat_1(A_15) | ~v1_relat_1(k6_relat_1(k2_relat_1(A_15))) | ~v1_relat_1(A_38) | ~v1_relat_1(A_15))), inference(superposition, [status(thm), theory('equality')], [c_18, c_191])).
% 3.31/1.66  tff(c_298, plain, (![A_41, A_42]: (k1_relat_1(k5_relat_1(A_41, A_42))=k1_relat_1(A_41) | k2_relat_1(A_41)!=k1_relat_1(A_42) | ~v1_relat_1(A_42) | ~v1_relat_1(A_41))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_14, c_236])).
% 3.31/1.66  tff(c_28, plain, (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1') | k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.31/1.66  tff(c_58, plain, (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_28])).
% 3.31/1.66  tff(c_317, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1') | k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_298, c_58])).
% 3.31/1.66  tff(c_340, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1') | k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_317])).
% 3.31/1.66  tff(c_349, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_340])).
% 3.31/1.66  tff(c_352, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_22, c_349])).
% 3.31/1.66  tff(c_356, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_352])).
% 3.31/1.66  tff(c_357, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1') | k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_340])).
% 3.31/1.66  tff(c_359, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_357])).
% 3.31/1.66  tff(c_362, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_26, c_359])).
% 3.31/1.66  tff(c_366, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_362])).
% 3.31/1.66  tff(c_367, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_357])).
% 3.31/1.66  tff(c_419, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_24, c_367])).
% 3.31/1.66  tff(c_423, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_419])).
% 3.31/1.66  tff(c_424, plain, (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_28])).
% 3.31/1.66  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.31/1.66  tff(c_588, plain, (![C_57, B_58, A_59]: (k1_relat_1(k5_relat_1(C_57, B_58))=k1_relat_1(k5_relat_1(C_57, A_59)) | k1_relat_1(B_58)!=k1_relat_1(A_59) | ~v1_relat_1(C_57) | ~v1_relat_1(B_58) | ~v1_relat_1(A_59))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.31/1.66  tff(c_645, plain, (![A_15, A_59]: (k1_relat_1(k5_relat_1(A_15, A_59))=k1_relat_1(A_15) | k1_relat_1(k6_relat_1(k2_relat_1(A_15)))!=k1_relat_1(A_59) | ~v1_relat_1(A_15) | ~v1_relat_1(k6_relat_1(k2_relat_1(A_15))) | ~v1_relat_1(A_59) | ~v1_relat_1(A_15))), inference(superposition, [status(thm), theory('equality')], [c_18, c_588])).
% 3.31/1.66  tff(c_724, plain, (![A_62, A_63]: (k1_relat_1(k5_relat_1(A_62, A_63))=k1_relat_1(A_62) | k2_relat_1(A_62)!=k1_relat_1(A_63) | ~v1_relat_1(A_63) | ~v1_relat_1(A_62))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_14, c_645])).
% 3.31/1.66  tff(c_425, plain, (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))=k2_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_28])).
% 3.31/1.66  tff(c_746, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1') | k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_724, c_425])).
% 3.31/1.66  tff(c_775, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1') | k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_746])).
% 3.31/1.66  tff(c_789, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_775])).
% 3.31/1.66  tff(c_792, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_22, c_789])).
% 3.31/1.66  tff(c_796, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_792])).
% 3.31/1.66  tff(c_798, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_775])).
% 3.31/1.66  tff(c_797, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1') | k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_775])).
% 3.31/1.66  tff(c_800, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_797])).
% 3.31/1.66  tff(c_803, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_24, c_800])).
% 3.31/1.66  tff(c_807, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_803])).
% 3.31/1.66  tff(c_809, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_797])).
% 3.31/1.66  tff(c_12, plain, (![B_13, A_11]: (k2_relat_1(k5_relat_1(B_13, A_11))=k2_relat_1(A_11) | ~r1_tarski(k1_relat_1(A_11), k2_relat_1(B_13)) | ~v1_relat_1(B_13) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.31/1.66  tff(c_839, plain, (![A_11]: (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), A_11))=k2_relat_1(A_11) | ~r1_tarski(k1_relat_1(A_11), k1_relat_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(A_11))), inference(superposition, [status(thm), theory('equality')], [c_809, c_12])).
% 3.31/1.66  tff(c_979, plain, (![A_65]: (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), A_65))=k2_relat_1(A_65) | ~r1_tarski(k1_relat_1(A_65), k1_relat_1('#skF_1')) | ~v1_relat_1(A_65))), inference(demodulation, [status(thm), theory('equality')], [c_798, c_839])).
% 3.31/1.66  tff(c_1010, plain, (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))=k2_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_6, c_979])).
% 3.31/1.66  tff(c_1017, plain, (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))=k2_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1010])).
% 3.31/1.66  tff(c_1019, plain, $false, inference(negUnitSimplification, [status(thm)], [c_424, c_1017])).
% 3.31/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.31/1.66  
% 3.31/1.66  Inference rules
% 3.31/1.66  ----------------------
% 3.31/1.66  #Ref     : 0
% 3.31/1.66  #Sup     : 214
% 3.31/1.66  #Fact    : 0
% 3.31/1.66  #Define  : 0
% 3.31/1.66  #Split   : 6
% 3.31/1.66  #Chain   : 0
% 3.31/1.66  #Close   : 0
% 3.31/1.66  
% 3.31/1.66  Ordering : KBO
% 3.31/1.66  
% 3.31/1.66  Simplification rules
% 3.31/1.66  ----------------------
% 3.31/1.66  #Subsume      : 8
% 3.31/1.66  #Demod        : 261
% 3.31/1.66  #Tautology    : 96
% 3.31/1.66  #SimpNegUnit  : 1
% 3.31/1.66  #BackRed      : 0
% 3.31/1.66  
% 3.31/1.66  #Partial instantiations: 0
% 3.31/1.66  #Strategies tried      : 1
% 3.31/1.66  
% 3.31/1.66  Timing (in seconds)
% 3.31/1.66  ----------------------
% 3.31/1.66  Preprocessing        : 0.39
% 3.31/1.66  Parsing              : 0.22
% 3.31/1.66  CNF conversion       : 0.02
% 3.31/1.66  Main loop            : 0.46
% 3.31/1.66  Inferencing          : 0.17
% 3.31/1.66  Reduction            : 0.15
% 3.31/1.66  Demodulation         : 0.11
% 3.31/1.66  BG Simplification    : 0.03
% 3.31/1.66  Subsumption          : 0.08
% 3.31/1.66  Abstraction          : 0.03
% 3.31/1.66  MUC search           : 0.00
% 3.31/1.66  Cooper               : 0.00
% 3.31/1.66  Total                : 0.89
% 3.31/1.66  Index Insertion      : 0.00
% 3.31/1.66  Index Deletion       : 0.00
% 3.31/1.66  Index Matching       : 0.00
% 3.31/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
