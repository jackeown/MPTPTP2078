%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:56 EST 2020

% Result     : Theorem 3.20s
% Output     : CNFRefutation 3.20s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 206 expanded)
%              Number of leaves         :   21 (  78 expanded)
%              Depth                    :    9
%              Number of atoms          :  150 ( 550 expanded)
%              Number of equality atoms :   59 ( 237 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1

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

tff(f_92,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v2_funct_1(A)
         => ( k1_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A)
            & k2_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_funct_1)).

tff(f_81,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_71,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_27,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_55,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( k1_relat_1(A) = k1_relat_1(B)
               => k1_relat_1(k5_relat_1(C,A)) = k1_relat_1(k5_relat_1(C,B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t198_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( k2_relat_1(A) = k2_relat_1(B)
               => k2_relat_1(k5_relat_1(A,C)) = k2_relat_1(k5_relat_1(B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t199_relat_1)).

tff(c_30,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_28,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_26,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_20,plain,(
    ! [A_20] :
      ( k2_relat_1(k2_funct_1(A_20)) = k1_relat_1(A_20)
      | ~ v2_funct_1(A_20)
      | ~ v1_funct_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_18,plain,(
    ! [A_19] :
      ( v1_relat_1(k2_funct_1(A_19))
      | ~ v1_funct_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2,plain,(
    ! [A_1] : v1_relat_1(k6_relat_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_16] : k1_relat_1(k6_relat_1(A_16)) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_14,plain,(
    ! [A_18] :
      ( k5_relat_1(A_18,k6_relat_1(k2_relat_1(A_18))) = A_18
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_624,plain,(
    ! [C_52,B_53,A_54] :
      ( k1_relat_1(k5_relat_1(C_52,B_53)) = k1_relat_1(k5_relat_1(C_52,A_54))
      | k1_relat_1(B_53) != k1_relat_1(A_54)
      | ~ v1_relat_1(C_52)
      | ~ v1_relat_1(B_53)
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_684,plain,(
    ! [A_18,B_53] :
      ( k1_relat_1(k5_relat_1(A_18,B_53)) = k1_relat_1(A_18)
      | k1_relat_1(k6_relat_1(k2_relat_1(A_18))) != k1_relat_1(B_53)
      | ~ v1_relat_1(A_18)
      | ~ v1_relat_1(B_53)
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(A_18)))
      | ~ v1_relat_1(A_18) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_624])).

tff(c_942,plain,(
    ! [A_62,B_63] :
      ( k1_relat_1(k5_relat_1(A_62,B_63)) = k1_relat_1(A_62)
      | k2_relat_1(A_62) != k1_relat_1(B_63)
      | ~ v1_relat_1(B_63)
      | ~ v1_relat_1(A_62) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_8,c_684])).

tff(c_22,plain,(
    ! [A_20] :
      ( k1_relat_1(k2_funct_1(A_20)) = k2_relat_1(A_20)
      | ~ v2_funct_1(A_20)
      | ~ v1_funct_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_277,plain,(
    ! [C_38,B_39,A_40] :
      ( k1_relat_1(k5_relat_1(C_38,B_39)) = k1_relat_1(k5_relat_1(C_38,A_40))
      | k1_relat_1(B_39) != k1_relat_1(A_40)
      | ~ v1_relat_1(C_38)
      | ~ v1_relat_1(B_39)
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_319,plain,(
    ! [A_18,B_39] :
      ( k1_relat_1(k5_relat_1(A_18,B_39)) = k1_relat_1(A_18)
      | k1_relat_1(k6_relat_1(k2_relat_1(A_18))) != k1_relat_1(B_39)
      | ~ v1_relat_1(A_18)
      | ~ v1_relat_1(B_39)
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(A_18)))
      | ~ v1_relat_1(A_18) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_277])).

tff(c_399,plain,(
    ! [A_43,B_44] :
      ( k1_relat_1(k5_relat_1(A_43,B_44)) = k1_relat_1(A_43)
      | k2_relat_1(A_43) != k1_relat_1(B_44)
      | ~ v1_relat_1(B_44)
      | ~ v1_relat_1(A_43) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_8,c_319])).

tff(c_24,plain,
    ( k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1')
    | k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_66,plain,(
    k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_415,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1')
    | k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_399,c_66])).

tff(c_444,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1')
    | k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_415])).

tff(c_455,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_444])).

tff(c_458,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_455])).

tff(c_462,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_458])).

tff(c_463,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1')
    | k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_444])).

tff(c_465,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_463])).

tff(c_468,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_465])).

tff(c_472,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_468])).

tff(c_473,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_463])).

tff(c_525,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_473])).

tff(c_529,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_525])).

tff(c_531,plain,(
    k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) = k2_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_961,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1')
    | k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_942,c_531])).

tff(c_999,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1')
    | k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_961])).

tff(c_1017,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_999])).

tff(c_1020,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_1017])).

tff(c_1024,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_1020])).

tff(c_1025,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1')
    | k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_999])).

tff(c_1027,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1025])).

tff(c_1030,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1027])).

tff(c_1034,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_1030])).

tff(c_1036,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1025])).

tff(c_1026,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_999])).

tff(c_10,plain,(
    ! [A_16] : k2_relat_1(k6_relat_1(A_16)) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_12,plain,(
    ! [A_17] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_17)),A_17) = A_17
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_788,plain,(
    ! [B_57,C_58,A_59] :
      ( k2_relat_1(k5_relat_1(B_57,C_58)) = k2_relat_1(k5_relat_1(A_59,C_58))
      | k2_relat_1(B_57) != k2_relat_1(A_59)
      | ~ v1_relat_1(C_58)
      | ~ v1_relat_1(B_57)
      | ~ v1_relat_1(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_860,plain,(
    ! [B_57,A_17] :
      ( k2_relat_1(k5_relat_1(B_57,A_17)) = k2_relat_1(A_17)
      | k2_relat_1(k6_relat_1(k1_relat_1(A_17))) != k2_relat_1(B_57)
      | ~ v1_relat_1(A_17)
      | ~ v1_relat_1(B_57)
      | ~ v1_relat_1(k6_relat_1(k1_relat_1(A_17)))
      | ~ v1_relat_1(A_17) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_788])).

tff(c_1063,plain,(
    ! [B_64,A_65] :
      ( k2_relat_1(k5_relat_1(B_64,A_65)) = k2_relat_1(A_65)
      | k2_relat_1(B_64) != k1_relat_1(A_65)
      | ~ v1_relat_1(B_64)
      | ~ v1_relat_1(A_65) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_10,c_860])).

tff(c_530,plain,(
    k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_1085,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1063,c_530])).

tff(c_1118,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1026,c_1085])).

tff(c_1161,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1036,c_1118])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:26:15 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.20/1.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.59  
% 3.20/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.60  %$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1
% 3.20/1.60  
% 3.20/1.60  %Foreground sorts:
% 3.20/1.60  
% 3.20/1.60  
% 3.20/1.60  %Background operators:
% 3.20/1.60  
% 3.20/1.60  
% 3.20/1.60  %Foreground operators:
% 3.20/1.60  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.20/1.60  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.20/1.60  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.20/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.20/1.60  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.20/1.60  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.20/1.60  tff('#skF_1', type, '#skF_1': $i).
% 3.20/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.20/1.60  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.20/1.60  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.20/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.20/1.60  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.20/1.60  
% 3.20/1.61  tff(f_92, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)) & (k2_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_funct_1)).
% 3.20/1.61  tff(f_81, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 3.20/1.61  tff(f_71, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 3.20/1.61  tff(f_27, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 3.20/1.61  tff(f_55, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 3.20/1.61  tff(f_63, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 3.20/1.61  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((k1_relat_1(A) = k1_relat_1(B)) => (k1_relat_1(k5_relat_1(C, A)) = k1_relat_1(k5_relat_1(C, B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t198_relat_1)).
% 3.20/1.61  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_relat_1)).
% 3.20/1.61  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((k2_relat_1(A) = k2_relat_1(B)) => (k2_relat_1(k5_relat_1(A, C)) = k2_relat_1(k5_relat_1(B, C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t199_relat_1)).
% 3.20/1.61  tff(c_30, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.20/1.61  tff(c_28, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.20/1.61  tff(c_26, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.20/1.61  tff(c_20, plain, (![A_20]: (k2_relat_1(k2_funct_1(A_20))=k1_relat_1(A_20) | ~v2_funct_1(A_20) | ~v1_funct_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.20/1.61  tff(c_18, plain, (![A_19]: (v1_relat_1(k2_funct_1(A_19)) | ~v1_funct_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.20/1.61  tff(c_2, plain, (![A_1]: (v1_relat_1(k6_relat_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.20/1.61  tff(c_8, plain, (![A_16]: (k1_relat_1(k6_relat_1(A_16))=A_16)), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.20/1.61  tff(c_14, plain, (![A_18]: (k5_relat_1(A_18, k6_relat_1(k2_relat_1(A_18)))=A_18 | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.20/1.61  tff(c_624, plain, (![C_52, B_53, A_54]: (k1_relat_1(k5_relat_1(C_52, B_53))=k1_relat_1(k5_relat_1(C_52, A_54)) | k1_relat_1(B_53)!=k1_relat_1(A_54) | ~v1_relat_1(C_52) | ~v1_relat_1(B_53) | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.20/1.61  tff(c_684, plain, (![A_18, B_53]: (k1_relat_1(k5_relat_1(A_18, B_53))=k1_relat_1(A_18) | k1_relat_1(k6_relat_1(k2_relat_1(A_18)))!=k1_relat_1(B_53) | ~v1_relat_1(A_18) | ~v1_relat_1(B_53) | ~v1_relat_1(k6_relat_1(k2_relat_1(A_18))) | ~v1_relat_1(A_18))), inference(superposition, [status(thm), theory('equality')], [c_14, c_624])).
% 3.20/1.61  tff(c_942, plain, (![A_62, B_63]: (k1_relat_1(k5_relat_1(A_62, B_63))=k1_relat_1(A_62) | k2_relat_1(A_62)!=k1_relat_1(B_63) | ~v1_relat_1(B_63) | ~v1_relat_1(A_62))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_8, c_684])).
% 3.20/1.61  tff(c_22, plain, (![A_20]: (k1_relat_1(k2_funct_1(A_20))=k2_relat_1(A_20) | ~v2_funct_1(A_20) | ~v1_funct_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.20/1.61  tff(c_277, plain, (![C_38, B_39, A_40]: (k1_relat_1(k5_relat_1(C_38, B_39))=k1_relat_1(k5_relat_1(C_38, A_40)) | k1_relat_1(B_39)!=k1_relat_1(A_40) | ~v1_relat_1(C_38) | ~v1_relat_1(B_39) | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.20/1.61  tff(c_319, plain, (![A_18, B_39]: (k1_relat_1(k5_relat_1(A_18, B_39))=k1_relat_1(A_18) | k1_relat_1(k6_relat_1(k2_relat_1(A_18)))!=k1_relat_1(B_39) | ~v1_relat_1(A_18) | ~v1_relat_1(B_39) | ~v1_relat_1(k6_relat_1(k2_relat_1(A_18))) | ~v1_relat_1(A_18))), inference(superposition, [status(thm), theory('equality')], [c_14, c_277])).
% 3.20/1.61  tff(c_399, plain, (![A_43, B_44]: (k1_relat_1(k5_relat_1(A_43, B_44))=k1_relat_1(A_43) | k2_relat_1(A_43)!=k1_relat_1(B_44) | ~v1_relat_1(B_44) | ~v1_relat_1(A_43))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_8, c_319])).
% 3.20/1.61  tff(c_24, plain, (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1') | k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.20/1.61  tff(c_66, plain, (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_24])).
% 3.20/1.61  tff(c_415, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1') | k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_399, c_66])).
% 3.20/1.61  tff(c_444, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1') | k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_415])).
% 3.20/1.61  tff(c_455, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_444])).
% 3.20/1.61  tff(c_458, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_18, c_455])).
% 3.20/1.61  tff(c_462, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_458])).
% 3.20/1.61  tff(c_463, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1') | k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_444])).
% 3.20/1.61  tff(c_465, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_463])).
% 3.20/1.61  tff(c_468, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_22, c_465])).
% 3.20/1.61  tff(c_472, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_468])).
% 3.20/1.61  tff(c_473, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_463])).
% 3.20/1.61  tff(c_525, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_20, c_473])).
% 3.20/1.61  tff(c_529, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_525])).
% 3.20/1.61  tff(c_531, plain, (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))=k2_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_24])).
% 3.20/1.61  tff(c_961, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1') | k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_942, c_531])).
% 3.20/1.61  tff(c_999, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1') | k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_961])).
% 3.20/1.61  tff(c_1017, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_999])).
% 3.20/1.61  tff(c_1020, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_18, c_1017])).
% 3.20/1.61  tff(c_1024, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_1020])).
% 3.20/1.61  tff(c_1025, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1') | k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_999])).
% 3.20/1.61  tff(c_1027, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_1025])).
% 3.20/1.61  tff(c_1030, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_20, c_1027])).
% 3.20/1.61  tff(c_1034, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_1030])).
% 3.20/1.61  tff(c_1036, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_1025])).
% 3.20/1.61  tff(c_1026, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_999])).
% 3.20/1.61  tff(c_10, plain, (![A_16]: (k2_relat_1(k6_relat_1(A_16))=A_16)), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.20/1.61  tff(c_12, plain, (![A_17]: (k5_relat_1(k6_relat_1(k1_relat_1(A_17)), A_17)=A_17 | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.20/1.61  tff(c_788, plain, (![B_57, C_58, A_59]: (k2_relat_1(k5_relat_1(B_57, C_58))=k2_relat_1(k5_relat_1(A_59, C_58)) | k2_relat_1(B_57)!=k2_relat_1(A_59) | ~v1_relat_1(C_58) | ~v1_relat_1(B_57) | ~v1_relat_1(A_59))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.20/1.61  tff(c_860, plain, (![B_57, A_17]: (k2_relat_1(k5_relat_1(B_57, A_17))=k2_relat_1(A_17) | k2_relat_1(k6_relat_1(k1_relat_1(A_17)))!=k2_relat_1(B_57) | ~v1_relat_1(A_17) | ~v1_relat_1(B_57) | ~v1_relat_1(k6_relat_1(k1_relat_1(A_17))) | ~v1_relat_1(A_17))), inference(superposition, [status(thm), theory('equality')], [c_12, c_788])).
% 3.20/1.61  tff(c_1063, plain, (![B_64, A_65]: (k2_relat_1(k5_relat_1(B_64, A_65))=k2_relat_1(A_65) | k2_relat_1(B_64)!=k1_relat_1(A_65) | ~v1_relat_1(B_64) | ~v1_relat_1(A_65))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_10, c_860])).
% 3.20/1.61  tff(c_530, plain, (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_24])).
% 3.20/1.61  tff(c_1085, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1063, c_530])).
% 3.20/1.61  tff(c_1118, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1026, c_1085])).
% 3.20/1.61  tff(c_1161, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1036, c_1118])).
% 3.20/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.61  
% 3.20/1.61  Inference rules
% 3.20/1.61  ----------------------
% 3.20/1.61  #Ref     : 0
% 3.20/1.61  #Sup     : 253
% 3.20/1.61  #Fact    : 0
% 3.20/1.61  #Define  : 0
% 3.20/1.61  #Split   : 6
% 3.20/1.61  #Chain   : 0
% 3.20/1.61  #Close   : 0
% 3.20/1.61  
% 3.20/1.61  Ordering : KBO
% 3.20/1.61  
% 3.20/1.61  Simplification rules
% 3.20/1.61  ----------------------
% 3.20/1.61  #Subsume      : 10
% 3.20/1.61  #Demod        : 260
% 3.20/1.61  #Tautology    : 92
% 3.20/1.61  #SimpNegUnit  : 0
% 3.20/1.61  #BackRed      : 0
% 3.20/1.61  
% 3.20/1.61  #Partial instantiations: 0
% 3.20/1.61  #Strategies tried      : 1
% 3.20/1.61  
% 3.20/1.61  Timing (in seconds)
% 3.20/1.61  ----------------------
% 3.20/1.61  Preprocessing        : 0.32
% 3.20/1.61  Parsing              : 0.17
% 3.20/1.61  CNF conversion       : 0.02
% 3.20/1.61  Main loop            : 0.42
% 3.20/1.61  Inferencing          : 0.16
% 3.20/1.62  Reduction            : 0.13
% 3.20/1.62  Demodulation         : 0.10
% 3.20/1.62  BG Simplification    : 0.03
% 3.20/1.62  Subsumption          : 0.07
% 3.20/1.62  Abstraction          : 0.03
% 3.20/1.62  MUC search           : 0.00
% 3.20/1.62  Cooper               : 0.00
% 3.20/1.62  Total                : 0.78
% 3.20/1.62  Index Insertion      : 0.00
% 3.20/1.62  Index Deletion       : 0.00
% 3.20/1.62  Index Matching       : 0.00
% 3.20/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
