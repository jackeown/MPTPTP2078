%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:01 EST 2020

% Result     : Theorem 5.15s
% Output     : CNFRefutation 5.15s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 213 expanded)
%              Number of leaves         :   27 (  88 expanded)
%              Depth                    :   13
%              Number of atoms          :  156 ( 579 expanded)
%              Number of equality atoms :   53 ( 208 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(f_119,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_funct_1)).

tff(f_66,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_78,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_46,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_91,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( k1_relat_1(k5_relat_1(B,A)) = k1_relat_1(B)
           => r1_tarski(k2_relat_1(B),k1_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_funct_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

tff(f_48,axiom,(
    ! [A] : k4_relat_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k5_relat_1(A,B)) = k5_relat_1(k4_relat_1(B),k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

tff(f_74,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_101,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

tff(c_32,plain,(
    k2_funct_1('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_42,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_46,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_44,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_38,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_157,plain,(
    ! [A_33] :
      ( k4_relat_1(A_33) = k2_funct_1(A_33)
      | ~ v2_funct_1(A_33)
      | ~ v1_funct_1(A_33)
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_160,plain,
    ( k4_relat_1('#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_157])).

tff(c_163,plain,(
    k4_relat_1('#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_160])).

tff(c_34,plain,(
    k6_relat_1(k1_relat_1('#skF_1')) = k5_relat_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_22,plain,(
    ! [A_18] : v1_relat_1(k6_relat_1(A_18)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_24,plain,(
    ! [A_18] : v1_funct_1(k6_relat_1(A_18)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_6,plain,(
    ! [A_11] : k1_relat_1(k6_relat_1(A_11)) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_8,plain,(
    ! [A_11] : k2_relat_1(k6_relat_1(A_11)) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_112,plain,(
    ! [A_31] :
      ( k5_relat_1(A_31,k6_relat_1(k2_relat_1(A_31))) = A_31
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_124,plain,(
    ! [A_11] :
      ( k5_relat_1(k6_relat_1(A_11),k6_relat_1(A_11)) = k6_relat_1(A_11)
      | ~ v1_relat_1(k6_relat_1(A_11)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_112])).

tff(c_133,plain,(
    ! [A_11] : k5_relat_1(k6_relat_1(A_11),k6_relat_1(A_11)) = k6_relat_1(A_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_124])).

tff(c_609,plain,(
    ! [B_54,A_55] :
      ( r1_tarski(k2_relat_1(B_54),k1_relat_1(A_55))
      | k1_relat_1(k5_relat_1(B_54,A_55)) != k1_relat_1(B_54)
      | ~ v1_funct_1(B_54)
      | ~ v1_relat_1(B_54)
      | ~ v1_funct_1(A_55)
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_618,plain,(
    ! [A_11,A_55] :
      ( r1_tarski(A_11,k1_relat_1(A_55))
      | k1_relat_1(k5_relat_1(k6_relat_1(A_11),A_55)) != k1_relat_1(k6_relat_1(A_11))
      | ~ v1_funct_1(k6_relat_1(A_11))
      | ~ v1_relat_1(k6_relat_1(A_11))
      | ~ v1_funct_1(A_55)
      | ~ v1_relat_1(A_55) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_609])).

tff(c_1235,plain,(
    ! [A_75,A_76] :
      ( r1_tarski(A_75,k1_relat_1(A_76))
      | k1_relat_1(k5_relat_1(k6_relat_1(A_75),A_76)) != A_75
      | ~ v1_funct_1(A_76)
      | ~ v1_relat_1(A_76) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_24,c_6,c_618])).

tff(c_1267,plain,(
    ! [A_11] :
      ( r1_tarski(A_11,k1_relat_1(k6_relat_1(A_11)))
      | k1_relat_1(k6_relat_1(A_11)) != A_11
      | ~ v1_funct_1(k6_relat_1(A_11))
      | ~ v1_relat_1(k6_relat_1(A_11)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_1235])).

tff(c_1293,plain,(
    ! [A_77] : r1_tarski(A_77,A_77) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_24,c_6,c_6,c_1267])).

tff(c_12,plain,(
    ! [A_13,B_14] :
      ( k5_relat_1(k6_relat_1(A_13),B_14) = B_14
      | ~ r1_tarski(k1_relat_1(B_14),A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1312,plain,(
    ! [B_78] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(B_78)),B_78) = B_78
      | ~ v1_relat_1(B_78) ) ),
    inference(resolution,[status(thm)],[c_1293,c_12])).

tff(c_1396,plain,
    ( k5_relat_1(k5_relat_1('#skF_1','#skF_2'),'#skF_1') = '#skF_1'
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_1312])).

tff(c_1440,plain,(
    k5_relat_1(k5_relat_1('#skF_1','#skF_2'),'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1396])).

tff(c_10,plain,(
    ! [A_12] : k4_relat_1(k6_relat_1(A_12)) = k6_relat_1(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_265,plain,(
    ! [B_41,A_42] :
      ( k5_relat_1(k4_relat_1(B_41),k4_relat_1(A_42)) = k4_relat_1(k5_relat_1(A_42,B_41))
      | ~ v1_relat_1(B_41)
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_274,plain,(
    ! [A_42] :
      ( k5_relat_1(k2_funct_1('#skF_1'),k4_relat_1(A_42)) = k4_relat_1(k5_relat_1(A_42,'#skF_1'))
      | ~ v1_relat_1('#skF_1')
      | ~ v1_relat_1(A_42) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_265])).

tff(c_304,plain,(
    ! [A_43] :
      ( k5_relat_1(k2_funct_1('#skF_1'),k4_relat_1(A_43)) = k4_relat_1(k5_relat_1(A_43,'#skF_1'))
      | ~ v1_relat_1(A_43) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_274])).

tff(c_319,plain,(
    ! [A_12] :
      ( k5_relat_1(k2_funct_1('#skF_1'),k6_relat_1(A_12)) = k4_relat_1(k5_relat_1(k6_relat_1(A_12),'#skF_1'))
      | ~ v1_relat_1(k6_relat_1(A_12)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_304])).

tff(c_432,plain,(
    ! [A_47] : k5_relat_1(k2_funct_1('#skF_1'),k6_relat_1(A_47)) = k4_relat_1(k5_relat_1(k6_relat_1(A_47),'#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_319])).

tff(c_452,plain,(
    k4_relat_1(k5_relat_1(k6_relat_1(k1_relat_1('#skF_1')),'#skF_1')) = k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_432])).

tff(c_457,plain,(
    k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1','#skF_2')) = k4_relat_1(k5_relat_1(k5_relat_1('#skF_1','#skF_2'),'#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_452])).

tff(c_1462,plain,(
    k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1','#skF_2')) = k4_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1440,c_457])).

tff(c_1463,plain,(
    k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1','#skF_2')) = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_1462])).

tff(c_20,plain,(
    ! [A_17] :
      ( v1_relat_1(k2_funct_1(A_17))
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_14,plain,(
    ! [A_15] :
      ( k5_relat_1(A_15,k6_relat_1(k2_relat_1(A_15))) = A_15
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_442,plain,
    ( k4_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(k2_funct_1('#skF_1'))),'#skF_1')) = k2_funct_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_432,c_14])).

tff(c_960,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_442])).

tff(c_1030,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_960])).

tff(c_1034,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_1030])).

tff(c_1036,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_442])).

tff(c_36,plain,(
    k2_relat_1('#skF_1') = k1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_28,plain,(
    ! [A_22] :
      ( k5_relat_1(k2_funct_1(A_22),A_22) = k6_relat_1(k2_relat_1(A_22))
      | ~ v2_funct_1(A_22)
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_328,plain,(
    ! [A_44,B_45,C_46] :
      ( k5_relat_1(k5_relat_1(A_44,B_45),C_46) = k5_relat_1(A_44,k5_relat_1(B_45,C_46))
      | ~ v1_relat_1(C_46)
      | ~ v1_relat_1(B_45)
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2873,plain,(
    ! [A_100,C_101] :
      ( k5_relat_1(k6_relat_1(k2_relat_1(A_100)),C_101) = k5_relat_1(k2_funct_1(A_100),k5_relat_1(A_100,C_101))
      | ~ v1_relat_1(C_101)
      | ~ v1_relat_1(A_100)
      | ~ v1_relat_1(k2_funct_1(A_100))
      | ~ v2_funct_1(A_100)
      | ~ v1_funct_1(A_100)
      | ~ v1_relat_1(A_100) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_328])).

tff(c_3173,plain,(
    ! [C_101] :
      ( k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')),C_101) = k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1',C_101))
      | ~ v1_relat_1(C_101)
      | ~ v1_relat_1('#skF_1')
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v2_funct_1('#skF_1')
      | ~ v1_funct_1('#skF_1')
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_2873])).

tff(c_3311,plain,(
    ! [C_102] :
      ( k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')),C_102) = k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1',C_102))
      | ~ v1_relat_1(C_102) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_38,c_1036,c_46,c_3173])).

tff(c_1310,plain,(
    ! [B_14] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(B_14)),B_14) = B_14
      | ~ v1_relat_1(B_14) ) ),
    inference(resolution,[status(thm)],[c_1293,c_12])).

tff(c_3344,plain,
    ( k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1','#skF_2')) = '#skF_2'
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3311,c_1310])).

tff(c_3485,plain,(
    k2_funct_1('#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_42,c_1463,c_3344])).

tff(c_3487,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_3485])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:31:55 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.15/1.93  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.15/1.94  
% 5.15/1.94  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.15/1.94  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1
% 5.15/1.94  
% 5.15/1.94  %Foreground sorts:
% 5.15/1.94  
% 5.15/1.94  
% 5.15/1.94  %Background operators:
% 5.15/1.94  
% 5.15/1.94  
% 5.15/1.94  %Foreground operators:
% 5.15/1.94  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.15/1.94  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.15/1.94  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.15/1.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.15/1.94  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.15/1.94  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.15/1.94  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.15/1.94  tff('#skF_2', type, '#skF_2': $i).
% 5.15/1.94  tff('#skF_1', type, '#skF_1': $i).
% 5.15/1.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.15/1.94  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.15/1.94  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.15/1.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.15/1.94  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.15/1.94  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 5.15/1.94  
% 5.15/1.95  tff(f_119, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(A) = k1_relat_1(B))) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_funct_1)).
% 5.15/1.95  tff(f_66, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 5.15/1.95  tff(f_78, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 5.15/1.95  tff(f_46, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 5.15/1.95  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 5.15/1.95  tff(f_91, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(k5_relat_1(B, A)) = k1_relat_1(B)) => r1_tarski(k2_relat_1(B), k1_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_funct_1)).
% 5.15/1.95  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_relat_1)).
% 5.15/1.95  tff(f_48, axiom, (![A]: (k4_relat_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_relat_1)).
% 5.15/1.95  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k5_relat_1(A, B)) = k5_relat_1(k4_relat_1(B), k4_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_relat_1)).
% 5.15/1.95  tff(f_74, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 5.15/1.95  tff(f_101, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 5.15/1.95  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 5.15/1.95  tff(c_32, plain, (k2_funct_1('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.15/1.95  tff(c_42, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.15/1.95  tff(c_46, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.15/1.95  tff(c_44, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.15/1.95  tff(c_38, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.15/1.95  tff(c_157, plain, (![A_33]: (k4_relat_1(A_33)=k2_funct_1(A_33) | ~v2_funct_1(A_33) | ~v1_funct_1(A_33) | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.15/1.95  tff(c_160, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_38, c_157])).
% 5.15/1.95  tff(c_163, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_160])).
% 5.15/1.95  tff(c_34, plain, (k6_relat_1(k1_relat_1('#skF_1'))=k5_relat_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.15/1.95  tff(c_22, plain, (![A_18]: (v1_relat_1(k6_relat_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.15/1.95  tff(c_24, plain, (![A_18]: (v1_funct_1(k6_relat_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.15/1.95  tff(c_6, plain, (![A_11]: (k1_relat_1(k6_relat_1(A_11))=A_11)), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.15/1.95  tff(c_8, plain, (![A_11]: (k2_relat_1(k6_relat_1(A_11))=A_11)), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.15/1.95  tff(c_112, plain, (![A_31]: (k5_relat_1(A_31, k6_relat_1(k2_relat_1(A_31)))=A_31 | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.15/1.95  tff(c_124, plain, (![A_11]: (k5_relat_1(k6_relat_1(A_11), k6_relat_1(A_11))=k6_relat_1(A_11) | ~v1_relat_1(k6_relat_1(A_11)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_112])).
% 5.15/1.95  tff(c_133, plain, (![A_11]: (k5_relat_1(k6_relat_1(A_11), k6_relat_1(A_11))=k6_relat_1(A_11))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_124])).
% 5.15/1.95  tff(c_609, plain, (![B_54, A_55]: (r1_tarski(k2_relat_1(B_54), k1_relat_1(A_55)) | k1_relat_1(k5_relat_1(B_54, A_55))!=k1_relat_1(B_54) | ~v1_funct_1(B_54) | ~v1_relat_1(B_54) | ~v1_funct_1(A_55) | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.15/1.95  tff(c_618, plain, (![A_11, A_55]: (r1_tarski(A_11, k1_relat_1(A_55)) | k1_relat_1(k5_relat_1(k6_relat_1(A_11), A_55))!=k1_relat_1(k6_relat_1(A_11)) | ~v1_funct_1(k6_relat_1(A_11)) | ~v1_relat_1(k6_relat_1(A_11)) | ~v1_funct_1(A_55) | ~v1_relat_1(A_55))), inference(superposition, [status(thm), theory('equality')], [c_8, c_609])).
% 5.15/1.95  tff(c_1235, plain, (![A_75, A_76]: (r1_tarski(A_75, k1_relat_1(A_76)) | k1_relat_1(k5_relat_1(k6_relat_1(A_75), A_76))!=A_75 | ~v1_funct_1(A_76) | ~v1_relat_1(A_76))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_24, c_6, c_618])).
% 5.15/1.95  tff(c_1267, plain, (![A_11]: (r1_tarski(A_11, k1_relat_1(k6_relat_1(A_11))) | k1_relat_1(k6_relat_1(A_11))!=A_11 | ~v1_funct_1(k6_relat_1(A_11)) | ~v1_relat_1(k6_relat_1(A_11)))), inference(superposition, [status(thm), theory('equality')], [c_133, c_1235])).
% 5.15/1.95  tff(c_1293, plain, (![A_77]: (r1_tarski(A_77, A_77))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_24, c_6, c_6, c_1267])).
% 5.15/1.95  tff(c_12, plain, (![A_13, B_14]: (k5_relat_1(k6_relat_1(A_13), B_14)=B_14 | ~r1_tarski(k1_relat_1(B_14), A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.15/1.95  tff(c_1312, plain, (![B_78]: (k5_relat_1(k6_relat_1(k1_relat_1(B_78)), B_78)=B_78 | ~v1_relat_1(B_78))), inference(resolution, [status(thm)], [c_1293, c_12])).
% 5.15/1.95  tff(c_1396, plain, (k5_relat_1(k5_relat_1('#skF_1', '#skF_2'), '#skF_1')='#skF_1' | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_34, c_1312])).
% 5.15/1.95  tff(c_1440, plain, (k5_relat_1(k5_relat_1('#skF_1', '#skF_2'), '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1396])).
% 5.15/1.95  tff(c_10, plain, (![A_12]: (k4_relat_1(k6_relat_1(A_12))=k6_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.15/1.95  tff(c_265, plain, (![B_41, A_42]: (k5_relat_1(k4_relat_1(B_41), k4_relat_1(A_42))=k4_relat_1(k5_relat_1(A_42, B_41)) | ~v1_relat_1(B_41) | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.15/1.95  tff(c_274, plain, (![A_42]: (k5_relat_1(k2_funct_1('#skF_1'), k4_relat_1(A_42))=k4_relat_1(k5_relat_1(A_42, '#skF_1')) | ~v1_relat_1('#skF_1') | ~v1_relat_1(A_42))), inference(superposition, [status(thm), theory('equality')], [c_163, c_265])).
% 5.15/1.95  tff(c_304, plain, (![A_43]: (k5_relat_1(k2_funct_1('#skF_1'), k4_relat_1(A_43))=k4_relat_1(k5_relat_1(A_43, '#skF_1')) | ~v1_relat_1(A_43))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_274])).
% 5.15/1.95  tff(c_319, plain, (![A_12]: (k5_relat_1(k2_funct_1('#skF_1'), k6_relat_1(A_12))=k4_relat_1(k5_relat_1(k6_relat_1(A_12), '#skF_1')) | ~v1_relat_1(k6_relat_1(A_12)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_304])).
% 5.15/1.95  tff(c_432, plain, (![A_47]: (k5_relat_1(k2_funct_1('#skF_1'), k6_relat_1(A_47))=k4_relat_1(k5_relat_1(k6_relat_1(A_47), '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_319])).
% 5.15/1.95  tff(c_452, plain, (k4_relat_1(k5_relat_1(k6_relat_1(k1_relat_1('#skF_1')), '#skF_1'))=k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_432])).
% 5.15/1.95  tff(c_457, plain, (k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', '#skF_2'))=k4_relat_1(k5_relat_1(k5_relat_1('#skF_1', '#skF_2'), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_452])).
% 5.15/1.95  tff(c_1462, plain, (k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', '#skF_2'))=k4_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1440, c_457])).
% 5.15/1.95  tff(c_1463, plain, (k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', '#skF_2'))=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_163, c_1462])).
% 5.15/1.95  tff(c_20, plain, (![A_17]: (v1_relat_1(k2_funct_1(A_17)) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.15/1.95  tff(c_14, plain, (![A_15]: (k5_relat_1(A_15, k6_relat_1(k2_relat_1(A_15)))=A_15 | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.15/1.95  tff(c_442, plain, (k4_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(k2_funct_1('#skF_1'))), '#skF_1'))=k2_funct_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_432, c_14])).
% 5.15/1.95  tff(c_960, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_442])).
% 5.15/1.95  tff(c_1030, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_20, c_960])).
% 5.15/1.95  tff(c_1034, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_1030])).
% 5.15/1.95  tff(c_1036, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_442])).
% 5.15/1.95  tff(c_36, plain, (k2_relat_1('#skF_1')=k1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.15/1.95  tff(c_28, plain, (![A_22]: (k5_relat_1(k2_funct_1(A_22), A_22)=k6_relat_1(k2_relat_1(A_22)) | ~v2_funct_1(A_22) | ~v1_funct_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.15/1.95  tff(c_328, plain, (![A_44, B_45, C_46]: (k5_relat_1(k5_relat_1(A_44, B_45), C_46)=k5_relat_1(A_44, k5_relat_1(B_45, C_46)) | ~v1_relat_1(C_46) | ~v1_relat_1(B_45) | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.15/1.95  tff(c_2873, plain, (![A_100, C_101]: (k5_relat_1(k6_relat_1(k2_relat_1(A_100)), C_101)=k5_relat_1(k2_funct_1(A_100), k5_relat_1(A_100, C_101)) | ~v1_relat_1(C_101) | ~v1_relat_1(A_100) | ~v1_relat_1(k2_funct_1(A_100)) | ~v2_funct_1(A_100) | ~v1_funct_1(A_100) | ~v1_relat_1(A_100))), inference(superposition, [status(thm), theory('equality')], [c_28, c_328])).
% 5.15/1.95  tff(c_3173, plain, (![C_101]: (k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')), C_101)=k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', C_101)) | ~v1_relat_1(C_101) | ~v1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_36, c_2873])).
% 5.15/1.95  tff(c_3311, plain, (![C_102]: (k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')), C_102)=k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', C_102)) | ~v1_relat_1(C_102))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_38, c_1036, c_46, c_3173])).
% 5.15/1.95  tff(c_1310, plain, (![B_14]: (k5_relat_1(k6_relat_1(k1_relat_1(B_14)), B_14)=B_14 | ~v1_relat_1(B_14))), inference(resolution, [status(thm)], [c_1293, c_12])).
% 5.15/1.95  tff(c_3344, plain, (k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', '#skF_2'))='#skF_2' | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3311, c_1310])).
% 5.15/1.95  tff(c_3485, plain, (k2_funct_1('#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_42, c_1463, c_3344])).
% 5.15/1.95  tff(c_3487, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_3485])).
% 5.15/1.95  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.15/1.95  
% 5.15/1.95  Inference rules
% 5.15/1.95  ----------------------
% 5.15/1.95  #Ref     : 0
% 5.15/1.95  #Sup     : 740
% 5.15/1.95  #Fact    : 0
% 5.15/1.95  #Define  : 0
% 5.15/1.95  #Split   : 4
% 5.15/1.95  #Chain   : 0
% 5.15/1.95  #Close   : 0
% 5.15/1.95  
% 5.15/1.95  Ordering : KBO
% 5.15/1.95  
% 5.15/1.95  Simplification rules
% 5.15/1.95  ----------------------
% 5.15/1.95  #Subsume      : 43
% 5.15/1.95  #Demod        : 1221
% 5.15/1.95  #Tautology    : 310
% 5.15/1.95  #SimpNegUnit  : 10
% 5.15/1.95  #BackRed      : 1
% 5.15/1.95  
% 5.15/1.95  #Partial instantiations: 0
% 5.15/1.95  #Strategies tried      : 1
% 5.15/1.95  
% 5.15/1.95  Timing (in seconds)
% 5.15/1.95  ----------------------
% 5.15/1.96  Preprocessing        : 0.32
% 5.15/1.96  Parsing              : 0.17
% 5.15/1.96  CNF conversion       : 0.02
% 5.15/1.96  Main loop            : 0.88
% 5.15/1.96  Inferencing          : 0.29
% 5.15/1.96  Reduction            : 0.36
% 5.15/1.96  Demodulation         : 0.28
% 5.15/1.96  BG Simplification    : 0.04
% 5.15/1.96  Subsumption          : 0.14
% 5.15/1.96  Abstraction          : 0.05
% 5.15/1.96  MUC search           : 0.00
% 5.15/1.96  Cooper               : 0.00
% 5.15/1.96  Total                : 1.23
% 5.15/1.96  Index Insertion      : 0.00
% 5.15/1.96  Index Deletion       : 0.00
% 5.15/1.96  Index Matching       : 0.00
% 5.15/1.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
