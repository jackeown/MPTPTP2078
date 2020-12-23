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
% DateTime   : Thu Dec  3 10:03:56 EST 2020

% Result     : Theorem 3.24s
% Output     : CNFRefutation 3.24s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 185 expanded)
%              Number of leaves         :   25 (  72 expanded)
%              Depth                    :   12
%              Number of atoms          :  154 ( 494 expanded)
%              Number of equality atoms :   62 ( 207 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(f_100,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v2_funct_1(A)
         => ( k1_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A)
            & k2_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_funct_1)).

tff(f_89,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_79,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_27,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_63,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( k2_relat_1(A) = k2_relat_1(B)
               => k2_relat_1(k5_relat_1(A,C)) = k2_relat_1(k5_relat_1(B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t199_relat_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( k1_relat_1(A) = k1_relat_1(B)
               => k1_relat_1(k5_relat_1(C,A)) = k1_relat_1(k5_relat_1(C,B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t198_relat_1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

tff(c_34,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_32,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_30,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_24,plain,(
    ! [A_24] :
      ( k2_relat_1(k2_funct_1(A_24)) = k1_relat_1(A_24)
      | ~ v2_funct_1(A_24)
      | ~ v1_funct_1(A_24)
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_4,plain,(
    ! [A_2] :
      ( k9_relat_1(A_2,k1_relat_1(A_2)) = k2_relat_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( k2_relat_1(k7_relat_1(B_4,A_3)) = k9_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_22,plain,(
    ! [A_23] :
      ( v1_relat_1(k2_funct_1(A_23))
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2,plain,(
    ! [A_1] : v1_relat_1(k6_relat_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_19] : k2_relat_1(k6_relat_1(A_19)) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_18,plain,(
    ! [A_21,B_22] :
      ( k5_relat_1(k6_relat_1(A_21),B_22) = k7_relat_1(B_22,A_21)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1098,plain,(
    ! [B_79,C_80,A_81] :
      ( k2_relat_1(k5_relat_1(B_79,C_80)) = k2_relat_1(k5_relat_1(A_81,C_80))
      | k2_relat_1(B_79) != k2_relat_1(A_81)
      | ~ v1_relat_1(C_80)
      | ~ v1_relat_1(B_79)
      | ~ v1_relat_1(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1143,plain,(
    ! [B_22,A_21,A_81] :
      ( k2_relat_1(k7_relat_1(B_22,A_21)) = k2_relat_1(k5_relat_1(A_81,B_22))
      | k2_relat_1(k6_relat_1(A_21)) != k2_relat_1(A_81)
      | ~ v1_relat_1(B_22)
      | ~ v1_relat_1(k6_relat_1(A_21))
      | ~ v1_relat_1(A_81)
      | ~ v1_relat_1(B_22) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1098])).

tff(c_1235,plain,(
    ! [B_84,A_85,A_86] :
      ( k2_relat_1(k7_relat_1(B_84,A_85)) = k2_relat_1(k5_relat_1(A_86,B_84))
      | k2_relat_1(A_86) != A_85
      | ~ v1_relat_1(A_86)
      | ~ v1_relat_1(B_84) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_14,c_1143])).

tff(c_26,plain,(
    ! [A_24] :
      ( k1_relat_1(k2_funct_1(A_24)) = k2_relat_1(A_24)
      | ~ v2_funct_1(A_24)
      | ~ v1_funct_1(A_24)
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_485,plain,(
    ! [C_53,B_54,A_55] :
      ( k1_relat_1(k5_relat_1(C_53,B_54)) = k1_relat_1(k5_relat_1(C_53,A_55))
      | k1_relat_1(B_54) != k1_relat_1(A_55)
      | ~ v1_relat_1(C_53)
      | ~ v1_relat_1(B_54)
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_28,plain,
    ( k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1')
    | k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_70,plain,(
    k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_506,plain,(
    ! [B_54] :
      ( k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),B_54)) != k2_relat_1('#skF_1')
      | k1_relat_1(B_54) != k1_relat_1('#skF_1')
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v1_relat_1(B_54)
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_485,c_70])).

tff(c_559,plain,(
    ! [B_54] :
      ( k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),B_54)) != k2_relat_1('#skF_1')
      | k1_relat_1(B_54) != k1_relat_1('#skF_1')
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v1_relat_1(B_54) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_506])).

tff(c_894,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_559])).

tff(c_897,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_894])).

tff(c_901,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_897])).

tff(c_903,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_559])).

tff(c_12,plain,(
    ! [A_19] : k1_relat_1(k6_relat_1(A_19)) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_16,plain,(
    ! [A_20] :
      ( k5_relat_1(A_20,k6_relat_1(k2_relat_1(A_20))) = A_20
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_554,plain,(
    ! [A_20,A_55] :
      ( k1_relat_1(k5_relat_1(A_20,A_55)) = k1_relat_1(A_20)
      | k1_relat_1(k6_relat_1(k2_relat_1(A_20))) != k1_relat_1(A_55)
      | ~ v1_relat_1(A_20)
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(A_20)))
      | ~ v1_relat_1(A_55)
      | ~ v1_relat_1(A_20) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_485])).

tff(c_801,plain,(
    ! [A_64,A_65] :
      ( k1_relat_1(k5_relat_1(A_64,A_65)) = k1_relat_1(A_64)
      | k2_relat_1(A_64) != k1_relat_1(A_65)
      | ~ v1_relat_1(A_65)
      | ~ v1_relat_1(A_64) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_12,c_554])).

tff(c_820,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1')
    | k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_801,c_70])).

tff(c_855,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1')
    | k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_820])).

tff(c_893,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_855])).

tff(c_905,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_903,c_893])).

tff(c_906,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1')
    | k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_855])).

tff(c_908,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_906])).

tff(c_911,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_908])).

tff(c_915,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_911])).

tff(c_916,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_906])).

tff(c_946,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_916])).

tff(c_950,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_946])).

tff(c_951,plain,(
    k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_1263,plain,(
    ! [A_85] :
      ( k2_relat_1(k7_relat_1('#skF_1',A_85)) != k2_relat_1('#skF_1')
      | k2_relat_1(k2_funct_1('#skF_1')) != A_85
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1235,c_951])).

tff(c_1300,plain,(
    ! [A_85] :
      ( k2_relat_1(k7_relat_1('#skF_1',A_85)) != k2_relat_1('#skF_1')
      | k2_relat_1(k2_funct_1('#skF_1')) != A_85
      | ~ v1_relat_1(k2_funct_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1263])).

tff(c_1315,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_1300])).

tff(c_1318,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_1315])).

tff(c_1322,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_1318])).

tff(c_1326,plain,(
    ! [A_87] :
      ( k2_relat_1(k7_relat_1('#skF_1',A_87)) != k2_relat_1('#skF_1')
      | k2_relat_1(k2_funct_1('#skF_1')) != A_87 ) ),
    inference(splitRight,[status(thm)],[c_1300])).

tff(c_1334,plain,(
    ! [A_3] :
      ( k9_relat_1('#skF_1',A_3) != k2_relat_1('#skF_1')
      | k2_relat_1(k2_funct_1('#skF_1')) != A_3
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_1326])).

tff(c_1340,plain,(
    ! [A_88] :
      ( k9_relat_1('#skF_1',A_88) != k2_relat_1('#skF_1')
      | k2_relat_1(k2_funct_1('#skF_1')) != A_88 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1334])).

tff(c_1343,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1340])).

tff(c_1346,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1343])).

tff(c_1349,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1346])).

tff(c_1353,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_1349])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:37:44 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.24/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.24/1.48  
% 3.24/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.24/1.48  %$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1
% 3.24/1.48  
% 3.24/1.48  %Foreground sorts:
% 3.24/1.48  
% 3.24/1.48  
% 3.24/1.48  %Background operators:
% 3.24/1.48  
% 3.24/1.48  
% 3.24/1.48  %Foreground operators:
% 3.24/1.48  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.24/1.48  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.24/1.48  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.24/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.24/1.48  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.24/1.48  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.24/1.48  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.24/1.48  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.24/1.48  tff('#skF_1', type, '#skF_1': $i).
% 3.24/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.24/1.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.24/1.48  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.24/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.24/1.48  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.24/1.48  
% 3.24/1.49  tff(f_100, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)) & (k2_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_funct_1)).
% 3.24/1.49  tff(f_89, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 3.24/1.49  tff(f_31, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 3.24/1.49  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 3.24/1.49  tff(f_79, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 3.24/1.49  tff(f_27, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 3.24/1.49  tff(f_63, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 3.24/1.49  tff(f_71, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 3.24/1.49  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((k2_relat_1(A) = k2_relat_1(B)) => (k2_relat_1(k5_relat_1(A, C)) = k2_relat_1(k5_relat_1(B, C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t199_relat_1)).
% 3.24/1.49  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((k1_relat_1(A) = k1_relat_1(B)) => (k1_relat_1(k5_relat_1(C, A)) = k1_relat_1(k5_relat_1(C, B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t198_relat_1)).
% 3.24/1.49  tff(f_67, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 3.24/1.49  tff(c_34, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.24/1.49  tff(c_32, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.24/1.49  tff(c_30, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.24/1.49  tff(c_24, plain, (![A_24]: (k2_relat_1(k2_funct_1(A_24))=k1_relat_1(A_24) | ~v2_funct_1(A_24) | ~v1_funct_1(A_24) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.24/1.49  tff(c_4, plain, (![A_2]: (k9_relat_1(A_2, k1_relat_1(A_2))=k2_relat_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.24/1.49  tff(c_6, plain, (![B_4, A_3]: (k2_relat_1(k7_relat_1(B_4, A_3))=k9_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.24/1.49  tff(c_22, plain, (![A_23]: (v1_relat_1(k2_funct_1(A_23)) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.24/1.49  tff(c_2, plain, (![A_1]: (v1_relat_1(k6_relat_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.24/1.49  tff(c_14, plain, (![A_19]: (k2_relat_1(k6_relat_1(A_19))=A_19)), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.24/1.49  tff(c_18, plain, (![A_21, B_22]: (k5_relat_1(k6_relat_1(A_21), B_22)=k7_relat_1(B_22, A_21) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.24/1.49  tff(c_1098, plain, (![B_79, C_80, A_81]: (k2_relat_1(k5_relat_1(B_79, C_80))=k2_relat_1(k5_relat_1(A_81, C_80)) | k2_relat_1(B_79)!=k2_relat_1(A_81) | ~v1_relat_1(C_80) | ~v1_relat_1(B_79) | ~v1_relat_1(A_81))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.24/1.49  tff(c_1143, plain, (![B_22, A_21, A_81]: (k2_relat_1(k7_relat_1(B_22, A_21))=k2_relat_1(k5_relat_1(A_81, B_22)) | k2_relat_1(k6_relat_1(A_21))!=k2_relat_1(A_81) | ~v1_relat_1(B_22) | ~v1_relat_1(k6_relat_1(A_21)) | ~v1_relat_1(A_81) | ~v1_relat_1(B_22))), inference(superposition, [status(thm), theory('equality')], [c_18, c_1098])).
% 3.24/1.49  tff(c_1235, plain, (![B_84, A_85, A_86]: (k2_relat_1(k7_relat_1(B_84, A_85))=k2_relat_1(k5_relat_1(A_86, B_84)) | k2_relat_1(A_86)!=A_85 | ~v1_relat_1(A_86) | ~v1_relat_1(B_84))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_14, c_1143])).
% 3.24/1.49  tff(c_26, plain, (![A_24]: (k1_relat_1(k2_funct_1(A_24))=k2_relat_1(A_24) | ~v2_funct_1(A_24) | ~v1_funct_1(A_24) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.24/1.49  tff(c_485, plain, (![C_53, B_54, A_55]: (k1_relat_1(k5_relat_1(C_53, B_54))=k1_relat_1(k5_relat_1(C_53, A_55)) | k1_relat_1(B_54)!=k1_relat_1(A_55) | ~v1_relat_1(C_53) | ~v1_relat_1(B_54) | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.24/1.49  tff(c_28, plain, (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1') | k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.24/1.49  tff(c_70, plain, (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_28])).
% 3.24/1.49  tff(c_506, plain, (![B_54]: (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), B_54))!=k2_relat_1('#skF_1') | k1_relat_1(B_54)!=k1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(B_54) | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_485, c_70])).
% 3.24/1.49  tff(c_559, plain, (![B_54]: (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), B_54))!=k2_relat_1('#skF_1') | k1_relat_1(B_54)!=k1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(B_54))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_506])).
% 3.24/1.49  tff(c_894, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_559])).
% 3.24/1.49  tff(c_897, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_22, c_894])).
% 3.24/1.49  tff(c_901, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_897])).
% 3.24/1.49  tff(c_903, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_559])).
% 3.24/1.49  tff(c_12, plain, (![A_19]: (k1_relat_1(k6_relat_1(A_19))=A_19)), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.24/1.49  tff(c_16, plain, (![A_20]: (k5_relat_1(A_20, k6_relat_1(k2_relat_1(A_20)))=A_20 | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.24/1.49  tff(c_554, plain, (![A_20, A_55]: (k1_relat_1(k5_relat_1(A_20, A_55))=k1_relat_1(A_20) | k1_relat_1(k6_relat_1(k2_relat_1(A_20)))!=k1_relat_1(A_55) | ~v1_relat_1(A_20) | ~v1_relat_1(k6_relat_1(k2_relat_1(A_20))) | ~v1_relat_1(A_55) | ~v1_relat_1(A_20))), inference(superposition, [status(thm), theory('equality')], [c_16, c_485])).
% 3.24/1.49  tff(c_801, plain, (![A_64, A_65]: (k1_relat_1(k5_relat_1(A_64, A_65))=k1_relat_1(A_64) | k2_relat_1(A_64)!=k1_relat_1(A_65) | ~v1_relat_1(A_65) | ~v1_relat_1(A_64))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_12, c_554])).
% 3.24/1.49  tff(c_820, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1') | k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_801, c_70])).
% 3.24/1.49  tff(c_855, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1') | k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_820])).
% 3.24/1.49  tff(c_893, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_855])).
% 3.24/1.49  tff(c_905, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_903, c_893])).
% 3.24/1.49  tff(c_906, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1') | k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_855])).
% 3.24/1.49  tff(c_908, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_906])).
% 3.24/1.49  tff(c_911, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_26, c_908])).
% 3.24/1.49  tff(c_915, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_911])).
% 3.24/1.49  tff(c_916, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_906])).
% 3.24/1.49  tff(c_946, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_24, c_916])).
% 3.24/1.49  tff(c_950, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_946])).
% 3.24/1.49  tff(c_951, plain, (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_28])).
% 3.24/1.49  tff(c_1263, plain, (![A_85]: (k2_relat_1(k7_relat_1('#skF_1', A_85))!=k2_relat_1('#skF_1') | k2_relat_1(k2_funct_1('#skF_1'))!=A_85 | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1235, c_951])).
% 3.24/1.49  tff(c_1300, plain, (![A_85]: (k2_relat_1(k7_relat_1('#skF_1', A_85))!=k2_relat_1('#skF_1') | k2_relat_1(k2_funct_1('#skF_1'))!=A_85 | ~v1_relat_1(k2_funct_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1263])).
% 3.24/1.49  tff(c_1315, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_1300])).
% 3.24/1.49  tff(c_1318, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_22, c_1315])).
% 3.24/1.49  tff(c_1322, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_1318])).
% 3.24/1.49  tff(c_1326, plain, (![A_87]: (k2_relat_1(k7_relat_1('#skF_1', A_87))!=k2_relat_1('#skF_1') | k2_relat_1(k2_funct_1('#skF_1'))!=A_87)), inference(splitRight, [status(thm)], [c_1300])).
% 3.24/1.49  tff(c_1334, plain, (![A_3]: (k9_relat_1('#skF_1', A_3)!=k2_relat_1('#skF_1') | k2_relat_1(k2_funct_1('#skF_1'))!=A_3 | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_6, c_1326])).
% 3.24/1.49  tff(c_1340, plain, (![A_88]: (k9_relat_1('#skF_1', A_88)!=k2_relat_1('#skF_1') | k2_relat_1(k2_funct_1('#skF_1'))!=A_88)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1334])).
% 3.24/1.49  tff(c_1343, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4, c_1340])).
% 3.24/1.49  tff(c_1346, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1343])).
% 3.24/1.49  tff(c_1349, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_24, c_1346])).
% 3.24/1.49  tff(c_1353, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_1349])).
% 3.24/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.24/1.49  
% 3.24/1.49  Inference rules
% 3.24/1.49  ----------------------
% 3.24/1.49  #Ref     : 0
% 3.24/1.49  #Sup     : 298
% 3.24/1.49  #Fact    : 0
% 3.24/1.49  #Define  : 0
% 3.24/1.49  #Split   : 6
% 3.24/1.49  #Chain   : 0
% 3.24/1.49  #Close   : 0
% 3.24/1.49  
% 3.24/1.49  Ordering : KBO
% 3.24/1.49  
% 3.24/1.49  Simplification rules
% 3.24/1.49  ----------------------
% 3.24/1.49  #Subsume      : 12
% 3.24/1.49  #Demod        : 250
% 3.24/1.49  #Tautology    : 105
% 3.24/1.49  #SimpNegUnit  : 0
% 3.24/1.49  #BackRed      : 0
% 3.24/1.49  
% 3.24/1.49  #Partial instantiations: 0
% 3.24/1.49  #Strategies tried      : 1
% 3.24/1.49  
% 3.24/1.49  Timing (in seconds)
% 3.24/1.49  ----------------------
% 3.24/1.50  Preprocessing        : 0.29
% 3.24/1.50  Parsing              : 0.16
% 3.24/1.50  CNF conversion       : 0.02
% 3.24/1.50  Main loop            : 0.44
% 3.24/1.50  Inferencing          : 0.17
% 3.24/1.50  Reduction            : 0.14
% 3.24/1.50  Demodulation         : 0.10
% 3.24/1.50  BG Simplification    : 0.03
% 3.24/1.50  Subsumption          : 0.07
% 3.24/1.50  Abstraction          : 0.03
% 3.24/1.50  MUC search           : 0.00
% 3.24/1.50  Cooper               : 0.00
% 3.24/1.50  Total                : 0.77
% 3.24/1.50  Index Insertion      : 0.00
% 3.24/1.50  Index Deletion       : 0.00
% 3.24/1.50  Index Matching       : 0.00
% 3.24/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
