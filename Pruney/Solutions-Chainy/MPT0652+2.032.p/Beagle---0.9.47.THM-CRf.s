%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:56 EST 2020

% Result     : Theorem 3.19s
% Output     : CNFRefutation 3.19s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 279 expanded)
%              Number of leaves         :   24 (  98 expanded)
%              Depth                    :   16
%              Number of atoms          :  154 ( 799 expanded)
%              Number of equality atoms :   64 ( 349 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k8_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

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

tff(f_93,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v2_funct_1(A)
         => ( k1_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A)
            & k2_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_1)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_68,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( k1_relat_1(A) = k1_relat_1(B)
               => k1_relat_1(k5_relat_1(C,A)) = k1_relat_1(k5_relat_1(C,B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t198_relat_1)).

tff(f_82,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k8_relat_1(k2_relat_1(A),A) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t126_relat_1)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_60,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

tff(c_34,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_6,plain,(
    ! [A_4] :
      ( k9_relat_1(A_4,k1_relat_1(A_4)) = k2_relat_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_32,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_18,plain,(
    ! [A_16] :
      ( v1_relat_1(k2_funct_1(A_16))
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_846,plain,(
    ! [C_71,B_72,A_73] :
      ( k1_relat_1(k5_relat_1(C_71,B_72)) = k1_relat_1(k5_relat_1(C_71,A_73))
      | k1_relat_1(B_72) != k1_relat_1(A_73)
      | ~ v1_relat_1(C_71)
      | ~ v1_relat_1(B_72)
      | ~ v1_relat_1(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_30,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_26,plain,(
    ! [A_18] :
      ( k1_relat_1(k2_funct_1(A_18)) = k2_relat_1(A_18)
      | ~ v2_funct_1(A_18)
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_24,plain,(
    ! [A_18] :
      ( k2_relat_1(k2_funct_1(A_18)) = k1_relat_1(A_18)
      | ~ v2_funct_1(A_18)
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_166,plain,(
    ! [C_35,B_36,A_37] :
      ( k1_relat_1(k5_relat_1(C_35,B_36)) = k1_relat_1(k5_relat_1(C_35,A_37))
      | k1_relat_1(B_36) != k1_relat_1(A_37)
      | ~ v1_relat_1(C_35)
      | ~ v1_relat_1(B_36)
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_28,plain,
    ( k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1')
    | k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_78,plain,(
    k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_187,plain,(
    ! [B_36] :
      ( k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),B_36)) != k2_relat_1('#skF_1')
      | k1_relat_1(B_36) != k1_relat_1('#skF_1')
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v1_relat_1(B_36)
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_78])).

tff(c_210,plain,(
    ! [B_36] :
      ( k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),B_36)) != k2_relat_1('#skF_1')
      | k1_relat_1(B_36) != k1_relat_1('#skF_1')
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v1_relat_1(B_36) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_187])).

tff(c_536,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_210])).

tff(c_539,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_536])).

tff(c_543,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_539])).

tff(c_545,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_210])).

tff(c_4,plain,(
    ! [A_3] :
      ( k8_relat_1(k2_relat_1(A_3),A_3) = A_3
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_20,plain,(
    ! [A_17] : v1_relat_1(k6_relat_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_12,plain,(
    ! [A_15] : k1_relat_1(k6_relat_1(A_15)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( k5_relat_1(B_2,k6_relat_1(A_1)) = k8_relat_1(A_1,B_2)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_609,plain,(
    ! [B_55] :
      ( k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),B_55)) != k2_relat_1('#skF_1')
      | k1_relat_1(B_55) != k1_relat_1('#skF_1')
      | ~ v1_relat_1(B_55) ) ),
    inference(splitRight,[status(thm)],[c_210])).

tff(c_625,plain,(
    ! [A_1] :
      ( k1_relat_1(k8_relat_1(A_1,k2_funct_1('#skF_1'))) != k2_relat_1('#skF_1')
      | k1_relat_1(k6_relat_1(A_1)) != k1_relat_1('#skF_1')
      | ~ v1_relat_1(k6_relat_1(A_1))
      | ~ v1_relat_1(k2_funct_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_609])).

tff(c_635,plain,(
    ! [A_56] :
      ( k1_relat_1(k8_relat_1(A_56,k2_funct_1('#skF_1'))) != k2_relat_1('#skF_1')
      | k1_relat_1('#skF_1') != A_56 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_545,c_20,c_12,c_625])).

tff(c_643,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1')
    | k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_635])).

tff(c_647,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1')
    | k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_545,c_643])).

tff(c_648,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_647])).

tff(c_651,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_648])).

tff(c_655,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_651])).

tff(c_656,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_647])).

tff(c_698,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_656])).

tff(c_702,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_698])).

tff(c_704,plain,(
    k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) = k2_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_867,plain,(
    ! [B_72] :
      ( k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),B_72)) = k2_relat_1('#skF_1')
      | k1_relat_1(B_72) != k1_relat_1('#skF_1')
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v1_relat_1(B_72)
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_846,c_704])).

tff(c_896,plain,(
    ! [B_72] :
      ( k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),B_72)) = k2_relat_1('#skF_1')
      | k1_relat_1(B_72) != k1_relat_1('#skF_1')
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v1_relat_1(B_72) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_867])).

tff(c_995,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_896])).

tff(c_998,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_995])).

tff(c_1002,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_998])).

tff(c_1004,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_896])).

tff(c_1067,plain,(
    ! [B_77] :
      ( k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),B_77)) = k2_relat_1('#skF_1')
      | k1_relat_1(B_77) != k1_relat_1('#skF_1')
      | ~ v1_relat_1(B_77) ) ),
    inference(splitRight,[status(thm)],[c_896])).

tff(c_1097,plain,(
    ! [A_1] :
      ( k1_relat_1(k8_relat_1(A_1,k2_funct_1('#skF_1'))) = k2_relat_1('#skF_1')
      | k1_relat_1(k6_relat_1(A_1)) != k1_relat_1('#skF_1')
      | ~ v1_relat_1(k6_relat_1(A_1))
      | ~ v1_relat_1(k2_funct_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1067])).

tff(c_1122,plain,(
    ! [A_78] :
      ( k1_relat_1(k8_relat_1(A_78,k2_funct_1('#skF_1'))) = k2_relat_1('#skF_1')
      | k1_relat_1('#skF_1') != A_78 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1004,c_20,c_12,c_1097])).

tff(c_1135,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1')
    | k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1122])).

tff(c_1139,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1')
    | k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1004,c_1135])).

tff(c_1208,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1139])).

tff(c_1211,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1208])).

tff(c_1215,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_1211])).

tff(c_1217,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1139])).

tff(c_8,plain,(
    ! [B_7,A_5] :
      ( k9_relat_1(B_7,k2_relat_1(A_5)) = k2_relat_1(k5_relat_1(A_5,B_7))
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1250,plain,(
    ! [B_7] :
      ( k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),B_7)) = k9_relat_1(B_7,k1_relat_1('#skF_1'))
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(k2_funct_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1217,c_8])).

tff(c_1404,plain,(
    ! [B_84] :
      ( k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),B_84)) = k9_relat_1(B_84,k1_relat_1('#skF_1'))
      | ~ v1_relat_1(B_84) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1004,c_1250])).

tff(c_703,plain,(
    k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_1426,plain,
    ( k9_relat_1('#skF_1',k1_relat_1('#skF_1')) != k2_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1404,c_703])).

tff(c_1450,plain,(
    k9_relat_1('#skF_1',k1_relat_1('#skF_1')) != k2_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1426])).

tff(c_1460,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_1450])).

tff(c_1464,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1460])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:57:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.19/1.57  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.19/1.57  
% 3.19/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.19/1.57  %$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k8_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1
% 3.19/1.57  
% 3.19/1.57  %Foreground sorts:
% 3.19/1.57  
% 3.19/1.57  
% 3.19/1.57  %Background operators:
% 3.19/1.57  
% 3.19/1.57  
% 3.19/1.57  %Foreground operators:
% 3.19/1.57  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 3.19/1.57  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.19/1.57  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.19/1.57  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.19/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.19/1.57  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.19/1.57  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.19/1.57  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.19/1.57  tff('#skF_1', type, '#skF_1': $i).
% 3.19/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.19/1.57  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.19/1.57  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.19/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.19/1.57  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.19/1.57  
% 3.19/1.59  tff(f_93, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)) & (k2_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_funct_1)).
% 3.19/1.59  tff(f_37, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 3.19/1.59  tff(f_68, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 3.19/1.59  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((k1_relat_1(A) = k1_relat_1(B)) => (k1_relat_1(k5_relat_1(C, A)) = k1_relat_1(k5_relat_1(C, B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t198_relat_1)).
% 3.19/1.59  tff(f_82, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 3.19/1.59  tff(f_33, axiom, (![A]: (v1_relat_1(A) => (k8_relat_1(k2_relat_1(A), A) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t126_relat_1)).
% 3.19/1.59  tff(f_72, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 3.19/1.59  tff(f_60, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 3.19/1.59  tff(f_29, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 3.19/1.59  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t160_relat_1)).
% 3.19/1.59  tff(c_34, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.19/1.59  tff(c_6, plain, (![A_4]: (k9_relat_1(A_4, k1_relat_1(A_4))=k2_relat_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.19/1.59  tff(c_32, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.19/1.59  tff(c_18, plain, (![A_16]: (v1_relat_1(k2_funct_1(A_16)) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.19/1.59  tff(c_846, plain, (![C_71, B_72, A_73]: (k1_relat_1(k5_relat_1(C_71, B_72))=k1_relat_1(k5_relat_1(C_71, A_73)) | k1_relat_1(B_72)!=k1_relat_1(A_73) | ~v1_relat_1(C_71) | ~v1_relat_1(B_72) | ~v1_relat_1(A_73))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.19/1.59  tff(c_30, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.19/1.59  tff(c_26, plain, (![A_18]: (k1_relat_1(k2_funct_1(A_18))=k2_relat_1(A_18) | ~v2_funct_1(A_18) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.19/1.59  tff(c_24, plain, (![A_18]: (k2_relat_1(k2_funct_1(A_18))=k1_relat_1(A_18) | ~v2_funct_1(A_18) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.19/1.59  tff(c_166, plain, (![C_35, B_36, A_37]: (k1_relat_1(k5_relat_1(C_35, B_36))=k1_relat_1(k5_relat_1(C_35, A_37)) | k1_relat_1(B_36)!=k1_relat_1(A_37) | ~v1_relat_1(C_35) | ~v1_relat_1(B_36) | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.19/1.59  tff(c_28, plain, (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1') | k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.19/1.59  tff(c_78, plain, (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_28])).
% 3.19/1.59  tff(c_187, plain, (![B_36]: (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), B_36))!=k2_relat_1('#skF_1') | k1_relat_1(B_36)!=k1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(B_36) | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_166, c_78])).
% 3.19/1.59  tff(c_210, plain, (![B_36]: (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), B_36))!=k2_relat_1('#skF_1') | k1_relat_1(B_36)!=k1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(B_36))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_187])).
% 3.19/1.59  tff(c_536, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_210])).
% 3.19/1.59  tff(c_539, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_18, c_536])).
% 3.19/1.59  tff(c_543, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_539])).
% 3.19/1.59  tff(c_545, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_210])).
% 3.19/1.59  tff(c_4, plain, (![A_3]: (k8_relat_1(k2_relat_1(A_3), A_3)=A_3 | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.19/1.59  tff(c_20, plain, (![A_17]: (v1_relat_1(k6_relat_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.19/1.59  tff(c_12, plain, (![A_15]: (k1_relat_1(k6_relat_1(A_15))=A_15)), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.19/1.59  tff(c_2, plain, (![B_2, A_1]: (k5_relat_1(B_2, k6_relat_1(A_1))=k8_relat_1(A_1, B_2) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.19/1.59  tff(c_609, plain, (![B_55]: (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), B_55))!=k2_relat_1('#skF_1') | k1_relat_1(B_55)!=k1_relat_1('#skF_1') | ~v1_relat_1(B_55))), inference(splitRight, [status(thm)], [c_210])).
% 3.19/1.59  tff(c_625, plain, (![A_1]: (k1_relat_1(k8_relat_1(A_1, k2_funct_1('#skF_1')))!=k2_relat_1('#skF_1') | k1_relat_1(k6_relat_1(A_1))!=k1_relat_1('#skF_1') | ~v1_relat_1(k6_relat_1(A_1)) | ~v1_relat_1(k2_funct_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_2, c_609])).
% 3.19/1.59  tff(c_635, plain, (![A_56]: (k1_relat_1(k8_relat_1(A_56, k2_funct_1('#skF_1')))!=k2_relat_1('#skF_1') | k1_relat_1('#skF_1')!=A_56)), inference(demodulation, [status(thm), theory('equality')], [c_545, c_20, c_12, c_625])).
% 3.19/1.59  tff(c_643, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1') | k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_4, c_635])).
% 3.19/1.59  tff(c_647, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1') | k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_545, c_643])).
% 3.19/1.59  tff(c_648, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_647])).
% 3.19/1.59  tff(c_651, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_24, c_648])).
% 3.19/1.59  tff(c_655, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_651])).
% 3.19/1.59  tff(c_656, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_647])).
% 3.19/1.59  tff(c_698, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_26, c_656])).
% 3.19/1.59  tff(c_702, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_698])).
% 3.19/1.59  tff(c_704, plain, (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))=k2_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_28])).
% 3.19/1.59  tff(c_867, plain, (![B_72]: (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), B_72))=k2_relat_1('#skF_1') | k1_relat_1(B_72)!=k1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(B_72) | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_846, c_704])).
% 3.19/1.59  tff(c_896, plain, (![B_72]: (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), B_72))=k2_relat_1('#skF_1') | k1_relat_1(B_72)!=k1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(B_72))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_867])).
% 3.19/1.59  tff(c_995, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_896])).
% 3.19/1.59  tff(c_998, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_18, c_995])).
% 3.19/1.59  tff(c_1002, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_998])).
% 3.19/1.59  tff(c_1004, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_896])).
% 3.19/1.59  tff(c_1067, plain, (![B_77]: (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), B_77))=k2_relat_1('#skF_1') | k1_relat_1(B_77)!=k1_relat_1('#skF_1') | ~v1_relat_1(B_77))), inference(splitRight, [status(thm)], [c_896])).
% 3.19/1.59  tff(c_1097, plain, (![A_1]: (k1_relat_1(k8_relat_1(A_1, k2_funct_1('#skF_1')))=k2_relat_1('#skF_1') | k1_relat_1(k6_relat_1(A_1))!=k1_relat_1('#skF_1') | ~v1_relat_1(k6_relat_1(A_1)) | ~v1_relat_1(k2_funct_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1067])).
% 3.19/1.59  tff(c_1122, plain, (![A_78]: (k1_relat_1(k8_relat_1(A_78, k2_funct_1('#skF_1')))=k2_relat_1('#skF_1') | k1_relat_1('#skF_1')!=A_78)), inference(demodulation, [status(thm), theory('equality')], [c_1004, c_20, c_12, c_1097])).
% 3.19/1.59  tff(c_1135, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1') | k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_4, c_1122])).
% 3.19/1.59  tff(c_1139, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1') | k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1004, c_1135])).
% 3.19/1.59  tff(c_1208, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_1139])).
% 3.19/1.59  tff(c_1211, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_24, c_1208])).
% 3.19/1.59  tff(c_1215, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_1211])).
% 3.19/1.59  tff(c_1217, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_1139])).
% 3.19/1.59  tff(c_8, plain, (![B_7, A_5]: (k9_relat_1(B_7, k2_relat_1(A_5))=k2_relat_1(k5_relat_1(A_5, B_7)) | ~v1_relat_1(B_7) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.19/1.59  tff(c_1250, plain, (![B_7]: (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), B_7))=k9_relat_1(B_7, k1_relat_1('#skF_1')) | ~v1_relat_1(B_7) | ~v1_relat_1(k2_funct_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_1217, c_8])).
% 3.19/1.59  tff(c_1404, plain, (![B_84]: (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), B_84))=k9_relat_1(B_84, k1_relat_1('#skF_1')) | ~v1_relat_1(B_84))), inference(demodulation, [status(thm), theory('equality')], [c_1004, c_1250])).
% 3.19/1.59  tff(c_703, plain, (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_28])).
% 3.19/1.59  tff(c_1426, plain, (k9_relat_1('#skF_1', k1_relat_1('#skF_1'))!=k2_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1404, c_703])).
% 3.19/1.59  tff(c_1450, plain, (k9_relat_1('#skF_1', k1_relat_1('#skF_1'))!=k2_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1426])).
% 3.19/1.59  tff(c_1460, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_6, c_1450])).
% 3.19/1.59  tff(c_1464, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_1460])).
% 3.19/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.19/1.59  
% 3.19/1.59  Inference rules
% 3.19/1.59  ----------------------
% 3.19/1.59  #Ref     : 1
% 3.19/1.59  #Sup     : 329
% 3.19/1.59  #Fact    : 0
% 3.19/1.59  #Define  : 0
% 3.19/1.59  #Split   : 6
% 3.19/1.59  #Chain   : 0
% 3.19/1.59  #Close   : 0
% 3.19/1.59  
% 3.19/1.59  Ordering : KBO
% 3.19/1.59  
% 3.19/1.59  Simplification rules
% 3.19/1.59  ----------------------
% 3.19/1.59  #Subsume      : 8
% 3.19/1.59  #Demod        : 268
% 3.19/1.59  #Tautology    : 125
% 3.19/1.59  #SimpNegUnit  : 0
% 3.19/1.59  #BackRed      : 0
% 3.19/1.59  
% 3.19/1.59  #Partial instantiations: 0
% 3.19/1.59  #Strategies tried      : 1
% 3.19/1.59  
% 3.19/1.59  Timing (in seconds)
% 3.19/1.59  ----------------------
% 3.19/1.59  Preprocessing        : 0.33
% 3.19/1.59  Parsing              : 0.17
% 3.19/1.59  CNF conversion       : 0.02
% 3.19/1.59  Main loop            : 0.44
% 3.19/1.59  Inferencing          : 0.17
% 3.19/1.59  Reduction            : 0.14
% 3.19/1.59  Demodulation         : 0.11
% 3.19/1.59  BG Simplification    : 0.03
% 3.19/1.59  Subsumption          : 0.07
% 3.19/1.59  Abstraction          : 0.03
% 3.19/1.59  MUC search           : 0.00
% 3.19/1.59  Cooper               : 0.00
% 3.19/1.59  Total                : 0.80
% 3.19/1.59  Index Insertion      : 0.00
% 3.19/1.59  Index Deletion       : 0.00
% 3.19/1.59  Index Matching       : 0.00
% 3.19/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
