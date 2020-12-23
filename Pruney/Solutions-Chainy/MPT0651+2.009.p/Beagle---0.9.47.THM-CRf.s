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
% DateTime   : Thu Dec  3 10:03:49 EST 2020

% Result     : Theorem 3.20s
% Output     : CNFRefutation 3.28s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 168 expanded)
%              Number of leaves         :   27 (  67 expanded)
%              Depth                    :   14
%              Number of atoms          :  165 ( 473 expanded)
%              Number of equality atoms :   63 ( 188 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_110,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v2_funct_1(A)
         => ( k1_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A)
            & k2_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).

tff(f_99,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_85,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( k1_relat_1(A) = k1_relat_1(B)
               => k1_relat_1(k5_relat_1(C,A)) = k1_relat_1(k5_relat_1(C,B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t198_relat_1)).

tff(f_89,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_67,axiom,(
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

tff(f_73,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( k2_relat_1(A) = k2_relat_1(B)
               => k2_relat_1(k5_relat_1(A,C)) = k2_relat_1(k5_relat_1(B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t199_relat_1)).

tff(c_42,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_40,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_38,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_32,plain,(
    ! [A_27] :
      ( k2_relat_1(k2_funct_1(A_27)) = k1_relat_1(A_27)
      | ~ v2_funct_1(A_27)
      | ~ v1_funct_1(A_27)
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_26,plain,(
    ! [A_25] :
      ( v1_relat_1(k2_funct_1(A_25))
      | ~ v1_funct_1(A_25)
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_978,plain,(
    ! [C_94,B_95,A_96] :
      ( k1_relat_1(k5_relat_1(C_94,B_95)) = k1_relat_1(k5_relat_1(C_94,A_96))
      | k1_relat_1(B_95) != k1_relat_1(A_96)
      | ~ v1_relat_1(C_94)
      | ~ v1_relat_1(B_95)
      | ~ v1_relat_1(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_34,plain,(
    ! [A_27] :
      ( k1_relat_1(k2_funct_1(A_27)) = k2_relat_1(A_27)
      | ~ v2_funct_1(A_27)
      | ~ v1_funct_1(A_27)
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_28,plain,(
    ! [A_26] : v1_relat_1(k6_relat_1(A_26)) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_16,plain,(
    ! [A_20] : k1_relat_1(k6_relat_1(A_20)) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_137,plain,(
    ! [B_45,A_46] :
      ( k5_relat_1(B_45,k6_relat_1(A_46)) = B_45
      | ~ r1_tarski(k2_relat_1(B_45),A_46)
      | ~ v1_relat_1(B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_153,plain,(
    ! [B_45] :
      ( k5_relat_1(B_45,k6_relat_1(k2_relat_1(B_45))) = B_45
      | ~ v1_relat_1(B_45) ) ),
    inference(resolution,[status(thm)],[c_6,c_137])).

tff(c_268,plain,(
    ! [C_52,B_53,A_54] :
      ( k1_relat_1(k5_relat_1(C_52,B_53)) = k1_relat_1(k5_relat_1(C_52,A_54))
      | k1_relat_1(B_53) != k1_relat_1(A_54)
      | ~ v1_relat_1(C_52)
      | ~ v1_relat_1(B_53)
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_36,plain,
    ( k2_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1')
    | k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_66,plain,(
    k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_292,plain,(
    ! [A_54] :
      ( k1_relat_1(k5_relat_1('#skF_1',A_54)) != k1_relat_1('#skF_1')
      | k1_relat_1(k2_funct_1('#skF_1')) != k1_relat_1(A_54)
      | ~ v1_relat_1('#skF_1')
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v1_relat_1(A_54) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_268,c_66])).

tff(c_332,plain,(
    ! [A_54] :
      ( k1_relat_1(k5_relat_1('#skF_1',A_54)) != k1_relat_1('#skF_1')
      | k1_relat_1(k2_funct_1('#skF_1')) != k1_relat_1(A_54)
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v1_relat_1(A_54) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_292])).

tff(c_410,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_332])).

tff(c_413,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_410])).

tff(c_417,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_413])).

tff(c_641,plain,(
    ! [A_68] :
      ( k1_relat_1(k5_relat_1('#skF_1',A_68)) != k1_relat_1('#skF_1')
      | k1_relat_1(k2_funct_1('#skF_1')) != k1_relat_1(A_68)
      | ~ v1_relat_1(A_68) ) ),
    inference(splitRight,[status(thm)],[c_332])).

tff(c_653,plain,
    ( k1_relat_1(k6_relat_1(k2_relat_1('#skF_1'))) != k1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k6_relat_1(k2_relat_1('#skF_1')))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_641])).

tff(c_660,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_28,c_16,c_653])).

tff(c_665,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_660])).

tff(c_669,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_665])).

tff(c_671,plain,(
    k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k1_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_999,plain,(
    ! [B_95] :
      ( k1_relat_1(k5_relat_1('#skF_1',B_95)) = k1_relat_1('#skF_1')
      | k1_relat_1(k2_funct_1('#skF_1')) != k1_relat_1(B_95)
      | ~ v1_relat_1('#skF_1')
      | ~ v1_relat_1(B_95)
      | ~ v1_relat_1(k2_funct_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_978,c_671])).

tff(c_1046,plain,(
    ! [B_95] :
      ( k1_relat_1(k5_relat_1('#skF_1',B_95)) = k1_relat_1('#skF_1')
      | k1_relat_1(k2_funct_1('#skF_1')) != k1_relat_1(B_95)
      | ~ v1_relat_1(B_95)
      | ~ v1_relat_1(k2_funct_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_999])).

tff(c_1150,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_1046])).

tff(c_1153,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_1150])).

tff(c_1157,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_1153])).

tff(c_1159,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_1046])).

tff(c_896,plain,(
    ! [A_88] :
      ( k1_relat_1(k2_funct_1(A_88)) = k2_relat_1(A_88)
      | ~ v2_funct_1(A_88)
      | ~ v1_funct_1(A_88)
      | ~ v1_relat_1(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_8,plain,(
    ! [A_3] :
      ( k9_relat_1(A_3,k1_relat_1(A_3)) = k2_relat_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_902,plain,(
    ! [A_88] :
      ( k9_relat_1(k2_funct_1(A_88),k2_relat_1(A_88)) = k2_relat_1(k2_funct_1(A_88))
      | ~ v1_relat_1(k2_funct_1(A_88))
      | ~ v2_funct_1(A_88)
      | ~ v1_funct_1(A_88)
      | ~ v1_relat_1(A_88) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_896,c_8])).

tff(c_10,plain,(
    ! [B_5,A_4] :
      ( k2_relat_1(k7_relat_1(B_5,A_4)) = k9_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_18,plain,(
    ! [A_20] : k2_relat_1(k6_relat_1(A_20)) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_22,plain,(
    ! [A_23,B_24] :
      ( k5_relat_1(k6_relat_1(A_23),B_24) = k7_relat_1(B_24,A_23)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1314,plain,(
    ! [B_107,C_108,A_109] :
      ( k2_relat_1(k5_relat_1(B_107,C_108)) = k2_relat_1(k5_relat_1(A_109,C_108))
      | k2_relat_1(B_107) != k2_relat_1(A_109)
      | ~ v1_relat_1(C_108)
      | ~ v1_relat_1(B_107)
      | ~ v1_relat_1(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_670,plain,(
    k2_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_1347,plain,(
    ! [B_107] :
      ( k2_relat_1(k5_relat_1(B_107,k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1')
      | k2_relat_1(B_107) != k2_relat_1('#skF_1')
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v1_relat_1(B_107)
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1314,c_670])).

tff(c_1514,plain,(
    ! [B_114] :
      ( k2_relat_1(k5_relat_1(B_114,k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1')
      | k2_relat_1(B_114) != k2_relat_1('#skF_1')
      | ~ v1_relat_1(B_114) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1159,c_1347])).

tff(c_1526,plain,(
    ! [A_23] :
      ( k2_relat_1(k7_relat_1(k2_funct_1('#skF_1'),A_23)) != k1_relat_1('#skF_1')
      | k2_relat_1(k6_relat_1(A_23)) != k2_relat_1('#skF_1')
      | ~ v1_relat_1(k6_relat_1(A_23))
      | ~ v1_relat_1(k2_funct_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1514])).

tff(c_1534,plain,(
    ! [A_115] :
      ( k2_relat_1(k7_relat_1(k2_funct_1('#skF_1'),A_115)) != k1_relat_1('#skF_1')
      | k2_relat_1('#skF_1') != A_115 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1159,c_28,c_18,c_1526])).

tff(c_1538,plain,(
    ! [A_4] :
      ( k9_relat_1(k2_funct_1('#skF_1'),A_4) != k1_relat_1('#skF_1')
      | k2_relat_1('#skF_1') != A_4
      | ~ v1_relat_1(k2_funct_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1534])).

tff(c_1542,plain,(
    ! [A_116] :
      ( k9_relat_1(k2_funct_1('#skF_1'),A_116) != k1_relat_1('#skF_1')
      | k2_relat_1('#skF_1') != A_116 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1159,c_1538])).

tff(c_1546,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_902,c_1542])).

tff(c_1553,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_1159,c_1546])).

tff(c_1558,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_1553])).

tff(c_1562,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_1558])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:52:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.20/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.48  
% 3.20/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.28/1.48  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1
% 3.28/1.48  
% 3.28/1.48  %Foreground sorts:
% 3.28/1.48  
% 3.28/1.48  
% 3.28/1.48  %Background operators:
% 3.28/1.48  
% 3.28/1.48  
% 3.28/1.48  %Foreground operators:
% 3.28/1.48  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.28/1.48  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.28/1.48  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.28/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.28/1.48  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.28/1.48  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.28/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.28/1.48  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.28/1.48  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.28/1.48  tff('#skF_1', type, '#skF_1': $i).
% 3.28/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.28/1.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.28/1.48  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.28/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.28/1.48  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.28/1.48  
% 3.28/1.50  tff(f_110, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)) & (k2_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_funct_1)).
% 3.28/1.50  tff(f_99, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 3.28/1.50  tff(f_85, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 3.28/1.50  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((k1_relat_1(A) = k1_relat_1(B)) => (k1_relat_1(k5_relat_1(C, A)) = k1_relat_1(k5_relat_1(C, B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t198_relat_1)).
% 3.28/1.50  tff(f_89, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 3.28/1.50  tff(f_67, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 3.28/1.50  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.28/1.50  tff(f_73, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 3.28/1.50  tff(f_35, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 3.28/1.50  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 3.28/1.50  tff(f_77, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 3.28/1.50  tff(f_63, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((k2_relat_1(A) = k2_relat_1(B)) => (k2_relat_1(k5_relat_1(A, C)) = k2_relat_1(k5_relat_1(B, C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t199_relat_1)).
% 3.28/1.50  tff(c_42, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.28/1.50  tff(c_40, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.28/1.50  tff(c_38, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.28/1.50  tff(c_32, plain, (![A_27]: (k2_relat_1(k2_funct_1(A_27))=k1_relat_1(A_27) | ~v2_funct_1(A_27) | ~v1_funct_1(A_27) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.28/1.50  tff(c_26, plain, (![A_25]: (v1_relat_1(k2_funct_1(A_25)) | ~v1_funct_1(A_25) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.28/1.50  tff(c_978, plain, (![C_94, B_95, A_96]: (k1_relat_1(k5_relat_1(C_94, B_95))=k1_relat_1(k5_relat_1(C_94, A_96)) | k1_relat_1(B_95)!=k1_relat_1(A_96) | ~v1_relat_1(C_94) | ~v1_relat_1(B_95) | ~v1_relat_1(A_96))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.28/1.50  tff(c_34, plain, (![A_27]: (k1_relat_1(k2_funct_1(A_27))=k2_relat_1(A_27) | ~v2_funct_1(A_27) | ~v1_funct_1(A_27) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.28/1.50  tff(c_28, plain, (![A_26]: (v1_relat_1(k6_relat_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.28/1.50  tff(c_16, plain, (![A_20]: (k1_relat_1(k6_relat_1(A_20))=A_20)), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.28/1.50  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.28/1.50  tff(c_137, plain, (![B_45, A_46]: (k5_relat_1(B_45, k6_relat_1(A_46))=B_45 | ~r1_tarski(k2_relat_1(B_45), A_46) | ~v1_relat_1(B_45))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.28/1.50  tff(c_153, plain, (![B_45]: (k5_relat_1(B_45, k6_relat_1(k2_relat_1(B_45)))=B_45 | ~v1_relat_1(B_45))), inference(resolution, [status(thm)], [c_6, c_137])).
% 3.28/1.50  tff(c_268, plain, (![C_52, B_53, A_54]: (k1_relat_1(k5_relat_1(C_52, B_53))=k1_relat_1(k5_relat_1(C_52, A_54)) | k1_relat_1(B_53)!=k1_relat_1(A_54) | ~v1_relat_1(C_52) | ~v1_relat_1(B_53) | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.28/1.50  tff(c_36, plain, (k2_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1') | k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.28/1.50  tff(c_66, plain, (k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_36])).
% 3.28/1.50  tff(c_292, plain, (![A_54]: (k1_relat_1(k5_relat_1('#skF_1', A_54))!=k1_relat_1('#skF_1') | k1_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1(A_54) | ~v1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(A_54))), inference(superposition, [status(thm), theory('equality')], [c_268, c_66])).
% 3.28/1.50  tff(c_332, plain, (![A_54]: (k1_relat_1(k5_relat_1('#skF_1', A_54))!=k1_relat_1('#skF_1') | k1_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1(A_54) | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(A_54))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_292])).
% 3.28/1.50  tff(c_410, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_332])).
% 3.28/1.50  tff(c_413, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_26, c_410])).
% 3.28/1.50  tff(c_417, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_413])).
% 3.28/1.50  tff(c_641, plain, (![A_68]: (k1_relat_1(k5_relat_1('#skF_1', A_68))!=k1_relat_1('#skF_1') | k1_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1(A_68) | ~v1_relat_1(A_68))), inference(splitRight, [status(thm)], [c_332])).
% 3.28/1.50  tff(c_653, plain, (k1_relat_1(k6_relat_1(k2_relat_1('#skF_1')))!=k1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k6_relat_1(k2_relat_1('#skF_1'))) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_153, c_641])).
% 3.28/1.50  tff(c_660, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_28, c_16, c_653])).
% 3.28/1.50  tff(c_665, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_34, c_660])).
% 3.28/1.50  tff(c_669, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_665])).
% 3.28/1.50  tff(c_671, plain, (k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k1_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_36])).
% 3.28/1.50  tff(c_999, plain, (![B_95]: (k1_relat_1(k5_relat_1('#skF_1', B_95))=k1_relat_1('#skF_1') | k1_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1(B_95) | ~v1_relat_1('#skF_1') | ~v1_relat_1(B_95) | ~v1_relat_1(k2_funct_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_978, c_671])).
% 3.28/1.50  tff(c_1046, plain, (![B_95]: (k1_relat_1(k5_relat_1('#skF_1', B_95))=k1_relat_1('#skF_1') | k1_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1(B_95) | ~v1_relat_1(B_95) | ~v1_relat_1(k2_funct_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_999])).
% 3.28/1.50  tff(c_1150, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_1046])).
% 3.28/1.50  tff(c_1153, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_26, c_1150])).
% 3.28/1.50  tff(c_1157, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_1153])).
% 3.28/1.50  tff(c_1159, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_1046])).
% 3.28/1.50  tff(c_896, plain, (![A_88]: (k1_relat_1(k2_funct_1(A_88))=k2_relat_1(A_88) | ~v2_funct_1(A_88) | ~v1_funct_1(A_88) | ~v1_relat_1(A_88))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.28/1.50  tff(c_8, plain, (![A_3]: (k9_relat_1(A_3, k1_relat_1(A_3))=k2_relat_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.28/1.50  tff(c_902, plain, (![A_88]: (k9_relat_1(k2_funct_1(A_88), k2_relat_1(A_88))=k2_relat_1(k2_funct_1(A_88)) | ~v1_relat_1(k2_funct_1(A_88)) | ~v2_funct_1(A_88) | ~v1_funct_1(A_88) | ~v1_relat_1(A_88))), inference(superposition, [status(thm), theory('equality')], [c_896, c_8])).
% 3.28/1.50  tff(c_10, plain, (![B_5, A_4]: (k2_relat_1(k7_relat_1(B_5, A_4))=k9_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.28/1.50  tff(c_18, plain, (![A_20]: (k2_relat_1(k6_relat_1(A_20))=A_20)), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.28/1.50  tff(c_22, plain, (![A_23, B_24]: (k5_relat_1(k6_relat_1(A_23), B_24)=k7_relat_1(B_24, A_23) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.28/1.50  tff(c_1314, plain, (![B_107, C_108, A_109]: (k2_relat_1(k5_relat_1(B_107, C_108))=k2_relat_1(k5_relat_1(A_109, C_108)) | k2_relat_1(B_107)!=k2_relat_1(A_109) | ~v1_relat_1(C_108) | ~v1_relat_1(B_107) | ~v1_relat_1(A_109))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.28/1.50  tff(c_670, plain, (k2_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_36])).
% 3.28/1.50  tff(c_1347, plain, (![B_107]: (k2_relat_1(k5_relat_1(B_107, k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1') | k2_relat_1(B_107)!=k2_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(B_107) | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1314, c_670])).
% 3.28/1.50  tff(c_1514, plain, (![B_114]: (k2_relat_1(k5_relat_1(B_114, k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1') | k2_relat_1(B_114)!=k2_relat_1('#skF_1') | ~v1_relat_1(B_114))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1159, c_1347])).
% 3.28/1.50  tff(c_1526, plain, (![A_23]: (k2_relat_1(k7_relat_1(k2_funct_1('#skF_1'), A_23))!=k1_relat_1('#skF_1') | k2_relat_1(k6_relat_1(A_23))!=k2_relat_1('#skF_1') | ~v1_relat_1(k6_relat_1(A_23)) | ~v1_relat_1(k2_funct_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_22, c_1514])).
% 3.28/1.50  tff(c_1534, plain, (![A_115]: (k2_relat_1(k7_relat_1(k2_funct_1('#skF_1'), A_115))!=k1_relat_1('#skF_1') | k2_relat_1('#skF_1')!=A_115)), inference(demodulation, [status(thm), theory('equality')], [c_1159, c_28, c_18, c_1526])).
% 3.28/1.50  tff(c_1538, plain, (![A_4]: (k9_relat_1(k2_funct_1('#skF_1'), A_4)!=k1_relat_1('#skF_1') | k2_relat_1('#skF_1')!=A_4 | ~v1_relat_1(k2_funct_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_10, c_1534])).
% 3.28/1.50  tff(c_1542, plain, (![A_116]: (k9_relat_1(k2_funct_1('#skF_1'), A_116)!=k1_relat_1('#skF_1') | k2_relat_1('#skF_1')!=A_116)), inference(demodulation, [status(thm), theory('equality')], [c_1159, c_1538])).
% 3.28/1.50  tff(c_1546, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_902, c_1542])).
% 3.28/1.50  tff(c_1553, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_1159, c_1546])).
% 3.28/1.50  tff(c_1558, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_32, c_1553])).
% 3.28/1.50  tff(c_1562, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_1558])).
% 3.28/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.28/1.50  
% 3.28/1.50  Inference rules
% 3.28/1.50  ----------------------
% 3.28/1.50  #Ref     : 1
% 3.28/1.50  #Sup     : 315
% 3.28/1.50  #Fact    : 0
% 3.28/1.50  #Define  : 0
% 3.28/1.50  #Split   : 4
% 3.28/1.50  #Chain   : 0
% 3.28/1.50  #Close   : 0
% 3.28/1.50  
% 3.28/1.50  Ordering : KBO
% 3.28/1.50  
% 3.28/1.50  Simplification rules
% 3.28/1.50  ----------------------
% 3.28/1.50  #Subsume      : 13
% 3.28/1.50  #Demod        : 352
% 3.28/1.50  #Tautology    : 137
% 3.28/1.50  #SimpNegUnit  : 0
% 3.28/1.50  #BackRed      : 0
% 3.28/1.50  
% 3.28/1.50  #Partial instantiations: 0
% 3.28/1.50  #Strategies tried      : 1
% 3.28/1.50  
% 3.28/1.50  Timing (in seconds)
% 3.28/1.50  ----------------------
% 3.28/1.50  Preprocessing        : 0.29
% 3.28/1.50  Parsing              : 0.16
% 3.28/1.50  CNF conversion       : 0.02
% 3.28/1.50  Main loop            : 0.45
% 3.28/1.50  Inferencing          : 0.17
% 3.28/1.50  Reduction            : 0.14
% 3.28/1.50  Demodulation         : 0.10
% 3.28/1.50  BG Simplification    : 0.03
% 3.28/1.50  Subsumption          : 0.07
% 3.28/1.50  Abstraction          : 0.03
% 3.28/1.50  MUC search           : 0.00
% 3.28/1.50  Cooper               : 0.00
% 3.28/1.50  Total                : 0.77
% 3.28/1.50  Index Insertion      : 0.00
% 3.28/1.50  Index Deletion       : 0.00
% 3.28/1.50  Index Matching       : 0.00
% 3.28/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
