%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:01 EST 2020

% Result     : Theorem 4.94s
% Output     : CNFRefutation 5.36s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 334 expanded)
%              Number of leaves         :   30 ( 136 expanded)
%              Depth                    :   15
%              Number of atoms          :  187 ( 834 expanded)
%              Number of equality atoms :   60 ( 243 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(f_129,negated_conjecture,(
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

tff(f_67,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_59,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_111,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_101,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( B = k6_relat_1(A)
      <=> ( k1_relat_1(B) = A
          & ! [C] :
              ( r2_hidden(C,A)
             => k1_funct_1(B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).

tff(f_88,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( k1_relat_1(k5_relat_1(B,A)) = k1_relat_1(B)
           => r1_tarski(k2_relat_1(B),k1_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_funct_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

tff(c_40,plain,(
    k2_funct_1('#skF_2') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_50,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_54,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_52,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_16,plain,(
    ! [A_13] :
      ( v1_relat_1(k2_funct_1(A_13))
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_42,plain,(
    k6_relat_1(k1_relat_1('#skF_2')) = k5_relat_1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_46,plain,(
    v2_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_150,plain,(
    ! [A_37] :
      ( k4_relat_1(A_37) = k2_funct_1(A_37)
      | ~ v2_funct_1(A_37)
      | ~ v1_funct_1(A_37)
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_159,plain,
    ( k4_relat_1('#skF_2') = k2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_150])).

tff(c_168,plain,(
    k4_relat_1('#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_159])).

tff(c_2,plain,(
    ! [A_1] :
      ( k2_relat_1(k4_relat_1(A_1)) = k1_relat_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_172,plain,
    ( k2_relat_1(k2_funct_1('#skF_2')) = k1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_2])).

tff(c_179,plain,(
    k2_relat_1(k2_funct_1('#skF_2')) = k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_172])).

tff(c_10,plain,(
    ! [A_11] :
      ( k5_relat_1(A_11,k6_relat_1(k2_relat_1(A_11))) = A_11
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_200,plain,
    ( k5_relat_1(k2_funct_1('#skF_2'),k6_relat_1(k1_relat_1('#skF_2'))) = k2_funct_1('#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_10])).

tff(c_203,plain,
    ( k5_relat_1(k2_funct_1('#skF_2'),k5_relat_1('#skF_2','#skF_3')) = k2_funct_1('#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_200])).

tff(c_365,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_203])).

tff(c_368,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_365])).

tff(c_372,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_368])).

tff(c_373,plain,(
    k5_relat_1(k2_funct_1('#skF_2'),k5_relat_1('#skF_2','#skF_3')) = k2_funct_1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_203])).

tff(c_374,plain,(
    v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_203])).

tff(c_44,plain,(
    k2_relat_1('#skF_2') = k1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_36,plain,(
    ! [A_24] :
      ( k5_relat_1(k2_funct_1(A_24),A_24) = k6_relat_1(k2_relat_1(A_24))
      | ~ v2_funct_1(A_24)
      | ~ v1_funct_1(A_24)
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1752,plain,(
    ! [A_92,B_93,C_94] :
      ( k5_relat_1(k5_relat_1(A_92,B_93),C_94) = k5_relat_1(A_92,k5_relat_1(B_93,C_94))
      | ~ v1_relat_1(C_94)
      | ~ v1_relat_1(B_93)
      | ~ v1_relat_1(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_3846,plain,(
    ! [A_131,C_132] :
      ( k5_relat_1(k6_relat_1(k2_relat_1(A_131)),C_132) = k5_relat_1(k2_funct_1(A_131),k5_relat_1(A_131,C_132))
      | ~ v1_relat_1(C_132)
      | ~ v1_relat_1(A_131)
      | ~ v1_relat_1(k2_funct_1(A_131))
      | ~ v2_funct_1(A_131)
      | ~ v1_funct_1(A_131)
      | ~ v1_relat_1(A_131) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_1752])).

tff(c_4045,plain,(
    ! [C_132] :
      ( k5_relat_1(k6_relat_1(k1_relat_1('#skF_3')),C_132) = k5_relat_1(k2_funct_1('#skF_2'),k5_relat_1('#skF_2',C_132))
      | ~ v1_relat_1(C_132)
      | ~ v1_relat_1('#skF_2')
      | ~ v1_relat_1(k2_funct_1('#skF_2'))
      | ~ v2_funct_1('#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_3846])).

tff(c_4138,plain,(
    ! [C_133] :
      ( k5_relat_1(k6_relat_1(k1_relat_1('#skF_3')),C_133) = k5_relat_1(k2_funct_1('#skF_2'),k5_relat_1('#skF_2',C_133))
      | ~ v1_relat_1(C_133) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_46,c_374,c_54,c_4045])).

tff(c_22,plain,(
    ! [A_15] : v1_relat_1(k6_relat_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_20,plain,(
    ! [A_14] : v1_funct_1(k6_relat_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_24,plain,(
    ! [A_15] : v2_funct_1(k6_relat_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_156,plain,(
    ! [A_15] :
      ( k4_relat_1(k6_relat_1(A_15)) = k2_funct_1(k6_relat_1(A_15))
      | ~ v1_funct_1(k6_relat_1(A_15))
      | ~ v1_relat_1(k6_relat_1(A_15)) ) ),
    inference(resolution,[status(thm)],[c_24,c_150])).

tff(c_165,plain,(
    ! [A_15] : k4_relat_1(k6_relat_1(A_15)) = k2_funct_1(k6_relat_1(A_15)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_156])).

tff(c_34,plain,(
    ! [A_19] :
      ( k1_relat_1(k6_relat_1(A_19)) = A_19
      | ~ v1_funct_1(k6_relat_1(A_19))
      | ~ v1_relat_1(k6_relat_1(A_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_56,plain,(
    ! [A_19] :
      ( k1_relat_1(k6_relat_1(A_19)) = A_19
      | ~ v1_funct_1(k6_relat_1(A_19)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_34])).

tff(c_60,plain,(
    ! [A_19] : k1_relat_1(k6_relat_1(A_19)) = A_19 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_56])).

tff(c_129,plain,(
    ! [A_36] :
      ( k5_relat_1(A_36,k6_relat_1(k2_relat_1(A_36))) = A_36
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_388,plain,(
    ! [A_50] :
      ( k5_relat_1(k4_relat_1(A_50),k6_relat_1(k1_relat_1(A_50))) = k4_relat_1(A_50)
      | ~ v1_relat_1(k4_relat_1(A_50))
      | ~ v1_relat_1(A_50) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_129])).

tff(c_406,plain,(
    ! [A_15] :
      ( k5_relat_1(k2_funct_1(k6_relat_1(A_15)),k6_relat_1(k1_relat_1(k6_relat_1(A_15)))) = k4_relat_1(k6_relat_1(A_15))
      | ~ v1_relat_1(k4_relat_1(k6_relat_1(A_15)))
      | ~ v1_relat_1(k6_relat_1(A_15)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_388])).

tff(c_1485,plain,(
    ! [A_81] :
      ( k5_relat_1(k2_funct_1(k6_relat_1(A_81)),k6_relat_1(A_81)) = k2_funct_1(k6_relat_1(A_81))
      | ~ v1_relat_1(k2_funct_1(k6_relat_1(A_81))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_165,c_60,c_165,c_406])).

tff(c_1491,plain,(
    ! [A_81] :
      ( k6_relat_1(k2_relat_1(k6_relat_1(A_81))) = k2_funct_1(k6_relat_1(A_81))
      | ~ v2_funct_1(k6_relat_1(A_81))
      | ~ v1_funct_1(k6_relat_1(A_81))
      | ~ v1_relat_1(k6_relat_1(A_81))
      | ~ v1_relat_1(k2_funct_1(k6_relat_1(A_81))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1485,c_36])).

tff(c_1512,plain,(
    ! [A_82] :
      ( k6_relat_1(k2_relat_1(k6_relat_1(A_82))) = k2_funct_1(k6_relat_1(A_82))
      | ~ v1_relat_1(k2_funct_1(k6_relat_1(A_82))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_24,c_1491])).

tff(c_1515,plain,(
    ! [A_82] :
      ( k6_relat_1(k2_relat_1(k6_relat_1(A_82))) = k2_funct_1(k6_relat_1(A_82))
      | ~ v1_funct_1(k6_relat_1(A_82))
      | ~ v1_relat_1(k6_relat_1(A_82)) ) ),
    inference(resolution,[status(thm)],[c_16,c_1512])).

tff(c_1525,plain,(
    ! [A_83] : k6_relat_1(k2_relat_1(k6_relat_1(A_83))) = k2_funct_1(k6_relat_1(A_83)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_1515])).

tff(c_1573,plain,(
    ! [A_83] : v1_relat_1(k2_funct_1(k6_relat_1(A_83))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1525,c_22])).

tff(c_1569,plain,(
    ! [A_83] : v1_funct_1(k2_funct_1(k6_relat_1(A_83))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1525,c_20])).

tff(c_212,plain,(
    ! [A_40] : k4_relat_1(k6_relat_1(A_40)) = k2_funct_1(k6_relat_1(A_40)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_156])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_relat_1(k4_relat_1(A_1)) = k2_relat_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_221,plain,(
    ! [A_40] :
      ( k1_relat_1(k2_funct_1(k6_relat_1(A_40))) = k2_relat_1(k6_relat_1(A_40))
      | ~ v1_relat_1(k6_relat_1(A_40)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_212,c_4])).

tff(c_232,plain,(
    ! [A_40] : k1_relat_1(k2_funct_1(k6_relat_1(A_40))) = k2_relat_1(k6_relat_1(A_40)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_221])).

tff(c_218,plain,(
    ! [A_40] :
      ( k2_relat_1(k2_funct_1(k6_relat_1(A_40))) = k1_relat_1(k6_relat_1(A_40))
      | ~ v1_relat_1(k6_relat_1(A_40)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_212,c_2])).

tff(c_230,plain,(
    ! [A_40] : k2_relat_1(k2_funct_1(k6_relat_1(A_40))) = A_40 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_60,c_218])).

tff(c_2130,plain,(
    ! [B_98,A_99] :
      ( r1_tarski(k2_relat_1(B_98),k1_relat_1(A_99))
      | k1_relat_1(k5_relat_1(B_98,A_99)) != k1_relat_1(B_98)
      | ~ v1_funct_1(B_98)
      | ~ v1_relat_1(B_98)
      | ~ v1_funct_1(A_99)
      | ~ v1_relat_1(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2160,plain,(
    ! [B_98,A_19] :
      ( r1_tarski(k2_relat_1(B_98),A_19)
      | k1_relat_1(k5_relat_1(B_98,k6_relat_1(A_19))) != k1_relat_1(B_98)
      | ~ v1_funct_1(B_98)
      | ~ v1_relat_1(B_98)
      | ~ v1_funct_1(k6_relat_1(A_19))
      | ~ v1_relat_1(k6_relat_1(A_19)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_2130])).

tff(c_2573,plain,(
    ! [B_110,A_111] :
      ( r1_tarski(k2_relat_1(B_110),A_111)
      | k1_relat_1(k5_relat_1(B_110,k6_relat_1(A_111))) != k1_relat_1(B_110)
      | ~ v1_funct_1(B_110)
      | ~ v1_relat_1(B_110) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_2160])).

tff(c_2593,plain,(
    ! [A_111] :
      ( r1_tarski(k2_relat_1(k2_funct_1(k6_relat_1(A_111))),A_111)
      | k1_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_111)))) != k1_relat_1(k2_funct_1(k6_relat_1(A_111)))
      | ~ v1_funct_1(k2_funct_1(k6_relat_1(A_111)))
      | ~ v1_relat_1(k2_funct_1(k6_relat_1(A_111)))
      | ~ v2_funct_1(k6_relat_1(A_111))
      | ~ v1_funct_1(k6_relat_1(A_111))
      | ~ v1_relat_1(k6_relat_1(A_111)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_2573])).

tff(c_2627,plain,(
    ! [A_112] : r1_tarski(A_112,A_112) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_24,c_1573,c_1569,c_60,c_232,c_230,c_2593])).

tff(c_8,plain,(
    ! [A_9,B_10] :
      ( k5_relat_1(k6_relat_1(A_9),B_10) = B_10
      | ~ r1_tarski(k1_relat_1(B_10),A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2632,plain,(
    ! [B_10] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(B_10)),B_10) = B_10
      | ~ v1_relat_1(B_10) ) ),
    inference(resolution,[status(thm)],[c_2627,c_8])).

tff(c_4158,plain,
    ( k5_relat_1(k2_funct_1('#skF_2'),k5_relat_1('#skF_2','#skF_3')) = '#skF_3'
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4138,c_2632])).

tff(c_4271,plain,(
    k2_funct_1('#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_50,c_373,c_4158])).

tff(c_4273,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_4271])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:26:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.94/1.97  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.36/1.97  
% 5.36/1.97  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.36/1.98  %$ r2_hidden > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 5.36/1.98  
% 5.36/1.98  %Foreground sorts:
% 5.36/1.98  
% 5.36/1.98  
% 5.36/1.98  %Background operators:
% 5.36/1.98  
% 5.36/1.98  
% 5.36/1.98  %Foreground operators:
% 5.36/1.98  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.36/1.98  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.36/1.98  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.36/1.98  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.36/1.98  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.36/1.98  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.36/1.98  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.36/1.98  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.36/1.98  tff('#skF_2', type, '#skF_2': $i).
% 5.36/1.98  tff('#skF_3', type, '#skF_3': $i).
% 5.36/1.98  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.36/1.98  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.36/1.98  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.36/1.98  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.36/1.98  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.36/1.98  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.36/1.98  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.36/1.98  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 5.36/1.98  
% 5.36/1.99  tff(f_129, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(A) = k1_relat_1(B))) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_funct_1)).
% 5.36/1.99  tff(f_67, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 5.36/1.99  tff(f_59, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 5.36/1.99  tff(f_31, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_relat_1)).
% 5.36/1.99  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 5.36/1.99  tff(f_111, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 5.36/1.99  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 5.36/1.99  tff(f_75, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 5.36/1.99  tff(f_71, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 5.36/1.99  tff(f_101, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k6_relat_1(A)) <=> ((k1_relat_1(B) = A) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_funct_1)).
% 5.36/1.99  tff(f_88, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(k5_relat_1(B, A)) = k1_relat_1(B)) => r1_tarski(k2_relat_1(B), k1_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_funct_1)).
% 5.36/1.99  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_relat_1)).
% 5.36/1.99  tff(c_40, plain, (k2_funct_1('#skF_2')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.36/1.99  tff(c_50, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.36/1.99  tff(c_54, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.36/1.99  tff(c_52, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.36/1.99  tff(c_16, plain, (![A_13]: (v1_relat_1(k2_funct_1(A_13)) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.36/1.99  tff(c_42, plain, (k6_relat_1(k1_relat_1('#skF_2'))=k5_relat_1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.36/1.99  tff(c_46, plain, (v2_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.36/1.99  tff(c_150, plain, (![A_37]: (k4_relat_1(A_37)=k2_funct_1(A_37) | ~v2_funct_1(A_37) | ~v1_funct_1(A_37) | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.36/1.99  tff(c_159, plain, (k4_relat_1('#skF_2')=k2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_46, c_150])).
% 5.36/1.99  tff(c_168, plain, (k4_relat_1('#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_159])).
% 5.36/1.99  tff(c_2, plain, (![A_1]: (k2_relat_1(k4_relat_1(A_1))=k1_relat_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.36/1.99  tff(c_172, plain, (k2_relat_1(k2_funct_1('#skF_2'))=k1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_168, c_2])).
% 5.36/1.99  tff(c_179, plain, (k2_relat_1(k2_funct_1('#skF_2'))=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_172])).
% 5.36/1.99  tff(c_10, plain, (![A_11]: (k5_relat_1(A_11, k6_relat_1(k2_relat_1(A_11)))=A_11 | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.36/1.99  tff(c_200, plain, (k5_relat_1(k2_funct_1('#skF_2'), k6_relat_1(k1_relat_1('#skF_2')))=k2_funct_1('#skF_2') | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_179, c_10])).
% 5.36/1.99  tff(c_203, plain, (k5_relat_1(k2_funct_1('#skF_2'), k5_relat_1('#skF_2', '#skF_3'))=k2_funct_1('#skF_2') | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_200])).
% 5.36/1.99  tff(c_365, plain, (~v1_relat_1(k2_funct_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_203])).
% 5.36/1.99  tff(c_368, plain, (~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_16, c_365])).
% 5.36/1.99  tff(c_372, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_368])).
% 5.36/1.99  tff(c_373, plain, (k5_relat_1(k2_funct_1('#skF_2'), k5_relat_1('#skF_2', '#skF_3'))=k2_funct_1('#skF_2')), inference(splitRight, [status(thm)], [c_203])).
% 5.36/1.99  tff(c_374, plain, (v1_relat_1(k2_funct_1('#skF_2'))), inference(splitRight, [status(thm)], [c_203])).
% 5.36/1.99  tff(c_44, plain, (k2_relat_1('#skF_2')=k1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.36/1.99  tff(c_36, plain, (![A_24]: (k5_relat_1(k2_funct_1(A_24), A_24)=k6_relat_1(k2_relat_1(A_24)) | ~v2_funct_1(A_24) | ~v1_funct_1(A_24) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.36/1.99  tff(c_1752, plain, (![A_92, B_93, C_94]: (k5_relat_1(k5_relat_1(A_92, B_93), C_94)=k5_relat_1(A_92, k5_relat_1(B_93, C_94)) | ~v1_relat_1(C_94) | ~v1_relat_1(B_93) | ~v1_relat_1(A_92))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.36/1.99  tff(c_3846, plain, (![A_131, C_132]: (k5_relat_1(k6_relat_1(k2_relat_1(A_131)), C_132)=k5_relat_1(k2_funct_1(A_131), k5_relat_1(A_131, C_132)) | ~v1_relat_1(C_132) | ~v1_relat_1(A_131) | ~v1_relat_1(k2_funct_1(A_131)) | ~v2_funct_1(A_131) | ~v1_funct_1(A_131) | ~v1_relat_1(A_131))), inference(superposition, [status(thm), theory('equality')], [c_36, c_1752])).
% 5.36/1.99  tff(c_4045, plain, (![C_132]: (k5_relat_1(k6_relat_1(k1_relat_1('#skF_3')), C_132)=k5_relat_1(k2_funct_1('#skF_2'), k5_relat_1('#skF_2', C_132)) | ~v1_relat_1(C_132) | ~v1_relat_1('#skF_2') | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_44, c_3846])).
% 5.36/1.99  tff(c_4138, plain, (![C_133]: (k5_relat_1(k6_relat_1(k1_relat_1('#skF_3')), C_133)=k5_relat_1(k2_funct_1('#skF_2'), k5_relat_1('#skF_2', C_133)) | ~v1_relat_1(C_133))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_46, c_374, c_54, c_4045])).
% 5.36/1.99  tff(c_22, plain, (![A_15]: (v1_relat_1(k6_relat_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.36/1.99  tff(c_20, plain, (![A_14]: (v1_funct_1(k6_relat_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.36/1.99  tff(c_24, plain, (![A_15]: (v2_funct_1(k6_relat_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.36/1.99  tff(c_156, plain, (![A_15]: (k4_relat_1(k6_relat_1(A_15))=k2_funct_1(k6_relat_1(A_15)) | ~v1_funct_1(k6_relat_1(A_15)) | ~v1_relat_1(k6_relat_1(A_15)))), inference(resolution, [status(thm)], [c_24, c_150])).
% 5.36/1.99  tff(c_165, plain, (![A_15]: (k4_relat_1(k6_relat_1(A_15))=k2_funct_1(k6_relat_1(A_15)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_156])).
% 5.36/1.99  tff(c_34, plain, (![A_19]: (k1_relat_1(k6_relat_1(A_19))=A_19 | ~v1_funct_1(k6_relat_1(A_19)) | ~v1_relat_1(k6_relat_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.36/1.99  tff(c_56, plain, (![A_19]: (k1_relat_1(k6_relat_1(A_19))=A_19 | ~v1_funct_1(k6_relat_1(A_19)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_34])).
% 5.36/1.99  tff(c_60, plain, (![A_19]: (k1_relat_1(k6_relat_1(A_19))=A_19)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_56])).
% 5.36/1.99  tff(c_129, plain, (![A_36]: (k5_relat_1(A_36, k6_relat_1(k2_relat_1(A_36)))=A_36 | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.36/1.99  tff(c_388, plain, (![A_50]: (k5_relat_1(k4_relat_1(A_50), k6_relat_1(k1_relat_1(A_50)))=k4_relat_1(A_50) | ~v1_relat_1(k4_relat_1(A_50)) | ~v1_relat_1(A_50))), inference(superposition, [status(thm), theory('equality')], [c_2, c_129])).
% 5.36/1.99  tff(c_406, plain, (![A_15]: (k5_relat_1(k2_funct_1(k6_relat_1(A_15)), k6_relat_1(k1_relat_1(k6_relat_1(A_15))))=k4_relat_1(k6_relat_1(A_15)) | ~v1_relat_1(k4_relat_1(k6_relat_1(A_15))) | ~v1_relat_1(k6_relat_1(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_165, c_388])).
% 5.36/1.99  tff(c_1485, plain, (![A_81]: (k5_relat_1(k2_funct_1(k6_relat_1(A_81)), k6_relat_1(A_81))=k2_funct_1(k6_relat_1(A_81)) | ~v1_relat_1(k2_funct_1(k6_relat_1(A_81))))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_165, c_60, c_165, c_406])).
% 5.36/1.99  tff(c_1491, plain, (![A_81]: (k6_relat_1(k2_relat_1(k6_relat_1(A_81)))=k2_funct_1(k6_relat_1(A_81)) | ~v2_funct_1(k6_relat_1(A_81)) | ~v1_funct_1(k6_relat_1(A_81)) | ~v1_relat_1(k6_relat_1(A_81)) | ~v1_relat_1(k2_funct_1(k6_relat_1(A_81))))), inference(superposition, [status(thm), theory('equality')], [c_1485, c_36])).
% 5.36/1.99  tff(c_1512, plain, (![A_82]: (k6_relat_1(k2_relat_1(k6_relat_1(A_82)))=k2_funct_1(k6_relat_1(A_82)) | ~v1_relat_1(k2_funct_1(k6_relat_1(A_82))))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_24, c_1491])).
% 5.36/1.99  tff(c_1515, plain, (![A_82]: (k6_relat_1(k2_relat_1(k6_relat_1(A_82)))=k2_funct_1(k6_relat_1(A_82)) | ~v1_funct_1(k6_relat_1(A_82)) | ~v1_relat_1(k6_relat_1(A_82)))), inference(resolution, [status(thm)], [c_16, c_1512])).
% 5.36/1.99  tff(c_1525, plain, (![A_83]: (k6_relat_1(k2_relat_1(k6_relat_1(A_83)))=k2_funct_1(k6_relat_1(A_83)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_1515])).
% 5.36/1.99  tff(c_1573, plain, (![A_83]: (v1_relat_1(k2_funct_1(k6_relat_1(A_83))))), inference(superposition, [status(thm), theory('equality')], [c_1525, c_22])).
% 5.36/1.99  tff(c_1569, plain, (![A_83]: (v1_funct_1(k2_funct_1(k6_relat_1(A_83))))), inference(superposition, [status(thm), theory('equality')], [c_1525, c_20])).
% 5.36/1.99  tff(c_212, plain, (![A_40]: (k4_relat_1(k6_relat_1(A_40))=k2_funct_1(k6_relat_1(A_40)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_156])).
% 5.36/1.99  tff(c_4, plain, (![A_1]: (k1_relat_1(k4_relat_1(A_1))=k2_relat_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.36/1.99  tff(c_221, plain, (![A_40]: (k1_relat_1(k2_funct_1(k6_relat_1(A_40)))=k2_relat_1(k6_relat_1(A_40)) | ~v1_relat_1(k6_relat_1(A_40)))), inference(superposition, [status(thm), theory('equality')], [c_212, c_4])).
% 5.36/1.99  tff(c_232, plain, (![A_40]: (k1_relat_1(k2_funct_1(k6_relat_1(A_40)))=k2_relat_1(k6_relat_1(A_40)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_221])).
% 5.36/1.99  tff(c_218, plain, (![A_40]: (k2_relat_1(k2_funct_1(k6_relat_1(A_40)))=k1_relat_1(k6_relat_1(A_40)) | ~v1_relat_1(k6_relat_1(A_40)))), inference(superposition, [status(thm), theory('equality')], [c_212, c_2])).
% 5.36/1.99  tff(c_230, plain, (![A_40]: (k2_relat_1(k2_funct_1(k6_relat_1(A_40)))=A_40)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_60, c_218])).
% 5.36/1.99  tff(c_2130, plain, (![B_98, A_99]: (r1_tarski(k2_relat_1(B_98), k1_relat_1(A_99)) | k1_relat_1(k5_relat_1(B_98, A_99))!=k1_relat_1(B_98) | ~v1_funct_1(B_98) | ~v1_relat_1(B_98) | ~v1_funct_1(A_99) | ~v1_relat_1(A_99))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.36/1.99  tff(c_2160, plain, (![B_98, A_19]: (r1_tarski(k2_relat_1(B_98), A_19) | k1_relat_1(k5_relat_1(B_98, k6_relat_1(A_19)))!=k1_relat_1(B_98) | ~v1_funct_1(B_98) | ~v1_relat_1(B_98) | ~v1_funct_1(k6_relat_1(A_19)) | ~v1_relat_1(k6_relat_1(A_19)))), inference(superposition, [status(thm), theory('equality')], [c_60, c_2130])).
% 5.36/1.99  tff(c_2573, plain, (![B_110, A_111]: (r1_tarski(k2_relat_1(B_110), A_111) | k1_relat_1(k5_relat_1(B_110, k6_relat_1(A_111)))!=k1_relat_1(B_110) | ~v1_funct_1(B_110) | ~v1_relat_1(B_110))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_2160])).
% 5.36/1.99  tff(c_2593, plain, (![A_111]: (r1_tarski(k2_relat_1(k2_funct_1(k6_relat_1(A_111))), A_111) | k1_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_111))))!=k1_relat_1(k2_funct_1(k6_relat_1(A_111))) | ~v1_funct_1(k2_funct_1(k6_relat_1(A_111))) | ~v1_relat_1(k2_funct_1(k6_relat_1(A_111))) | ~v2_funct_1(k6_relat_1(A_111)) | ~v1_funct_1(k6_relat_1(A_111)) | ~v1_relat_1(k6_relat_1(A_111)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_2573])).
% 5.36/1.99  tff(c_2627, plain, (![A_112]: (r1_tarski(A_112, A_112))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_24, c_1573, c_1569, c_60, c_232, c_230, c_2593])).
% 5.36/1.99  tff(c_8, plain, (![A_9, B_10]: (k5_relat_1(k6_relat_1(A_9), B_10)=B_10 | ~r1_tarski(k1_relat_1(B_10), A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.36/1.99  tff(c_2632, plain, (![B_10]: (k5_relat_1(k6_relat_1(k1_relat_1(B_10)), B_10)=B_10 | ~v1_relat_1(B_10))), inference(resolution, [status(thm)], [c_2627, c_8])).
% 5.36/1.99  tff(c_4158, plain, (k5_relat_1(k2_funct_1('#skF_2'), k5_relat_1('#skF_2', '#skF_3'))='#skF_3' | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4138, c_2632])).
% 5.36/1.99  tff(c_4271, plain, (k2_funct_1('#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_50, c_373, c_4158])).
% 5.36/1.99  tff(c_4273, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_4271])).
% 5.36/1.99  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.36/1.99  
% 5.36/1.99  Inference rules
% 5.36/1.99  ----------------------
% 5.36/1.99  #Ref     : 0
% 5.36/1.99  #Sup     : 911
% 5.36/1.99  #Fact    : 0
% 5.36/1.99  #Define  : 0
% 5.36/1.99  #Split   : 6
% 5.36/1.99  #Chain   : 0
% 5.36/1.99  #Close   : 0
% 5.36/1.99  
% 5.36/1.99  Ordering : KBO
% 5.36/1.99  
% 5.36/1.99  Simplification rules
% 5.36/1.99  ----------------------
% 5.36/1.99  #Subsume      : 19
% 5.36/1.99  #Demod        : 2013
% 5.36/1.99  #Tautology    : 466
% 5.36/1.99  #SimpNegUnit  : 1
% 5.36/1.99  #BackRed      : 42
% 5.36/1.99  
% 5.36/1.99  #Partial instantiations: 0
% 5.36/1.99  #Strategies tried      : 1
% 5.36/1.99  
% 5.36/1.99  Timing (in seconds)
% 5.36/1.99  ----------------------
% 5.48/2.00  Preprocessing        : 0.33
% 5.48/2.00  Parsing              : 0.17
% 5.48/2.00  CNF conversion       : 0.02
% 5.48/2.00  Main loop            : 0.89
% 5.48/2.00  Inferencing          : 0.28
% 5.48/2.00  Reduction            : 0.37
% 5.48/2.00  Demodulation         : 0.29
% 5.48/2.00  BG Simplification    : 0.04
% 5.48/2.00  Subsumption          : 0.15
% 5.48/2.00  Abstraction          : 0.05
% 5.48/2.00  MUC search           : 0.00
% 5.48/2.00  Cooper               : 0.00
% 5.48/2.00  Total                : 1.26
% 5.48/2.00  Index Insertion      : 0.00
% 5.48/2.00  Index Deletion       : 0.00
% 5.48/2.00  Index Matching       : 0.00
% 5.48/2.00  BG Taut test         : 0.00
%------------------------------------------------------------------------------
