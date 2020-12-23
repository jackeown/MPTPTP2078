%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:01 EST 2020

% Result     : Theorem 8.67s
% Output     : CNFRefutation 8.67s
% Verified   : 
% Statistics : Number of formulae       :  229 (110837 expanded)
%              Number of leaves         :   26 (40328 expanded)
%              Depth                    :   39
%              Number of atoms          :  560 (379980 expanded)
%              Number of equality atoms :  129 (141726 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(f_139,negated_conjecture,(
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

tff(f_61,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v1_relat_1(k5_relat_1(A,B))
        & v1_funct_1(k5_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funct_1)).

tff(f_49,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_111,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( ? [B] :
            ( v1_relat_1(B)
            & v1_funct_1(B)
            & k5_relat_1(A,B) = k6_relat_1(k1_relat_1(A)) )
       => v2_funct_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_funct_1)).

tff(f_98,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).

tff(f_69,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_121,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

tff(c_36,plain,(
    k2_funct_1('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_46,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_50,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_48,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_42,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_240,plain,(
    ! [A_38] :
      ( k4_relat_1(A_38) = k2_funct_1(A_38)
      | ~ v2_funct_1(A_38)
      | ~ v1_funct_1(A_38)
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_243,plain,
    ( k4_relat_1('#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_240])).

tff(c_246,plain,(
    k4_relat_1('#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_243])).

tff(c_2,plain,(
    ! [A_1] :
      ( v1_relat_1(k4_relat_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_256,plain,
    ( v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_246,c_2])).

tff(c_264,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_256])).

tff(c_38,plain,(
    k6_relat_1(k1_relat_1('#skF_1')) = k5_relat_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_4,plain,(
    ! [A_2] :
      ( k2_relat_1(k4_relat_1(A_2)) = k1_relat_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_253,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_246,c_4])).

tff(c_262,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_253])).

tff(c_14,plain,(
    ! [A_11] :
      ( k5_relat_1(A_11,k6_relat_1(k2_relat_1(A_11))) = A_11
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_282,plain,
    ( k5_relat_1(k2_funct_1('#skF_1'),k6_relat_1(k1_relat_1('#skF_1'))) = k2_funct_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_262,c_14])).

tff(c_286,plain,(
    k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1','#skF_2')) = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_38,c_282])).

tff(c_44,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_40,plain,(
    k2_relat_1('#skF_1') = k1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_22,plain,(
    ! [A_14,B_15] :
      ( v1_funct_1(k5_relat_1(A_14,B_15))
      | ~ v1_funct_1(B_15)
      | ~ v1_relat_1(B_15)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_218,plain,(
    ! [A_36,B_37] :
      ( v1_relat_1(k5_relat_1(A_36,B_37))
      | ~ v1_funct_1(B_37)
      | ~ v1_relat_1(B_37)
      | ~ v1_funct_1(A_36)
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_12,plain,(
    ! [A_10] : k2_relat_1(k6_relat_1(A_10)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_76,plain,(
    k2_relat_1(k5_relat_1('#skF_1','#skF_2')) = k1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_12])).

tff(c_112,plain,(
    ! [A_31] :
      ( k5_relat_1(A_31,k6_relat_1(k2_relat_1(A_31))) = A_31
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_124,plain,
    ( k5_relat_1(k5_relat_1('#skF_1','#skF_2'),k6_relat_1(k1_relat_1('#skF_1'))) = k5_relat_1('#skF_1','#skF_2')
    | ~ v1_relat_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_112])).

tff(c_133,plain,
    ( k5_relat_1(k5_relat_1('#skF_1','#skF_2'),k5_relat_1('#skF_1','#skF_2')) = k5_relat_1('#skF_1','#skF_2')
    | ~ v1_relat_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_124])).

tff(c_140,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_133])).

tff(c_221,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_218,c_140])).

tff(c_237,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_221])).

tff(c_239,plain,(
    v1_relat_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_133])).

tff(c_10,plain,(
    ! [A_10] : k1_relat_1(k6_relat_1(A_10)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_79,plain,(
    k1_relat_1(k5_relat_1('#skF_1','#skF_2')) = k1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_10])).

tff(c_297,plain,(
    ! [A_41] :
      ( k5_relat_1(k6_relat_1(A_41),k6_relat_1(A_41)) = k6_relat_1(A_41)
      | ~ v1_relat_1(k6_relat_1(A_41)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_112])).

tff(c_309,plain,
    ( k5_relat_1(k5_relat_1('#skF_1','#skF_2'),k6_relat_1(k1_relat_1('#skF_1'))) = k6_relat_1(k1_relat_1('#skF_1'))
    | ~ v1_relat_1(k6_relat_1(k1_relat_1('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_297])).

tff(c_316,plain,(
    k5_relat_1(k5_relat_1('#skF_1','#skF_2'),k5_relat_1('#skF_1','#skF_2')) = k5_relat_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_239,c_38,c_38,c_38,c_309])).

tff(c_559,plain,(
    ! [A_50,B_51] :
      ( v2_funct_1(A_50)
      | k6_relat_1(k1_relat_1(A_50)) != k5_relat_1(A_50,B_51)
      | ~ v1_funct_1(B_51)
      | ~ v1_relat_1(B_51)
      | ~ v1_funct_1(A_50)
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_573,plain,
    ( v2_funct_1(k5_relat_1('#skF_1','#skF_2'))
    | k6_relat_1(k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) != k5_relat_1('#skF_1','#skF_2')
    | ~ v1_funct_1(k5_relat_1('#skF_1','#skF_2'))
    | ~ v1_relat_1(k5_relat_1('#skF_1','#skF_2'))
    | ~ v1_funct_1(k5_relat_1('#skF_1','#skF_2'))
    | ~ v1_relat_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_316,c_559])).

tff(c_598,plain,
    ( v2_funct_1(k5_relat_1('#skF_1','#skF_2'))
    | ~ v1_funct_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_239,c_239,c_38,c_79,c_573])).

tff(c_611,plain,(
    ~ v1_funct_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_598])).

tff(c_614,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_611])).

tff(c_618,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_614])).

tff(c_619,plain,(
    v2_funct_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_598])).

tff(c_664,plain,(
    ! [A_52,B_53] :
      ( v2_funct_1(A_52)
      | k2_relat_1(B_53) != k1_relat_1(A_52)
      | ~ v2_funct_1(k5_relat_1(B_53,A_52))
      | ~ v1_funct_1(B_53)
      | ~ v1_relat_1(B_53)
      | ~ v1_funct_1(A_52)
      | ~ v1_relat_1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_667,plain,
    ( v2_funct_1('#skF_2')
    | k2_relat_1('#skF_1') != k1_relat_1('#skF_2')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_619,c_664])).

tff(c_700,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_50,c_48,c_40,c_667])).

tff(c_16,plain,(
    ! [A_12] :
      ( k4_relat_1(A_12) = k2_funct_1(A_12)
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_716,plain,
    ( k4_relat_1('#skF_2') = k2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_700,c_16])).

tff(c_719,plain,(
    k4_relat_1('#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_716])).

tff(c_732,plain,
    ( v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_719,c_2])).

tff(c_742,plain,(
    v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_732])).

tff(c_18,plain,(
    ! [A_13] :
      ( v1_funct_1(k2_funct_1(A_13))
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_130,plain,
    ( k5_relat_1('#skF_1',k6_relat_1(k1_relat_1('#skF_2'))) = '#skF_1'
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_112])).

tff(c_135,plain,(
    k5_relat_1('#skF_1',k6_relat_1(k1_relat_1('#skF_2'))) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_130])).

tff(c_694,plain,
    ( v2_funct_1(k6_relat_1(k1_relat_1('#skF_2')))
    | k1_relat_1(k6_relat_1(k1_relat_1('#skF_2'))) != k2_relat_1('#skF_1')
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_funct_1(k6_relat_1(k1_relat_1('#skF_2')))
    | ~ v1_relat_1(k6_relat_1(k1_relat_1('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_664])).

tff(c_711,plain,
    ( v2_funct_1(k6_relat_1(k1_relat_1('#skF_2')))
    | ~ v1_funct_1(k6_relat_1(k1_relat_1('#skF_2')))
    | ~ v1_relat_1(k6_relat_1(k1_relat_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_42,c_40,c_10,c_694])).

tff(c_744,plain,(
    ~ v1_relat_1(k6_relat_1(k1_relat_1('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_711])).

tff(c_32,plain,(
    ! [A_22] :
      ( k5_relat_1(k2_funct_1(A_22),A_22) = k6_relat_1(k2_relat_1(A_22))
      | ~ v2_funct_1(A_22)
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_34,plain,(
    ! [A_22] :
      ( k5_relat_1(A_22,k2_funct_1(A_22)) = k6_relat_1(k1_relat_1(A_22))
      | ~ v2_funct_1(A_22)
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_8,plain,(
    ! [A_3,B_7,C_9] :
      ( k5_relat_1(k5_relat_1(A_3,B_7),C_9) = k5_relat_1(A_3,k5_relat_1(B_7,C_9))
      | ~ v1_relat_1(C_9)
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_382,plain,(
    ! [A_46,B_47,C_48] :
      ( k5_relat_1(k5_relat_1(A_46,B_47),C_48) = k5_relat_1(A_46,k5_relat_1(B_47,C_48))
      | ~ v1_relat_1(C_48)
      | ~ v1_relat_1(B_47)
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_433,plain,(
    ! [C_48] :
      ( k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1(k5_relat_1('#skF_1','#skF_2'),C_48)) = k5_relat_1(k2_funct_1('#skF_1'),C_48)
      | ~ v1_relat_1(C_48)
      | ~ v1_relat_1(k5_relat_1('#skF_1','#skF_2'))
      | ~ v1_relat_1(k2_funct_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_286,c_382])).

tff(c_1027,plain,(
    ! [C_58] :
      ( k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1(k5_relat_1('#skF_1','#skF_2'),C_58)) = k5_relat_1(k2_funct_1('#skF_1'),C_58)
      | ~ v1_relat_1(C_58) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_239,c_433])).

tff(c_1054,plain,(
    ! [C_9] :
      ( k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1',k5_relat_1('#skF_2',C_9))) = k5_relat_1(k2_funct_1('#skF_1'),C_9)
      | ~ v1_relat_1(C_9)
      | ~ v1_relat_1(C_9)
      | ~ v1_relat_1('#skF_2')
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_1027])).

tff(c_1088,plain,(
    ! [C_59] :
      ( k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1',k5_relat_1('#skF_2',C_59))) = k5_relat_1(k2_funct_1('#skF_1'),C_59)
      | ~ v1_relat_1(C_59) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_1054])).

tff(c_1118,plain,
    ( k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1',k6_relat_1(k1_relat_1('#skF_2')))) = k5_relat_1(k2_funct_1('#skF_1'),k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_1088])).

tff(c_1140,plain,(
    k5_relat_1(k2_funct_1('#skF_1'),k2_funct_1('#skF_2')) = k5_relat_1(k2_funct_1('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_700,c_742,c_135,c_1118])).

tff(c_1157,plain,
    ( v1_funct_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v1_funct_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1140,c_22])).

tff(c_1172,plain,
    ( v1_funct_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_funct_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_742,c_1157])).

tff(c_1176,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_1172])).

tff(c_1179,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_1176])).

tff(c_1183,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_1179])).

tff(c_1185,plain,(
    v1_funct_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_1172])).

tff(c_1184,plain,
    ( ~ v1_funct_1(k2_funct_1('#skF_2'))
    | v1_funct_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) ),
    inference(splitRight,[status(thm)],[c_1172])).

tff(c_1186,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1184])).

tff(c_1272,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_1186])).

tff(c_1276,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_1272])).

tff(c_1278,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1184])).

tff(c_24,plain,(
    ! [A_14,B_15] :
      ( v1_relat_1(k5_relat_1(A_14,B_15))
      | ~ v1_funct_1(B_15)
      | ~ v1_relat_1(B_15)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1160,plain,
    ( v1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v1_funct_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1140,c_24])).

tff(c_1174,plain,
    ( v1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_funct_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_742,c_1160])).

tff(c_1285,plain,(
    v1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1185,c_1278,c_1174])).

tff(c_1288,plain,
    ( v1_relat_1(k6_relat_1(k2_relat_1('#skF_1')))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_1285])).

tff(c_1290,plain,(
    v1_relat_1(k6_relat_1(k1_relat_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_42,c_40,c_1288])).

tff(c_1292,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_744,c_1290])).

tff(c_1294,plain,(
    v1_relat_1(k6_relat_1(k1_relat_1('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_711])).

tff(c_1293,plain,
    ( ~ v1_funct_1(k6_relat_1(k1_relat_1('#skF_2')))
    | v2_funct_1(k6_relat_1(k1_relat_1('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_711])).

tff(c_1448,plain,(
    ~ v1_funct_1(k6_relat_1(k1_relat_1('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_1293])).

tff(c_1756,plain,(
    ! [C_68] :
      ( k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1(k5_relat_1('#skF_1','#skF_2'),C_68)) = k5_relat_1(k2_funct_1('#skF_1'),C_68)
      | ~ v1_relat_1(C_68) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_239,c_433])).

tff(c_1786,plain,(
    ! [C_9] :
      ( k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1',k5_relat_1('#skF_2',C_9))) = k5_relat_1(k2_funct_1('#skF_1'),C_9)
      | ~ v1_relat_1(C_9)
      | ~ v1_relat_1(C_9)
      | ~ v1_relat_1('#skF_2')
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_1756])).

tff(c_1821,plain,(
    ! [C_69] :
      ( k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1',k5_relat_1('#skF_2',C_69))) = k5_relat_1(k2_funct_1('#skF_1'),C_69)
      | ~ v1_relat_1(C_69) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_1786])).

tff(c_1851,plain,
    ( k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1',k6_relat_1(k1_relat_1('#skF_2')))) = k5_relat_1(k2_funct_1('#skF_1'),k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_1821])).

tff(c_1873,plain,(
    k5_relat_1(k2_funct_1('#skF_1'),k2_funct_1('#skF_2')) = k5_relat_1(k2_funct_1('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_700,c_742,c_135,c_1851])).

tff(c_1890,plain,
    ( v1_funct_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v1_funct_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1873,c_22])).

tff(c_1905,plain,
    ( v1_funct_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_funct_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_742,c_1890])).

tff(c_1909,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_1905])).

tff(c_1943,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_1909])).

tff(c_1947,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_1943])).

tff(c_1948,plain,
    ( ~ v1_funct_1(k2_funct_1('#skF_2'))
    | v1_funct_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) ),
    inference(splitRight,[status(thm)],[c_1905])).

tff(c_1950,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1948])).

tff(c_1954,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_1950])).

tff(c_1958,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_1954])).

tff(c_1959,plain,(
    v1_funct_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) ),
    inference(splitRight,[status(thm)],[c_1948])).

tff(c_1963,plain,
    ( v1_funct_1(k6_relat_1(k2_relat_1('#skF_1')))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_1959])).

tff(c_1965,plain,(
    v1_funct_1(k6_relat_1(k1_relat_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_42,c_40,c_1963])).

tff(c_1967,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1448,c_1965])).

tff(c_1969,plain,(
    v1_funct_1(k6_relat_1(k1_relat_1('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_1293])).

tff(c_6,plain,(
    ! [A_2] :
      ( k1_relat_1(k4_relat_1(A_2)) = k2_relat_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_726,plain,
    ( k1_relat_1(k2_funct_1('#skF_2')) = k2_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_719,c_6])).

tff(c_738,plain,(
    k1_relat_1(k2_funct_1('#skF_2')) = k2_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_726])).

tff(c_729,plain,
    ( k2_relat_1(k2_funct_1('#skF_2')) = k1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_719,c_4])).

tff(c_740,plain,(
    k2_relat_1(k2_funct_1('#skF_2')) = k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_729])).

tff(c_1420,plain,
    ( k5_relat_1(k2_funct_1('#skF_2'),k6_relat_1(k1_relat_1('#skF_2'))) = k2_funct_1('#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_740,c_14])).

tff(c_1424,plain,(
    k5_relat_1(k2_funct_1('#skF_2'),k6_relat_1(k1_relat_1('#skF_2'))) = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_742,c_1420])).

tff(c_30,plain,(
    ! [A_19,B_21] :
      ( v2_funct_1(A_19)
      | k6_relat_1(k1_relat_1(A_19)) != k5_relat_1(A_19,B_21)
      | ~ v1_funct_1(B_21)
      | ~ v1_relat_1(B_21)
      | ~ v1_funct_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_2021,plain,
    ( v2_funct_1(k2_funct_1('#skF_2'))
    | k6_relat_1(k1_relat_1(k2_funct_1('#skF_2'))) != k2_funct_1('#skF_2')
    | ~ v1_funct_1(k6_relat_1(k1_relat_1('#skF_2')))
    | ~ v1_relat_1(k6_relat_1(k1_relat_1('#skF_2')))
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1424,c_30])).

tff(c_2038,plain,
    ( v2_funct_1(k2_funct_1('#skF_2'))
    | k6_relat_1(k2_relat_1('#skF_2')) != k2_funct_1('#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_742,c_1294,c_1969,c_738,c_2021])).

tff(c_2092,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_2038])).

tff(c_2095,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_2092])).

tff(c_2099,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_2095])).

tff(c_2101,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_2038])).

tff(c_1968,plain,(
    v2_funct_1(k6_relat_1(k1_relat_1('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_1293])).

tff(c_4648,plain,(
    ! [A_100,C_101] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_100)),C_101) = k5_relat_1(A_100,k5_relat_1(k2_funct_1(A_100),C_101))
      | ~ v1_relat_1(C_101)
      | ~ v1_relat_1(k2_funct_1(A_100))
      | ~ v1_relat_1(A_100)
      | ~ v2_funct_1(A_100)
      | ~ v1_funct_1(A_100)
      | ~ v1_relat_1(A_100) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_382])).

tff(c_1972,plain,
    ( k4_relat_1(k6_relat_1(k1_relat_1('#skF_2'))) = k2_funct_1(k6_relat_1(k1_relat_1('#skF_2')))
    | ~ v1_funct_1(k6_relat_1(k1_relat_1('#skF_2')))
    | ~ v1_relat_1(k6_relat_1(k1_relat_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_1968,c_16])).

tff(c_1975,plain,
    ( k4_relat_1(k6_relat_1(k1_relat_1('#skF_2'))) = k2_funct_1(k6_relat_1(k1_relat_1('#skF_2')))
    | ~ v1_funct_1(k6_relat_1(k1_relat_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1294,c_1972])).

tff(c_2104,plain,(
    k4_relat_1(k6_relat_1(k1_relat_1('#skF_2'))) = k2_funct_1(k6_relat_1(k1_relat_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1969,c_1975])).

tff(c_2117,plain,
    ( v1_relat_1(k2_funct_1(k6_relat_1(k1_relat_1('#skF_2'))))
    | ~ v1_relat_1(k6_relat_1(k1_relat_1('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2104,c_2])).

tff(c_2127,plain,(
    v1_relat_1(k2_funct_1(k6_relat_1(k1_relat_1('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1294,c_2117])).

tff(c_2114,plain,
    ( k2_relat_1(k2_funct_1(k6_relat_1(k1_relat_1('#skF_2')))) = k1_relat_1(k6_relat_1(k1_relat_1('#skF_2')))
    | ~ v1_relat_1(k6_relat_1(k1_relat_1('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2104,c_4])).

tff(c_2125,plain,(
    k2_relat_1(k2_funct_1(k6_relat_1(k1_relat_1('#skF_2')))) = k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1294,c_10,c_2114])).

tff(c_2224,plain,
    ( k5_relat_1(k2_funct_1(k6_relat_1(k1_relat_1('#skF_2'))),k6_relat_1(k1_relat_1('#skF_2'))) = k2_funct_1(k6_relat_1(k1_relat_1('#skF_2')))
    | ~ v1_relat_1(k2_funct_1(k6_relat_1(k1_relat_1('#skF_2')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2125,c_14])).

tff(c_2228,plain,(
    k5_relat_1(k2_funct_1(k6_relat_1(k1_relat_1('#skF_2'))),k6_relat_1(k1_relat_1('#skF_2'))) = k2_funct_1(k6_relat_1(k1_relat_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2127,c_2224])).

tff(c_2617,plain,
    ( k6_relat_1(k2_relat_1(k6_relat_1(k1_relat_1('#skF_2')))) = k2_funct_1(k6_relat_1(k1_relat_1('#skF_2')))
    | ~ v2_funct_1(k6_relat_1(k1_relat_1('#skF_2')))
    | ~ v1_funct_1(k6_relat_1(k1_relat_1('#skF_2')))
    | ~ v1_relat_1(k6_relat_1(k1_relat_1('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2228,c_32])).

tff(c_2638,plain,(
    k2_funct_1(k6_relat_1(k1_relat_1('#skF_2'))) = k6_relat_1(k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1294,c_1969,c_1968,c_12,c_2617])).

tff(c_2646,plain,(
    k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')),k6_relat_1(k1_relat_1('#skF_2'))) = k6_relat_1(k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2638,c_2638,c_2228])).

tff(c_4701,plain,
    ( k5_relat_1('#skF_2',k5_relat_1(k2_funct_1('#skF_2'),k6_relat_1(k1_relat_1('#skF_2')))) = k6_relat_1(k1_relat_1('#skF_2'))
    | ~ v1_relat_1(k6_relat_1(k1_relat_1('#skF_2')))
    | ~ v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1('#skF_2')
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4648,c_2646])).

tff(c_4857,plain,(
    k5_relat_1('#skF_2',k2_funct_1('#skF_2')) = k6_relat_1(k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_700,c_46,c_742,c_1294,c_1424,c_4701])).

tff(c_26,plain,(
    ! [A_16,B_18] :
      ( v2_funct_1(A_16)
      | k2_relat_1(B_18) != k1_relat_1(A_16)
      | ~ v2_funct_1(k5_relat_1(B_18,A_16))
      | ~ v1_funct_1(B_18)
      | ~ v1_relat_1(B_18)
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_5429,plain,
    ( v2_funct_1(k2_funct_1('#skF_2'))
    | k1_relat_1(k2_funct_1('#skF_2')) != k2_relat_1('#skF_2')
    | ~ v2_funct_1(k6_relat_1(k1_relat_1('#skF_2')))
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4857,c_26])).

tff(c_5460,plain,(
    v2_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_742,c_2101,c_46,c_44,c_1968,c_738,c_5429])).

tff(c_5479,plain,
    ( k4_relat_1(k2_funct_1('#skF_2')) = k2_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_5460,c_16])).

tff(c_5482,plain,(
    k4_relat_1(k2_funct_1('#skF_2')) = k2_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_742,c_2101,c_5479])).

tff(c_5497,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1('#skF_2')))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5482,c_2])).

tff(c_5509,plain,(
    v1_relat_1(k2_funct_1(k2_funct_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_742,c_5497])).

tff(c_367,plain,(
    ! [A_45] :
      ( k5_relat_1(k2_funct_1(A_45),A_45) = k6_relat_1(k2_relat_1(A_45))
      | ~ v2_funct_1(A_45)
      | ~ v1_funct_1(A_45)
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_376,plain,(
    ! [A_45] :
      ( v1_relat_1(k6_relat_1(k2_relat_1(A_45)))
      | ~ v1_funct_1(A_45)
      | ~ v1_relat_1(A_45)
      | ~ v1_funct_1(k2_funct_1(A_45))
      | ~ v1_relat_1(k2_funct_1(A_45))
      | ~ v2_funct_1(A_45)
      | ~ v1_funct_1(A_45)
      | ~ v1_relat_1(A_45) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_367,c_24])).

tff(c_2298,plain,(
    ! [A_74,C_75] :
      ( k5_relat_1(A_74,k5_relat_1(k6_relat_1(k2_relat_1(A_74)),C_75)) = k5_relat_1(A_74,C_75)
      | ~ v1_relat_1(C_75)
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(A_74)))
      | ~ v1_relat_1(A_74)
      | ~ v1_relat_1(A_74) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_382])).

tff(c_2365,plain,(
    ! [C_75] :
      ( k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1(k6_relat_1(k1_relat_1('#skF_1')),C_75)) = k5_relat_1(k2_funct_1('#skF_1'),C_75)
      | ~ v1_relat_1(C_75)
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(k2_funct_1('#skF_1'))))
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v1_relat_1(k2_funct_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_262,c_2298])).

tff(c_2679,plain,(
    ! [C_78] :
      ( k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1(k5_relat_1('#skF_1','#skF_2'),C_78)) = k5_relat_1(k2_funct_1('#skF_1'),C_78)
      | ~ v1_relat_1(C_78) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_264,c_239,c_38,c_262,c_38,c_2365])).

tff(c_2713,plain,(
    ! [C_9] :
      ( k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1',k5_relat_1('#skF_2',C_9))) = k5_relat_1(k2_funct_1('#skF_1'),C_9)
      | ~ v1_relat_1(C_9)
      | ~ v1_relat_1(C_9)
      | ~ v1_relat_1('#skF_2')
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_2679])).

tff(c_2859,plain,(
    ! [C_80] :
      ( k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1',k5_relat_1('#skF_2',C_80))) = k5_relat_1(k2_funct_1('#skF_1'),C_80)
      | ~ v1_relat_1(C_80) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_2713])).

tff(c_2897,plain,
    ( k5_relat_1(k2_funct_1('#skF_1'),k6_relat_1(k2_relat_1('#skF_2'))) = k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1(k2_relat_1('#skF_2')))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_2859])).

tff(c_2919,plain,
    ( k5_relat_1(k2_funct_1('#skF_1'),k6_relat_1(k2_relat_1('#skF_2'))) = k2_funct_1('#skF_1')
    | ~ v1_relat_1(k6_relat_1(k2_relat_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_286,c_2897])).

tff(c_3003,plain,(
    ~ v1_relat_1(k6_relat_1(k2_relat_1('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_2919])).

tff(c_3006,plain,
    ( ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_376,c_3003])).

tff(c_3010,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_700,c_742,c_2101,c_3006])).

tff(c_3012,plain,(
    v1_relat_1(k6_relat_1(k2_relat_1('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_2919])).

tff(c_373,plain,(
    ! [A_45] :
      ( v1_funct_1(k6_relat_1(k2_relat_1(A_45)))
      | ~ v1_funct_1(A_45)
      | ~ v1_relat_1(A_45)
      | ~ v1_funct_1(k2_funct_1(A_45))
      | ~ v1_relat_1(k2_funct_1(A_45))
      | ~ v2_funct_1(A_45)
      | ~ v1_funct_1(A_45)
      | ~ v1_relat_1(A_45) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_367,c_22])).

tff(c_127,plain,(
    ! [A_10] :
      ( k5_relat_1(k6_relat_1(A_10),k6_relat_1(A_10)) = k6_relat_1(A_10)
      | ~ v1_relat_1(k6_relat_1(A_10)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_112])).

tff(c_575,plain,(
    ! [A_10] :
      ( v2_funct_1(k6_relat_1(A_10))
      | k6_relat_1(k1_relat_1(k6_relat_1(A_10))) != k6_relat_1(A_10)
      | ~ v1_funct_1(k6_relat_1(A_10))
      | ~ v1_relat_1(k6_relat_1(A_10))
      | ~ v1_funct_1(k6_relat_1(A_10))
      | ~ v1_relat_1(k6_relat_1(A_10))
      | ~ v1_relat_1(k6_relat_1(A_10)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_559])).

tff(c_2046,plain,(
    ! [A_72] :
      ( v2_funct_1(k6_relat_1(A_72))
      | ~ v1_funct_1(k6_relat_1(A_72))
      | ~ v1_relat_1(k6_relat_1(A_72)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_575])).

tff(c_2053,plain,(
    ! [A_72] :
      ( k4_relat_1(k6_relat_1(A_72)) = k2_funct_1(k6_relat_1(A_72))
      | ~ v1_funct_1(k6_relat_1(A_72))
      | ~ v1_relat_1(k6_relat_1(A_72)) ) ),
    inference(resolution,[status(thm)],[c_2046,c_16])).

tff(c_3093,plain,
    ( k4_relat_1(k6_relat_1(k2_relat_1('#skF_2'))) = k2_funct_1(k6_relat_1(k2_relat_1('#skF_2')))
    | ~ v1_funct_1(k6_relat_1(k2_relat_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_3012,c_2053])).

tff(c_3743,plain,(
    ~ v1_funct_1(k6_relat_1(k2_relat_1('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_3093])).

tff(c_3778,plain,
    ( ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_373,c_3743])).

tff(c_3782,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_700,c_742,c_2101,c_3778])).

tff(c_3784,plain,(
    v1_funct_1(k6_relat_1(k2_relat_1('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_3093])).

tff(c_600,plain,(
    ! [A_10] :
      ( v2_funct_1(k6_relat_1(A_10))
      | ~ v1_funct_1(k6_relat_1(A_10))
      | ~ v1_relat_1(k6_relat_1(A_10)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_575])).

tff(c_3783,plain,(
    k4_relat_1(k6_relat_1(k2_relat_1('#skF_2'))) = k2_funct_1(k6_relat_1(k2_relat_1('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_3093])).

tff(c_3797,plain,
    ( v1_relat_1(k2_funct_1(k6_relat_1(k2_relat_1('#skF_2'))))
    | ~ v1_relat_1(k6_relat_1(k2_relat_1('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_3783,c_2])).

tff(c_3807,plain,(
    v1_relat_1(k2_funct_1(k6_relat_1(k2_relat_1('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3012,c_3797])).

tff(c_3794,plain,
    ( k2_relat_1(k2_funct_1(k6_relat_1(k2_relat_1('#skF_2')))) = k1_relat_1(k6_relat_1(k2_relat_1('#skF_2')))
    | ~ v1_relat_1(k6_relat_1(k2_relat_1('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_3783,c_4])).

tff(c_3805,plain,(
    k2_relat_1(k2_funct_1(k6_relat_1(k2_relat_1('#skF_2')))) = k2_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3012,c_10,c_3794])).

tff(c_3972,plain,
    ( k5_relat_1(k2_funct_1(k6_relat_1(k2_relat_1('#skF_2'))),k6_relat_1(k2_relat_1('#skF_2'))) = k2_funct_1(k6_relat_1(k2_relat_1('#skF_2')))
    | ~ v1_relat_1(k2_funct_1(k6_relat_1(k2_relat_1('#skF_2')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_3805,c_14])).

tff(c_3984,plain,(
    k5_relat_1(k2_funct_1(k6_relat_1(k2_relat_1('#skF_2'))),k6_relat_1(k2_relat_1('#skF_2'))) = k2_funct_1(k6_relat_1(k2_relat_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3807,c_3972])).

tff(c_4063,plain,
    ( k6_relat_1(k2_relat_1(k6_relat_1(k2_relat_1('#skF_2')))) = k2_funct_1(k6_relat_1(k2_relat_1('#skF_2')))
    | ~ v2_funct_1(k6_relat_1(k2_relat_1('#skF_2')))
    | ~ v1_funct_1(k6_relat_1(k2_relat_1('#skF_2')))
    | ~ v1_relat_1(k6_relat_1(k2_relat_1('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_3984,c_32])).

tff(c_4084,plain,
    ( k2_funct_1(k6_relat_1(k2_relat_1('#skF_2'))) = k6_relat_1(k2_relat_1('#skF_2'))
    | ~ v2_funct_1(k6_relat_1(k2_relat_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3012,c_3784,c_12,c_4063])).

tff(c_4092,plain,(
    ~ v2_funct_1(k6_relat_1(k2_relat_1('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_4084])).

tff(c_4096,plain,
    ( ~ v1_funct_1(k6_relat_1(k2_relat_1('#skF_2')))
    | ~ v1_relat_1(k6_relat_1(k2_relat_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_600,c_4092])).

tff(c_4100,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3012,c_3784,c_4096])).

tff(c_4101,plain,(
    k2_funct_1(k6_relat_1(k2_relat_1('#skF_2'))) = k6_relat_1(k2_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_4084])).

tff(c_4109,plain,(
    k5_relat_1(k6_relat_1(k2_relat_1('#skF_2')),k6_relat_1(k2_relat_1('#skF_2'))) = k6_relat_1(k2_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4101,c_4101,c_3984])).

tff(c_5494,plain,
    ( k2_relat_1(k2_funct_1(k2_funct_1('#skF_2'))) = k1_relat_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5482,c_4])).

tff(c_5507,plain,(
    k2_relat_1(k2_funct_1(k2_funct_1('#skF_2'))) = k2_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_742,c_738,c_5494])).

tff(c_5664,plain,
    ( k5_relat_1(k2_funct_1(k2_funct_1('#skF_2')),k6_relat_1(k2_relat_1('#skF_2'))) = k2_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_5507,c_14])).

tff(c_5676,plain,(
    k5_relat_1(k2_funct_1(k2_funct_1('#skF_2')),k6_relat_1(k2_relat_1('#skF_2'))) = k2_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5509,c_5664])).

tff(c_417,plain,(
    ! [A_22,C_48] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_22)),C_48) = k5_relat_1(A_22,k5_relat_1(k2_funct_1(A_22),C_48))
      | ~ v1_relat_1(C_48)
      | ~ v1_relat_1(k2_funct_1(A_22))
      | ~ v1_relat_1(A_22)
      | ~ v2_funct_1(A_22)
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_382])).

tff(c_8725,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(k2_funct_1('#skF_2'))),k6_relat_1(k2_relat_1('#skF_2'))) = k5_relat_1(k2_funct_1('#skF_2'),k2_funct_1(k2_funct_1('#skF_2')))
    | ~ v1_relat_1(k6_relat_1(k2_relat_1('#skF_2')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_2')))
    | ~ v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v2_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5676,c_417])).

tff(c_8757,plain,(
    k5_relat_1(k2_funct_1('#skF_2'),k2_funct_1(k2_funct_1('#skF_2'))) = k6_relat_1(k2_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_742,c_2101,c_5460,c_742,c_5509,c_3012,c_4109,c_738,c_8725])).

tff(c_414,plain,(
    ! [A_22,C_48] :
      ( k5_relat_1(k6_relat_1(k2_relat_1(A_22)),C_48) = k5_relat_1(k2_funct_1(A_22),k5_relat_1(A_22,C_48))
      | ~ v1_relat_1(C_48)
      | ~ v1_relat_1(A_22)
      | ~ v1_relat_1(k2_funct_1(A_22))
      | ~ v2_funct_1(A_22)
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_382])).

tff(c_8785,plain,
    ( k5_relat_1(k6_relat_1(k2_relat_1(k2_funct_1('#skF_2'))),k2_funct_1(k2_funct_1('#skF_2'))) = k5_relat_1(k2_funct_1(k2_funct_1('#skF_2')),k6_relat_1(k2_relat_1('#skF_2')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_2')))
    | ~ v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_2')))
    | ~ v2_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_8757,c_414])).

tff(c_8821,plain,(
    k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')),k2_funct_1(k2_funct_1('#skF_2'))) = k2_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_742,c_2101,c_5460,c_5509,c_742,c_5509,c_5676,c_740,c_8785])).

tff(c_8859,plain,
    ( k5_relat_1('#skF_2',k5_relat_1(k2_funct_1('#skF_2'),k2_funct_1(k2_funct_1('#skF_2')))) = k2_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_2')))
    | ~ v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1('#skF_2')
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_8821,c_417])).

tff(c_8902,plain,(
    k5_relat_1('#skF_2',k6_relat_1(k2_relat_1('#skF_2'))) = k2_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_700,c_46,c_742,c_5509,c_8757,c_8859])).

tff(c_8973,plain,
    ( k2_funct_1(k2_funct_1('#skF_2')) = '#skF_2'
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_8902,c_14])).

tff(c_9010,plain,(
    k2_funct_1(k2_funct_1('#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_8973])).

tff(c_9058,plain,(
    k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')),'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9010,c_9010,c_8821])).

tff(c_5135,plain,(
    ! [A_103,C_104] :
      ( k5_relat_1(k6_relat_1(k2_relat_1(A_103)),C_104) = k5_relat_1(k2_funct_1(A_103),k5_relat_1(A_103,C_104))
      | ~ v1_relat_1(C_104)
      | ~ v1_relat_1(A_103)
      | ~ v1_relat_1(k2_funct_1(A_103))
      | ~ v2_funct_1(A_103)
      | ~ v1_funct_1(A_103)
      | ~ v1_relat_1(A_103) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_382])).

tff(c_5345,plain,(
    ! [C_104] :
      ( k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')),C_104) = k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1',C_104))
      | ~ v1_relat_1(C_104)
      | ~ v1_relat_1('#skF_1')
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v2_funct_1('#skF_1')
      | ~ v1_funct_1('#skF_1')
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_5135])).

tff(c_5408,plain,(
    ! [C_104] :
      ( k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')),C_104) = k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1',C_104))
      | ~ v1_relat_1(C_104) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_42,c_264,c_50,c_5345])).

tff(c_9423,plain,
    ( k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1','#skF_2')) = '#skF_2'
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_9058,c_5408])).

tff(c_9466,plain,(
    k2_funct_1('#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_286,c_9423])).

tff(c_9468,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_9466])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:39:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.67/2.90  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.67/2.93  
% 8.67/2.93  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.67/2.93  %$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1
% 8.67/2.93  
% 8.67/2.93  %Foreground sorts:
% 8.67/2.93  
% 8.67/2.93  
% 8.67/2.93  %Background operators:
% 8.67/2.93  
% 8.67/2.93  
% 8.67/2.93  %Foreground operators:
% 8.67/2.93  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.67/2.93  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 8.67/2.93  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 8.67/2.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.67/2.93  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 8.67/2.93  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.67/2.93  tff('#skF_2', type, '#skF_2': $i).
% 8.67/2.93  tff('#skF_1', type, '#skF_1': $i).
% 8.67/2.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.67/2.93  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.67/2.93  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 8.67/2.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.67/2.93  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.67/2.93  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 8.67/2.93  
% 8.67/2.96  tff(f_139, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(A) = k1_relat_1(B))) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_funct_1)).
% 8.67/2.96  tff(f_61, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 8.67/2.96  tff(f_29, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 8.67/2.96  tff(f_35, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_relat_1)).
% 8.67/2.96  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 8.67/2.96  tff(f_81, axiom, (![A, B]: ((((v1_relat_1(A) & v1_funct_1(A)) & v1_relat_1(B)) & v1_funct_1(B)) => (v1_relat_1(k5_relat_1(A, B)) & v1_funct_1(k5_relat_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_funct_1)).
% 8.67/2.96  tff(f_49, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 8.67/2.96  tff(f_111, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((?[B]: ((v1_relat_1(B) & v1_funct_1(B)) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A))))) => v2_funct_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_funct_1)).
% 8.67/2.96  tff(f_98, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & (k2_relat_1(B) = k1_relat_1(A))) => (v2_funct_1(B) & v2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_funct_1)).
% 8.67/2.96  tff(f_69, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 8.67/2.96  tff(f_121, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 8.67/2.96  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 8.67/2.96  tff(c_36, plain, (k2_funct_1('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_139])).
% 8.67/2.96  tff(c_46, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_139])).
% 8.67/2.96  tff(c_50, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_139])).
% 8.67/2.96  tff(c_48, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_139])).
% 8.67/2.96  tff(c_42, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_139])).
% 8.67/2.96  tff(c_240, plain, (![A_38]: (k4_relat_1(A_38)=k2_funct_1(A_38) | ~v2_funct_1(A_38) | ~v1_funct_1(A_38) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.67/2.96  tff(c_243, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_42, c_240])).
% 8.67/2.96  tff(c_246, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_243])).
% 8.67/2.96  tff(c_2, plain, (![A_1]: (v1_relat_1(k4_relat_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.67/2.96  tff(c_256, plain, (v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_246, c_2])).
% 8.67/2.96  tff(c_264, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_256])).
% 8.67/2.96  tff(c_38, plain, (k6_relat_1(k1_relat_1('#skF_1'))=k5_relat_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_139])).
% 8.67/2.96  tff(c_4, plain, (![A_2]: (k2_relat_1(k4_relat_1(A_2))=k1_relat_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.67/2.96  tff(c_253, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_246, c_4])).
% 8.67/2.96  tff(c_262, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_253])).
% 8.67/2.96  tff(c_14, plain, (![A_11]: (k5_relat_1(A_11, k6_relat_1(k2_relat_1(A_11)))=A_11 | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.67/2.96  tff(c_282, plain, (k5_relat_1(k2_funct_1('#skF_1'), k6_relat_1(k1_relat_1('#skF_1')))=k2_funct_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_262, c_14])).
% 8.67/2.96  tff(c_286, plain, (k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', '#skF_2'))=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_264, c_38, c_282])).
% 8.67/2.96  tff(c_44, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_139])).
% 8.67/2.96  tff(c_40, plain, (k2_relat_1('#skF_1')=k1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_139])).
% 8.67/2.96  tff(c_22, plain, (![A_14, B_15]: (v1_funct_1(k5_relat_1(A_14, B_15)) | ~v1_funct_1(B_15) | ~v1_relat_1(B_15) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.67/2.96  tff(c_218, plain, (![A_36, B_37]: (v1_relat_1(k5_relat_1(A_36, B_37)) | ~v1_funct_1(B_37) | ~v1_relat_1(B_37) | ~v1_funct_1(A_36) | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.67/2.96  tff(c_12, plain, (![A_10]: (k2_relat_1(k6_relat_1(A_10))=A_10)), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.67/2.96  tff(c_76, plain, (k2_relat_1(k5_relat_1('#skF_1', '#skF_2'))=k1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_38, c_12])).
% 8.67/2.96  tff(c_112, plain, (![A_31]: (k5_relat_1(A_31, k6_relat_1(k2_relat_1(A_31)))=A_31 | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.67/2.96  tff(c_124, plain, (k5_relat_1(k5_relat_1('#skF_1', '#skF_2'), k6_relat_1(k1_relat_1('#skF_1')))=k5_relat_1('#skF_1', '#skF_2') | ~v1_relat_1(k5_relat_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_76, c_112])).
% 8.67/2.96  tff(c_133, plain, (k5_relat_1(k5_relat_1('#skF_1', '#skF_2'), k5_relat_1('#skF_1', '#skF_2'))=k5_relat_1('#skF_1', '#skF_2') | ~v1_relat_1(k5_relat_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_124])).
% 8.67/2.96  tff(c_140, plain, (~v1_relat_1(k5_relat_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_133])).
% 8.67/2.96  tff(c_221, plain, (~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_218, c_140])).
% 8.67/2.96  tff(c_237, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_221])).
% 8.67/2.96  tff(c_239, plain, (v1_relat_1(k5_relat_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_133])).
% 8.67/2.96  tff(c_10, plain, (![A_10]: (k1_relat_1(k6_relat_1(A_10))=A_10)), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.67/2.96  tff(c_79, plain, (k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))=k1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_38, c_10])).
% 8.67/2.96  tff(c_297, plain, (![A_41]: (k5_relat_1(k6_relat_1(A_41), k6_relat_1(A_41))=k6_relat_1(A_41) | ~v1_relat_1(k6_relat_1(A_41)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_112])).
% 8.67/2.96  tff(c_309, plain, (k5_relat_1(k5_relat_1('#skF_1', '#skF_2'), k6_relat_1(k1_relat_1('#skF_1')))=k6_relat_1(k1_relat_1('#skF_1')) | ~v1_relat_1(k6_relat_1(k1_relat_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_38, c_297])).
% 8.67/2.96  tff(c_316, plain, (k5_relat_1(k5_relat_1('#skF_1', '#skF_2'), k5_relat_1('#skF_1', '#skF_2'))=k5_relat_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_239, c_38, c_38, c_38, c_309])).
% 8.67/2.96  tff(c_559, plain, (![A_50, B_51]: (v2_funct_1(A_50) | k6_relat_1(k1_relat_1(A_50))!=k5_relat_1(A_50, B_51) | ~v1_funct_1(B_51) | ~v1_relat_1(B_51) | ~v1_funct_1(A_50) | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_111])).
% 8.67/2.96  tff(c_573, plain, (v2_funct_1(k5_relat_1('#skF_1', '#skF_2')) | k6_relat_1(k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))!=k5_relat_1('#skF_1', '#skF_2') | ~v1_funct_1(k5_relat_1('#skF_1', '#skF_2')) | ~v1_relat_1(k5_relat_1('#skF_1', '#skF_2')) | ~v1_funct_1(k5_relat_1('#skF_1', '#skF_2')) | ~v1_relat_1(k5_relat_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_316, c_559])).
% 8.67/2.96  tff(c_598, plain, (v2_funct_1(k5_relat_1('#skF_1', '#skF_2')) | ~v1_funct_1(k5_relat_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_239, c_239, c_38, c_79, c_573])).
% 8.67/2.96  tff(c_611, plain, (~v1_funct_1(k5_relat_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_598])).
% 8.67/2.96  tff(c_614, plain, (~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_22, c_611])).
% 8.67/2.96  tff(c_618, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_614])).
% 8.67/2.96  tff(c_619, plain, (v2_funct_1(k5_relat_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_598])).
% 8.67/2.96  tff(c_664, plain, (![A_52, B_53]: (v2_funct_1(A_52) | k2_relat_1(B_53)!=k1_relat_1(A_52) | ~v2_funct_1(k5_relat_1(B_53, A_52)) | ~v1_funct_1(B_53) | ~v1_relat_1(B_53) | ~v1_funct_1(A_52) | ~v1_relat_1(A_52))), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.67/2.96  tff(c_667, plain, (v2_funct_1('#skF_2') | k2_relat_1('#skF_1')!=k1_relat_1('#skF_2') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_619, c_664])).
% 8.67/2.96  tff(c_700, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_50, c_48, c_40, c_667])).
% 8.67/2.96  tff(c_16, plain, (![A_12]: (k4_relat_1(A_12)=k2_funct_1(A_12) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.67/2.96  tff(c_716, plain, (k4_relat_1('#skF_2')=k2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_700, c_16])).
% 8.67/2.96  tff(c_719, plain, (k4_relat_1('#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_716])).
% 8.67/2.96  tff(c_732, plain, (v1_relat_1(k2_funct_1('#skF_2')) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_719, c_2])).
% 8.67/2.96  tff(c_742, plain, (v1_relat_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_732])).
% 8.67/2.96  tff(c_18, plain, (![A_13]: (v1_funct_1(k2_funct_1(A_13)) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.67/2.96  tff(c_130, plain, (k5_relat_1('#skF_1', k6_relat_1(k1_relat_1('#skF_2')))='#skF_1' | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_40, c_112])).
% 8.67/2.96  tff(c_135, plain, (k5_relat_1('#skF_1', k6_relat_1(k1_relat_1('#skF_2')))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_130])).
% 8.67/2.96  tff(c_694, plain, (v2_funct_1(k6_relat_1(k1_relat_1('#skF_2'))) | k1_relat_1(k6_relat_1(k1_relat_1('#skF_2')))!=k2_relat_1('#skF_1') | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1') | ~v1_funct_1(k6_relat_1(k1_relat_1('#skF_2'))) | ~v1_relat_1(k6_relat_1(k1_relat_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_135, c_664])).
% 8.67/2.96  tff(c_711, plain, (v2_funct_1(k6_relat_1(k1_relat_1('#skF_2'))) | ~v1_funct_1(k6_relat_1(k1_relat_1('#skF_2'))) | ~v1_relat_1(k6_relat_1(k1_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_42, c_40, c_10, c_694])).
% 8.67/2.96  tff(c_744, plain, (~v1_relat_1(k6_relat_1(k1_relat_1('#skF_2')))), inference(splitLeft, [status(thm)], [c_711])).
% 8.67/2.96  tff(c_32, plain, (![A_22]: (k5_relat_1(k2_funct_1(A_22), A_22)=k6_relat_1(k2_relat_1(A_22)) | ~v2_funct_1(A_22) | ~v1_funct_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_121])).
% 8.67/2.96  tff(c_34, plain, (![A_22]: (k5_relat_1(A_22, k2_funct_1(A_22))=k6_relat_1(k1_relat_1(A_22)) | ~v2_funct_1(A_22) | ~v1_funct_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_121])).
% 8.67/2.96  tff(c_8, plain, (![A_3, B_7, C_9]: (k5_relat_1(k5_relat_1(A_3, B_7), C_9)=k5_relat_1(A_3, k5_relat_1(B_7, C_9)) | ~v1_relat_1(C_9) | ~v1_relat_1(B_7) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.67/2.96  tff(c_382, plain, (![A_46, B_47, C_48]: (k5_relat_1(k5_relat_1(A_46, B_47), C_48)=k5_relat_1(A_46, k5_relat_1(B_47, C_48)) | ~v1_relat_1(C_48) | ~v1_relat_1(B_47) | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.67/2.96  tff(c_433, plain, (![C_48]: (k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1(k5_relat_1('#skF_1', '#skF_2'), C_48))=k5_relat_1(k2_funct_1('#skF_1'), C_48) | ~v1_relat_1(C_48) | ~v1_relat_1(k5_relat_1('#skF_1', '#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_286, c_382])).
% 8.67/2.96  tff(c_1027, plain, (![C_58]: (k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1(k5_relat_1('#skF_1', '#skF_2'), C_58))=k5_relat_1(k2_funct_1('#skF_1'), C_58) | ~v1_relat_1(C_58))), inference(demodulation, [status(thm), theory('equality')], [c_264, c_239, c_433])).
% 8.67/2.96  tff(c_1054, plain, (![C_9]: (k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', k5_relat_1('#skF_2', C_9)))=k5_relat_1(k2_funct_1('#skF_1'), C_9) | ~v1_relat_1(C_9) | ~v1_relat_1(C_9) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_8, c_1027])).
% 8.67/2.96  tff(c_1088, plain, (![C_59]: (k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', k5_relat_1('#skF_2', C_59)))=k5_relat_1(k2_funct_1('#skF_1'), C_59) | ~v1_relat_1(C_59))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_1054])).
% 8.67/2.96  tff(c_1118, plain, (k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', k6_relat_1(k1_relat_1('#skF_2'))))=k5_relat_1(k2_funct_1('#skF_1'), k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_34, c_1088])).
% 8.67/2.96  tff(c_1140, plain, (k5_relat_1(k2_funct_1('#skF_1'), k2_funct_1('#skF_2'))=k5_relat_1(k2_funct_1('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_700, c_742, c_135, c_1118])).
% 8.67/2.96  tff(c_1157, plain, (v1_funct_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1140, c_22])).
% 8.67/2.96  tff(c_1172, plain, (v1_funct_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_264, c_742, c_1157])).
% 8.67/2.96  tff(c_1176, plain, (~v1_funct_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_1172])).
% 8.67/2.96  tff(c_1179, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_18, c_1176])).
% 8.67/2.96  tff(c_1183, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_1179])).
% 8.67/2.96  tff(c_1185, plain, (v1_funct_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_1172])).
% 8.67/2.96  tff(c_1184, plain, (~v1_funct_1(k2_funct_1('#skF_2')) | v1_funct_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))), inference(splitRight, [status(thm)], [c_1172])).
% 8.67/2.96  tff(c_1186, plain, (~v1_funct_1(k2_funct_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_1184])).
% 8.67/2.96  tff(c_1272, plain, (~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_18, c_1186])).
% 8.67/2.96  tff(c_1276, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_1272])).
% 8.67/2.96  tff(c_1278, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(splitRight, [status(thm)], [c_1184])).
% 8.67/2.96  tff(c_24, plain, (![A_14, B_15]: (v1_relat_1(k5_relat_1(A_14, B_15)) | ~v1_funct_1(B_15) | ~v1_relat_1(B_15) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.67/2.96  tff(c_1160, plain, (v1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1140, c_24])).
% 8.67/2.96  tff(c_1174, plain, (v1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_264, c_742, c_1160])).
% 8.67/2.96  tff(c_1285, plain, (v1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1185, c_1278, c_1174])).
% 8.67/2.96  tff(c_1288, plain, (v1_relat_1(k6_relat_1(k2_relat_1('#skF_1'))) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_32, c_1285])).
% 8.67/2.96  tff(c_1290, plain, (v1_relat_1(k6_relat_1(k1_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_42, c_40, c_1288])).
% 8.67/2.96  tff(c_1292, plain, $false, inference(negUnitSimplification, [status(thm)], [c_744, c_1290])).
% 8.67/2.96  tff(c_1294, plain, (v1_relat_1(k6_relat_1(k1_relat_1('#skF_2')))), inference(splitRight, [status(thm)], [c_711])).
% 8.67/2.96  tff(c_1293, plain, (~v1_funct_1(k6_relat_1(k1_relat_1('#skF_2'))) | v2_funct_1(k6_relat_1(k1_relat_1('#skF_2')))), inference(splitRight, [status(thm)], [c_711])).
% 8.67/2.96  tff(c_1448, plain, (~v1_funct_1(k6_relat_1(k1_relat_1('#skF_2')))), inference(splitLeft, [status(thm)], [c_1293])).
% 8.67/2.96  tff(c_1756, plain, (![C_68]: (k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1(k5_relat_1('#skF_1', '#skF_2'), C_68))=k5_relat_1(k2_funct_1('#skF_1'), C_68) | ~v1_relat_1(C_68))), inference(demodulation, [status(thm), theory('equality')], [c_264, c_239, c_433])).
% 8.67/2.96  tff(c_1786, plain, (![C_9]: (k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', k5_relat_1('#skF_2', C_9)))=k5_relat_1(k2_funct_1('#skF_1'), C_9) | ~v1_relat_1(C_9) | ~v1_relat_1(C_9) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_8, c_1756])).
% 8.67/2.96  tff(c_1821, plain, (![C_69]: (k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', k5_relat_1('#skF_2', C_69)))=k5_relat_1(k2_funct_1('#skF_1'), C_69) | ~v1_relat_1(C_69))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_1786])).
% 8.67/2.96  tff(c_1851, plain, (k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', k6_relat_1(k1_relat_1('#skF_2'))))=k5_relat_1(k2_funct_1('#skF_1'), k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_34, c_1821])).
% 8.67/2.96  tff(c_1873, plain, (k5_relat_1(k2_funct_1('#skF_1'), k2_funct_1('#skF_2'))=k5_relat_1(k2_funct_1('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_700, c_742, c_135, c_1851])).
% 8.67/2.96  tff(c_1890, plain, (v1_funct_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1873, c_22])).
% 8.67/2.96  tff(c_1905, plain, (v1_funct_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_264, c_742, c_1890])).
% 8.67/2.96  tff(c_1909, plain, (~v1_funct_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_1905])).
% 8.67/2.96  tff(c_1943, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_18, c_1909])).
% 8.67/2.96  tff(c_1947, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_1943])).
% 8.67/2.96  tff(c_1948, plain, (~v1_funct_1(k2_funct_1('#skF_2')) | v1_funct_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))), inference(splitRight, [status(thm)], [c_1905])).
% 8.67/2.96  tff(c_1950, plain, (~v1_funct_1(k2_funct_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_1948])).
% 8.67/2.96  tff(c_1954, plain, (~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_18, c_1950])).
% 8.67/2.96  tff(c_1958, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_1954])).
% 8.67/2.96  tff(c_1959, plain, (v1_funct_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))), inference(splitRight, [status(thm)], [c_1948])).
% 8.67/2.96  tff(c_1963, plain, (v1_funct_1(k6_relat_1(k2_relat_1('#skF_1'))) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_32, c_1959])).
% 8.67/2.96  tff(c_1965, plain, (v1_funct_1(k6_relat_1(k1_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_42, c_40, c_1963])).
% 8.67/2.96  tff(c_1967, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1448, c_1965])).
% 8.67/2.96  tff(c_1969, plain, (v1_funct_1(k6_relat_1(k1_relat_1('#skF_2')))), inference(splitRight, [status(thm)], [c_1293])).
% 8.67/2.96  tff(c_6, plain, (![A_2]: (k1_relat_1(k4_relat_1(A_2))=k2_relat_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.67/2.96  tff(c_726, plain, (k1_relat_1(k2_funct_1('#skF_2'))=k2_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_719, c_6])).
% 8.67/2.96  tff(c_738, plain, (k1_relat_1(k2_funct_1('#skF_2'))=k2_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_726])).
% 8.67/2.96  tff(c_729, plain, (k2_relat_1(k2_funct_1('#skF_2'))=k1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_719, c_4])).
% 8.67/2.96  tff(c_740, plain, (k2_relat_1(k2_funct_1('#skF_2'))=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_729])).
% 8.67/2.96  tff(c_1420, plain, (k5_relat_1(k2_funct_1('#skF_2'), k6_relat_1(k1_relat_1('#skF_2')))=k2_funct_1('#skF_2') | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_740, c_14])).
% 8.67/2.96  tff(c_1424, plain, (k5_relat_1(k2_funct_1('#skF_2'), k6_relat_1(k1_relat_1('#skF_2')))=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_742, c_1420])).
% 8.67/2.96  tff(c_30, plain, (![A_19, B_21]: (v2_funct_1(A_19) | k6_relat_1(k1_relat_1(A_19))!=k5_relat_1(A_19, B_21) | ~v1_funct_1(B_21) | ~v1_relat_1(B_21) | ~v1_funct_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_111])).
% 8.67/2.96  tff(c_2021, plain, (v2_funct_1(k2_funct_1('#skF_2')) | k6_relat_1(k1_relat_1(k2_funct_1('#skF_2')))!=k2_funct_1('#skF_2') | ~v1_funct_1(k6_relat_1(k1_relat_1('#skF_2'))) | ~v1_relat_1(k6_relat_1(k1_relat_1('#skF_2'))) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1424, c_30])).
% 8.67/2.96  tff(c_2038, plain, (v2_funct_1(k2_funct_1('#skF_2')) | k6_relat_1(k2_relat_1('#skF_2'))!=k2_funct_1('#skF_2') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_742, c_1294, c_1969, c_738, c_2021])).
% 8.67/2.96  tff(c_2092, plain, (~v1_funct_1(k2_funct_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_2038])).
% 8.67/2.96  tff(c_2095, plain, (~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_18, c_2092])).
% 8.67/2.96  tff(c_2099, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_2095])).
% 8.67/2.96  tff(c_2101, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(splitRight, [status(thm)], [c_2038])).
% 8.67/2.96  tff(c_1968, plain, (v2_funct_1(k6_relat_1(k1_relat_1('#skF_2')))), inference(splitRight, [status(thm)], [c_1293])).
% 8.67/2.96  tff(c_4648, plain, (![A_100, C_101]: (k5_relat_1(k6_relat_1(k1_relat_1(A_100)), C_101)=k5_relat_1(A_100, k5_relat_1(k2_funct_1(A_100), C_101)) | ~v1_relat_1(C_101) | ~v1_relat_1(k2_funct_1(A_100)) | ~v1_relat_1(A_100) | ~v2_funct_1(A_100) | ~v1_funct_1(A_100) | ~v1_relat_1(A_100))), inference(superposition, [status(thm), theory('equality')], [c_34, c_382])).
% 8.67/2.96  tff(c_1972, plain, (k4_relat_1(k6_relat_1(k1_relat_1('#skF_2')))=k2_funct_1(k6_relat_1(k1_relat_1('#skF_2'))) | ~v1_funct_1(k6_relat_1(k1_relat_1('#skF_2'))) | ~v1_relat_1(k6_relat_1(k1_relat_1('#skF_2')))), inference(resolution, [status(thm)], [c_1968, c_16])).
% 8.67/2.96  tff(c_1975, plain, (k4_relat_1(k6_relat_1(k1_relat_1('#skF_2')))=k2_funct_1(k6_relat_1(k1_relat_1('#skF_2'))) | ~v1_funct_1(k6_relat_1(k1_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_1294, c_1972])).
% 8.67/2.96  tff(c_2104, plain, (k4_relat_1(k6_relat_1(k1_relat_1('#skF_2')))=k2_funct_1(k6_relat_1(k1_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_1969, c_1975])).
% 8.67/2.96  tff(c_2117, plain, (v1_relat_1(k2_funct_1(k6_relat_1(k1_relat_1('#skF_2')))) | ~v1_relat_1(k6_relat_1(k1_relat_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_2104, c_2])).
% 8.67/2.96  tff(c_2127, plain, (v1_relat_1(k2_funct_1(k6_relat_1(k1_relat_1('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_1294, c_2117])).
% 8.67/2.96  tff(c_2114, plain, (k2_relat_1(k2_funct_1(k6_relat_1(k1_relat_1('#skF_2'))))=k1_relat_1(k6_relat_1(k1_relat_1('#skF_2'))) | ~v1_relat_1(k6_relat_1(k1_relat_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_2104, c_4])).
% 8.67/2.96  tff(c_2125, plain, (k2_relat_1(k2_funct_1(k6_relat_1(k1_relat_1('#skF_2'))))=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1294, c_10, c_2114])).
% 8.67/2.96  tff(c_2224, plain, (k5_relat_1(k2_funct_1(k6_relat_1(k1_relat_1('#skF_2'))), k6_relat_1(k1_relat_1('#skF_2')))=k2_funct_1(k6_relat_1(k1_relat_1('#skF_2'))) | ~v1_relat_1(k2_funct_1(k6_relat_1(k1_relat_1('#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_2125, c_14])).
% 8.67/2.96  tff(c_2228, plain, (k5_relat_1(k2_funct_1(k6_relat_1(k1_relat_1('#skF_2'))), k6_relat_1(k1_relat_1('#skF_2')))=k2_funct_1(k6_relat_1(k1_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_2127, c_2224])).
% 8.67/2.96  tff(c_2617, plain, (k6_relat_1(k2_relat_1(k6_relat_1(k1_relat_1('#skF_2'))))=k2_funct_1(k6_relat_1(k1_relat_1('#skF_2'))) | ~v2_funct_1(k6_relat_1(k1_relat_1('#skF_2'))) | ~v1_funct_1(k6_relat_1(k1_relat_1('#skF_2'))) | ~v1_relat_1(k6_relat_1(k1_relat_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_2228, c_32])).
% 8.67/2.96  tff(c_2638, plain, (k2_funct_1(k6_relat_1(k1_relat_1('#skF_2')))=k6_relat_1(k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1294, c_1969, c_1968, c_12, c_2617])).
% 8.67/2.96  tff(c_2646, plain, (k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')), k6_relat_1(k1_relat_1('#skF_2')))=k6_relat_1(k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2638, c_2638, c_2228])).
% 8.67/2.96  tff(c_4701, plain, (k5_relat_1('#skF_2', k5_relat_1(k2_funct_1('#skF_2'), k6_relat_1(k1_relat_1('#skF_2'))))=k6_relat_1(k1_relat_1('#skF_2')) | ~v1_relat_1(k6_relat_1(k1_relat_1('#skF_2'))) | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v1_relat_1('#skF_2') | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4648, c_2646])).
% 8.67/2.96  tff(c_4857, plain, (k5_relat_1('#skF_2', k2_funct_1('#skF_2'))=k6_relat_1(k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_700, c_46, c_742, c_1294, c_1424, c_4701])).
% 8.67/2.96  tff(c_26, plain, (![A_16, B_18]: (v2_funct_1(A_16) | k2_relat_1(B_18)!=k1_relat_1(A_16) | ~v2_funct_1(k5_relat_1(B_18, A_16)) | ~v1_funct_1(B_18) | ~v1_relat_1(B_18) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.67/2.96  tff(c_5429, plain, (v2_funct_1(k2_funct_1('#skF_2')) | k1_relat_1(k2_funct_1('#skF_2'))!=k2_relat_1('#skF_2') | ~v2_funct_1(k6_relat_1(k1_relat_1('#skF_2'))) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4857, c_26])).
% 8.67/2.96  tff(c_5460, plain, (v2_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_742, c_2101, c_46, c_44, c_1968, c_738, c_5429])).
% 8.67/2.96  tff(c_5479, plain, (k4_relat_1(k2_funct_1('#skF_2'))=k2_funct_1(k2_funct_1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_5460, c_16])).
% 8.67/2.96  tff(c_5482, plain, (k4_relat_1(k2_funct_1('#skF_2'))=k2_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_742, c_2101, c_5479])).
% 8.67/2.96  tff(c_5497, plain, (v1_relat_1(k2_funct_1(k2_funct_1('#skF_2'))) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_5482, c_2])).
% 8.67/2.96  tff(c_5509, plain, (v1_relat_1(k2_funct_1(k2_funct_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_742, c_5497])).
% 8.67/2.96  tff(c_367, plain, (![A_45]: (k5_relat_1(k2_funct_1(A_45), A_45)=k6_relat_1(k2_relat_1(A_45)) | ~v2_funct_1(A_45) | ~v1_funct_1(A_45) | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_121])).
% 8.67/2.96  tff(c_376, plain, (![A_45]: (v1_relat_1(k6_relat_1(k2_relat_1(A_45))) | ~v1_funct_1(A_45) | ~v1_relat_1(A_45) | ~v1_funct_1(k2_funct_1(A_45)) | ~v1_relat_1(k2_funct_1(A_45)) | ~v2_funct_1(A_45) | ~v1_funct_1(A_45) | ~v1_relat_1(A_45))), inference(superposition, [status(thm), theory('equality')], [c_367, c_24])).
% 8.67/2.96  tff(c_2298, plain, (![A_74, C_75]: (k5_relat_1(A_74, k5_relat_1(k6_relat_1(k2_relat_1(A_74)), C_75))=k5_relat_1(A_74, C_75) | ~v1_relat_1(C_75) | ~v1_relat_1(k6_relat_1(k2_relat_1(A_74))) | ~v1_relat_1(A_74) | ~v1_relat_1(A_74))), inference(superposition, [status(thm), theory('equality')], [c_14, c_382])).
% 8.67/2.96  tff(c_2365, plain, (![C_75]: (k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1(k6_relat_1(k1_relat_1('#skF_1')), C_75))=k5_relat_1(k2_funct_1('#skF_1'), C_75) | ~v1_relat_1(C_75) | ~v1_relat_1(k6_relat_1(k2_relat_1(k2_funct_1('#skF_1')))) | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_262, c_2298])).
% 8.67/2.96  tff(c_2679, plain, (![C_78]: (k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1(k5_relat_1('#skF_1', '#skF_2'), C_78))=k5_relat_1(k2_funct_1('#skF_1'), C_78) | ~v1_relat_1(C_78))), inference(demodulation, [status(thm), theory('equality')], [c_264, c_264, c_239, c_38, c_262, c_38, c_2365])).
% 8.67/2.96  tff(c_2713, plain, (![C_9]: (k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', k5_relat_1('#skF_2', C_9)))=k5_relat_1(k2_funct_1('#skF_1'), C_9) | ~v1_relat_1(C_9) | ~v1_relat_1(C_9) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_8, c_2679])).
% 8.67/2.96  tff(c_2859, plain, (![C_80]: (k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', k5_relat_1('#skF_2', C_80)))=k5_relat_1(k2_funct_1('#skF_1'), C_80) | ~v1_relat_1(C_80))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_2713])).
% 8.67/2.96  tff(c_2897, plain, (k5_relat_1(k2_funct_1('#skF_1'), k6_relat_1(k2_relat_1('#skF_2')))=k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1(k2_relat_1('#skF_2'))) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_14, c_2859])).
% 8.67/2.96  tff(c_2919, plain, (k5_relat_1(k2_funct_1('#skF_1'), k6_relat_1(k2_relat_1('#skF_2')))=k2_funct_1('#skF_1') | ~v1_relat_1(k6_relat_1(k2_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_286, c_2897])).
% 8.67/2.96  tff(c_3003, plain, (~v1_relat_1(k6_relat_1(k2_relat_1('#skF_2')))), inference(splitLeft, [status(thm)], [c_2919])).
% 8.67/2.96  tff(c_3006, plain, (~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_376, c_3003])).
% 8.67/2.96  tff(c_3010, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_700, c_742, c_2101, c_3006])).
% 8.67/2.96  tff(c_3012, plain, (v1_relat_1(k6_relat_1(k2_relat_1('#skF_2')))), inference(splitRight, [status(thm)], [c_2919])).
% 8.67/2.96  tff(c_373, plain, (![A_45]: (v1_funct_1(k6_relat_1(k2_relat_1(A_45))) | ~v1_funct_1(A_45) | ~v1_relat_1(A_45) | ~v1_funct_1(k2_funct_1(A_45)) | ~v1_relat_1(k2_funct_1(A_45)) | ~v2_funct_1(A_45) | ~v1_funct_1(A_45) | ~v1_relat_1(A_45))), inference(superposition, [status(thm), theory('equality')], [c_367, c_22])).
% 8.67/2.96  tff(c_127, plain, (![A_10]: (k5_relat_1(k6_relat_1(A_10), k6_relat_1(A_10))=k6_relat_1(A_10) | ~v1_relat_1(k6_relat_1(A_10)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_112])).
% 8.67/2.96  tff(c_575, plain, (![A_10]: (v2_funct_1(k6_relat_1(A_10)) | k6_relat_1(k1_relat_1(k6_relat_1(A_10)))!=k6_relat_1(A_10) | ~v1_funct_1(k6_relat_1(A_10)) | ~v1_relat_1(k6_relat_1(A_10)) | ~v1_funct_1(k6_relat_1(A_10)) | ~v1_relat_1(k6_relat_1(A_10)) | ~v1_relat_1(k6_relat_1(A_10)))), inference(superposition, [status(thm), theory('equality')], [c_127, c_559])).
% 8.67/2.96  tff(c_2046, plain, (![A_72]: (v2_funct_1(k6_relat_1(A_72)) | ~v1_funct_1(k6_relat_1(A_72)) | ~v1_relat_1(k6_relat_1(A_72)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_575])).
% 8.67/2.96  tff(c_2053, plain, (![A_72]: (k4_relat_1(k6_relat_1(A_72))=k2_funct_1(k6_relat_1(A_72)) | ~v1_funct_1(k6_relat_1(A_72)) | ~v1_relat_1(k6_relat_1(A_72)))), inference(resolution, [status(thm)], [c_2046, c_16])).
% 8.67/2.96  tff(c_3093, plain, (k4_relat_1(k6_relat_1(k2_relat_1('#skF_2')))=k2_funct_1(k6_relat_1(k2_relat_1('#skF_2'))) | ~v1_funct_1(k6_relat_1(k2_relat_1('#skF_2')))), inference(resolution, [status(thm)], [c_3012, c_2053])).
% 8.67/2.96  tff(c_3743, plain, (~v1_funct_1(k6_relat_1(k2_relat_1('#skF_2')))), inference(splitLeft, [status(thm)], [c_3093])).
% 8.67/2.96  tff(c_3778, plain, (~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_373, c_3743])).
% 8.67/2.96  tff(c_3782, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_700, c_742, c_2101, c_3778])).
% 8.67/2.96  tff(c_3784, plain, (v1_funct_1(k6_relat_1(k2_relat_1('#skF_2')))), inference(splitRight, [status(thm)], [c_3093])).
% 8.67/2.96  tff(c_600, plain, (![A_10]: (v2_funct_1(k6_relat_1(A_10)) | ~v1_funct_1(k6_relat_1(A_10)) | ~v1_relat_1(k6_relat_1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_575])).
% 8.67/2.96  tff(c_3783, plain, (k4_relat_1(k6_relat_1(k2_relat_1('#skF_2')))=k2_funct_1(k6_relat_1(k2_relat_1('#skF_2')))), inference(splitRight, [status(thm)], [c_3093])).
% 8.67/2.96  tff(c_3797, plain, (v1_relat_1(k2_funct_1(k6_relat_1(k2_relat_1('#skF_2')))) | ~v1_relat_1(k6_relat_1(k2_relat_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_3783, c_2])).
% 8.67/2.96  tff(c_3807, plain, (v1_relat_1(k2_funct_1(k6_relat_1(k2_relat_1('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_3012, c_3797])).
% 8.67/2.96  tff(c_3794, plain, (k2_relat_1(k2_funct_1(k6_relat_1(k2_relat_1('#skF_2'))))=k1_relat_1(k6_relat_1(k2_relat_1('#skF_2'))) | ~v1_relat_1(k6_relat_1(k2_relat_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_3783, c_4])).
% 8.67/2.96  tff(c_3805, plain, (k2_relat_1(k2_funct_1(k6_relat_1(k2_relat_1('#skF_2'))))=k2_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3012, c_10, c_3794])).
% 8.67/2.96  tff(c_3972, plain, (k5_relat_1(k2_funct_1(k6_relat_1(k2_relat_1('#skF_2'))), k6_relat_1(k2_relat_1('#skF_2')))=k2_funct_1(k6_relat_1(k2_relat_1('#skF_2'))) | ~v1_relat_1(k2_funct_1(k6_relat_1(k2_relat_1('#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_3805, c_14])).
% 8.67/2.96  tff(c_3984, plain, (k5_relat_1(k2_funct_1(k6_relat_1(k2_relat_1('#skF_2'))), k6_relat_1(k2_relat_1('#skF_2')))=k2_funct_1(k6_relat_1(k2_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_3807, c_3972])).
% 8.67/2.96  tff(c_4063, plain, (k6_relat_1(k2_relat_1(k6_relat_1(k2_relat_1('#skF_2'))))=k2_funct_1(k6_relat_1(k2_relat_1('#skF_2'))) | ~v2_funct_1(k6_relat_1(k2_relat_1('#skF_2'))) | ~v1_funct_1(k6_relat_1(k2_relat_1('#skF_2'))) | ~v1_relat_1(k6_relat_1(k2_relat_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_3984, c_32])).
% 8.67/2.96  tff(c_4084, plain, (k2_funct_1(k6_relat_1(k2_relat_1('#skF_2')))=k6_relat_1(k2_relat_1('#skF_2')) | ~v2_funct_1(k6_relat_1(k2_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_3012, c_3784, c_12, c_4063])).
% 8.67/2.96  tff(c_4092, plain, (~v2_funct_1(k6_relat_1(k2_relat_1('#skF_2')))), inference(splitLeft, [status(thm)], [c_4084])).
% 8.67/2.96  tff(c_4096, plain, (~v1_funct_1(k6_relat_1(k2_relat_1('#skF_2'))) | ~v1_relat_1(k6_relat_1(k2_relat_1('#skF_2')))), inference(resolution, [status(thm)], [c_600, c_4092])).
% 8.67/2.96  tff(c_4100, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3012, c_3784, c_4096])).
% 8.67/2.96  tff(c_4101, plain, (k2_funct_1(k6_relat_1(k2_relat_1('#skF_2')))=k6_relat_1(k2_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_4084])).
% 8.67/2.96  tff(c_4109, plain, (k5_relat_1(k6_relat_1(k2_relat_1('#skF_2')), k6_relat_1(k2_relat_1('#skF_2')))=k6_relat_1(k2_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_4101, c_4101, c_3984])).
% 8.67/2.96  tff(c_5494, plain, (k2_relat_1(k2_funct_1(k2_funct_1('#skF_2')))=k1_relat_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_5482, c_4])).
% 8.67/2.96  tff(c_5507, plain, (k2_relat_1(k2_funct_1(k2_funct_1('#skF_2')))=k2_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_742, c_738, c_5494])).
% 8.67/2.96  tff(c_5664, plain, (k5_relat_1(k2_funct_1(k2_funct_1('#skF_2')), k6_relat_1(k2_relat_1('#skF_2')))=k2_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_5507, c_14])).
% 8.67/2.96  tff(c_5676, plain, (k5_relat_1(k2_funct_1(k2_funct_1('#skF_2')), k6_relat_1(k2_relat_1('#skF_2')))=k2_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_5509, c_5664])).
% 8.67/2.96  tff(c_417, plain, (![A_22, C_48]: (k5_relat_1(k6_relat_1(k1_relat_1(A_22)), C_48)=k5_relat_1(A_22, k5_relat_1(k2_funct_1(A_22), C_48)) | ~v1_relat_1(C_48) | ~v1_relat_1(k2_funct_1(A_22)) | ~v1_relat_1(A_22) | ~v2_funct_1(A_22) | ~v1_funct_1(A_22) | ~v1_relat_1(A_22))), inference(superposition, [status(thm), theory('equality')], [c_34, c_382])).
% 8.67/2.96  tff(c_8725, plain, (k5_relat_1(k6_relat_1(k1_relat_1(k2_funct_1('#skF_2'))), k6_relat_1(k2_relat_1('#skF_2')))=k5_relat_1(k2_funct_1('#skF_2'), k2_funct_1(k2_funct_1('#skF_2'))) | ~v1_relat_1(k6_relat_1(k2_relat_1('#skF_2'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_2'))) | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v2_funct_1(k2_funct_1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_5676, c_417])).
% 8.67/2.96  tff(c_8757, plain, (k5_relat_1(k2_funct_1('#skF_2'), k2_funct_1(k2_funct_1('#skF_2')))=k6_relat_1(k2_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_742, c_2101, c_5460, c_742, c_5509, c_3012, c_4109, c_738, c_8725])).
% 8.67/2.96  tff(c_414, plain, (![A_22, C_48]: (k5_relat_1(k6_relat_1(k2_relat_1(A_22)), C_48)=k5_relat_1(k2_funct_1(A_22), k5_relat_1(A_22, C_48)) | ~v1_relat_1(C_48) | ~v1_relat_1(A_22) | ~v1_relat_1(k2_funct_1(A_22)) | ~v2_funct_1(A_22) | ~v1_funct_1(A_22) | ~v1_relat_1(A_22))), inference(superposition, [status(thm), theory('equality')], [c_32, c_382])).
% 8.67/2.96  tff(c_8785, plain, (k5_relat_1(k6_relat_1(k2_relat_1(k2_funct_1('#skF_2'))), k2_funct_1(k2_funct_1('#skF_2')))=k5_relat_1(k2_funct_1(k2_funct_1('#skF_2')), k6_relat_1(k2_relat_1('#skF_2'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_2'))) | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_2'))) | ~v2_funct_1(k2_funct_1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_8757, c_414])).
% 8.67/2.96  tff(c_8821, plain, (k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')), k2_funct_1(k2_funct_1('#skF_2')))=k2_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_742, c_2101, c_5460, c_5509, c_742, c_5509, c_5676, c_740, c_8785])).
% 8.67/2.96  tff(c_8859, plain, (k5_relat_1('#skF_2', k5_relat_1(k2_funct_1('#skF_2'), k2_funct_1(k2_funct_1('#skF_2'))))=k2_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_2'))) | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v1_relat_1('#skF_2') | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_8821, c_417])).
% 8.67/2.96  tff(c_8902, plain, (k5_relat_1('#skF_2', k6_relat_1(k2_relat_1('#skF_2')))=k2_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_700, c_46, c_742, c_5509, c_8757, c_8859])).
% 8.67/2.96  tff(c_8973, plain, (k2_funct_1(k2_funct_1('#skF_2'))='#skF_2' | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_8902, c_14])).
% 8.67/2.96  tff(c_9010, plain, (k2_funct_1(k2_funct_1('#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_8973])).
% 8.67/2.96  tff(c_9058, plain, (k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')), '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_9010, c_9010, c_8821])).
% 8.67/2.96  tff(c_5135, plain, (![A_103, C_104]: (k5_relat_1(k6_relat_1(k2_relat_1(A_103)), C_104)=k5_relat_1(k2_funct_1(A_103), k5_relat_1(A_103, C_104)) | ~v1_relat_1(C_104) | ~v1_relat_1(A_103) | ~v1_relat_1(k2_funct_1(A_103)) | ~v2_funct_1(A_103) | ~v1_funct_1(A_103) | ~v1_relat_1(A_103))), inference(superposition, [status(thm), theory('equality')], [c_32, c_382])).
% 8.67/2.96  tff(c_5345, plain, (![C_104]: (k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')), C_104)=k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', C_104)) | ~v1_relat_1(C_104) | ~v1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_40, c_5135])).
% 8.67/2.96  tff(c_5408, plain, (![C_104]: (k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')), C_104)=k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', C_104)) | ~v1_relat_1(C_104))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_42, c_264, c_50, c_5345])).
% 8.67/2.96  tff(c_9423, plain, (k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', '#skF_2'))='#skF_2' | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_9058, c_5408])).
% 8.67/2.96  tff(c_9466, plain, (k2_funct_1('#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_286, c_9423])).
% 8.67/2.96  tff(c_9468, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_9466])).
% 8.67/2.96  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.67/2.96  
% 8.67/2.96  Inference rules
% 8.67/2.96  ----------------------
% 8.67/2.96  #Ref     : 0
% 8.67/2.96  #Sup     : 2070
% 8.67/2.96  #Fact    : 0
% 8.67/2.96  #Define  : 0
% 8.67/2.96  #Split   : 24
% 8.67/2.96  #Chain   : 0
% 8.67/2.96  #Close   : 0
% 8.67/2.96  
% 8.67/2.96  Ordering : KBO
% 8.67/2.96  
% 8.67/2.96  Simplification rules
% 8.67/2.96  ----------------------
% 8.67/2.96  #Subsume      : 94
% 8.67/2.96  #Demod        : 6420
% 8.67/2.96  #Tautology    : 1066
% 8.67/2.96  #SimpNegUnit  : 3
% 8.67/2.96  #BackRed      : 62
% 8.67/2.96  
% 8.67/2.96  #Partial instantiations: 0
% 8.67/2.96  #Strategies tried      : 1
% 8.67/2.96  
% 8.67/2.96  Timing (in seconds)
% 8.67/2.96  ----------------------
% 8.67/2.96  Preprocessing        : 0.32
% 8.67/2.97  Parsing              : 0.17
% 8.67/2.97  CNF conversion       : 0.02
% 8.67/2.97  Main loop            : 1.83
% 8.67/2.97  Inferencing          : 0.51
% 8.67/2.97  Reduction            : 0.83
% 8.67/2.97  Demodulation         : 0.66
% 8.67/2.97  BG Simplification    : 0.07
% 8.67/2.97  Subsumption          : 0.33
% 8.67/2.97  Abstraction          : 0.09
% 8.67/2.97  MUC search           : 0.00
% 8.67/2.97  Cooper               : 0.00
% 8.67/2.97  Total                : 2.22
% 8.67/2.97  Index Insertion      : 0.00
% 8.67/2.97  Index Deletion       : 0.00
% 8.67/2.97  Index Matching       : 0.00
% 8.67/2.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
