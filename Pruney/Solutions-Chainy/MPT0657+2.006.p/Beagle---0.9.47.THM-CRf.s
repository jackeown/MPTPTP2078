%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:04 EST 2020

% Result     : Theorem 4.51s
% Output     : CNFRefutation 4.70s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 517 expanded)
%              Number of leaves         :   28 ( 201 expanded)
%              Depth                    :   17
%              Number of atoms          :  175 (1690 expanded)
%              Number of equality atoms :   64 ( 661 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k10_relat_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

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

tff(f_141,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_66,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_98,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v1_relat_1(k5_relat_1(A,B))
        & v1_funct_1(k5_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funct_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_113,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( k2_relat_1(A) = k1_relat_1(B)
              & k5_relat_1(A,B) = A )
           => B = k6_relat_1(k1_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_funct_1)).

tff(f_123,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_78,axiom,(
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

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

tff(c_38,plain,(
    k2_funct_1('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_48,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_52,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_642,plain,(
    ! [A_52,B_53,C_54] :
      ( k5_relat_1(k5_relat_1(A_52,B_53),C_54) = k5_relat_1(A_52,k5_relat_1(B_53,C_54))
      | ~ v1_relat_1(C_54)
      | ~ v1_relat_1(B_53)
      | ~ v1_relat_1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_40,plain,(
    k6_relat_1(k2_relat_1('#skF_1')) = k5_relat_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_16,plain,(
    ! [A_16] : k1_relat_1(k6_relat_1(A_16)) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_81,plain,(
    k1_relat_1(k5_relat_1('#skF_2','#skF_1')) = k2_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_16])).

tff(c_294,plain,(
    ! [A_45,B_46] :
      ( k10_relat_1(A_45,k1_relat_1(B_46)) = k1_relat_1(k5_relat_1(A_45,B_46))
      | ~ v1_relat_1(B_46)
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_42,plain,(
    k2_relat_1('#skF_2') = k1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_114,plain,(
    ! [A_34] :
      ( k10_relat_1(A_34,k2_relat_1(A_34)) = k1_relat_1(A_34)
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_132,plain,
    ( k10_relat_1('#skF_2',k1_relat_1('#skF_1')) = k1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_114])).

tff(c_138,plain,(
    k10_relat_1('#skF_2',k1_relat_1('#skF_1')) = k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_132])).

tff(c_303,plain,
    ( k1_relat_1(k5_relat_1('#skF_2','#skF_1')) = k1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_294,c_138])).

tff(c_329,plain,(
    k2_relat_1('#skF_1') = k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_52,c_81,c_303])).

tff(c_371,plain,(
    k6_relat_1(k1_relat_1('#skF_2')) = k5_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_329,c_40])).

tff(c_20,plain,(
    ! [A_17] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_17)),A_17) = A_17
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_445,plain,
    ( k5_relat_1(k5_relat_1('#skF_2','#skF_1'),'#skF_2') = '#skF_2'
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_371,c_20])).

tff(c_461,plain,(
    k5_relat_1(k5_relat_1('#skF_2','#skF_1'),'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_445])).

tff(c_663,plain,
    ( k5_relat_1('#skF_2',k5_relat_1('#skF_1','#skF_2')) = '#skF_2'
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_642,c_461])).

tff(c_722,plain,(
    k5_relat_1('#skF_2',k5_relat_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_52,c_48,c_663])).

tff(c_50,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_46,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_28,plain,(
    ! [A_20,B_21] :
      ( v1_funct_1(k5_relat_1(A_20,B_21))
      | ~ v1_funct_1(B_21)
      | ~ v1_relat_1(B_21)
      | ~ v1_funct_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( v1_relat_1(k5_relat_1(A_2,B_3))
      | ~ v1_relat_1(B_3)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ! [A_4] :
      ( k10_relat_1(A_4,k2_relat_1(A_4)) = k1_relat_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_375,plain,
    ( k10_relat_1('#skF_1',k1_relat_1('#skF_2')) = k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_329,c_6])).

tff(c_379,plain,(
    k10_relat_1('#skF_1',k1_relat_1('#skF_2')) = k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_375])).

tff(c_8,plain,(
    ! [A_5,B_7] :
      ( k10_relat_1(A_5,k1_relat_1(B_7)) = k1_relat_1(k5_relat_1(A_5,B_7))
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_468,plain,
    ( k1_relat_1(k5_relat_1('#skF_1','#skF_2')) = k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_379,c_8])).

tff(c_475,plain,(
    k1_relat_1(k5_relat_1('#skF_1','#skF_2')) = k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_468])).

tff(c_1240,plain,(
    ! [B_63,A_64] :
      ( k6_relat_1(k1_relat_1(B_63)) = B_63
      | k5_relat_1(A_64,B_63) != A_64
      | k2_relat_1(A_64) != k1_relat_1(B_63)
      | ~ v1_funct_1(B_63)
      | ~ v1_relat_1(B_63)
      | ~ v1_funct_1(A_64)
      | ~ v1_relat_1(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1248,plain,
    ( k6_relat_1(k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) = k5_relat_1('#skF_1','#skF_2')
    | k1_relat_1(k5_relat_1('#skF_1','#skF_2')) != k2_relat_1('#skF_2')
    | ~ v1_funct_1(k5_relat_1('#skF_1','#skF_2'))
    | ~ v1_relat_1(k5_relat_1('#skF_1','#skF_2'))
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_722,c_1240])).

tff(c_1273,plain,
    ( k6_relat_1(k1_relat_1('#skF_1')) = k5_relat_1('#skF_1','#skF_2')
    | ~ v1_funct_1(k5_relat_1('#skF_1','#skF_2'))
    | ~ v1_relat_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_42,c_475,c_475,c_1248])).

tff(c_2733,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1273])).

tff(c_2736,plain,
    ( ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_2733])).

tff(c_2740,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_2736])).

tff(c_2741,plain,
    ( ~ v1_funct_1(k5_relat_1('#skF_1','#skF_2'))
    | k6_relat_1(k1_relat_1('#skF_1')) = k5_relat_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_1273])).

tff(c_2743,plain,(
    ~ v1_funct_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_2741])).

tff(c_2803,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_2743])).

tff(c_2807,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_2803])).

tff(c_2808,plain,(
    k6_relat_1(k1_relat_1('#skF_1')) = k5_relat_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_2741])).

tff(c_44,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_36,plain,(
    ! [A_25] :
      ( k5_relat_1(A_25,k2_funct_1(A_25)) = k6_relat_1(k1_relat_1(A_25))
      | ~ v2_funct_1(A_25)
      | ~ v1_funct_1(A_25)
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_178,plain,(
    ! [A_40] :
      ( k4_relat_1(A_40) = k2_funct_1(A_40)
      | ~ v2_funct_1(A_40)
      | ~ v1_funct_1(A_40)
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_181,plain,
    ( k4_relat_1('#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_178])).

tff(c_184,plain,(
    k4_relat_1('#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_181])).

tff(c_2,plain,(
    ! [A_1] :
      ( v1_relat_1(k4_relat_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_194,plain,
    ( v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_2])).

tff(c_202,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_194])).

tff(c_12,plain,(
    ! [A_8] :
      ( k1_relat_1(k4_relat_1(A_8)) = k2_relat_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_191,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_12])).

tff(c_200,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_191])).

tff(c_225,plain,
    ( k5_relat_1(k6_relat_1(k2_relat_1('#skF_1')),k2_funct_1('#skF_1')) = k2_funct_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_20])).

tff(c_229,plain,(
    k5_relat_1(k5_relat_1('#skF_2','#skF_1'),k2_funct_1('#skF_1')) = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_40,c_225])).

tff(c_706,plain,
    ( k5_relat_1('#skF_2',k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k2_funct_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_642])).

tff(c_735,plain,(
    k5_relat_1('#skF_2',k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_52,c_202,c_706])).

tff(c_773,plain,
    ( k5_relat_1('#skF_2',k6_relat_1(k1_relat_1('#skF_1'))) = k2_funct_1('#skF_1')
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_735])).

tff(c_783,plain,(
    k5_relat_1('#skF_2',k6_relat_1(k1_relat_1('#skF_1'))) = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_44,c_773])).

tff(c_2818,plain,(
    k5_relat_1('#skF_2',k5_relat_1('#skF_1','#skF_2')) = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2808,c_783])).

tff(c_2821,plain,(
    k2_funct_1('#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_722,c_2818])).

tff(c_2823,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_2821])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 20:40:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.51/1.81  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.70/1.82  
% 4.70/1.82  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.70/1.82  %$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k10_relat_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1
% 4.70/1.82  
% 4.70/1.82  %Foreground sorts:
% 4.70/1.82  
% 4.70/1.82  
% 4.70/1.82  %Background operators:
% 4.70/1.82  
% 4.70/1.82  
% 4.70/1.82  %Foreground operators:
% 4.70/1.82  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.70/1.82  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.70/1.82  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.70/1.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.70/1.82  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.70/1.82  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.70/1.82  tff('#skF_2', type, '#skF_2': $i).
% 4.70/1.82  tff('#skF_1', type, '#skF_1': $i).
% 4.70/1.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.70/1.82  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.70/1.82  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.70/1.82  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.70/1.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.70/1.82  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.70/1.82  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 4.70/1.82  
% 4.70/1.84  tff(f_141, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_1)).
% 4.70/1.84  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 4.70/1.84  tff(f_66, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 4.70/1.84  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 4.70/1.84  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 4.70/1.84  tff(f_70, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_relat_1)).
% 4.70/1.84  tff(f_98, axiom, (![A, B]: ((((v1_relat_1(A) & v1_funct_1(A)) & v1_relat_1(B)) & v1_funct_1(B)) => (v1_relat_1(k5_relat_1(A, B)) & v1_funct_1(k5_relat_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_funct_1)).
% 4.70/1.84  tff(f_35, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 4.70/1.84  tff(f_113, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k2_relat_1(A) = k1_relat_1(B)) & (k5_relat_1(A, B) = A)) => (B = k6_relat_1(k1_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_funct_1)).
% 4.70/1.84  tff(f_123, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 4.70/1.84  tff(f_78, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 4.70/1.84  tff(f_29, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 4.70/1.84  tff(f_52, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_relat_1)).
% 4.70/1.84  tff(c_38, plain, (k2_funct_1('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_141])).
% 4.70/1.84  tff(c_48, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_141])).
% 4.70/1.84  tff(c_52, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_141])).
% 4.70/1.84  tff(c_642, plain, (![A_52, B_53, C_54]: (k5_relat_1(k5_relat_1(A_52, B_53), C_54)=k5_relat_1(A_52, k5_relat_1(B_53, C_54)) | ~v1_relat_1(C_54) | ~v1_relat_1(B_53) | ~v1_relat_1(A_52))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.70/1.84  tff(c_40, plain, (k6_relat_1(k2_relat_1('#skF_1'))=k5_relat_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_141])).
% 4.70/1.84  tff(c_16, plain, (![A_16]: (k1_relat_1(k6_relat_1(A_16))=A_16)), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.70/1.84  tff(c_81, plain, (k1_relat_1(k5_relat_1('#skF_2', '#skF_1'))=k2_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_40, c_16])).
% 4.70/1.84  tff(c_294, plain, (![A_45, B_46]: (k10_relat_1(A_45, k1_relat_1(B_46))=k1_relat_1(k5_relat_1(A_45, B_46)) | ~v1_relat_1(B_46) | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.70/1.84  tff(c_42, plain, (k2_relat_1('#skF_2')=k1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_141])).
% 4.70/1.84  tff(c_114, plain, (![A_34]: (k10_relat_1(A_34, k2_relat_1(A_34))=k1_relat_1(A_34) | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.70/1.84  tff(c_132, plain, (k10_relat_1('#skF_2', k1_relat_1('#skF_1'))=k1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_42, c_114])).
% 4.70/1.84  tff(c_138, plain, (k10_relat_1('#skF_2', k1_relat_1('#skF_1'))=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_132])).
% 4.70/1.84  tff(c_303, plain, (k1_relat_1(k5_relat_1('#skF_2', '#skF_1'))=k1_relat_1('#skF_2') | ~v1_relat_1('#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_294, c_138])).
% 4.70/1.84  tff(c_329, plain, (k2_relat_1('#skF_1')=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_52, c_81, c_303])).
% 4.70/1.84  tff(c_371, plain, (k6_relat_1(k1_relat_1('#skF_2'))=k5_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_329, c_40])).
% 4.70/1.84  tff(c_20, plain, (![A_17]: (k5_relat_1(k6_relat_1(k1_relat_1(A_17)), A_17)=A_17 | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.70/1.84  tff(c_445, plain, (k5_relat_1(k5_relat_1('#skF_2', '#skF_1'), '#skF_2')='#skF_2' | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_371, c_20])).
% 4.70/1.84  tff(c_461, plain, (k5_relat_1(k5_relat_1('#skF_2', '#skF_1'), '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_445])).
% 4.70/1.84  tff(c_663, plain, (k5_relat_1('#skF_2', k5_relat_1('#skF_1', '#skF_2'))='#skF_2' | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_642, c_461])).
% 4.70/1.84  tff(c_722, plain, (k5_relat_1('#skF_2', k5_relat_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_52, c_48, c_663])).
% 4.70/1.84  tff(c_50, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_141])).
% 4.70/1.84  tff(c_46, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_141])).
% 4.70/1.84  tff(c_28, plain, (![A_20, B_21]: (v1_funct_1(k5_relat_1(A_20, B_21)) | ~v1_funct_1(B_21) | ~v1_relat_1(B_21) | ~v1_funct_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.70/1.84  tff(c_4, plain, (![A_2, B_3]: (v1_relat_1(k5_relat_1(A_2, B_3)) | ~v1_relat_1(B_3) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.70/1.84  tff(c_6, plain, (![A_4]: (k10_relat_1(A_4, k2_relat_1(A_4))=k1_relat_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.70/1.84  tff(c_375, plain, (k10_relat_1('#skF_1', k1_relat_1('#skF_2'))=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_329, c_6])).
% 4.70/1.84  tff(c_379, plain, (k10_relat_1('#skF_1', k1_relat_1('#skF_2'))=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_375])).
% 4.70/1.84  tff(c_8, plain, (![A_5, B_7]: (k10_relat_1(A_5, k1_relat_1(B_7))=k1_relat_1(k5_relat_1(A_5, B_7)) | ~v1_relat_1(B_7) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.70/1.84  tff(c_468, plain, (k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_379, c_8])).
% 4.70/1.84  tff(c_475, plain, (k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_468])).
% 4.70/1.84  tff(c_1240, plain, (![B_63, A_64]: (k6_relat_1(k1_relat_1(B_63))=B_63 | k5_relat_1(A_64, B_63)!=A_64 | k2_relat_1(A_64)!=k1_relat_1(B_63) | ~v1_funct_1(B_63) | ~v1_relat_1(B_63) | ~v1_funct_1(A_64) | ~v1_relat_1(A_64))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.70/1.84  tff(c_1248, plain, (k6_relat_1(k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))=k5_relat_1('#skF_1', '#skF_2') | k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))!=k2_relat_1('#skF_2') | ~v1_funct_1(k5_relat_1('#skF_1', '#skF_2')) | ~v1_relat_1(k5_relat_1('#skF_1', '#skF_2')) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_722, c_1240])).
% 4.70/1.84  tff(c_1273, plain, (k6_relat_1(k1_relat_1('#skF_1'))=k5_relat_1('#skF_1', '#skF_2') | ~v1_funct_1(k5_relat_1('#skF_1', '#skF_2')) | ~v1_relat_1(k5_relat_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_42, c_475, c_475, c_1248])).
% 4.70/1.84  tff(c_2733, plain, (~v1_relat_1(k5_relat_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_1273])).
% 4.70/1.84  tff(c_2736, plain, (~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_4, c_2733])).
% 4.70/1.84  tff(c_2740, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_2736])).
% 4.70/1.84  tff(c_2741, plain, (~v1_funct_1(k5_relat_1('#skF_1', '#skF_2')) | k6_relat_1(k1_relat_1('#skF_1'))=k5_relat_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_1273])).
% 4.70/1.84  tff(c_2743, plain, (~v1_funct_1(k5_relat_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_2741])).
% 4.70/1.84  tff(c_2803, plain, (~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_28, c_2743])).
% 4.70/1.84  tff(c_2807, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_2803])).
% 4.70/1.84  tff(c_2808, plain, (k6_relat_1(k1_relat_1('#skF_1'))=k5_relat_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_2741])).
% 4.70/1.84  tff(c_44, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_141])).
% 4.70/1.84  tff(c_36, plain, (![A_25]: (k5_relat_1(A_25, k2_funct_1(A_25))=k6_relat_1(k1_relat_1(A_25)) | ~v2_funct_1(A_25) | ~v1_funct_1(A_25) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.70/1.84  tff(c_178, plain, (![A_40]: (k4_relat_1(A_40)=k2_funct_1(A_40) | ~v2_funct_1(A_40) | ~v1_funct_1(A_40) | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.70/1.84  tff(c_181, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_44, c_178])).
% 4.70/1.84  tff(c_184, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_181])).
% 4.70/1.84  tff(c_2, plain, (![A_1]: (v1_relat_1(k4_relat_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.70/1.84  tff(c_194, plain, (v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_184, c_2])).
% 4.70/1.84  tff(c_202, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_194])).
% 4.70/1.84  tff(c_12, plain, (![A_8]: (k1_relat_1(k4_relat_1(A_8))=k2_relat_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.70/1.84  tff(c_191, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_184, c_12])).
% 4.70/1.84  tff(c_200, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_191])).
% 4.70/1.84  tff(c_225, plain, (k5_relat_1(k6_relat_1(k2_relat_1('#skF_1')), k2_funct_1('#skF_1'))=k2_funct_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_200, c_20])).
% 4.70/1.84  tff(c_229, plain, (k5_relat_1(k5_relat_1('#skF_2', '#skF_1'), k2_funct_1('#skF_1'))=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_202, c_40, c_225])).
% 4.70/1.84  tff(c_706, plain, (k5_relat_1('#skF_2', k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k2_funct_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_229, c_642])).
% 4.70/1.84  tff(c_735, plain, (k5_relat_1('#skF_2', k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_52, c_202, c_706])).
% 4.70/1.84  tff(c_773, plain, (k5_relat_1('#skF_2', k6_relat_1(k1_relat_1('#skF_1')))=k2_funct_1('#skF_1') | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_36, c_735])).
% 4.70/1.84  tff(c_783, plain, (k5_relat_1('#skF_2', k6_relat_1(k1_relat_1('#skF_1')))=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_44, c_773])).
% 4.70/1.84  tff(c_2818, plain, (k5_relat_1('#skF_2', k5_relat_1('#skF_1', '#skF_2'))=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2808, c_783])).
% 4.70/1.84  tff(c_2821, plain, (k2_funct_1('#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_722, c_2818])).
% 4.70/1.84  tff(c_2823, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_2821])).
% 4.70/1.84  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.70/1.84  
% 4.70/1.84  Inference rules
% 4.70/1.84  ----------------------
% 4.70/1.84  #Ref     : 0
% 4.70/1.84  #Sup     : 643
% 4.70/1.84  #Fact    : 0
% 4.70/1.84  #Define  : 0
% 4.70/1.84  #Split   : 19
% 4.70/1.84  #Chain   : 0
% 4.70/1.84  #Close   : 0
% 4.70/1.84  
% 4.70/1.84  Ordering : KBO
% 4.70/1.84  
% 4.70/1.84  Simplification rules
% 4.70/1.84  ----------------------
% 4.70/1.84  #Subsume      : 36
% 4.70/1.84  #Demod        : 1006
% 4.70/1.84  #Tautology    : 329
% 4.70/1.84  #SimpNegUnit  : 3
% 4.70/1.84  #BackRed      : 17
% 4.70/1.84  
% 4.70/1.84  #Partial instantiations: 0
% 4.70/1.84  #Strategies tried      : 1
% 4.70/1.84  
% 4.70/1.84  Timing (in seconds)
% 4.70/1.84  ----------------------
% 4.79/1.84  Preprocessing        : 0.32
% 4.79/1.84  Parsing              : 0.17
% 4.79/1.84  CNF conversion       : 0.02
% 4.79/1.84  Main loop            : 0.74
% 4.79/1.84  Inferencing          : 0.25
% 4.79/1.84  Reduction            : 0.28
% 4.79/1.84  Demodulation         : 0.21
% 4.79/1.84  BG Simplification    : 0.04
% 4.79/1.84  Subsumption          : 0.13
% 4.79/1.84  Abstraction          : 0.04
% 4.79/1.84  MUC search           : 0.00
% 4.79/1.84  Cooper               : 0.00
% 4.79/1.84  Total                : 1.10
% 4.79/1.84  Index Insertion      : 0.00
% 4.79/1.84  Index Deletion       : 0.00
% 4.79/1.84  Index Matching       : 0.00
% 4.79/1.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
