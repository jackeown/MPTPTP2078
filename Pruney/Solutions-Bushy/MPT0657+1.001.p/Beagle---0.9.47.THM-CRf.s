%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0657+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:39 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.65s
% Verified   : 
% Statistics : Number of formulae       :   40 (  48 expanded)
%              Number of leaves         :   18 (  26 expanded)
%              Depth                    :   10
%              Number of atoms          :  125 ( 185 expanded)
%              Number of equality atoms :   39 (  60 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(f_92,negated_conjecture,(
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

tff(f_32,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_64,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_74,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ! [D] :
              ( ( v1_relat_1(D)
                & v1_funct_1(D) )
             => ( ( k2_relat_1(B) = A
                  & k5_relat_1(B,C) = k6_relat_1(k1_relat_1(D))
                  & k5_relat_1(C,D) = k6_relat_1(A) )
               => D = B ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l72_funct_1)).

tff(c_16,plain,(
    k2_funct_1('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_30,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_28,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_22,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_18,plain,(
    k6_relat_1(k2_relat_1('#skF_1')) = k5_relat_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2,plain,(
    ! [A_1] :
      ( v1_funct_1(k2_funct_1(A_1))
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_relat_1(k2_funct_1(A_1))
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10,plain,(
    ! [A_10] :
      ( k1_relat_1(k2_funct_1(A_10)) = k2_relat_1(A_10)
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_26,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_24,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_20,plain,(
    k2_relat_1('#skF_2') = k1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_14,plain,(
    ! [A_11] :
      ( k5_relat_1(A_11,k2_funct_1(A_11)) = k6_relat_1(k1_relat_1(A_11))
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_77,plain,(
    ! [D_19,B_20,C_21] :
      ( D_19 = B_20
      | k6_relat_1(k2_relat_1(B_20)) != k5_relat_1(C_21,D_19)
      | k6_relat_1(k1_relat_1(D_19)) != k5_relat_1(B_20,C_21)
      | ~ v1_funct_1(D_19)
      | ~ v1_relat_1(D_19)
      | ~ v1_funct_1(C_21)
      | ~ v1_relat_1(C_21)
      | ~ v1_funct_1(B_20)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_169,plain,(
    ! [A_39,B_40] :
      ( k2_funct_1(A_39) = B_40
      | k6_relat_1(k2_relat_1(B_40)) != k6_relat_1(k1_relat_1(A_39))
      | k6_relat_1(k1_relat_1(k2_funct_1(A_39))) != k5_relat_1(B_40,A_39)
      | ~ v1_funct_1(k2_funct_1(A_39))
      | ~ v1_relat_1(k2_funct_1(A_39))
      | ~ v1_funct_1(A_39)
      | ~ v1_relat_1(A_39)
      | ~ v1_funct_1(B_40)
      | ~ v1_relat_1(B_40)
      | ~ v2_funct_1(A_39)
      | ~ v1_funct_1(A_39)
      | ~ v1_relat_1(A_39) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_77])).

tff(c_177,plain,(
    ! [A_39] :
      ( k2_funct_1(A_39) = '#skF_2'
      | k6_relat_1(k1_relat_1(A_39)) != k6_relat_1(k1_relat_1('#skF_1'))
      | k6_relat_1(k1_relat_1(k2_funct_1(A_39))) != k5_relat_1('#skF_2',A_39)
      | ~ v1_funct_1(k2_funct_1(A_39))
      | ~ v1_relat_1(k2_funct_1(A_39))
      | ~ v1_funct_1(A_39)
      | ~ v1_relat_1(A_39)
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2')
      | ~ v2_funct_1(A_39)
      | ~ v1_funct_1(A_39)
      | ~ v1_relat_1(A_39) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_169])).

tff(c_186,plain,(
    ! [A_42] :
      ( k2_funct_1(A_42) = '#skF_2'
      | k6_relat_1(k1_relat_1(A_42)) != k6_relat_1(k1_relat_1('#skF_1'))
      | k6_relat_1(k1_relat_1(k2_funct_1(A_42))) != k5_relat_1('#skF_2',A_42)
      | ~ v1_funct_1(k2_funct_1(A_42))
      | ~ v1_relat_1(k2_funct_1(A_42))
      | ~ v2_funct_1(A_42)
      | ~ v1_funct_1(A_42)
      | ~ v1_relat_1(A_42) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_177])).

tff(c_227,plain,(
    ! [A_48] :
      ( k2_funct_1(A_48) = '#skF_2'
      | k6_relat_1(k1_relat_1(A_48)) != k6_relat_1(k1_relat_1('#skF_1'))
      | k6_relat_1(k2_relat_1(A_48)) != k5_relat_1('#skF_2',A_48)
      | ~ v1_funct_1(k2_funct_1(A_48))
      | ~ v1_relat_1(k2_funct_1(A_48))
      | ~ v2_funct_1(A_48)
      | ~ v1_funct_1(A_48)
      | ~ v1_relat_1(A_48)
      | ~ v2_funct_1(A_48)
      | ~ v1_funct_1(A_48)
      | ~ v1_relat_1(A_48) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_186])).

tff(c_232,plain,(
    ! [A_49] :
      ( k2_funct_1(A_49) = '#skF_2'
      | k6_relat_1(k1_relat_1(A_49)) != k6_relat_1(k1_relat_1('#skF_1'))
      | k6_relat_1(k2_relat_1(A_49)) != k5_relat_1('#skF_2',A_49)
      | ~ v1_funct_1(k2_funct_1(A_49))
      | ~ v2_funct_1(A_49)
      | ~ v1_funct_1(A_49)
      | ~ v1_relat_1(A_49) ) ),
    inference(resolution,[status(thm)],[c_4,c_227])).

tff(c_237,plain,(
    ! [A_50] :
      ( k2_funct_1(A_50) = '#skF_2'
      | k6_relat_1(k1_relat_1(A_50)) != k6_relat_1(k1_relat_1('#skF_1'))
      | k6_relat_1(k2_relat_1(A_50)) != k5_relat_1('#skF_2',A_50)
      | ~ v2_funct_1(A_50)
      | ~ v1_funct_1(A_50)
      | ~ v1_relat_1(A_50) ) ),
    inference(resolution,[status(thm)],[c_2,c_232])).

tff(c_243,plain,
    ( k2_funct_1('#skF_1') = '#skF_2'
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_237])).

tff(c_249,plain,(
    k2_funct_1('#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_22,c_243])).

tff(c_251,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_249])).

%------------------------------------------------------------------------------
