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
% DateTime   : Thu Dec  3 10:03:38 EST 2020

% Result     : Theorem 2.68s
% Output     : CNFRefutation 2.68s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 317 expanded)
%              Number of leaves         :   21 ( 127 expanded)
%              Depth                    :   13
%              Number of atoms          :  200 (1246 expanded)
%              Number of equality atoms :   27 ( 144 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_90,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ( ( v2_funct_1(k5_relat_1(B,A))
                & r1_tarski(k2_relat_1(B),k1_relat_1(A)) )
             => v2_funct_1(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_funct_1)).

tff(f_49,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
      <=> ! [B,C] :
            ( ( r2_hidden(B,k1_relat_1(A))
              & r2_hidden(C,k1_relat_1(A))
              & k1_funct_1(A,B) = k1_funct_1(A,C) )
           => B = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v1_relat_1(k5_relat_1(A,B))
        & v1_funct_1(k5_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funct_1)).

tff(f_34,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(B))
           => k1_funct_1(k5_relat_1(B,C),A) = k1_funct_1(C,k1_funct_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).

tff(c_20,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_28,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_26,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_12,plain,(
    ! [A_4] :
      ( r2_hidden('#skF_1'(A_4),k1_relat_1(A_4))
      | v2_funct_1(A_4)
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_10,plain,(
    ! [A_4] :
      ( r2_hidden('#skF_2'(A_4),k1_relat_1(A_4))
      | v2_funct_1(A_4)
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_33,plain,(
    ! [A_18] :
      ( '#skF_2'(A_18) != '#skF_1'(A_18)
      | v2_funct_1(A_18)
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_36,plain,
    ( '#skF_2'('#skF_4') != '#skF_1'('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_33,c_20])).

tff(c_39,plain,(
    '#skF_2'('#skF_4') != '#skF_1'('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_36])).

tff(c_32,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_30,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( v1_relat_1(k5_relat_1(A_11,B_12))
      | ~ v1_funct_1(B_12)
      | ~ v1_relat_1(B_12)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_22,plain,(
    r1_tarski(k2_relat_1('#skF_4'),k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_53,plain,(
    ! [A_26,B_27] :
      ( k1_relat_1(k5_relat_1(A_26,B_27)) = k1_relat_1(A_26)
      | ~ r1_tarski(k2_relat_1(A_26),k1_relat_1(B_27))
      | ~ v1_relat_1(B_27)
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_56,plain,
    ( k1_relat_1(k5_relat_1('#skF_4','#skF_3')) = k1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_53])).

tff(c_59,plain,(
    k1_relat_1(k5_relat_1('#skF_4','#skF_3')) = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_32,c_56])).

tff(c_2,plain,(
    ! [A_1,B_3] :
      ( k1_relat_1(k5_relat_1(A_1,B_3)) = k1_relat_1(A_1)
      | ~ r1_tarski(k2_relat_1(A_1),k1_relat_1(B_3))
      | ~ v1_relat_1(B_3)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_72,plain,(
    ! [A_1] :
      ( k1_relat_1(k5_relat_1(A_1,k5_relat_1('#skF_4','#skF_3'))) = k1_relat_1(A_1)
      | ~ r1_tarski(k2_relat_1(A_1),k1_relat_1('#skF_4'))
      | ~ v1_relat_1(k5_relat_1('#skF_4','#skF_3'))
      | ~ v1_relat_1(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_2])).

tff(c_84,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_87,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_84])).

tff(c_91,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_32,c_30,c_87])).

tff(c_93,plain,(
    v1_relat_1(k5_relat_1('#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( v1_funct_1(k5_relat_1(A_11,B_12))
      | ~ v1_funct_1(B_12)
      | ~ v1_relat_1(B_12)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_95,plain,(
    ! [B_32,C_33,A_34] :
      ( k1_funct_1(k5_relat_1(B_32,C_33),A_34) = k1_funct_1(C_33,k1_funct_1(B_32,A_34))
      | ~ r2_hidden(A_34,k1_relat_1(B_32))
      | ~ v1_funct_1(C_33)
      | ~ v1_relat_1(C_33)
      | ~ v1_funct_1(B_32)
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_97,plain,(
    ! [C_33,A_34] :
      ( k1_funct_1(k5_relat_1(k5_relat_1('#skF_4','#skF_3'),C_33),A_34) = k1_funct_1(C_33,k1_funct_1(k5_relat_1('#skF_4','#skF_3'),A_34))
      | ~ r2_hidden(A_34,k1_relat_1('#skF_4'))
      | ~ v1_funct_1(C_33)
      | ~ v1_relat_1(C_33)
      | ~ v1_funct_1(k5_relat_1('#skF_4','#skF_3'))
      | ~ v1_relat_1(k5_relat_1('#skF_4','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_95])).

tff(c_103,plain,(
    ! [C_33,A_34] :
      ( k1_funct_1(k5_relat_1(k5_relat_1('#skF_4','#skF_3'),C_33),A_34) = k1_funct_1(C_33,k1_funct_1(k5_relat_1('#skF_4','#skF_3'),A_34))
      | ~ r2_hidden(A_34,k1_relat_1('#skF_4'))
      | ~ v1_funct_1(C_33)
      | ~ v1_relat_1(C_33)
      | ~ v1_funct_1(k5_relat_1('#skF_4','#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_97])).

tff(c_132,plain,(
    ~ v1_funct_1(k5_relat_1('#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_103])).

tff(c_135,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_132])).

tff(c_139,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_32,c_30,c_135])).

tff(c_141,plain,(
    v1_funct_1(k5_relat_1('#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_103])).

tff(c_24,plain,(
    v2_funct_1(k5_relat_1('#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_105,plain,(
    ! [A_4,C_33] :
      ( k1_funct_1(k5_relat_1(A_4,C_33),'#skF_1'(A_4)) = k1_funct_1(C_33,k1_funct_1(A_4,'#skF_1'(A_4)))
      | ~ v1_funct_1(C_33)
      | ~ v1_relat_1(C_33)
      | v2_funct_1(A_4)
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(resolution,[status(thm)],[c_12,c_95])).

tff(c_8,plain,(
    ! [A_4] :
      ( k1_funct_1(A_4,'#skF_2'(A_4)) = k1_funct_1(A_4,'#skF_1'(A_4))
      | v2_funct_1(A_4)
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_106,plain,(
    ! [A_35,C_36] :
      ( k1_funct_1(k5_relat_1(A_35,C_36),'#skF_2'(A_35)) = k1_funct_1(C_36,k1_funct_1(A_35,'#skF_2'(A_35)))
      | ~ v1_funct_1(C_36)
      | ~ v1_relat_1(C_36)
      | v2_funct_1(A_35)
      | ~ v1_funct_1(A_35)
      | ~ v1_relat_1(A_35) ) ),
    inference(resolution,[status(thm)],[c_10,c_95])).

tff(c_4,plain,(
    ! [C_10,B_9,A_4] :
      ( C_10 = B_9
      | k1_funct_1(A_4,C_10) != k1_funct_1(A_4,B_9)
      | ~ r2_hidden(C_10,k1_relat_1(A_4))
      | ~ r2_hidden(B_9,k1_relat_1(A_4))
      | ~ v2_funct_1(A_4)
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_191,plain,(
    ! [C_41,A_42,C_43] :
      ( C_41 = '#skF_2'(A_42)
      | k1_funct_1(k5_relat_1(A_42,C_43),C_41) != k1_funct_1(C_43,k1_funct_1(A_42,'#skF_2'(A_42)))
      | ~ r2_hidden(C_41,k1_relat_1(k5_relat_1(A_42,C_43)))
      | ~ r2_hidden('#skF_2'(A_42),k1_relat_1(k5_relat_1(A_42,C_43)))
      | ~ v2_funct_1(k5_relat_1(A_42,C_43))
      | ~ v1_funct_1(k5_relat_1(A_42,C_43))
      | ~ v1_relat_1(k5_relat_1(A_42,C_43))
      | ~ v1_funct_1(C_43)
      | ~ v1_relat_1(C_43)
      | v2_funct_1(A_42)
      | ~ v1_funct_1(A_42)
      | ~ v1_relat_1(A_42) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_4])).

tff(c_263,plain,(
    ! [C_48,A_49,C_50] :
      ( C_48 = '#skF_2'(A_49)
      | k1_funct_1(k5_relat_1(A_49,C_50),C_48) != k1_funct_1(C_50,k1_funct_1(A_49,'#skF_1'(A_49)))
      | ~ r2_hidden(C_48,k1_relat_1(k5_relat_1(A_49,C_50)))
      | ~ r2_hidden('#skF_2'(A_49),k1_relat_1(k5_relat_1(A_49,C_50)))
      | ~ v2_funct_1(k5_relat_1(A_49,C_50))
      | ~ v1_funct_1(k5_relat_1(A_49,C_50))
      | ~ v1_relat_1(k5_relat_1(A_49,C_50))
      | ~ v1_funct_1(C_50)
      | ~ v1_relat_1(C_50)
      | v2_funct_1(A_49)
      | ~ v1_funct_1(A_49)
      | ~ v1_relat_1(A_49)
      | v2_funct_1(A_49)
      | ~ v1_funct_1(A_49)
      | ~ v1_relat_1(A_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_191])).

tff(c_327,plain,(
    ! [A_54,C_55] :
      ( '#skF_2'(A_54) = '#skF_1'(A_54)
      | ~ r2_hidden('#skF_1'(A_54),k1_relat_1(k5_relat_1(A_54,C_55)))
      | ~ r2_hidden('#skF_2'(A_54),k1_relat_1(k5_relat_1(A_54,C_55)))
      | ~ v2_funct_1(k5_relat_1(A_54,C_55))
      | ~ v1_funct_1(k5_relat_1(A_54,C_55))
      | ~ v1_relat_1(k5_relat_1(A_54,C_55))
      | ~ v1_funct_1(C_55)
      | ~ v1_relat_1(C_55)
      | v2_funct_1(A_54)
      | ~ v1_funct_1(A_54)
      | ~ v1_relat_1(A_54) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_263])).

tff(c_330,plain,
    ( '#skF_2'('#skF_4') = '#skF_1'('#skF_4')
    | ~ r2_hidden('#skF_1'('#skF_4'),k1_relat_1(k5_relat_1('#skF_4','#skF_3')))
    | ~ r2_hidden('#skF_2'('#skF_4'),k1_relat_1('#skF_4'))
    | ~ v2_funct_1(k5_relat_1('#skF_4','#skF_3'))
    | ~ v1_funct_1(k5_relat_1('#skF_4','#skF_3'))
    | ~ v1_relat_1(k5_relat_1('#skF_4','#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_327])).

tff(c_332,plain,
    ( '#skF_2'('#skF_4') = '#skF_1'('#skF_4')
    | ~ r2_hidden('#skF_1'('#skF_4'),k1_relat_1('#skF_4'))
    | ~ r2_hidden('#skF_2'('#skF_4'),k1_relat_1('#skF_4'))
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_32,c_30,c_93,c_141,c_24,c_59,c_330])).

tff(c_333,plain,
    ( ~ r2_hidden('#skF_1'('#skF_4'),k1_relat_1('#skF_4'))
    | ~ r2_hidden('#skF_2'('#skF_4'),k1_relat_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_39,c_332])).

tff(c_334,plain,(
    ~ r2_hidden('#skF_2'('#skF_4'),k1_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_333])).

tff(c_337,plain,
    ( v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_334])).

tff(c_340,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_337])).

tff(c_342,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_340])).

tff(c_343,plain,(
    ~ r2_hidden('#skF_1'('#skF_4'),k1_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_333])).

tff(c_363,plain,
    ( v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_343])).

tff(c_366,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_363])).

tff(c_368,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_366])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:59:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.68/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.42  
% 2.68/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.43  %$ r2_hidden > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1 > #skF_3 > #skF_4
% 2.68/1.43  
% 2.68/1.43  %Foreground sorts:
% 2.68/1.43  
% 2.68/1.43  
% 2.68/1.43  %Background operators:
% 2.68/1.43  
% 2.68/1.43  
% 2.68/1.43  %Foreground operators:
% 2.68/1.43  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.68/1.43  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.68/1.43  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.68/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.68/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.68/1.43  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.68/1.43  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.68/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.68/1.43  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.68/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.68/1.43  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.68/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.68/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.68/1.43  tff('#skF_4', type, '#skF_4': $i).
% 2.68/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.68/1.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.68/1.43  
% 2.68/1.44  tff(f_90, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & r1_tarski(k2_relat_1(B), k1_relat_1(A))) => v2_funct_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_funct_1)).
% 2.68/1.44  tff(f_49, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) <=> (![B, C]: (((r2_hidden(B, k1_relat_1(A)) & r2_hidden(C, k1_relat_1(A))) & (k1_funct_1(A, B) = k1_funct_1(A, C))) => (B = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_funct_1)).
% 2.68/1.44  tff(f_61, axiom, (![A, B]: ((((v1_relat_1(A) & v1_funct_1(A)) & v1_relat_1(B)) & v1_funct_1(B)) => (v1_relat_1(k5_relat_1(A, B)) & v1_funct_1(k5_relat_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_funct_1)).
% 2.68/1.44  tff(f_34, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_relat_1)).
% 2.68/1.44  tff(f_74, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(B)) => (k1_funct_1(k5_relat_1(B, C), A) = k1_funct_1(C, k1_funct_1(B, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_funct_1)).
% 2.68/1.44  tff(c_20, plain, (~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.68/1.44  tff(c_28, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.68/1.44  tff(c_26, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.68/1.44  tff(c_12, plain, (![A_4]: (r2_hidden('#skF_1'(A_4), k1_relat_1(A_4)) | v2_funct_1(A_4) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.68/1.44  tff(c_10, plain, (![A_4]: (r2_hidden('#skF_2'(A_4), k1_relat_1(A_4)) | v2_funct_1(A_4) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.68/1.44  tff(c_33, plain, (![A_18]: ('#skF_2'(A_18)!='#skF_1'(A_18) | v2_funct_1(A_18) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.68/1.44  tff(c_36, plain, ('#skF_2'('#skF_4')!='#skF_1'('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_33, c_20])).
% 2.68/1.44  tff(c_39, plain, ('#skF_2'('#skF_4')!='#skF_1'('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_36])).
% 2.68/1.44  tff(c_32, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.68/1.44  tff(c_30, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.68/1.44  tff(c_16, plain, (![A_11, B_12]: (v1_relat_1(k5_relat_1(A_11, B_12)) | ~v1_funct_1(B_12) | ~v1_relat_1(B_12) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.68/1.44  tff(c_22, plain, (r1_tarski(k2_relat_1('#skF_4'), k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.68/1.44  tff(c_53, plain, (![A_26, B_27]: (k1_relat_1(k5_relat_1(A_26, B_27))=k1_relat_1(A_26) | ~r1_tarski(k2_relat_1(A_26), k1_relat_1(B_27)) | ~v1_relat_1(B_27) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.68/1.44  tff(c_56, plain, (k1_relat_1(k5_relat_1('#skF_4', '#skF_3'))=k1_relat_1('#skF_4') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_22, c_53])).
% 2.68/1.44  tff(c_59, plain, (k1_relat_1(k5_relat_1('#skF_4', '#skF_3'))=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_32, c_56])).
% 2.68/1.44  tff(c_2, plain, (![A_1, B_3]: (k1_relat_1(k5_relat_1(A_1, B_3))=k1_relat_1(A_1) | ~r1_tarski(k2_relat_1(A_1), k1_relat_1(B_3)) | ~v1_relat_1(B_3) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.68/1.44  tff(c_72, plain, (![A_1]: (k1_relat_1(k5_relat_1(A_1, k5_relat_1('#skF_4', '#skF_3')))=k1_relat_1(A_1) | ~r1_tarski(k2_relat_1(A_1), k1_relat_1('#skF_4')) | ~v1_relat_1(k5_relat_1('#skF_4', '#skF_3')) | ~v1_relat_1(A_1))), inference(superposition, [status(thm), theory('equality')], [c_59, c_2])).
% 2.68/1.44  tff(c_84, plain, (~v1_relat_1(k5_relat_1('#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_72])).
% 2.68/1.44  tff(c_87, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_16, c_84])).
% 2.68/1.44  tff(c_91, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_32, c_30, c_87])).
% 2.68/1.44  tff(c_93, plain, (v1_relat_1(k5_relat_1('#skF_4', '#skF_3'))), inference(splitRight, [status(thm)], [c_72])).
% 2.68/1.44  tff(c_14, plain, (![A_11, B_12]: (v1_funct_1(k5_relat_1(A_11, B_12)) | ~v1_funct_1(B_12) | ~v1_relat_1(B_12) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.68/1.44  tff(c_95, plain, (![B_32, C_33, A_34]: (k1_funct_1(k5_relat_1(B_32, C_33), A_34)=k1_funct_1(C_33, k1_funct_1(B_32, A_34)) | ~r2_hidden(A_34, k1_relat_1(B_32)) | ~v1_funct_1(C_33) | ~v1_relat_1(C_33) | ~v1_funct_1(B_32) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.68/1.44  tff(c_97, plain, (![C_33, A_34]: (k1_funct_1(k5_relat_1(k5_relat_1('#skF_4', '#skF_3'), C_33), A_34)=k1_funct_1(C_33, k1_funct_1(k5_relat_1('#skF_4', '#skF_3'), A_34)) | ~r2_hidden(A_34, k1_relat_1('#skF_4')) | ~v1_funct_1(C_33) | ~v1_relat_1(C_33) | ~v1_funct_1(k5_relat_1('#skF_4', '#skF_3')) | ~v1_relat_1(k5_relat_1('#skF_4', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_59, c_95])).
% 2.68/1.44  tff(c_103, plain, (![C_33, A_34]: (k1_funct_1(k5_relat_1(k5_relat_1('#skF_4', '#skF_3'), C_33), A_34)=k1_funct_1(C_33, k1_funct_1(k5_relat_1('#skF_4', '#skF_3'), A_34)) | ~r2_hidden(A_34, k1_relat_1('#skF_4')) | ~v1_funct_1(C_33) | ~v1_relat_1(C_33) | ~v1_funct_1(k5_relat_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_97])).
% 2.68/1.44  tff(c_132, plain, (~v1_funct_1(k5_relat_1('#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_103])).
% 2.68/1.44  tff(c_135, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_14, c_132])).
% 2.68/1.44  tff(c_139, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_32, c_30, c_135])).
% 2.68/1.44  tff(c_141, plain, (v1_funct_1(k5_relat_1('#skF_4', '#skF_3'))), inference(splitRight, [status(thm)], [c_103])).
% 2.68/1.44  tff(c_24, plain, (v2_funct_1(k5_relat_1('#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.68/1.44  tff(c_105, plain, (![A_4, C_33]: (k1_funct_1(k5_relat_1(A_4, C_33), '#skF_1'(A_4))=k1_funct_1(C_33, k1_funct_1(A_4, '#skF_1'(A_4))) | ~v1_funct_1(C_33) | ~v1_relat_1(C_33) | v2_funct_1(A_4) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(resolution, [status(thm)], [c_12, c_95])).
% 2.68/1.44  tff(c_8, plain, (![A_4]: (k1_funct_1(A_4, '#skF_2'(A_4))=k1_funct_1(A_4, '#skF_1'(A_4)) | v2_funct_1(A_4) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.68/1.44  tff(c_106, plain, (![A_35, C_36]: (k1_funct_1(k5_relat_1(A_35, C_36), '#skF_2'(A_35))=k1_funct_1(C_36, k1_funct_1(A_35, '#skF_2'(A_35))) | ~v1_funct_1(C_36) | ~v1_relat_1(C_36) | v2_funct_1(A_35) | ~v1_funct_1(A_35) | ~v1_relat_1(A_35))), inference(resolution, [status(thm)], [c_10, c_95])).
% 2.68/1.44  tff(c_4, plain, (![C_10, B_9, A_4]: (C_10=B_9 | k1_funct_1(A_4, C_10)!=k1_funct_1(A_4, B_9) | ~r2_hidden(C_10, k1_relat_1(A_4)) | ~r2_hidden(B_9, k1_relat_1(A_4)) | ~v2_funct_1(A_4) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.68/1.44  tff(c_191, plain, (![C_41, A_42, C_43]: (C_41='#skF_2'(A_42) | k1_funct_1(k5_relat_1(A_42, C_43), C_41)!=k1_funct_1(C_43, k1_funct_1(A_42, '#skF_2'(A_42))) | ~r2_hidden(C_41, k1_relat_1(k5_relat_1(A_42, C_43))) | ~r2_hidden('#skF_2'(A_42), k1_relat_1(k5_relat_1(A_42, C_43))) | ~v2_funct_1(k5_relat_1(A_42, C_43)) | ~v1_funct_1(k5_relat_1(A_42, C_43)) | ~v1_relat_1(k5_relat_1(A_42, C_43)) | ~v1_funct_1(C_43) | ~v1_relat_1(C_43) | v2_funct_1(A_42) | ~v1_funct_1(A_42) | ~v1_relat_1(A_42))), inference(superposition, [status(thm), theory('equality')], [c_106, c_4])).
% 2.68/1.44  tff(c_263, plain, (![C_48, A_49, C_50]: (C_48='#skF_2'(A_49) | k1_funct_1(k5_relat_1(A_49, C_50), C_48)!=k1_funct_1(C_50, k1_funct_1(A_49, '#skF_1'(A_49))) | ~r2_hidden(C_48, k1_relat_1(k5_relat_1(A_49, C_50))) | ~r2_hidden('#skF_2'(A_49), k1_relat_1(k5_relat_1(A_49, C_50))) | ~v2_funct_1(k5_relat_1(A_49, C_50)) | ~v1_funct_1(k5_relat_1(A_49, C_50)) | ~v1_relat_1(k5_relat_1(A_49, C_50)) | ~v1_funct_1(C_50) | ~v1_relat_1(C_50) | v2_funct_1(A_49) | ~v1_funct_1(A_49) | ~v1_relat_1(A_49) | v2_funct_1(A_49) | ~v1_funct_1(A_49) | ~v1_relat_1(A_49))), inference(superposition, [status(thm), theory('equality')], [c_8, c_191])).
% 2.68/1.44  tff(c_327, plain, (![A_54, C_55]: ('#skF_2'(A_54)='#skF_1'(A_54) | ~r2_hidden('#skF_1'(A_54), k1_relat_1(k5_relat_1(A_54, C_55))) | ~r2_hidden('#skF_2'(A_54), k1_relat_1(k5_relat_1(A_54, C_55))) | ~v2_funct_1(k5_relat_1(A_54, C_55)) | ~v1_funct_1(k5_relat_1(A_54, C_55)) | ~v1_relat_1(k5_relat_1(A_54, C_55)) | ~v1_funct_1(C_55) | ~v1_relat_1(C_55) | v2_funct_1(A_54) | ~v1_funct_1(A_54) | ~v1_relat_1(A_54))), inference(superposition, [status(thm), theory('equality')], [c_105, c_263])).
% 2.68/1.44  tff(c_330, plain, ('#skF_2'('#skF_4')='#skF_1'('#skF_4') | ~r2_hidden('#skF_1'('#skF_4'), k1_relat_1(k5_relat_1('#skF_4', '#skF_3'))) | ~r2_hidden('#skF_2'('#skF_4'), k1_relat_1('#skF_4')) | ~v2_funct_1(k5_relat_1('#skF_4', '#skF_3')) | ~v1_funct_1(k5_relat_1('#skF_4', '#skF_3')) | ~v1_relat_1(k5_relat_1('#skF_4', '#skF_3')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_59, c_327])).
% 2.68/1.44  tff(c_332, plain, ('#skF_2'('#skF_4')='#skF_1'('#skF_4') | ~r2_hidden('#skF_1'('#skF_4'), k1_relat_1('#skF_4')) | ~r2_hidden('#skF_2'('#skF_4'), k1_relat_1('#skF_4')) | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_32, c_30, c_93, c_141, c_24, c_59, c_330])).
% 2.68/1.44  tff(c_333, plain, (~r2_hidden('#skF_1'('#skF_4'), k1_relat_1('#skF_4')) | ~r2_hidden('#skF_2'('#skF_4'), k1_relat_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_20, c_39, c_332])).
% 2.68/1.44  tff(c_334, plain, (~r2_hidden('#skF_2'('#skF_4'), k1_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_333])).
% 2.68/1.44  tff(c_337, plain, (v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_10, c_334])).
% 2.68/1.44  tff(c_340, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_337])).
% 2.68/1.44  tff(c_342, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_340])).
% 2.68/1.44  tff(c_343, plain, (~r2_hidden('#skF_1'('#skF_4'), k1_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_333])).
% 2.68/1.44  tff(c_363, plain, (v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_12, c_343])).
% 2.68/1.44  tff(c_366, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_363])).
% 2.68/1.44  tff(c_368, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_366])).
% 2.68/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.44  
% 2.68/1.44  Inference rules
% 2.68/1.44  ----------------------
% 2.68/1.44  #Ref     : 1
% 2.68/1.44  #Sup     : 78
% 2.68/1.44  #Fact    : 0
% 2.68/1.44  #Define  : 0
% 2.68/1.44  #Split   : 4
% 2.68/1.44  #Chain   : 0
% 2.68/1.44  #Close   : 0
% 2.68/1.44  
% 2.68/1.44  Ordering : KBO
% 2.68/1.44  
% 2.68/1.44  Simplification rules
% 2.68/1.44  ----------------------
% 2.68/1.44  #Subsume      : 3
% 2.68/1.44  #Demod        : 84
% 2.68/1.44  #Tautology    : 40
% 2.68/1.44  #SimpNegUnit  : 6
% 2.68/1.44  #BackRed      : 0
% 2.68/1.44  
% 2.68/1.44  #Partial instantiations: 0
% 2.68/1.44  #Strategies tried      : 1
% 2.68/1.44  
% 2.68/1.44  Timing (in seconds)
% 2.68/1.44  ----------------------
% 2.68/1.44  Preprocessing        : 0.30
% 2.68/1.44  Parsing              : 0.16
% 2.68/1.44  CNF conversion       : 0.02
% 2.68/1.44  Main loop            : 0.33
% 2.68/1.44  Inferencing          : 0.12
% 2.68/1.44  Reduction            : 0.10
% 2.68/1.44  Demodulation         : 0.07
% 2.68/1.44  BG Simplification    : 0.02
% 2.68/1.44  Subsumption          : 0.08
% 2.68/1.44  Abstraction          : 0.02
% 2.68/1.44  MUC search           : 0.00
% 2.68/1.44  Cooper               : 0.00
% 2.68/1.44  Total                : 0.67
% 2.68/1.44  Index Insertion      : 0.00
% 2.68/1.45  Index Deletion       : 0.00
% 2.68/1.45  Index Matching       : 0.00
% 2.68/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
