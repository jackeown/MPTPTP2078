%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:03 EST 2020

% Result     : Theorem 3.95s
% Output     : CNFRefutation 3.95s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 247 expanded)
%              Number of leaves         :   23 ( 101 expanded)
%              Depth                    :   13
%              Number of atoms          :  166 ( 949 expanded)
%              Number of equality atoms :   45 ( 306 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(f_108,negated_conjecture,(
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

tff(f_57,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_80,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_90,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_39,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_70,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( k1_relat_1(k5_relat_1(B,A)) = k1_relat_1(B)
           => r1_tarski(k2_relat_1(B),k1_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_funct_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

tff(c_26,plain,(
    k2_funct_1('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_36,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_40,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_38,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_14,plain,(
    ! [A_12] :
      ( v1_relat_1(k2_funct_1(A_12))
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_32,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_28,plain,(
    k6_relat_1(k1_relat_1('#skF_1')) = k5_relat_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_104,plain,(
    ! [A_24] :
      ( k2_relat_1(k2_funct_1(A_24)) = k1_relat_1(A_24)
      | ~ v2_funct_1(A_24)
      | ~ v1_funct_1(A_24)
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_10,plain,(
    ! [A_11] :
      ( k5_relat_1(A_11,k6_relat_1(k2_relat_1(A_11))) = A_11
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_395,plain,(
    ! [A_42] :
      ( k5_relat_1(k2_funct_1(A_42),k6_relat_1(k1_relat_1(A_42))) = k2_funct_1(A_42)
      | ~ v1_relat_1(k2_funct_1(A_42))
      | ~ v2_funct_1(A_42)
      | ~ v1_funct_1(A_42)
      | ~ v1_relat_1(A_42) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_10])).

tff(c_413,plain,
    ( k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1','#skF_2')) = k2_funct_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_395])).

tff(c_421,plain,
    ( k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1','#skF_2')) = k2_funct_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_32,c_413])).

tff(c_422,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_421])).

tff(c_425,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_422])).

tff(c_429,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_425])).

tff(c_430,plain,(
    k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1','#skF_2')) = k2_funct_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_421])).

tff(c_431,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_421])).

tff(c_30,plain,(
    k2_relat_1('#skF_1') = k1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_22,plain,(
    ! [A_17] :
      ( k5_relat_1(k2_funct_1(A_17),A_17) = k6_relat_1(k2_relat_1(A_17))
      | ~ v2_funct_1(A_17)
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_210,plain,(
    ! [A_33,B_34,C_35] :
      ( k5_relat_1(k5_relat_1(A_33,B_34),C_35) = k5_relat_1(A_33,k5_relat_1(B_34,C_35))
      | ~ v1_relat_1(C_35)
      | ~ v1_relat_1(B_34)
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1271,plain,(
    ! [A_66,C_67] :
      ( k5_relat_1(k6_relat_1(k2_relat_1(A_66)),C_67) = k5_relat_1(k2_funct_1(A_66),k5_relat_1(A_66,C_67))
      | ~ v1_relat_1(C_67)
      | ~ v1_relat_1(A_66)
      | ~ v1_relat_1(k2_funct_1(A_66))
      | ~ v2_funct_1(A_66)
      | ~ v1_funct_1(A_66)
      | ~ v1_relat_1(A_66) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_210])).

tff(c_1444,plain,(
    ! [C_67] :
      ( k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')),C_67) = k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1',C_67))
      | ~ v1_relat_1(C_67)
      | ~ v1_relat_1('#skF_1')
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v2_funct_1('#skF_1')
      | ~ v1_funct_1('#skF_1')
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1271])).

tff(c_1478,plain,(
    ! [C_68] :
      ( k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')),C_68) = k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1',C_68))
      | ~ v1_relat_1(C_68) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_32,c_431,c_40,c_1444])).

tff(c_4,plain,(
    ! [A_8] : k1_relat_1(k6_relat_1(A_8)) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_69,plain,(
    k1_relat_1(k5_relat_1('#skF_1','#skF_2')) = k1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_4])).

tff(c_24,plain,(
    ! [A_17] :
      ( k5_relat_1(A_17,k2_funct_1(A_17)) = k6_relat_1(k1_relat_1(A_17))
      | ~ v2_funct_1(A_17)
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_12,plain,(
    ! [A_12] :
      ( v1_funct_1(k2_funct_1(A_12))
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_20,plain,(
    ! [A_16] :
      ( k1_relat_1(k2_funct_1(A_16)) = k2_relat_1(A_16)
      | ~ v2_funct_1(A_16)
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_323,plain,(
    ! [B_38,A_39] :
      ( r1_tarski(k2_relat_1(B_38),k1_relat_1(A_39))
      | k1_relat_1(k5_relat_1(B_38,A_39)) != k1_relat_1(B_38)
      | ~ v1_funct_1(B_38)
      | ~ v1_relat_1(B_38)
      | ~ v1_funct_1(A_39)
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_344,plain,(
    ! [A_39] :
      ( r1_tarski(k1_relat_1('#skF_2'),k1_relat_1(A_39))
      | k1_relat_1(k5_relat_1('#skF_1',A_39)) != k1_relat_1('#skF_1')
      | ~ v1_funct_1('#skF_1')
      | ~ v1_relat_1('#skF_1')
      | ~ v1_funct_1(A_39)
      | ~ v1_relat_1(A_39) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_323])).

tff(c_349,plain,(
    ! [A_40] :
      ( r1_tarski(k1_relat_1('#skF_2'),k1_relat_1(A_40))
      | k1_relat_1(k5_relat_1('#skF_1',A_40)) != k1_relat_1('#skF_1')
      | ~ v1_funct_1(A_40)
      | ~ v1_relat_1(A_40) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_344])).

tff(c_539,plain,(
    ! [A_47] :
      ( r1_tarski(k1_relat_1('#skF_2'),k2_relat_1(A_47))
      | k1_relat_1(k5_relat_1('#skF_1',k2_funct_1(A_47))) != k1_relat_1('#skF_1')
      | ~ v1_funct_1(k2_funct_1(A_47))
      | ~ v1_relat_1(k2_funct_1(A_47))
      | ~ v2_funct_1(A_47)
      | ~ v1_funct_1(A_47)
      | ~ v1_relat_1(A_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_349])).

tff(c_554,plain,
    ( r1_tarski(k1_relat_1('#skF_2'),k1_relat_1('#skF_2'))
    | k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_539])).

tff(c_559,plain,
    ( r1_tarski(k1_relat_1('#skF_2'),k1_relat_1('#skF_2'))
    | k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_32,c_431,c_554])).

tff(c_560,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_559])).

tff(c_563,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_560])).

tff(c_567,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_563])).

tff(c_568,plain,
    ( k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1')
    | r1_tarski(k1_relat_1('#skF_2'),k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_559])).

tff(c_570,plain,(
    k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_568])).

tff(c_573,plain,
    ( k1_relat_1(k6_relat_1(k1_relat_1('#skF_1'))) != k1_relat_1('#skF_1')
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_570])).

tff(c_576,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_32,c_69,c_28,c_573])).

tff(c_577,plain,(
    r1_tarski(k1_relat_1('#skF_2'),k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_568])).

tff(c_8,plain,(
    ! [A_9,B_10] :
      ( k5_relat_1(k6_relat_1(A_9),B_10) = B_10
      | ~ r1_tarski(k1_relat_1(B_10),A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_611,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')),'#skF_2') = '#skF_2'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_577,c_8])).

tff(c_614,plain,(
    k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')),'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_611])).

tff(c_1508,plain,
    ( k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1','#skF_2')) = '#skF_2'
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1478,c_614])).

tff(c_1593,plain,(
    k2_funct_1('#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_430,c_1508])).

tff(c_1595,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_1593])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:05:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.95/1.71  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.95/1.71  
% 3.95/1.71  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.95/1.71  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1
% 3.95/1.71  
% 3.95/1.71  %Foreground sorts:
% 3.95/1.71  
% 3.95/1.71  
% 3.95/1.71  %Background operators:
% 3.95/1.71  
% 3.95/1.71  
% 3.95/1.71  %Foreground operators:
% 3.95/1.71  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.95/1.71  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.95/1.71  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.95/1.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.95/1.71  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.95/1.71  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.95/1.71  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.95/1.71  tff('#skF_2', type, '#skF_2': $i).
% 3.95/1.71  tff('#skF_1', type, '#skF_1': $i).
% 3.95/1.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.95/1.71  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.95/1.71  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.95/1.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.95/1.71  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.95/1.71  
% 3.95/1.73  tff(f_108, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(A) = k1_relat_1(B))) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_funct_1)).
% 3.95/1.73  tff(f_57, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 3.95/1.73  tff(f_80, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 3.95/1.73  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 3.95/1.73  tff(f_90, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 3.95/1.73  tff(f_35, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 3.95/1.73  tff(f_39, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 3.95/1.73  tff(f_70, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(k5_relat_1(B, A)) = k1_relat_1(B)) => r1_tarski(k2_relat_1(B), k1_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_funct_1)).
% 3.95/1.73  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_relat_1)).
% 3.95/1.73  tff(c_26, plain, (k2_funct_1('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.95/1.73  tff(c_36, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.95/1.73  tff(c_40, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.95/1.73  tff(c_38, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.95/1.73  tff(c_14, plain, (![A_12]: (v1_relat_1(k2_funct_1(A_12)) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.95/1.73  tff(c_32, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.95/1.73  tff(c_28, plain, (k6_relat_1(k1_relat_1('#skF_1'))=k5_relat_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.95/1.73  tff(c_104, plain, (![A_24]: (k2_relat_1(k2_funct_1(A_24))=k1_relat_1(A_24) | ~v2_funct_1(A_24) | ~v1_funct_1(A_24) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.95/1.73  tff(c_10, plain, (![A_11]: (k5_relat_1(A_11, k6_relat_1(k2_relat_1(A_11)))=A_11 | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.95/1.73  tff(c_395, plain, (![A_42]: (k5_relat_1(k2_funct_1(A_42), k6_relat_1(k1_relat_1(A_42)))=k2_funct_1(A_42) | ~v1_relat_1(k2_funct_1(A_42)) | ~v2_funct_1(A_42) | ~v1_funct_1(A_42) | ~v1_relat_1(A_42))), inference(superposition, [status(thm), theory('equality')], [c_104, c_10])).
% 3.95/1.73  tff(c_413, plain, (k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', '#skF_2'))=k2_funct_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_28, c_395])).
% 3.95/1.73  tff(c_421, plain, (k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', '#skF_2'))=k2_funct_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_32, c_413])).
% 3.95/1.73  tff(c_422, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_421])).
% 3.95/1.73  tff(c_425, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_14, c_422])).
% 3.95/1.73  tff(c_429, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_425])).
% 3.95/1.73  tff(c_430, plain, (k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', '#skF_2'))=k2_funct_1('#skF_1')), inference(splitRight, [status(thm)], [c_421])).
% 3.95/1.73  tff(c_431, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_421])).
% 3.95/1.73  tff(c_30, plain, (k2_relat_1('#skF_1')=k1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.95/1.73  tff(c_22, plain, (![A_17]: (k5_relat_1(k2_funct_1(A_17), A_17)=k6_relat_1(k2_relat_1(A_17)) | ~v2_funct_1(A_17) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.95/1.73  tff(c_210, plain, (![A_33, B_34, C_35]: (k5_relat_1(k5_relat_1(A_33, B_34), C_35)=k5_relat_1(A_33, k5_relat_1(B_34, C_35)) | ~v1_relat_1(C_35) | ~v1_relat_1(B_34) | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.95/1.73  tff(c_1271, plain, (![A_66, C_67]: (k5_relat_1(k6_relat_1(k2_relat_1(A_66)), C_67)=k5_relat_1(k2_funct_1(A_66), k5_relat_1(A_66, C_67)) | ~v1_relat_1(C_67) | ~v1_relat_1(A_66) | ~v1_relat_1(k2_funct_1(A_66)) | ~v2_funct_1(A_66) | ~v1_funct_1(A_66) | ~v1_relat_1(A_66))), inference(superposition, [status(thm), theory('equality')], [c_22, c_210])).
% 3.95/1.73  tff(c_1444, plain, (![C_67]: (k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')), C_67)=k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', C_67)) | ~v1_relat_1(C_67) | ~v1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_30, c_1271])).
% 3.95/1.73  tff(c_1478, plain, (![C_68]: (k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')), C_68)=k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', C_68)) | ~v1_relat_1(C_68))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_32, c_431, c_40, c_1444])).
% 3.95/1.73  tff(c_4, plain, (![A_8]: (k1_relat_1(k6_relat_1(A_8))=A_8)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.95/1.73  tff(c_69, plain, (k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))=k1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_28, c_4])).
% 3.95/1.73  tff(c_24, plain, (![A_17]: (k5_relat_1(A_17, k2_funct_1(A_17))=k6_relat_1(k1_relat_1(A_17)) | ~v2_funct_1(A_17) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.95/1.73  tff(c_12, plain, (![A_12]: (v1_funct_1(k2_funct_1(A_12)) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.95/1.73  tff(c_20, plain, (![A_16]: (k1_relat_1(k2_funct_1(A_16))=k2_relat_1(A_16) | ~v2_funct_1(A_16) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.95/1.73  tff(c_323, plain, (![B_38, A_39]: (r1_tarski(k2_relat_1(B_38), k1_relat_1(A_39)) | k1_relat_1(k5_relat_1(B_38, A_39))!=k1_relat_1(B_38) | ~v1_funct_1(B_38) | ~v1_relat_1(B_38) | ~v1_funct_1(A_39) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.95/1.73  tff(c_344, plain, (![A_39]: (r1_tarski(k1_relat_1('#skF_2'), k1_relat_1(A_39)) | k1_relat_1(k5_relat_1('#skF_1', A_39))!=k1_relat_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1') | ~v1_funct_1(A_39) | ~v1_relat_1(A_39))), inference(superposition, [status(thm), theory('equality')], [c_30, c_323])).
% 3.95/1.73  tff(c_349, plain, (![A_40]: (r1_tarski(k1_relat_1('#skF_2'), k1_relat_1(A_40)) | k1_relat_1(k5_relat_1('#skF_1', A_40))!=k1_relat_1('#skF_1') | ~v1_funct_1(A_40) | ~v1_relat_1(A_40))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_344])).
% 3.95/1.73  tff(c_539, plain, (![A_47]: (r1_tarski(k1_relat_1('#skF_2'), k2_relat_1(A_47)) | k1_relat_1(k5_relat_1('#skF_1', k2_funct_1(A_47)))!=k1_relat_1('#skF_1') | ~v1_funct_1(k2_funct_1(A_47)) | ~v1_relat_1(k2_funct_1(A_47)) | ~v2_funct_1(A_47) | ~v1_funct_1(A_47) | ~v1_relat_1(A_47))), inference(superposition, [status(thm), theory('equality')], [c_20, c_349])).
% 3.95/1.73  tff(c_554, plain, (r1_tarski(k1_relat_1('#skF_2'), k1_relat_1('#skF_2')) | k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1') | ~v1_funct_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_30, c_539])).
% 3.95/1.73  tff(c_559, plain, (r1_tarski(k1_relat_1('#skF_2'), k1_relat_1('#skF_2')) | k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1') | ~v1_funct_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_32, c_431, c_554])).
% 3.95/1.73  tff(c_560, plain, (~v1_funct_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_559])).
% 3.95/1.73  tff(c_563, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_12, c_560])).
% 3.95/1.73  tff(c_567, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_563])).
% 3.95/1.73  tff(c_568, plain, (k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1') | r1_tarski(k1_relat_1('#skF_2'), k1_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_559])).
% 3.95/1.73  tff(c_570, plain, (k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_568])).
% 3.95/1.73  tff(c_573, plain, (k1_relat_1(k6_relat_1(k1_relat_1('#skF_1')))!=k1_relat_1('#skF_1') | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_24, c_570])).
% 3.95/1.73  tff(c_576, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_32, c_69, c_28, c_573])).
% 3.95/1.73  tff(c_577, plain, (r1_tarski(k1_relat_1('#skF_2'), k1_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_568])).
% 3.95/1.73  tff(c_8, plain, (![A_9, B_10]: (k5_relat_1(k6_relat_1(A_9), B_10)=B_10 | ~r1_tarski(k1_relat_1(B_10), A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.95/1.73  tff(c_611, plain, (k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')), '#skF_2')='#skF_2' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_577, c_8])).
% 3.95/1.73  tff(c_614, plain, (k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')), '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_611])).
% 3.95/1.73  tff(c_1508, plain, (k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', '#skF_2'))='#skF_2' | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1478, c_614])).
% 3.95/1.73  tff(c_1593, plain, (k2_funct_1('#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_430, c_1508])).
% 3.95/1.73  tff(c_1595, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_1593])).
% 3.95/1.73  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.95/1.73  
% 3.95/1.73  Inference rules
% 3.95/1.73  ----------------------
% 3.95/1.73  #Ref     : 0
% 3.95/1.73  #Sup     : 366
% 3.95/1.73  #Fact    : 0
% 3.95/1.73  #Define  : 0
% 3.95/1.73  #Split   : 11
% 3.95/1.73  #Chain   : 0
% 3.95/1.73  #Close   : 0
% 3.95/1.73  
% 3.95/1.73  Ordering : KBO
% 3.95/1.73  
% 3.95/1.73  Simplification rules
% 3.95/1.73  ----------------------
% 3.95/1.73  #Subsume      : 72
% 3.95/1.73  #Demod        : 361
% 3.95/1.73  #Tautology    : 97
% 3.95/1.73  #SimpNegUnit  : 1
% 3.95/1.73  #BackRed      : 0
% 3.95/1.73  
% 3.95/1.73  #Partial instantiations: 0
% 3.95/1.73  #Strategies tried      : 1
% 3.95/1.73  
% 3.95/1.73  Timing (in seconds)
% 3.95/1.73  ----------------------
% 3.95/1.73  Preprocessing        : 0.34
% 3.95/1.73  Parsing              : 0.18
% 3.95/1.73  CNF conversion       : 0.02
% 3.95/1.73  Main loop            : 0.57
% 3.95/1.73  Inferencing          : 0.21
% 3.95/1.73  Reduction            : 0.20
% 3.95/1.73  Demodulation         : 0.14
% 3.95/1.73  BG Simplification    : 0.03
% 3.95/1.73  Subsumption          : 0.11
% 3.95/1.73  Abstraction          : 0.04
% 3.95/1.73  MUC search           : 0.00
% 3.95/1.73  Cooper               : 0.00
% 3.95/1.73  Total                : 0.94
% 3.95/1.73  Index Insertion      : 0.00
% 3.95/1.73  Index Deletion       : 0.00
% 3.95/1.73  Index Matching       : 0.00
% 3.95/1.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
