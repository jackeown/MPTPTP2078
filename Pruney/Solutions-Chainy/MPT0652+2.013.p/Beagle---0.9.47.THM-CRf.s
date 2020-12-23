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
% DateTime   : Thu Dec  3 10:03:54 EST 2020

% Result     : Theorem 2.97s
% Output     : CNFRefutation 3.18s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 203 expanded)
%              Number of leaves         :   22 (  77 expanded)
%              Depth                    :   12
%              Number of atoms          :  144 ( 546 expanded)
%              Number of equality atoms :   53 ( 229 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_funct_1)).

tff(f_82,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_68,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_56,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( k1_relat_1(A) = k1_relat_1(B)
               => k1_relat_1(k5_relat_1(C,A)) = k1_relat_1(k5_relat_1(C,B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t198_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).

tff(c_36,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_34,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_32,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_26,plain,(
    ! [A_17] :
      ( k2_relat_1(k2_funct_1(A_17)) = k1_relat_1(A_17)
      | ~ v2_funct_1(A_17)
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_28,plain,(
    ! [A_17] :
      ( k1_relat_1(k2_funct_1(A_17)) = k2_relat_1(A_17)
      | ~ v2_funct_1(A_17)
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_20,plain,(
    ! [A_15] :
      ( v1_relat_1(k2_funct_1(A_15))
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_22,plain,(
    ! [A_16] : v1_relat_1(k6_relat_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_12,plain,(
    ! [A_13] : k1_relat_1(k6_relat_1(A_13)) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_16,plain,(
    ! [A_14] :
      ( k5_relat_1(A_14,k6_relat_1(k2_relat_1(A_14))) = A_14
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_156,plain,(
    ! [C_35,B_36,A_37] :
      ( k1_relat_1(k5_relat_1(C_35,B_36)) = k1_relat_1(k5_relat_1(C_35,A_37))
      | k1_relat_1(B_36) != k1_relat_1(A_37)
      | ~ v1_relat_1(C_35)
      | ~ v1_relat_1(B_36)
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_201,plain,(
    ! [A_14,A_37] :
      ( k1_relat_1(k5_relat_1(A_14,A_37)) = k1_relat_1(A_14)
      | k1_relat_1(k6_relat_1(k2_relat_1(A_14))) != k1_relat_1(A_37)
      | ~ v1_relat_1(A_14)
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(A_14)))
      | ~ v1_relat_1(A_37)
      | ~ v1_relat_1(A_14) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_156])).

tff(c_301,plain,(
    ! [A_42,A_43] :
      ( k1_relat_1(k5_relat_1(A_42,A_43)) = k1_relat_1(A_42)
      | k2_relat_1(A_42) != k1_relat_1(A_43)
      | ~ v1_relat_1(A_43)
      | ~ v1_relat_1(A_42) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_12,c_201])).

tff(c_30,plain,
    ( k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1')
    | k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_60,plain,(
    k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_320,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1')
    | k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_301,c_60])).

tff(c_343,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1')
    | k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_320])).

tff(c_352,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_343])).

tff(c_355,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_352])).

tff(c_359,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_355])).

tff(c_360,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1')
    | k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_343])).

tff(c_362,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_360])).

tff(c_392,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_362])).

tff(c_396,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_392])).

tff(c_397,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_360])).

tff(c_422,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_397])).

tff(c_426,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_422])).

tff(c_427,plain,(
    k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_592,plain,(
    ! [C_59,B_60,A_61] :
      ( k1_relat_1(k5_relat_1(C_59,B_60)) = k1_relat_1(k5_relat_1(C_59,A_61))
      | k1_relat_1(B_60) != k1_relat_1(A_61)
      | ~ v1_relat_1(C_59)
      | ~ v1_relat_1(B_60)
      | ~ v1_relat_1(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_649,plain,(
    ! [A_14,A_61] :
      ( k1_relat_1(k5_relat_1(A_14,A_61)) = k1_relat_1(A_14)
      | k1_relat_1(k6_relat_1(k2_relat_1(A_14))) != k1_relat_1(A_61)
      | ~ v1_relat_1(A_14)
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(A_14)))
      | ~ v1_relat_1(A_61)
      | ~ v1_relat_1(A_14) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_592])).

tff(c_728,plain,(
    ! [A_64,A_65] :
      ( k1_relat_1(k5_relat_1(A_64,A_65)) = k1_relat_1(A_64)
      | k2_relat_1(A_64) != k1_relat_1(A_65)
      | ~ v1_relat_1(A_65)
      | ~ v1_relat_1(A_64) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_12,c_649])).

tff(c_428,plain,(
    k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) = k2_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_750,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1')
    | k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_728,c_428])).

tff(c_779,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1')
    | k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_750])).

tff(c_794,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_779])).

tff(c_797,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_794])).

tff(c_801,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_797])).

tff(c_803,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_779])).

tff(c_802,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1')
    | k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_779])).

tff(c_804,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_802])).

tff(c_807,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_804])).

tff(c_811,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_807])).

tff(c_813,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_802])).

tff(c_10,plain,(
    ! [B_12,A_10] :
      ( k2_relat_1(k5_relat_1(B_12,A_10)) = k2_relat_1(A_10)
      | ~ r1_tarski(k1_relat_1(A_10),k2_relat_1(B_12))
      | ~ v1_relat_1(B_12)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_843,plain,(
    ! [A_10] :
      ( k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),A_10)) = k2_relat_1(A_10)
      | ~ r1_tarski(k1_relat_1(A_10),k1_relat_1('#skF_1'))
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v1_relat_1(A_10) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_813,c_10])).

tff(c_985,plain,(
    ! [A_67] :
      ( k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),A_67)) = k2_relat_1(A_67)
      | ~ r1_tarski(k1_relat_1(A_67),k1_relat_1('#skF_1'))
      | ~ v1_relat_1(A_67) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_803,c_843])).

tff(c_1016,plain,
    ( k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) = k2_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_985])).

tff(c_1023,plain,(
    k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) = k2_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1016])).

tff(c_1025,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_427,c_1023])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:10:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.97/1.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.97/1.45  
% 2.97/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.97/1.45  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1
% 2.97/1.45  
% 2.97/1.45  %Foreground sorts:
% 2.97/1.45  
% 2.97/1.45  
% 2.97/1.45  %Background operators:
% 2.97/1.45  
% 2.97/1.45  
% 2.97/1.45  %Foreground operators:
% 2.97/1.45  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.97/1.45  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.97/1.45  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.97/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.97/1.45  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.97/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.97/1.45  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.97/1.45  tff('#skF_1', type, '#skF_1': $i).
% 2.97/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.97/1.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.97/1.45  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.97/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.97/1.45  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.97/1.45  
% 3.18/1.47  tff(f_93, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)) & (k2_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_funct_1)).
% 3.18/1.47  tff(f_82, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 3.18/1.47  tff(f_68, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 3.18/1.47  tff(f_72, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 3.18/1.47  tff(f_56, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 3.18/1.47  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 3.18/1.47  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((k1_relat_1(A) = k1_relat_1(B)) => (k1_relat_1(k5_relat_1(C, A)) = k1_relat_1(k5_relat_1(C, B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t198_relat_1)).
% 3.18/1.47  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.18/1.47  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_relat_1)).
% 3.18/1.47  tff(c_36, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.18/1.47  tff(c_34, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.18/1.47  tff(c_32, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.18/1.47  tff(c_26, plain, (![A_17]: (k2_relat_1(k2_funct_1(A_17))=k1_relat_1(A_17) | ~v2_funct_1(A_17) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.18/1.47  tff(c_28, plain, (![A_17]: (k1_relat_1(k2_funct_1(A_17))=k2_relat_1(A_17) | ~v2_funct_1(A_17) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.18/1.47  tff(c_20, plain, (![A_15]: (v1_relat_1(k2_funct_1(A_15)) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.18/1.47  tff(c_22, plain, (![A_16]: (v1_relat_1(k6_relat_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.18/1.47  tff(c_12, plain, (![A_13]: (k1_relat_1(k6_relat_1(A_13))=A_13)), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.18/1.47  tff(c_16, plain, (![A_14]: (k5_relat_1(A_14, k6_relat_1(k2_relat_1(A_14)))=A_14 | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.18/1.47  tff(c_156, plain, (![C_35, B_36, A_37]: (k1_relat_1(k5_relat_1(C_35, B_36))=k1_relat_1(k5_relat_1(C_35, A_37)) | k1_relat_1(B_36)!=k1_relat_1(A_37) | ~v1_relat_1(C_35) | ~v1_relat_1(B_36) | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.18/1.47  tff(c_201, plain, (![A_14, A_37]: (k1_relat_1(k5_relat_1(A_14, A_37))=k1_relat_1(A_14) | k1_relat_1(k6_relat_1(k2_relat_1(A_14)))!=k1_relat_1(A_37) | ~v1_relat_1(A_14) | ~v1_relat_1(k6_relat_1(k2_relat_1(A_14))) | ~v1_relat_1(A_37) | ~v1_relat_1(A_14))), inference(superposition, [status(thm), theory('equality')], [c_16, c_156])).
% 3.18/1.47  tff(c_301, plain, (![A_42, A_43]: (k1_relat_1(k5_relat_1(A_42, A_43))=k1_relat_1(A_42) | k2_relat_1(A_42)!=k1_relat_1(A_43) | ~v1_relat_1(A_43) | ~v1_relat_1(A_42))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_12, c_201])).
% 3.18/1.47  tff(c_30, plain, (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1') | k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.18/1.47  tff(c_60, plain, (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_30])).
% 3.18/1.47  tff(c_320, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1') | k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_301, c_60])).
% 3.18/1.47  tff(c_343, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1') | k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_320])).
% 3.18/1.47  tff(c_352, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_343])).
% 3.18/1.47  tff(c_355, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_20, c_352])).
% 3.18/1.47  tff(c_359, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_355])).
% 3.18/1.47  tff(c_360, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1') | k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_343])).
% 3.18/1.47  tff(c_362, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_360])).
% 3.18/1.47  tff(c_392, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_28, c_362])).
% 3.18/1.47  tff(c_396, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_392])).
% 3.18/1.47  tff(c_397, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_360])).
% 3.18/1.47  tff(c_422, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_26, c_397])).
% 3.18/1.47  tff(c_426, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_422])).
% 3.18/1.47  tff(c_427, plain, (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_30])).
% 3.18/1.47  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.18/1.47  tff(c_592, plain, (![C_59, B_60, A_61]: (k1_relat_1(k5_relat_1(C_59, B_60))=k1_relat_1(k5_relat_1(C_59, A_61)) | k1_relat_1(B_60)!=k1_relat_1(A_61) | ~v1_relat_1(C_59) | ~v1_relat_1(B_60) | ~v1_relat_1(A_61))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.18/1.47  tff(c_649, plain, (![A_14, A_61]: (k1_relat_1(k5_relat_1(A_14, A_61))=k1_relat_1(A_14) | k1_relat_1(k6_relat_1(k2_relat_1(A_14)))!=k1_relat_1(A_61) | ~v1_relat_1(A_14) | ~v1_relat_1(k6_relat_1(k2_relat_1(A_14))) | ~v1_relat_1(A_61) | ~v1_relat_1(A_14))), inference(superposition, [status(thm), theory('equality')], [c_16, c_592])).
% 3.18/1.47  tff(c_728, plain, (![A_64, A_65]: (k1_relat_1(k5_relat_1(A_64, A_65))=k1_relat_1(A_64) | k2_relat_1(A_64)!=k1_relat_1(A_65) | ~v1_relat_1(A_65) | ~v1_relat_1(A_64))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_12, c_649])).
% 3.18/1.47  tff(c_428, plain, (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))=k2_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_30])).
% 3.18/1.47  tff(c_750, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1') | k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_728, c_428])).
% 3.18/1.47  tff(c_779, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1') | k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_750])).
% 3.18/1.47  tff(c_794, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_779])).
% 3.18/1.47  tff(c_797, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_20, c_794])).
% 3.18/1.47  tff(c_801, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_797])).
% 3.18/1.47  tff(c_803, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_779])).
% 3.18/1.47  tff(c_802, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1') | k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_779])).
% 3.18/1.47  tff(c_804, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_802])).
% 3.18/1.47  tff(c_807, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_26, c_804])).
% 3.18/1.47  tff(c_811, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_807])).
% 3.18/1.47  tff(c_813, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_802])).
% 3.18/1.47  tff(c_10, plain, (![B_12, A_10]: (k2_relat_1(k5_relat_1(B_12, A_10))=k2_relat_1(A_10) | ~r1_tarski(k1_relat_1(A_10), k2_relat_1(B_12)) | ~v1_relat_1(B_12) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.18/1.47  tff(c_843, plain, (![A_10]: (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), A_10))=k2_relat_1(A_10) | ~r1_tarski(k1_relat_1(A_10), k1_relat_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(A_10))), inference(superposition, [status(thm), theory('equality')], [c_813, c_10])).
% 3.18/1.47  tff(c_985, plain, (![A_67]: (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), A_67))=k2_relat_1(A_67) | ~r1_tarski(k1_relat_1(A_67), k1_relat_1('#skF_1')) | ~v1_relat_1(A_67))), inference(demodulation, [status(thm), theory('equality')], [c_803, c_843])).
% 3.18/1.47  tff(c_1016, plain, (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))=k2_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_6, c_985])).
% 3.18/1.47  tff(c_1023, plain, (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))=k2_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1016])).
% 3.18/1.47  tff(c_1025, plain, $false, inference(negUnitSimplification, [status(thm)], [c_427, c_1023])).
% 3.18/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.18/1.47  
% 3.18/1.47  Inference rules
% 3.18/1.47  ----------------------
% 3.18/1.47  #Ref     : 0
% 3.18/1.47  #Sup     : 214
% 3.18/1.47  #Fact    : 0
% 3.18/1.47  #Define  : 0
% 3.18/1.47  #Split   : 6
% 3.18/1.47  #Chain   : 0
% 3.18/1.47  #Close   : 0
% 3.18/1.47  
% 3.18/1.47  Ordering : KBO
% 3.18/1.47  
% 3.18/1.47  Simplification rules
% 3.18/1.47  ----------------------
% 3.18/1.47  #Subsume      : 10
% 3.18/1.47  #Demod        : 263
% 3.18/1.47  #Tautology    : 96
% 3.18/1.47  #SimpNegUnit  : 1
% 3.18/1.47  #BackRed      : 0
% 3.18/1.47  
% 3.18/1.47  #Partial instantiations: 0
% 3.18/1.47  #Strategies tried      : 1
% 3.18/1.47  
% 3.18/1.47  Timing (in seconds)
% 3.18/1.47  ----------------------
% 3.18/1.47  Preprocessing        : 0.29
% 3.18/1.47  Parsing              : 0.16
% 3.18/1.47  CNF conversion       : 0.02
% 3.18/1.47  Main loop            : 0.39
% 3.18/1.47  Inferencing          : 0.14
% 3.18/1.47  Reduction            : 0.12
% 3.18/1.47  Demodulation         : 0.09
% 3.18/1.47  BG Simplification    : 0.03
% 3.18/1.47  Subsumption          : 0.07
% 3.18/1.47  Abstraction          : 0.02
% 3.18/1.47  MUC search           : 0.00
% 3.18/1.47  Cooper               : 0.00
% 3.18/1.47  Total                : 0.71
% 3.18/1.47  Index Insertion      : 0.00
% 3.18/1.47  Index Deletion       : 0.00
% 3.18/1.47  Index Matching       : 0.00
% 3.18/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
