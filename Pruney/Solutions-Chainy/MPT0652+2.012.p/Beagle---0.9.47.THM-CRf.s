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
% DateTime   : Thu Dec  3 10:03:54 EST 2020

% Result     : Theorem 2.78s
% Output     : CNFRefutation 2.78s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 173 expanded)
%              Number of leaves         :   25 (  68 expanded)
%              Depth                    :   10
%              Number of atoms          :  142 ( 471 expanded)
%              Number of equality atoms :   54 ( 192 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1

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

tff(f_106,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v2_funct_1(A)
         => ( k1_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A)
            & k2_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_1)).

tff(f_95,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_73,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_81,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_85,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_59,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( k2_relat_1(A) = k2_relat_1(B)
               => k2_relat_1(k5_relat_1(A,C)) = k2_relat_1(k5_relat_1(B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t199_relat_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( k1_relat_1(A) = k1_relat_1(B)
               => k1_relat_1(k5_relat_1(C,A)) = k1_relat_1(k5_relat_1(C,B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t198_relat_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

tff(c_40,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_38,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_36,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_30,plain,(
    ! [A_25] :
      ( k2_relat_1(k2_funct_1(A_25)) = k1_relat_1(A_25)
      | ~ v2_funct_1(A_25)
      | ~ v1_funct_1(A_25)
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_588,plain,(
    ! [B_65,A_66] :
      ( k7_relat_1(B_65,A_66) = B_65
      | ~ r1_tarski(k1_relat_1(B_65),A_66)
      | ~ v1_relat_1(B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_601,plain,(
    ! [B_65] :
      ( k7_relat_1(B_65,k1_relat_1(B_65)) = B_65
      | ~ v1_relat_1(B_65) ) ),
    inference(resolution,[status(thm)],[c_6,c_588])).

tff(c_24,plain,(
    ! [A_23] :
      ( v1_relat_1(k2_funct_1(A_23))
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_26,plain,(
    ! [A_24] : v1_relat_1(k6_relat_1(A_24)) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_14,plain,(
    ! [A_17] : k2_relat_1(k6_relat_1(A_17)) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_18,plain,(
    ! [A_19,B_20] :
      ( k5_relat_1(k6_relat_1(A_19),B_20) = k7_relat_1(B_20,A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_728,plain,(
    ! [B_76,C_77,A_78] :
      ( k2_relat_1(k5_relat_1(B_76,C_77)) = k2_relat_1(k5_relat_1(A_78,C_77))
      | k2_relat_1(B_76) != k2_relat_1(A_78)
      | ~ v1_relat_1(C_77)
      | ~ v1_relat_1(B_76)
      | ~ v1_relat_1(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_773,plain,(
    ! [B_20,A_19,A_78] :
      ( k2_relat_1(k7_relat_1(B_20,A_19)) = k2_relat_1(k5_relat_1(A_78,B_20))
      | k2_relat_1(k6_relat_1(A_19)) != k2_relat_1(A_78)
      | ~ v1_relat_1(B_20)
      | ~ v1_relat_1(k6_relat_1(A_19))
      | ~ v1_relat_1(A_78)
      | ~ v1_relat_1(B_20) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_728])).

tff(c_861,plain,(
    ! [B_81,A_82,A_83] :
      ( k2_relat_1(k7_relat_1(B_81,A_82)) = k2_relat_1(k5_relat_1(A_83,B_81))
      | k2_relat_1(A_83) != A_82
      | ~ v1_relat_1(A_83)
      | ~ v1_relat_1(B_81) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_14,c_773])).

tff(c_32,plain,(
    ! [A_25] :
      ( k1_relat_1(k2_funct_1(A_25)) = k2_relat_1(A_25)
      | ~ v2_funct_1(A_25)
      | ~ v1_funct_1(A_25)
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_228,plain,(
    ! [C_47,B_48,A_49] :
      ( k1_relat_1(k5_relat_1(C_47,B_48)) = k1_relat_1(k5_relat_1(C_47,A_49))
      | k1_relat_1(B_48) != k1_relat_1(A_49)
      | ~ v1_relat_1(C_47)
      | ~ v1_relat_1(B_48)
      | ~ v1_relat_1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_34,plain,
    ( k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1')
    | k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_64,plain,(
    k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_255,plain,(
    ! [B_48] :
      ( k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),B_48)) != k2_relat_1('#skF_1')
      | k1_relat_1(B_48) != k1_relat_1('#skF_1')
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v1_relat_1(B_48)
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_228,c_64])).

tff(c_290,plain,(
    ! [B_48] :
      ( k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),B_48)) != k2_relat_1('#skF_1')
      | k1_relat_1(B_48) != k1_relat_1('#skF_1')
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v1_relat_1(B_48) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_255])).

tff(c_391,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_290])).

tff(c_394,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_391])).

tff(c_398,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_394])).

tff(c_400,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_290])).

tff(c_12,plain,(
    ! [A_17] : k1_relat_1(k6_relat_1(A_17)) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_16,plain,(
    ! [A_18] :
      ( k5_relat_1(A_18,k6_relat_1(k2_relat_1(A_18))) = A_18
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_401,plain,(
    ! [B_54] :
      ( k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),B_54)) != k2_relat_1('#skF_1')
      | k1_relat_1(B_54) != k1_relat_1('#skF_1')
      | ~ v1_relat_1(B_54) ) ),
    inference(splitRight,[status(thm)],[c_290])).

tff(c_413,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1')
    | k1_relat_1(k6_relat_1(k2_relat_1(k2_funct_1('#skF_1')))) != k1_relat_1('#skF_1')
    | ~ v1_relat_1(k6_relat_1(k2_relat_1(k2_funct_1('#skF_1'))))
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_401])).

tff(c_419,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1')
    | k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_400,c_26,c_12,c_413])).

tff(c_420,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_419])).

tff(c_423,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_420])).

tff(c_427,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_423])).

tff(c_428,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_419])).

tff(c_514,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_428])).

tff(c_518,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_514])).

tff(c_519,plain,(
    k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_892,plain,(
    ! [A_82] :
      ( k2_relat_1(k7_relat_1('#skF_1',A_82)) != k2_relat_1('#skF_1')
      | k2_relat_1(k2_funct_1('#skF_1')) != A_82
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_861,c_519])).

tff(c_935,plain,(
    ! [A_82] :
      ( k2_relat_1(k7_relat_1('#skF_1',A_82)) != k2_relat_1('#skF_1')
      | k2_relat_1(k2_funct_1('#skF_1')) != A_82
      | ~ v1_relat_1(k2_funct_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_892])).

tff(c_950,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_935])).

tff(c_953,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_950])).

tff(c_957,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_953])).

tff(c_1048,plain,(
    ! [A_87] :
      ( k2_relat_1(k7_relat_1('#skF_1',A_87)) != k2_relat_1('#skF_1')
      | k2_relat_1(k2_funct_1('#skF_1')) != A_87 ) ),
    inference(splitRight,[status(thm)],[c_935])).

tff(c_1056,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_601,c_1048])).

tff(c_1061,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1056])).

tff(c_1064,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1061])).

tff(c_1068,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_1064])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:15:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.78/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.78/1.42  
% 2.78/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.78/1.42  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1
% 2.78/1.42  
% 2.78/1.42  %Foreground sorts:
% 2.78/1.42  
% 2.78/1.42  
% 2.78/1.42  %Background operators:
% 2.78/1.42  
% 2.78/1.42  
% 2.78/1.42  %Foreground operators:
% 2.78/1.42  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.78/1.42  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.78/1.42  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.78/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.78/1.42  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.78/1.42  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.78/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.78/1.42  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.78/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.78/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.78/1.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.78/1.42  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.78/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.78/1.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.78/1.42  
% 2.78/1.44  tff(f_106, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)) & (k2_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_funct_1)).
% 2.78/1.44  tff(f_95, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 2.78/1.44  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.78/1.44  tff(f_73, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 2.78/1.44  tff(f_81, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 2.78/1.44  tff(f_85, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.78/1.44  tff(f_59, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.78/1.44  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 2.78/1.44  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((k2_relat_1(A) = k2_relat_1(B)) => (k2_relat_1(k5_relat_1(A, C)) = k2_relat_1(k5_relat_1(B, C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t199_relat_1)).
% 2.78/1.44  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((k1_relat_1(A) = k1_relat_1(B)) => (k1_relat_1(k5_relat_1(C, A)) = k1_relat_1(k5_relat_1(C, B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t198_relat_1)).
% 2.78/1.44  tff(f_63, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 2.78/1.44  tff(c_40, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.78/1.44  tff(c_38, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.78/1.44  tff(c_36, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.78/1.44  tff(c_30, plain, (![A_25]: (k2_relat_1(k2_funct_1(A_25))=k1_relat_1(A_25) | ~v2_funct_1(A_25) | ~v1_funct_1(A_25) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.78/1.44  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.78/1.44  tff(c_588, plain, (![B_65, A_66]: (k7_relat_1(B_65, A_66)=B_65 | ~r1_tarski(k1_relat_1(B_65), A_66) | ~v1_relat_1(B_65))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.78/1.44  tff(c_601, plain, (![B_65]: (k7_relat_1(B_65, k1_relat_1(B_65))=B_65 | ~v1_relat_1(B_65))), inference(resolution, [status(thm)], [c_6, c_588])).
% 2.78/1.44  tff(c_24, plain, (![A_23]: (v1_relat_1(k2_funct_1(A_23)) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.78/1.44  tff(c_26, plain, (![A_24]: (v1_relat_1(k6_relat_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.78/1.44  tff(c_14, plain, (![A_17]: (k2_relat_1(k6_relat_1(A_17))=A_17)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.78/1.44  tff(c_18, plain, (![A_19, B_20]: (k5_relat_1(k6_relat_1(A_19), B_20)=k7_relat_1(B_20, A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.78/1.44  tff(c_728, plain, (![B_76, C_77, A_78]: (k2_relat_1(k5_relat_1(B_76, C_77))=k2_relat_1(k5_relat_1(A_78, C_77)) | k2_relat_1(B_76)!=k2_relat_1(A_78) | ~v1_relat_1(C_77) | ~v1_relat_1(B_76) | ~v1_relat_1(A_78))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.78/1.44  tff(c_773, plain, (![B_20, A_19, A_78]: (k2_relat_1(k7_relat_1(B_20, A_19))=k2_relat_1(k5_relat_1(A_78, B_20)) | k2_relat_1(k6_relat_1(A_19))!=k2_relat_1(A_78) | ~v1_relat_1(B_20) | ~v1_relat_1(k6_relat_1(A_19)) | ~v1_relat_1(A_78) | ~v1_relat_1(B_20))), inference(superposition, [status(thm), theory('equality')], [c_18, c_728])).
% 2.78/1.44  tff(c_861, plain, (![B_81, A_82, A_83]: (k2_relat_1(k7_relat_1(B_81, A_82))=k2_relat_1(k5_relat_1(A_83, B_81)) | k2_relat_1(A_83)!=A_82 | ~v1_relat_1(A_83) | ~v1_relat_1(B_81))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_14, c_773])).
% 2.78/1.44  tff(c_32, plain, (![A_25]: (k1_relat_1(k2_funct_1(A_25))=k2_relat_1(A_25) | ~v2_funct_1(A_25) | ~v1_funct_1(A_25) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.78/1.44  tff(c_228, plain, (![C_47, B_48, A_49]: (k1_relat_1(k5_relat_1(C_47, B_48))=k1_relat_1(k5_relat_1(C_47, A_49)) | k1_relat_1(B_48)!=k1_relat_1(A_49) | ~v1_relat_1(C_47) | ~v1_relat_1(B_48) | ~v1_relat_1(A_49))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.78/1.44  tff(c_34, plain, (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1') | k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.78/1.44  tff(c_64, plain, (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_34])).
% 2.78/1.44  tff(c_255, plain, (![B_48]: (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), B_48))!=k2_relat_1('#skF_1') | k1_relat_1(B_48)!=k1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(B_48) | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_228, c_64])).
% 2.78/1.44  tff(c_290, plain, (![B_48]: (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), B_48))!=k2_relat_1('#skF_1') | k1_relat_1(B_48)!=k1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(B_48))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_255])).
% 2.78/1.44  tff(c_391, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_290])).
% 2.78/1.44  tff(c_394, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_24, c_391])).
% 2.78/1.44  tff(c_398, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_394])).
% 2.78/1.44  tff(c_400, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_290])).
% 2.78/1.44  tff(c_12, plain, (![A_17]: (k1_relat_1(k6_relat_1(A_17))=A_17)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.78/1.44  tff(c_16, plain, (![A_18]: (k5_relat_1(A_18, k6_relat_1(k2_relat_1(A_18)))=A_18 | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.78/1.44  tff(c_401, plain, (![B_54]: (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), B_54))!=k2_relat_1('#skF_1') | k1_relat_1(B_54)!=k1_relat_1('#skF_1') | ~v1_relat_1(B_54))), inference(splitRight, [status(thm)], [c_290])).
% 2.78/1.44  tff(c_413, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1') | k1_relat_1(k6_relat_1(k2_relat_1(k2_funct_1('#skF_1'))))!=k1_relat_1('#skF_1') | ~v1_relat_1(k6_relat_1(k2_relat_1(k2_funct_1('#skF_1')))) | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_16, c_401])).
% 2.78/1.44  tff(c_419, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1') | k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_400, c_26, c_12, c_413])).
% 2.78/1.44  tff(c_420, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_419])).
% 2.78/1.44  tff(c_423, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_30, c_420])).
% 2.78/1.44  tff(c_427, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_423])).
% 2.78/1.44  tff(c_428, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_419])).
% 2.78/1.44  tff(c_514, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_32, c_428])).
% 2.78/1.44  tff(c_518, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_514])).
% 2.78/1.44  tff(c_519, plain, (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_34])).
% 2.78/1.44  tff(c_892, plain, (![A_82]: (k2_relat_1(k7_relat_1('#skF_1', A_82))!=k2_relat_1('#skF_1') | k2_relat_1(k2_funct_1('#skF_1'))!=A_82 | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_861, c_519])).
% 2.78/1.44  tff(c_935, plain, (![A_82]: (k2_relat_1(k7_relat_1('#skF_1', A_82))!=k2_relat_1('#skF_1') | k2_relat_1(k2_funct_1('#skF_1'))!=A_82 | ~v1_relat_1(k2_funct_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_892])).
% 2.78/1.44  tff(c_950, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_935])).
% 2.78/1.44  tff(c_953, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_24, c_950])).
% 2.78/1.44  tff(c_957, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_953])).
% 2.78/1.44  tff(c_1048, plain, (![A_87]: (k2_relat_1(k7_relat_1('#skF_1', A_87))!=k2_relat_1('#skF_1') | k2_relat_1(k2_funct_1('#skF_1'))!=A_87)), inference(splitRight, [status(thm)], [c_935])).
% 2.78/1.44  tff(c_1056, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_601, c_1048])).
% 2.78/1.44  tff(c_1061, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1056])).
% 2.78/1.44  tff(c_1064, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_30, c_1061])).
% 2.78/1.44  tff(c_1068, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_1064])).
% 2.78/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.78/1.44  
% 2.78/1.44  Inference rules
% 2.78/1.44  ----------------------
% 2.78/1.44  #Ref     : 0
% 2.78/1.44  #Sup     : 224
% 2.78/1.44  #Fact    : 0
% 2.78/1.44  #Define  : 0
% 2.78/1.44  #Split   : 5
% 2.78/1.44  #Chain   : 0
% 2.78/1.44  #Close   : 0
% 2.78/1.44  
% 2.78/1.44  Ordering : KBO
% 2.78/1.44  
% 2.78/1.44  Simplification rules
% 2.78/1.44  ----------------------
% 2.78/1.44  #Subsume      : 5
% 2.78/1.44  #Demod        : 195
% 2.78/1.44  #Tautology    : 81
% 2.78/1.44  #SimpNegUnit  : 0
% 2.78/1.44  #BackRed      : 0
% 2.78/1.44  
% 2.78/1.44  #Partial instantiations: 0
% 2.78/1.44  #Strategies tried      : 1
% 2.78/1.44  
% 2.78/1.44  Timing (in seconds)
% 2.78/1.44  ----------------------
% 2.78/1.44  Preprocessing        : 0.29
% 2.78/1.44  Parsing              : 0.16
% 2.78/1.44  CNF conversion       : 0.02
% 2.78/1.44  Main loop            : 0.38
% 2.78/1.44  Inferencing          : 0.15
% 2.78/1.44  Reduction            : 0.12
% 2.78/1.44  Demodulation         : 0.09
% 2.78/1.44  BG Simplification    : 0.03
% 2.78/1.44  Subsumption          : 0.06
% 2.78/1.44  Abstraction          : 0.02
% 2.78/1.44  MUC search           : 0.00
% 2.78/1.44  Cooper               : 0.00
% 2.78/1.44  Total                : 0.70
% 2.78/1.44  Index Insertion      : 0.00
% 2.78/1.44  Index Deletion       : 0.00
% 2.78/1.44  Index Matching       : 0.00
% 2.78/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
