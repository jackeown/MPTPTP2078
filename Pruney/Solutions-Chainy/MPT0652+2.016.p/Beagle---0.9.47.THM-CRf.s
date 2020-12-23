%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:54 EST 2020

% Result     : Theorem 3.39s
% Output     : CNFRefutation 3.39s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 169 expanded)
%              Number of leaves         :   23 (  66 expanded)
%              Depth                    :   10
%              Number of atoms          :  132 ( 461 expanded)
%              Number of equality atoms :   47 ( 183 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

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

tff(f_102,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v2_funct_1(A)
         => ( k1_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A)
            & k2_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_funct_1)).

tff(f_91,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_77,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_81,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_59,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( k2_relat_1(A) = k2_relat_1(B)
               => k2_relat_1(k5_relat_1(A,C)) = k2_relat_1(k5_relat_1(B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t199_relat_1)).

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

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(c_38,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_36,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_34,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_28,plain,(
    ! [A_23] :
      ( k2_relat_1(k2_funct_1(A_23)) = k1_relat_1(A_23)
      | ~ v2_funct_1(A_23)
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_22,plain,(
    ! [A_21] :
      ( v1_relat_1(k2_funct_1(A_21))
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_24,plain,(
    ! [A_22] : v1_relat_1(k6_relat_1(A_22)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_14,plain,(
    ! [A_17] : k2_relat_1(k6_relat_1(A_17)) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_16,plain,(
    ! [A_18] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_18)),A_18) = A_18
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_938,plain,(
    ! [B_75,C_76,A_77] :
      ( k2_relat_1(k5_relat_1(B_75,C_76)) = k2_relat_1(k5_relat_1(A_77,C_76))
      | k2_relat_1(B_75) != k2_relat_1(A_77)
      | ~ v1_relat_1(C_76)
      | ~ v1_relat_1(B_75)
      | ~ v1_relat_1(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1013,plain,(
    ! [A_77,A_18] :
      ( k2_relat_1(k5_relat_1(A_77,A_18)) = k2_relat_1(A_18)
      | k2_relat_1(k6_relat_1(k1_relat_1(A_18))) != k2_relat_1(A_77)
      | ~ v1_relat_1(A_18)
      | ~ v1_relat_1(k6_relat_1(k1_relat_1(A_18)))
      | ~ v1_relat_1(A_77)
      | ~ v1_relat_1(A_18) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_938])).

tff(c_1106,plain,(
    ! [A_80,A_81] :
      ( k2_relat_1(k5_relat_1(A_80,A_81)) = k2_relat_1(A_81)
      | k2_relat_1(A_80) != k1_relat_1(A_81)
      | ~ v1_relat_1(A_80)
      | ~ v1_relat_1(A_81) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_14,c_1013])).

tff(c_30,plain,(
    ! [A_23] :
      ( k1_relat_1(k2_funct_1(A_23)) = k2_relat_1(A_23)
      | ~ v2_funct_1(A_23)
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_395,plain,(
    ! [C_49,B_50,A_51] :
      ( k1_relat_1(k5_relat_1(C_49,B_50)) = k1_relat_1(k5_relat_1(C_49,A_51))
      | k1_relat_1(B_50) != k1_relat_1(A_51)
      | ~ v1_relat_1(C_49)
      | ~ v1_relat_1(B_50)
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_32,plain,
    ( k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1')
    | k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_62,plain,(
    k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_419,plain,(
    ! [A_51] :
      ( k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),A_51)) != k2_relat_1('#skF_1')
      | k1_relat_1(A_51) != k1_relat_1('#skF_1')
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v1_relat_1('#skF_1')
      | ~ v1_relat_1(A_51) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_395,c_62])).

tff(c_459,plain,(
    ! [A_51] :
      ( k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),A_51)) != k2_relat_1('#skF_1')
      | k1_relat_1(A_51) != k1_relat_1('#skF_1')
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v1_relat_1(A_51) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_419])).

tff(c_553,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_459])).

tff(c_556,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_553])).

tff(c_560,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_556])).

tff(c_562,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_459])).

tff(c_12,plain,(
    ! [A_17] : k1_relat_1(k6_relat_1(A_17)) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_115,plain,(
    ! [B_37,A_38] :
      ( k5_relat_1(B_37,k6_relat_1(A_38)) = B_37
      | ~ r1_tarski(k2_relat_1(B_37),A_38)
      | ~ v1_relat_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_128,plain,(
    ! [B_37] :
      ( k5_relat_1(B_37,k6_relat_1(k2_relat_1(B_37))) = B_37
      | ~ v1_relat_1(B_37) ) ),
    inference(resolution,[status(thm)],[c_6,c_115])).

tff(c_716,plain,(
    ! [A_61] :
      ( k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),A_61)) != k2_relat_1('#skF_1')
      | k1_relat_1(A_61) != k1_relat_1('#skF_1')
      | ~ v1_relat_1(A_61) ) ),
    inference(splitRight,[status(thm)],[c_459])).

tff(c_728,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1')
    | k1_relat_1(k6_relat_1(k2_relat_1(k2_funct_1('#skF_1')))) != k1_relat_1('#skF_1')
    | ~ v1_relat_1(k6_relat_1(k2_relat_1(k2_funct_1('#skF_1'))))
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_716])).

tff(c_734,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1')
    | k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_562,c_24,c_12,c_728])).

tff(c_735,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_734])).

tff(c_738,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_735])).

tff(c_742,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_738])).

tff(c_743,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_734])).

tff(c_775,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_743])).

tff(c_779,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_775])).

tff(c_780,plain,(
    k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_1131,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1106,c_780])).

tff(c_1164,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1131])).

tff(c_1183,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_1164])).

tff(c_1186,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_1183])).

tff(c_1190,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_1186])).

tff(c_1191,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1164])).

tff(c_1195,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1191])).

tff(c_1199,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_1195])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:43:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.39/1.57  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.39/1.57  
% 3.39/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.39/1.58  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1
% 3.39/1.58  
% 3.39/1.58  %Foreground sorts:
% 3.39/1.58  
% 3.39/1.58  
% 3.39/1.58  %Background operators:
% 3.39/1.58  
% 3.39/1.58  
% 3.39/1.58  %Foreground operators:
% 3.39/1.58  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.39/1.58  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.39/1.58  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.39/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.39/1.58  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.39/1.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.39/1.58  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.39/1.58  tff('#skF_1', type, '#skF_1': $i).
% 3.39/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.39/1.58  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.39/1.58  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.39/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.39/1.58  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.39/1.58  
% 3.39/1.59  tff(f_102, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)) & (k2_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_funct_1)).
% 3.39/1.59  tff(f_91, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 3.39/1.59  tff(f_77, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 3.39/1.59  tff(f_81, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 3.39/1.59  tff(f_59, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 3.39/1.59  tff(f_63, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_relat_1)).
% 3.39/1.59  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((k2_relat_1(A) = k2_relat_1(B)) => (k2_relat_1(k5_relat_1(A, C)) = k2_relat_1(k5_relat_1(B, C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t199_relat_1)).
% 3.39/1.59  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((k1_relat_1(A) = k1_relat_1(B)) => (k1_relat_1(k5_relat_1(C, A)) = k1_relat_1(k5_relat_1(C, B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t198_relat_1)).
% 3.39/1.59  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.39/1.59  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 3.39/1.59  tff(c_38, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.39/1.59  tff(c_36, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.39/1.59  tff(c_34, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.39/1.59  tff(c_28, plain, (![A_23]: (k2_relat_1(k2_funct_1(A_23))=k1_relat_1(A_23) | ~v2_funct_1(A_23) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.39/1.59  tff(c_22, plain, (![A_21]: (v1_relat_1(k2_funct_1(A_21)) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.39/1.59  tff(c_24, plain, (![A_22]: (v1_relat_1(k6_relat_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.39/1.59  tff(c_14, plain, (![A_17]: (k2_relat_1(k6_relat_1(A_17))=A_17)), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.39/1.59  tff(c_16, plain, (![A_18]: (k5_relat_1(k6_relat_1(k1_relat_1(A_18)), A_18)=A_18 | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.39/1.59  tff(c_938, plain, (![B_75, C_76, A_77]: (k2_relat_1(k5_relat_1(B_75, C_76))=k2_relat_1(k5_relat_1(A_77, C_76)) | k2_relat_1(B_75)!=k2_relat_1(A_77) | ~v1_relat_1(C_76) | ~v1_relat_1(B_75) | ~v1_relat_1(A_77))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.39/1.59  tff(c_1013, plain, (![A_77, A_18]: (k2_relat_1(k5_relat_1(A_77, A_18))=k2_relat_1(A_18) | k2_relat_1(k6_relat_1(k1_relat_1(A_18)))!=k2_relat_1(A_77) | ~v1_relat_1(A_18) | ~v1_relat_1(k6_relat_1(k1_relat_1(A_18))) | ~v1_relat_1(A_77) | ~v1_relat_1(A_18))), inference(superposition, [status(thm), theory('equality')], [c_16, c_938])).
% 3.39/1.59  tff(c_1106, plain, (![A_80, A_81]: (k2_relat_1(k5_relat_1(A_80, A_81))=k2_relat_1(A_81) | k2_relat_1(A_80)!=k1_relat_1(A_81) | ~v1_relat_1(A_80) | ~v1_relat_1(A_81))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_14, c_1013])).
% 3.39/1.59  tff(c_30, plain, (![A_23]: (k1_relat_1(k2_funct_1(A_23))=k2_relat_1(A_23) | ~v2_funct_1(A_23) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.39/1.59  tff(c_395, plain, (![C_49, B_50, A_51]: (k1_relat_1(k5_relat_1(C_49, B_50))=k1_relat_1(k5_relat_1(C_49, A_51)) | k1_relat_1(B_50)!=k1_relat_1(A_51) | ~v1_relat_1(C_49) | ~v1_relat_1(B_50) | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.39/1.59  tff(c_32, plain, (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1') | k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.39/1.59  tff(c_62, plain, (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_32])).
% 3.39/1.59  tff(c_419, plain, (![A_51]: (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), A_51))!=k2_relat_1('#skF_1') | k1_relat_1(A_51)!=k1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1') | ~v1_relat_1(A_51))), inference(superposition, [status(thm), theory('equality')], [c_395, c_62])).
% 3.39/1.59  tff(c_459, plain, (![A_51]: (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), A_51))!=k2_relat_1('#skF_1') | k1_relat_1(A_51)!=k1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(A_51))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_419])).
% 3.39/1.59  tff(c_553, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_459])).
% 3.39/1.59  tff(c_556, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_22, c_553])).
% 3.39/1.59  tff(c_560, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_556])).
% 3.39/1.59  tff(c_562, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_459])).
% 3.39/1.59  tff(c_12, plain, (![A_17]: (k1_relat_1(k6_relat_1(A_17))=A_17)), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.39/1.59  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.39/1.59  tff(c_115, plain, (![B_37, A_38]: (k5_relat_1(B_37, k6_relat_1(A_38))=B_37 | ~r1_tarski(k2_relat_1(B_37), A_38) | ~v1_relat_1(B_37))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.39/1.59  tff(c_128, plain, (![B_37]: (k5_relat_1(B_37, k6_relat_1(k2_relat_1(B_37)))=B_37 | ~v1_relat_1(B_37))), inference(resolution, [status(thm)], [c_6, c_115])).
% 3.39/1.59  tff(c_716, plain, (![A_61]: (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), A_61))!=k2_relat_1('#skF_1') | k1_relat_1(A_61)!=k1_relat_1('#skF_1') | ~v1_relat_1(A_61))), inference(splitRight, [status(thm)], [c_459])).
% 3.39/1.59  tff(c_728, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1') | k1_relat_1(k6_relat_1(k2_relat_1(k2_funct_1('#skF_1'))))!=k1_relat_1('#skF_1') | ~v1_relat_1(k6_relat_1(k2_relat_1(k2_funct_1('#skF_1')))) | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_128, c_716])).
% 3.39/1.59  tff(c_734, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1') | k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_562, c_24, c_12, c_728])).
% 3.39/1.59  tff(c_735, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_734])).
% 3.39/1.59  tff(c_738, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_28, c_735])).
% 3.39/1.59  tff(c_742, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_738])).
% 3.39/1.59  tff(c_743, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_734])).
% 3.39/1.59  tff(c_775, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_30, c_743])).
% 3.39/1.59  tff(c_779, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_775])).
% 3.39/1.59  tff(c_780, plain, (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_32])).
% 3.39/1.59  tff(c_1131, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1106, c_780])).
% 3.39/1.59  tff(c_1164, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1131])).
% 3.39/1.59  tff(c_1183, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_1164])).
% 3.39/1.59  tff(c_1186, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_22, c_1183])).
% 3.39/1.59  tff(c_1190, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_1186])).
% 3.39/1.59  tff(c_1191, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_1164])).
% 3.39/1.59  tff(c_1195, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_28, c_1191])).
% 3.39/1.59  tff(c_1199, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_1195])).
% 3.39/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.39/1.59  
% 3.39/1.59  Inference rules
% 3.39/1.59  ----------------------
% 3.39/1.59  #Ref     : 1
% 3.39/1.59  #Sup     : 245
% 3.39/1.59  #Fact    : 0
% 3.39/1.59  #Define  : 0
% 3.39/1.59  #Split   : 5
% 3.39/1.59  #Chain   : 0
% 3.39/1.59  #Close   : 0
% 3.39/1.59  
% 3.39/1.59  Ordering : KBO
% 3.39/1.59  
% 3.39/1.59  Simplification rules
% 3.39/1.59  ----------------------
% 3.39/1.59  #Subsume      : 14
% 3.39/1.59  #Demod        : 300
% 3.39/1.59  #Tautology    : 106
% 3.39/1.59  #SimpNegUnit  : 0
% 3.39/1.59  #BackRed      : 0
% 3.39/1.59  
% 3.39/1.59  #Partial instantiations: 0
% 3.39/1.59  #Strategies tried      : 1
% 3.39/1.59  
% 3.39/1.59  Timing (in seconds)
% 3.39/1.59  ----------------------
% 3.39/1.59  Preprocessing        : 0.31
% 3.39/1.59  Parsing              : 0.17
% 3.39/1.59  CNF conversion       : 0.02
% 3.39/1.59  Main loop            : 0.47
% 3.39/1.59  Inferencing          : 0.18
% 3.39/1.60  Reduction            : 0.15
% 3.39/1.60  Demodulation         : 0.12
% 3.39/1.60  BG Simplification    : 0.03
% 3.39/1.60  Subsumption          : 0.08
% 3.39/1.60  Abstraction          : 0.03
% 3.39/1.60  MUC search           : 0.00
% 3.39/1.60  Cooper               : 0.00
% 3.39/1.60  Total                : 0.82
% 3.39/1.60  Index Insertion      : 0.00
% 3.39/1.60  Index Deletion       : 0.00
% 3.39/1.60  Index Matching       : 0.00
% 3.39/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
