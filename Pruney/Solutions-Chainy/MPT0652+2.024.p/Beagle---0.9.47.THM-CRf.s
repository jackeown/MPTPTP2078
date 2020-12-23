%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:55 EST 2020

% Result     : Theorem 3.19s
% Output     : CNFRefutation 3.19s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 164 expanded)
%              Number of leaves         :   24 (  69 expanded)
%              Depth                    :   10
%              Number of atoms          :  128 ( 390 expanded)
%              Number of equality atoms :   41 ( 135 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1

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

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(f_89,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v2_funct_1(A)
         => ( k1_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A)
            & k2_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_1)).

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

tff(f_37,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_31,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_66,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).

tff(c_24,plain,
    ( k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1')
    | k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_69,plain,(
    k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_30,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_28,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_26,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_96,plain,(
    ! [A_24] :
      ( k4_relat_1(A_24) = k2_funct_1(A_24)
      | ~ v2_funct_1(A_24)
      | ~ v1_funct_1(A_24)
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_99,plain,
    ( k4_relat_1('#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_96])).

tff(c_102,plain,(
    k4_relat_1('#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_99])).

tff(c_2,plain,(
    ! [A_1] :
      ( v1_relat_1(k4_relat_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_112,plain,
    ( v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_2])).

tff(c_120,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_112])).

tff(c_8,plain,(
    ! [A_3] :
      ( k1_relat_1(k4_relat_1(A_3)) = k2_relat_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_106,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_8])).

tff(c_116,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_106])).

tff(c_4,plain,(
    ! [A_2] : v1_relat_1(k6_relat_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    ! [A_13] : k2_relat_1(k6_relat_1(A_13)) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_6,plain,(
    ! [A_3] :
      ( k2_relat_1(k4_relat_1(A_3)) = k1_relat_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_70,plain,(
    ! [A_22] :
      ( k5_relat_1(A_22,k6_relat_1(k2_relat_1(A_22))) = A_22
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_186,plain,(
    ! [A_31] :
      ( k5_relat_1(k4_relat_1(A_31),k6_relat_1(k1_relat_1(A_31))) = k4_relat_1(A_31)
      | ~ v1_relat_1(k4_relat_1(A_31))
      | ~ v1_relat_1(A_31) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_70])).

tff(c_10,plain,(
    ! [A_4,B_6] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_4,B_6)),k2_relat_1(B_6))
      | ~ v1_relat_1(B_6)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_195,plain,(
    ! [A_31] :
      ( r1_tarski(k2_relat_1(k4_relat_1(A_31)),k2_relat_1(k6_relat_1(k1_relat_1(A_31))))
      | ~ v1_relat_1(k6_relat_1(k1_relat_1(A_31)))
      | ~ v1_relat_1(k4_relat_1(A_31))
      | ~ v1_relat_1(k4_relat_1(A_31))
      | ~ v1_relat_1(A_31) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_10])).

tff(c_259,plain,(
    ! [A_34] :
      ( r1_tarski(k2_relat_1(k4_relat_1(A_34)),k1_relat_1(A_34))
      | ~ v1_relat_1(k4_relat_1(A_34))
      | ~ v1_relat_1(A_34) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_18,c_195])).

tff(c_12,plain,(
    ! [A_7,B_9] :
      ( k1_relat_1(k5_relat_1(A_7,B_9)) = k1_relat_1(A_7)
      | ~ r1_tarski(k2_relat_1(A_7),k1_relat_1(B_9))
      | ~ v1_relat_1(B_9)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_675,plain,(
    ! [A_49] :
      ( k1_relat_1(k5_relat_1(k4_relat_1(A_49),A_49)) = k1_relat_1(k4_relat_1(A_49))
      | ~ v1_relat_1(k4_relat_1(A_49))
      | ~ v1_relat_1(A_49) ) ),
    inference(resolution,[status(thm)],[c_259,c_12])).

tff(c_713,plain,
    ( k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) = k1_relat_1(k4_relat_1('#skF_1'))
    | ~ v1_relat_1(k4_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_675])).

tff(c_732,plain,(
    k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) = k2_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_120,c_102,c_116,c_102,c_713])).

tff(c_734,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_732])).

tff(c_735,plain,(
    k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_741,plain,(
    ! [A_50] :
      ( k5_relat_1(A_50,k6_relat_1(k2_relat_1(A_50))) = A_50
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_753,plain,(
    ! [A_13] :
      ( k5_relat_1(k6_relat_1(A_13),k6_relat_1(A_13)) = k6_relat_1(A_13)
      | ~ v1_relat_1(k6_relat_1(A_13)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_741])).

tff(c_757,plain,(
    ! [A_13] : k5_relat_1(k6_relat_1(A_13),k6_relat_1(A_13)) = k6_relat_1(A_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_753])).

tff(c_810,plain,(
    ! [A_53,B_54] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_53,B_54)),k2_relat_1(B_54))
      | ~ v1_relat_1(B_54)
      | ~ v1_relat_1(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_819,plain,(
    ! [A_13] :
      ( r1_tarski(k2_relat_1(k6_relat_1(A_13)),k2_relat_1(k6_relat_1(A_13)))
      | ~ v1_relat_1(k6_relat_1(A_13))
      | ~ v1_relat_1(k6_relat_1(A_13)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_757,c_810])).

tff(c_834,plain,(
    ! [A_13] : r1_tarski(A_13,A_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_4,c_18,c_18,c_819])).

tff(c_767,plain,(
    ! [A_52] :
      ( k4_relat_1(A_52) = k2_funct_1(A_52)
      | ~ v2_funct_1(A_52)
      | ~ v1_funct_1(A_52)
      | ~ v1_relat_1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_770,plain,
    ( k4_relat_1('#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_767])).

tff(c_773,plain,(
    k4_relat_1('#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_770])).

tff(c_783,plain,
    ( v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_773,c_2])).

tff(c_791,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_783])).

tff(c_780,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_773,c_6])).

tff(c_789,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_780])).

tff(c_963,plain,(
    ! [B_65,A_66] :
      ( k2_relat_1(k5_relat_1(B_65,A_66)) = k2_relat_1(A_66)
      | ~ r1_tarski(k1_relat_1(A_66),k2_relat_1(B_65))
      | ~ v1_relat_1(B_65)
      | ~ v1_relat_1(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_975,plain,(
    ! [A_66] :
      ( k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),A_66)) = k2_relat_1(A_66)
      | ~ r1_tarski(k1_relat_1(A_66),k1_relat_1('#skF_1'))
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v1_relat_1(A_66) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_789,c_963])).

tff(c_1337,plain,(
    ! [A_79] :
      ( k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),A_79)) = k2_relat_1(A_79)
      | ~ r1_tarski(k1_relat_1(A_79),k1_relat_1('#skF_1'))
      | ~ v1_relat_1(A_79) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_791,c_975])).

tff(c_1350,plain,
    ( k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) = k2_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_834,c_1337])).

tff(c_1365,plain,(
    k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) = k2_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1350])).

tff(c_1367,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_735,c_1365])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:27:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.19/1.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.19/1.50  
% 3.19/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.19/1.50  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1
% 3.19/1.50  
% 3.19/1.50  %Foreground sorts:
% 3.19/1.50  
% 3.19/1.50  
% 3.19/1.50  %Background operators:
% 3.19/1.50  
% 3.19/1.50  
% 3.19/1.50  %Foreground operators:
% 3.19/1.50  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.19/1.50  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.19/1.50  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.19/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.19/1.50  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.19/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.19/1.50  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.19/1.50  tff('#skF_1', type, '#skF_1': $i).
% 3.19/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.19/1.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.19/1.50  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.19/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.19/1.50  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.19/1.50  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 3.19/1.50  
% 3.19/1.51  tff(f_89, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)) & (k2_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_funct_1)).
% 3.19/1.51  tff(f_78, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 3.19/1.51  tff(f_29, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 3.19/1.51  tff(f_37, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_relat_1)).
% 3.19/1.51  tff(f_31, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 3.19/1.51  tff(f_66, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 3.19/1.51  tff(f_70, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 3.19/1.51  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 3.19/1.51  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_relat_1)).
% 3.19/1.51  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_relat_1)).
% 3.19/1.51  tff(c_24, plain, (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1') | k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.19/1.51  tff(c_69, plain, (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_24])).
% 3.19/1.51  tff(c_30, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.19/1.51  tff(c_28, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.19/1.51  tff(c_26, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.19/1.51  tff(c_96, plain, (![A_24]: (k4_relat_1(A_24)=k2_funct_1(A_24) | ~v2_funct_1(A_24) | ~v1_funct_1(A_24) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.19/1.51  tff(c_99, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_26, c_96])).
% 3.19/1.51  tff(c_102, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_99])).
% 3.19/1.51  tff(c_2, plain, (![A_1]: (v1_relat_1(k4_relat_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.19/1.51  tff(c_112, plain, (v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_102, c_2])).
% 3.19/1.51  tff(c_120, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_112])).
% 3.19/1.51  tff(c_8, plain, (![A_3]: (k1_relat_1(k4_relat_1(A_3))=k2_relat_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.19/1.51  tff(c_106, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_102, c_8])).
% 3.19/1.51  tff(c_116, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_106])).
% 3.19/1.51  tff(c_4, plain, (![A_2]: (v1_relat_1(k6_relat_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.19/1.51  tff(c_18, plain, (![A_13]: (k2_relat_1(k6_relat_1(A_13))=A_13)), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.19/1.51  tff(c_6, plain, (![A_3]: (k2_relat_1(k4_relat_1(A_3))=k1_relat_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.19/1.51  tff(c_70, plain, (![A_22]: (k5_relat_1(A_22, k6_relat_1(k2_relat_1(A_22)))=A_22 | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.19/1.51  tff(c_186, plain, (![A_31]: (k5_relat_1(k4_relat_1(A_31), k6_relat_1(k1_relat_1(A_31)))=k4_relat_1(A_31) | ~v1_relat_1(k4_relat_1(A_31)) | ~v1_relat_1(A_31))), inference(superposition, [status(thm), theory('equality')], [c_6, c_70])).
% 3.19/1.51  tff(c_10, plain, (![A_4, B_6]: (r1_tarski(k2_relat_1(k5_relat_1(A_4, B_6)), k2_relat_1(B_6)) | ~v1_relat_1(B_6) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.19/1.51  tff(c_195, plain, (![A_31]: (r1_tarski(k2_relat_1(k4_relat_1(A_31)), k2_relat_1(k6_relat_1(k1_relat_1(A_31)))) | ~v1_relat_1(k6_relat_1(k1_relat_1(A_31))) | ~v1_relat_1(k4_relat_1(A_31)) | ~v1_relat_1(k4_relat_1(A_31)) | ~v1_relat_1(A_31))), inference(superposition, [status(thm), theory('equality')], [c_186, c_10])).
% 3.19/1.51  tff(c_259, plain, (![A_34]: (r1_tarski(k2_relat_1(k4_relat_1(A_34)), k1_relat_1(A_34)) | ~v1_relat_1(k4_relat_1(A_34)) | ~v1_relat_1(A_34))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_18, c_195])).
% 3.19/1.51  tff(c_12, plain, (![A_7, B_9]: (k1_relat_1(k5_relat_1(A_7, B_9))=k1_relat_1(A_7) | ~r1_tarski(k2_relat_1(A_7), k1_relat_1(B_9)) | ~v1_relat_1(B_9) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.19/1.51  tff(c_675, plain, (![A_49]: (k1_relat_1(k5_relat_1(k4_relat_1(A_49), A_49))=k1_relat_1(k4_relat_1(A_49)) | ~v1_relat_1(k4_relat_1(A_49)) | ~v1_relat_1(A_49))), inference(resolution, [status(thm)], [c_259, c_12])).
% 3.19/1.51  tff(c_713, plain, (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))=k1_relat_1(k4_relat_1('#skF_1')) | ~v1_relat_1(k4_relat_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_102, c_675])).
% 3.19/1.51  tff(c_732, plain, (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))=k2_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_120, c_102, c_116, c_102, c_713])).
% 3.19/1.51  tff(c_734, plain, $false, inference(negUnitSimplification, [status(thm)], [c_69, c_732])).
% 3.19/1.51  tff(c_735, plain, (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_24])).
% 3.19/1.51  tff(c_741, plain, (![A_50]: (k5_relat_1(A_50, k6_relat_1(k2_relat_1(A_50)))=A_50 | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.19/1.51  tff(c_753, plain, (![A_13]: (k5_relat_1(k6_relat_1(A_13), k6_relat_1(A_13))=k6_relat_1(A_13) | ~v1_relat_1(k6_relat_1(A_13)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_741])).
% 3.19/1.51  tff(c_757, plain, (![A_13]: (k5_relat_1(k6_relat_1(A_13), k6_relat_1(A_13))=k6_relat_1(A_13))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_753])).
% 3.19/1.51  tff(c_810, plain, (![A_53, B_54]: (r1_tarski(k2_relat_1(k5_relat_1(A_53, B_54)), k2_relat_1(B_54)) | ~v1_relat_1(B_54) | ~v1_relat_1(A_53))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.19/1.51  tff(c_819, plain, (![A_13]: (r1_tarski(k2_relat_1(k6_relat_1(A_13)), k2_relat_1(k6_relat_1(A_13))) | ~v1_relat_1(k6_relat_1(A_13)) | ~v1_relat_1(k6_relat_1(A_13)))), inference(superposition, [status(thm), theory('equality')], [c_757, c_810])).
% 3.19/1.51  tff(c_834, plain, (![A_13]: (r1_tarski(A_13, A_13))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_4, c_18, c_18, c_819])).
% 3.19/1.51  tff(c_767, plain, (![A_52]: (k4_relat_1(A_52)=k2_funct_1(A_52) | ~v2_funct_1(A_52) | ~v1_funct_1(A_52) | ~v1_relat_1(A_52))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.19/1.51  tff(c_770, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_26, c_767])).
% 3.19/1.51  tff(c_773, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_770])).
% 3.19/1.51  tff(c_783, plain, (v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_773, c_2])).
% 3.19/1.51  tff(c_791, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_783])).
% 3.19/1.51  tff(c_780, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_773, c_6])).
% 3.19/1.51  tff(c_789, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_780])).
% 3.19/1.51  tff(c_963, plain, (![B_65, A_66]: (k2_relat_1(k5_relat_1(B_65, A_66))=k2_relat_1(A_66) | ~r1_tarski(k1_relat_1(A_66), k2_relat_1(B_65)) | ~v1_relat_1(B_65) | ~v1_relat_1(A_66))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.19/1.51  tff(c_975, plain, (![A_66]: (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), A_66))=k2_relat_1(A_66) | ~r1_tarski(k1_relat_1(A_66), k1_relat_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(A_66))), inference(superposition, [status(thm), theory('equality')], [c_789, c_963])).
% 3.19/1.51  tff(c_1337, plain, (![A_79]: (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), A_79))=k2_relat_1(A_79) | ~r1_tarski(k1_relat_1(A_79), k1_relat_1('#skF_1')) | ~v1_relat_1(A_79))), inference(demodulation, [status(thm), theory('equality')], [c_791, c_975])).
% 3.19/1.51  tff(c_1350, plain, (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))=k2_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_834, c_1337])).
% 3.19/1.51  tff(c_1365, plain, (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))=k2_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1350])).
% 3.19/1.51  tff(c_1367, plain, $false, inference(negUnitSimplification, [status(thm)], [c_735, c_1365])).
% 3.19/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.19/1.51  
% 3.19/1.51  Inference rules
% 3.19/1.51  ----------------------
% 3.19/1.51  #Ref     : 0
% 3.19/1.51  #Sup     : 307
% 3.19/1.51  #Fact    : 0
% 3.19/1.51  #Define  : 0
% 3.19/1.51  #Split   : 5
% 3.19/1.51  #Chain   : 0
% 3.19/1.51  #Close   : 0
% 3.19/1.51  
% 3.19/1.51  Ordering : KBO
% 3.19/1.51  
% 3.19/1.51  Simplification rules
% 3.19/1.51  ----------------------
% 3.19/1.51  #Subsume      : 12
% 3.19/1.51  #Demod        : 335
% 3.19/1.51  #Tautology    : 142
% 3.19/1.51  #SimpNegUnit  : 2
% 3.19/1.51  #BackRed      : 0
% 3.19/1.51  
% 3.19/1.52  #Partial instantiations: 0
% 3.19/1.52  #Strategies tried      : 1
% 3.19/1.52  
% 3.19/1.52  Timing (in seconds)
% 3.19/1.52  ----------------------
% 3.19/1.52  Preprocessing        : 0.29
% 3.19/1.52  Parsing              : 0.16
% 3.19/1.52  CNF conversion       : 0.02
% 3.19/1.52  Main loop            : 0.46
% 3.19/1.52  Inferencing          : 0.16
% 3.19/1.52  Reduction            : 0.16
% 3.19/1.52  Demodulation         : 0.12
% 3.19/1.52  BG Simplification    : 0.03
% 3.19/1.52  Subsumption          : 0.07
% 3.19/1.52  Abstraction          : 0.03
% 3.19/1.52  MUC search           : 0.00
% 3.19/1.52  Cooper               : 0.00
% 3.19/1.52  Total                : 0.79
% 3.19/1.52  Index Insertion      : 0.00
% 3.19/1.52  Index Deletion       : 0.00
% 3.19/1.52  Index Matching       : 0.00
% 3.19/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
