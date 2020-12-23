%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:28 EST 2020

% Result     : Theorem 3.26s
% Output     : CNFRefutation 3.26s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 250 expanded)
%              Number of leaves         :   29 ( 101 expanded)
%              Depth                    :   22
%              Number of atoms          :  118 ( 449 expanded)
%              Number of equality atoms :   41 ( 157 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_92,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_tarski(k10_relat_1(A,C),B)
           => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_46,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => r1_tarski(k10_relat_1(B,k9_relat_1(B,A)),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k10_relat_1(k5_relat_1(B,C),A) = k10_relat_1(B,k10_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t181_relat_1)).

tff(c_34,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') != k10_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_40,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_36,plain,(
    r1_tarski(k10_relat_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_26,plain,(
    ! [A_16] : v1_relat_1(k6_relat_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_12,plain,(
    ! [A_9] : k1_relat_1(k6_relat_1(A_9)) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_134,plain,(
    ! [B_38,A_39] :
      ( k7_relat_1(B_38,A_39) = B_38
      | ~ r1_tarski(k1_relat_1(B_38),A_39)
      | ~ v1_relat_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_137,plain,(
    ! [A_9,A_39] :
      ( k7_relat_1(k6_relat_1(A_9),A_39) = k6_relat_1(A_9)
      | ~ r1_tarski(A_9,A_39)
      | ~ v1_relat_1(k6_relat_1(A_9)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_134])).

tff(c_143,plain,(
    ! [A_9,A_39] :
      ( k7_relat_1(k6_relat_1(A_9),A_39) = k6_relat_1(A_9)
      | ~ r1_tarski(A_9,A_39) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_137])).

tff(c_14,plain,(
    ! [A_9] : k2_relat_1(k6_relat_1(A_9)) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_65,plain,(
    ! [A_29] :
      ( k7_relat_1(A_29,k1_relat_1(A_29)) = A_29
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_74,plain,(
    ! [A_9] :
      ( k7_relat_1(k6_relat_1(A_9),A_9) = k6_relat_1(A_9)
      | ~ v1_relat_1(k6_relat_1(A_9)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_65])).

tff(c_78,plain,(
    ! [A_9] : k7_relat_1(k6_relat_1(A_9),A_9) = k6_relat_1(A_9) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_74])).

tff(c_98,plain,(
    ! [B_33,A_34] :
      ( k2_relat_1(k7_relat_1(B_33,A_34)) = k9_relat_1(B_33,A_34)
      | ~ v1_relat_1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_107,plain,(
    ! [A_9] :
      ( k9_relat_1(k6_relat_1(A_9),A_9) = k2_relat_1(k6_relat_1(A_9))
      | ~ v1_relat_1(k6_relat_1(A_9)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_98])).

tff(c_114,plain,(
    ! [A_9] : k9_relat_1(k6_relat_1(A_9),A_9) = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_14,c_107])).

tff(c_145,plain,(
    ! [A_40,B_41] :
      ( r1_tarski(A_40,k10_relat_1(B_41,k9_relat_1(B_41,A_40)))
      | ~ r1_tarski(A_40,k1_relat_1(B_41))
      | ~ v1_relat_1(B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_154,plain,(
    ! [A_9] :
      ( r1_tarski(A_9,k10_relat_1(k6_relat_1(A_9),A_9))
      | ~ r1_tarski(A_9,k1_relat_1(k6_relat_1(A_9)))
      | ~ v1_relat_1(k6_relat_1(A_9)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_145])).

tff(c_158,plain,(
    ! [A_9] : r1_tarski(A_9,k10_relat_1(k6_relat_1(A_9),A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_6,c_12,c_154])).

tff(c_24,plain,(
    ! [A_15] : v1_funct_1(k6_relat_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_28,plain,(
    ! [A_16] : v2_funct_1(k6_relat_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_288,plain,(
    ! [B_49,A_50] :
      ( r1_tarski(k10_relat_1(B_49,k9_relat_1(B_49,A_50)),A_50)
      | ~ v2_funct_1(B_49)
      | ~ v1_funct_1(B_49)
      | ~ v1_relat_1(B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_299,plain,(
    ! [A_9] :
      ( r1_tarski(k10_relat_1(k6_relat_1(A_9),A_9),A_9)
      | ~ v2_funct_1(k6_relat_1(A_9))
      | ~ v1_funct_1(k6_relat_1(A_9))
      | ~ v1_relat_1(k6_relat_1(A_9)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_288])).

tff(c_305,plain,(
    ! [A_51] : r1_tarski(k10_relat_1(k6_relat_1(A_51),A_51),A_51) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_28,c_299])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_307,plain,(
    ! [A_51] :
      ( k10_relat_1(k6_relat_1(A_51),A_51) = A_51
      | ~ r1_tarski(A_51,k10_relat_1(k6_relat_1(A_51),A_51)) ) ),
    inference(resolution,[status(thm)],[c_305,c_2])).

tff(c_310,plain,(
    ! [A_51] : k10_relat_1(k6_relat_1(A_51),A_51) = A_51 ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_307])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( k5_relat_1(k6_relat_1(A_10),B_11) = k7_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_358,plain,(
    ! [B_54,C_55,A_56] :
      ( k10_relat_1(k5_relat_1(B_54,C_55),A_56) = k10_relat_1(B_54,k10_relat_1(C_55,A_56))
      | ~ v1_relat_1(C_55)
      | ~ v1_relat_1(B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_383,plain,(
    ! [A_10,B_11,A_56] :
      ( k10_relat_1(k6_relat_1(A_10),k10_relat_1(B_11,A_56)) = k10_relat_1(k7_relat_1(B_11,A_10),A_56)
      | ~ v1_relat_1(B_11)
      | ~ v1_relat_1(k6_relat_1(A_10))
      | ~ v1_relat_1(B_11) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_358])).

tff(c_434,plain,(
    ! [A_58,B_59,A_60] :
      ( k10_relat_1(k6_relat_1(A_58),k10_relat_1(B_59,A_60)) = k10_relat_1(k7_relat_1(B_59,A_58),A_60)
      | ~ v1_relat_1(B_59) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_383])).

tff(c_456,plain,(
    ! [A_51,A_58] :
      ( k10_relat_1(k7_relat_1(k6_relat_1(A_51),A_58),A_51) = k10_relat_1(k6_relat_1(A_58),A_51)
      | ~ v1_relat_1(k6_relat_1(A_51)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_310,c_434])).

tff(c_469,plain,(
    ! [A_61,A_62] : k10_relat_1(k7_relat_1(k6_relat_1(A_61),A_62),A_61) = k10_relat_1(k6_relat_1(A_62),A_61) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_456])).

tff(c_485,plain,(
    ! [A_9,A_39] :
      ( k10_relat_1(k6_relat_1(A_9),A_9) = k10_relat_1(k6_relat_1(A_39),A_9)
      | ~ r1_tarski(A_9,A_39) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_469])).

tff(c_501,plain,(
    ! [A_63,A_64] :
      ( k10_relat_1(k6_relat_1(A_63),A_64) = A_64
      | ~ r1_tarski(A_64,A_63) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_310,c_485])).

tff(c_387,plain,(
    ! [A_10,B_11,A_56] :
      ( k10_relat_1(k6_relat_1(A_10),k10_relat_1(B_11,A_56)) = k10_relat_1(k7_relat_1(B_11,A_10),A_56)
      | ~ v1_relat_1(B_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_383])).

tff(c_507,plain,(
    ! [A_63,A_10,A_64] :
      ( k10_relat_1(k7_relat_1(k6_relat_1(A_63),A_10),A_64) = k10_relat_1(k6_relat_1(A_10),A_64)
      | ~ v1_relat_1(k6_relat_1(A_63))
      | ~ r1_tarski(A_64,A_63) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_501,c_387])).

tff(c_749,plain,(
    ! [A_74,A_75,A_76] :
      ( k10_relat_1(k7_relat_1(k6_relat_1(A_74),A_75),A_76) = k10_relat_1(k6_relat_1(A_75),A_76)
      | ~ r1_tarski(A_76,A_74) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_507])).

tff(c_982,plain,(
    ! [A_83,A_82,A_81] :
      ( k10_relat_1(k6_relat_1(A_83),A_82) = k10_relat_1(k6_relat_1(A_81),A_82)
      | ~ r1_tarski(A_82,A_81)
      | ~ r1_tarski(A_81,A_83) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_749])).

tff(c_1002,plain,(
    ! [A_84] :
      ( k10_relat_1(k6_relat_1(k10_relat_1('#skF_1','#skF_3')),A_84) = k10_relat_1(k6_relat_1('#skF_2'),A_84)
      | ~ r1_tarski(A_84,k10_relat_1('#skF_1','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_36,c_982])).

tff(c_1041,plain,
    ( k10_relat_1(k6_relat_1('#skF_2'),k10_relat_1('#skF_1','#skF_3')) = k10_relat_1('#skF_1','#skF_3')
    | ~ r1_tarski(k10_relat_1('#skF_1','#skF_3'),k10_relat_1('#skF_1','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1002,c_310])).

tff(c_1083,plain,(
    k10_relat_1(k6_relat_1('#skF_2'),k10_relat_1('#skF_1','#skF_3')) = k10_relat_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1041])).

tff(c_1108,plain,
    ( k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1083,c_387])).

tff(c_1127,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1108])).

tff(c_1129,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_1127])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:56:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.26/1.61  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.26/1.61  
% 3.26/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.26/1.62  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.26/1.62  
% 3.26/1.62  %Foreground sorts:
% 3.26/1.62  
% 3.26/1.62  
% 3.26/1.62  %Background operators:
% 3.26/1.62  
% 3.26/1.62  
% 3.26/1.62  %Foreground operators:
% 3.26/1.62  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.26/1.62  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.26/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.26/1.62  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.26/1.62  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.26/1.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.26/1.62  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.26/1.62  tff('#skF_2', type, '#skF_2': $i).
% 3.26/1.62  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.26/1.62  tff('#skF_3', type, '#skF_3': $i).
% 3.26/1.62  tff('#skF_1', type, '#skF_1': $i).
% 3.26/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.26/1.62  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.26/1.62  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.26/1.62  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.26/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.26/1.62  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.26/1.62  
% 3.26/1.63  tff(f_92, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_funct_2)).
% 3.26/1.63  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.26/1.63  tff(f_68, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 3.26/1.63  tff(f_46, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 3.26/1.63  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 3.26/1.63  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_relat_1)).
% 3.26/1.63  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 3.26/1.63  tff(f_74, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_funct_1)).
% 3.26/1.63  tff(f_64, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 3.26/1.63  tff(f_82, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => r1_tarski(k10_relat_1(B, k9_relat_1(B, A)), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_funct_1)).
% 3.26/1.63  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 3.26/1.63  tff(f_42, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k10_relat_1(k5_relat_1(B, C), A) = k10_relat_1(B, k10_relat_1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t181_relat_1)).
% 3.26/1.63  tff(c_34, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')!=k10_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.26/1.63  tff(c_40, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.26/1.63  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.26/1.63  tff(c_36, plain, (r1_tarski(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.26/1.63  tff(c_26, plain, (![A_16]: (v1_relat_1(k6_relat_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.26/1.63  tff(c_12, plain, (![A_9]: (k1_relat_1(k6_relat_1(A_9))=A_9)), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.26/1.63  tff(c_134, plain, (![B_38, A_39]: (k7_relat_1(B_38, A_39)=B_38 | ~r1_tarski(k1_relat_1(B_38), A_39) | ~v1_relat_1(B_38))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.26/1.63  tff(c_137, plain, (![A_9, A_39]: (k7_relat_1(k6_relat_1(A_9), A_39)=k6_relat_1(A_9) | ~r1_tarski(A_9, A_39) | ~v1_relat_1(k6_relat_1(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_134])).
% 3.26/1.63  tff(c_143, plain, (![A_9, A_39]: (k7_relat_1(k6_relat_1(A_9), A_39)=k6_relat_1(A_9) | ~r1_tarski(A_9, A_39))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_137])).
% 3.26/1.63  tff(c_14, plain, (![A_9]: (k2_relat_1(k6_relat_1(A_9))=A_9)), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.26/1.63  tff(c_65, plain, (![A_29]: (k7_relat_1(A_29, k1_relat_1(A_29))=A_29 | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.26/1.63  tff(c_74, plain, (![A_9]: (k7_relat_1(k6_relat_1(A_9), A_9)=k6_relat_1(A_9) | ~v1_relat_1(k6_relat_1(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_65])).
% 3.26/1.63  tff(c_78, plain, (![A_9]: (k7_relat_1(k6_relat_1(A_9), A_9)=k6_relat_1(A_9))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_74])).
% 3.26/1.63  tff(c_98, plain, (![B_33, A_34]: (k2_relat_1(k7_relat_1(B_33, A_34))=k9_relat_1(B_33, A_34) | ~v1_relat_1(B_33))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.26/1.63  tff(c_107, plain, (![A_9]: (k9_relat_1(k6_relat_1(A_9), A_9)=k2_relat_1(k6_relat_1(A_9)) | ~v1_relat_1(k6_relat_1(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_78, c_98])).
% 3.26/1.63  tff(c_114, plain, (![A_9]: (k9_relat_1(k6_relat_1(A_9), A_9)=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_14, c_107])).
% 3.26/1.63  tff(c_145, plain, (![A_40, B_41]: (r1_tarski(A_40, k10_relat_1(B_41, k9_relat_1(B_41, A_40))) | ~r1_tarski(A_40, k1_relat_1(B_41)) | ~v1_relat_1(B_41))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.26/1.63  tff(c_154, plain, (![A_9]: (r1_tarski(A_9, k10_relat_1(k6_relat_1(A_9), A_9)) | ~r1_tarski(A_9, k1_relat_1(k6_relat_1(A_9))) | ~v1_relat_1(k6_relat_1(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_114, c_145])).
% 3.26/1.63  tff(c_158, plain, (![A_9]: (r1_tarski(A_9, k10_relat_1(k6_relat_1(A_9), A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_6, c_12, c_154])).
% 3.26/1.63  tff(c_24, plain, (![A_15]: (v1_funct_1(k6_relat_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.26/1.63  tff(c_28, plain, (![A_16]: (v2_funct_1(k6_relat_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.26/1.63  tff(c_288, plain, (![B_49, A_50]: (r1_tarski(k10_relat_1(B_49, k9_relat_1(B_49, A_50)), A_50) | ~v2_funct_1(B_49) | ~v1_funct_1(B_49) | ~v1_relat_1(B_49))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.26/1.63  tff(c_299, plain, (![A_9]: (r1_tarski(k10_relat_1(k6_relat_1(A_9), A_9), A_9) | ~v2_funct_1(k6_relat_1(A_9)) | ~v1_funct_1(k6_relat_1(A_9)) | ~v1_relat_1(k6_relat_1(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_114, c_288])).
% 3.26/1.63  tff(c_305, plain, (![A_51]: (r1_tarski(k10_relat_1(k6_relat_1(A_51), A_51), A_51))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_28, c_299])).
% 3.26/1.63  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.26/1.63  tff(c_307, plain, (![A_51]: (k10_relat_1(k6_relat_1(A_51), A_51)=A_51 | ~r1_tarski(A_51, k10_relat_1(k6_relat_1(A_51), A_51)))), inference(resolution, [status(thm)], [c_305, c_2])).
% 3.26/1.63  tff(c_310, plain, (![A_51]: (k10_relat_1(k6_relat_1(A_51), A_51)=A_51)), inference(demodulation, [status(thm), theory('equality')], [c_158, c_307])).
% 3.26/1.63  tff(c_16, plain, (![A_10, B_11]: (k5_relat_1(k6_relat_1(A_10), B_11)=k7_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.26/1.63  tff(c_358, plain, (![B_54, C_55, A_56]: (k10_relat_1(k5_relat_1(B_54, C_55), A_56)=k10_relat_1(B_54, k10_relat_1(C_55, A_56)) | ~v1_relat_1(C_55) | ~v1_relat_1(B_54))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.26/1.63  tff(c_383, plain, (![A_10, B_11, A_56]: (k10_relat_1(k6_relat_1(A_10), k10_relat_1(B_11, A_56))=k10_relat_1(k7_relat_1(B_11, A_10), A_56) | ~v1_relat_1(B_11) | ~v1_relat_1(k6_relat_1(A_10)) | ~v1_relat_1(B_11))), inference(superposition, [status(thm), theory('equality')], [c_16, c_358])).
% 3.26/1.63  tff(c_434, plain, (![A_58, B_59, A_60]: (k10_relat_1(k6_relat_1(A_58), k10_relat_1(B_59, A_60))=k10_relat_1(k7_relat_1(B_59, A_58), A_60) | ~v1_relat_1(B_59))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_383])).
% 3.26/1.63  tff(c_456, plain, (![A_51, A_58]: (k10_relat_1(k7_relat_1(k6_relat_1(A_51), A_58), A_51)=k10_relat_1(k6_relat_1(A_58), A_51) | ~v1_relat_1(k6_relat_1(A_51)))), inference(superposition, [status(thm), theory('equality')], [c_310, c_434])).
% 3.26/1.63  tff(c_469, plain, (![A_61, A_62]: (k10_relat_1(k7_relat_1(k6_relat_1(A_61), A_62), A_61)=k10_relat_1(k6_relat_1(A_62), A_61))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_456])).
% 3.26/1.63  tff(c_485, plain, (![A_9, A_39]: (k10_relat_1(k6_relat_1(A_9), A_9)=k10_relat_1(k6_relat_1(A_39), A_9) | ~r1_tarski(A_9, A_39))), inference(superposition, [status(thm), theory('equality')], [c_143, c_469])).
% 3.26/1.63  tff(c_501, plain, (![A_63, A_64]: (k10_relat_1(k6_relat_1(A_63), A_64)=A_64 | ~r1_tarski(A_64, A_63))), inference(demodulation, [status(thm), theory('equality')], [c_310, c_485])).
% 3.26/1.63  tff(c_387, plain, (![A_10, B_11, A_56]: (k10_relat_1(k6_relat_1(A_10), k10_relat_1(B_11, A_56))=k10_relat_1(k7_relat_1(B_11, A_10), A_56) | ~v1_relat_1(B_11))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_383])).
% 3.26/1.63  tff(c_507, plain, (![A_63, A_10, A_64]: (k10_relat_1(k7_relat_1(k6_relat_1(A_63), A_10), A_64)=k10_relat_1(k6_relat_1(A_10), A_64) | ~v1_relat_1(k6_relat_1(A_63)) | ~r1_tarski(A_64, A_63))), inference(superposition, [status(thm), theory('equality')], [c_501, c_387])).
% 3.26/1.63  tff(c_749, plain, (![A_74, A_75, A_76]: (k10_relat_1(k7_relat_1(k6_relat_1(A_74), A_75), A_76)=k10_relat_1(k6_relat_1(A_75), A_76) | ~r1_tarski(A_76, A_74))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_507])).
% 3.26/1.63  tff(c_982, plain, (![A_83, A_82, A_81]: (k10_relat_1(k6_relat_1(A_83), A_82)=k10_relat_1(k6_relat_1(A_81), A_82) | ~r1_tarski(A_82, A_81) | ~r1_tarski(A_81, A_83))), inference(superposition, [status(thm), theory('equality')], [c_143, c_749])).
% 3.26/1.63  tff(c_1002, plain, (![A_84]: (k10_relat_1(k6_relat_1(k10_relat_1('#skF_1', '#skF_3')), A_84)=k10_relat_1(k6_relat_1('#skF_2'), A_84) | ~r1_tarski(A_84, k10_relat_1('#skF_1', '#skF_3')))), inference(resolution, [status(thm)], [c_36, c_982])).
% 3.26/1.63  tff(c_1041, plain, (k10_relat_1(k6_relat_1('#skF_2'), k10_relat_1('#skF_1', '#skF_3'))=k10_relat_1('#skF_1', '#skF_3') | ~r1_tarski(k10_relat_1('#skF_1', '#skF_3'), k10_relat_1('#skF_1', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1002, c_310])).
% 3.26/1.63  tff(c_1083, plain, (k10_relat_1(k6_relat_1('#skF_2'), k10_relat_1('#skF_1', '#skF_3'))=k10_relat_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1041])).
% 3.26/1.63  tff(c_1108, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1083, c_387])).
% 3.26/1.63  tff(c_1127, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1108])).
% 3.26/1.63  tff(c_1129, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_1127])).
% 3.26/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.26/1.63  
% 3.26/1.63  Inference rules
% 3.26/1.63  ----------------------
% 3.26/1.63  #Ref     : 0
% 3.26/1.63  #Sup     : 227
% 3.26/1.63  #Fact    : 0
% 3.26/1.63  #Define  : 0
% 3.26/1.63  #Split   : 1
% 3.26/1.63  #Chain   : 0
% 3.26/1.63  #Close   : 0
% 3.26/1.63  
% 3.26/1.63  Ordering : KBO
% 3.26/1.63  
% 3.26/1.63  Simplification rules
% 3.26/1.63  ----------------------
% 3.26/1.63  #Subsume      : 12
% 3.26/1.64  #Demod        : 317
% 3.26/1.64  #Tautology    : 121
% 3.26/1.64  #SimpNegUnit  : 1
% 3.26/1.64  #BackRed      : 2
% 3.26/1.64  
% 3.26/1.64  #Partial instantiations: 0
% 3.26/1.64  #Strategies tried      : 1
% 3.26/1.64  
% 3.26/1.64  Timing (in seconds)
% 3.26/1.64  ----------------------
% 3.26/1.64  Preprocessing        : 0.30
% 3.26/1.64  Parsing              : 0.17
% 3.26/1.64  CNF conversion       : 0.02
% 3.26/1.64  Main loop            : 0.46
% 3.26/1.64  Inferencing          : 0.18
% 3.26/1.64  Reduction            : 0.15
% 3.26/1.64  Demodulation         : 0.11
% 3.26/1.64  BG Simplification    : 0.02
% 3.26/1.64  Subsumption          : 0.08
% 3.26/1.64  Abstraction          : 0.03
% 3.26/1.64  MUC search           : 0.00
% 3.26/1.64  Cooper               : 0.00
% 3.26/1.64  Total                : 0.79
% 3.26/1.64  Index Insertion      : 0.00
% 3.26/1.64  Index Deletion       : 0.00
% 3.26/1.64  Index Matching       : 0.00
% 3.26/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
