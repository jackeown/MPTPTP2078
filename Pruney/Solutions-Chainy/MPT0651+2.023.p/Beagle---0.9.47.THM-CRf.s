%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:51 EST 2020

% Result     : Theorem 3.32s
% Output     : CNFRefutation 3.32s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 165 expanded)
%              Number of leaves         :   24 (  69 expanded)
%              Depth                    :   10
%              Number of atoms          :  135 ( 401 expanded)
%              Number of equality atoms :   42 ( 135 expanded)
%              Maximal formula depth    :    8 (   3 average)
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

tff(f_101,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v2_funct_1(A)
         => ( k1_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A)
            & k2_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_64,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_76,axiom,(
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

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).

tff(c_30,plain,
    ( k2_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1')
    | k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_67,plain,(
    k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_36,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_22,plain,(
    ! [A_15] : v1_relat_1(k6_relat_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_14,plain,(
    ! [A_12] : k1_relat_1(k6_relat_1(A_12)) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_16,plain,(
    ! [A_12] : k2_relat_1(k6_relat_1(A_12)) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_77,plain,(
    ! [A_24] :
      ( k5_relat_1(A_24,k6_relat_1(k2_relat_1(A_24))) = A_24
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_89,plain,(
    ! [A_12] :
      ( k5_relat_1(k6_relat_1(A_12),k6_relat_1(A_12)) = k6_relat_1(A_12)
      | ~ v1_relat_1(k6_relat_1(A_12)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_77])).

tff(c_93,plain,(
    ! [A_12] : k5_relat_1(k6_relat_1(A_12),k6_relat_1(A_12)) = k6_relat_1(A_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_89])).

tff(c_170,plain,(
    ! [A_28,B_29] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_28,B_29)),k1_relat_1(A_28))
      | ~ v1_relat_1(B_29)
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_179,plain,(
    ! [A_12] :
      ( r1_tarski(k1_relat_1(k6_relat_1(A_12)),k1_relat_1(k6_relat_1(A_12)))
      | ~ v1_relat_1(k6_relat_1(A_12))
      | ~ v1_relat_1(k6_relat_1(A_12)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_170])).

tff(c_194,plain,(
    ! [A_12] : r1_tarski(A_12,A_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_14,c_14,c_179])).

tff(c_34,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_32,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_103,plain,(
    ! [A_26] :
      ( k4_relat_1(A_26) = k2_funct_1(A_26)
      | ~ v2_funct_1(A_26)
      | ~ v1_funct_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_106,plain,
    ( k4_relat_1('#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_103])).

tff(c_109,plain,(
    k4_relat_1('#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_106])).

tff(c_2,plain,(
    ! [A_1] :
      ( v1_relat_1(k4_relat_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_131,plain,
    ( v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_2])).

tff(c_139,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_131])).

tff(c_6,plain,(
    ! [A_2] :
      ( k1_relat_1(k4_relat_1(A_2)) = k2_relat_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_125,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_6])).

tff(c_135,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_125])).

tff(c_362,plain,(
    ! [A_39,B_40] :
      ( k1_relat_1(k5_relat_1(A_39,B_40)) = k1_relat_1(A_39)
      | ~ r1_tarski(k2_relat_1(A_39),k1_relat_1(B_40))
      | ~ v1_relat_1(B_40)
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_371,plain,(
    ! [A_39] :
      ( k1_relat_1(k5_relat_1(A_39,k2_funct_1('#skF_1'))) = k1_relat_1(A_39)
      | ~ r1_tarski(k2_relat_1(A_39),k2_relat_1('#skF_1'))
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v1_relat_1(A_39) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_362])).

tff(c_561,plain,(
    ! [A_47] :
      ( k1_relat_1(k5_relat_1(A_47,k2_funct_1('#skF_1'))) = k1_relat_1(A_47)
      | ~ r1_tarski(k2_relat_1(A_47),k2_relat_1('#skF_1'))
      | ~ v1_relat_1(A_47) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_371])).

tff(c_568,plain,
    ( k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_194,c_561])).

tff(c_583,plain,(
    k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_568])).

tff(c_585,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_583])).

tff(c_586,plain,(
    k2_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_627,plain,(
    ! [A_51] :
      ( k4_relat_1(A_51) = k2_funct_1(A_51)
      | ~ v2_funct_1(A_51)
      | ~ v1_funct_1(A_51)
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_630,plain,
    ( k4_relat_1('#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_627])).

tff(c_633,plain,(
    k4_relat_1('#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_630])).

tff(c_643,plain,
    ( v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_633,c_2])).

tff(c_651,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_643])).

tff(c_4,plain,(
    ! [A_2] :
      ( k2_relat_1(k4_relat_1(A_2)) = k1_relat_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_640,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_633,c_4])).

tff(c_649,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_640])).

tff(c_601,plain,(
    ! [A_49] :
      ( k5_relat_1(A_49,k6_relat_1(k2_relat_1(A_49))) = A_49
      | ~ v1_relat_1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_610,plain,(
    ! [A_2] :
      ( k5_relat_1(k4_relat_1(A_2),k6_relat_1(k1_relat_1(A_2))) = k4_relat_1(A_2)
      | ~ v1_relat_1(k4_relat_1(A_2))
      | ~ v1_relat_1(A_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_601])).

tff(c_715,plain,(
    ! [A_54,B_55] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_54,B_55)),k1_relat_1(A_54))
      | ~ v1_relat_1(B_55)
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1218,plain,(
    ! [A_76,B_77] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k4_relat_1(A_76),B_77)),k2_relat_1(A_76))
      | ~ v1_relat_1(B_77)
      | ~ v1_relat_1(k4_relat_1(A_76))
      | ~ v1_relat_1(A_76) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_715])).

tff(c_1236,plain,(
    ! [A_2] :
      ( r1_tarski(k1_relat_1(k4_relat_1(A_2)),k2_relat_1(A_2))
      | ~ v1_relat_1(k6_relat_1(k1_relat_1(A_2)))
      | ~ v1_relat_1(k4_relat_1(A_2))
      | ~ v1_relat_1(A_2)
      | ~ v1_relat_1(k4_relat_1(A_2))
      | ~ v1_relat_1(A_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_610,c_1218])).

tff(c_1294,plain,(
    ! [A_79] :
      ( r1_tarski(k1_relat_1(k4_relat_1(A_79)),k2_relat_1(A_79))
      | ~ v1_relat_1(k4_relat_1(A_79))
      | ~ v1_relat_1(A_79) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1236])).

tff(c_12,plain,(
    ! [B_11,A_9] :
      ( k2_relat_1(k5_relat_1(B_11,A_9)) = k2_relat_1(A_9)
      | ~ r1_tarski(k1_relat_1(A_9),k2_relat_1(B_11))
      | ~ v1_relat_1(B_11)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1446,plain,(
    ! [A_81] :
      ( k2_relat_1(k5_relat_1(A_81,k4_relat_1(A_81))) = k2_relat_1(k4_relat_1(A_81))
      | ~ v1_relat_1(k4_relat_1(A_81))
      | ~ v1_relat_1(A_81) ) ),
    inference(resolution,[status(thm)],[c_1294,c_12])).

tff(c_1484,plain,
    ( k2_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k2_relat_1(k4_relat_1('#skF_1'))
    | ~ v1_relat_1(k4_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_633,c_1446])).

tff(c_1500,plain,(
    k2_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_651,c_633,c_649,c_633,c_1484])).

tff(c_1502,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_586,c_1500])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n016.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 18:20:19 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.32/1.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.56  
% 3.32/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.57  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1
% 3.32/1.57  
% 3.32/1.57  %Foreground sorts:
% 3.32/1.57  
% 3.32/1.57  
% 3.32/1.57  %Background operators:
% 3.32/1.57  
% 3.32/1.57  
% 3.32/1.57  %Foreground operators:
% 3.32/1.57  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.32/1.57  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.32/1.57  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.32/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.32/1.57  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.32/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.32/1.57  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.32/1.57  tff('#skF_1', type, '#skF_1': $i).
% 3.32/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.32/1.57  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.32/1.57  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.32/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.32/1.57  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.32/1.57  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 3.32/1.57  
% 3.32/1.58  tff(f_101, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)) & (k2_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_funct_1)).
% 3.32/1.58  tff(f_80, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 3.32/1.58  tff(f_64, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 3.32/1.58  tff(f_68, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 3.32/1.58  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_relat_1)).
% 3.32/1.58  tff(f_76, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 3.32/1.58  tff(f_29, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 3.32/1.58  tff(f_35, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_relat_1)).
% 3.32/1.58  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_relat_1)).
% 3.32/1.58  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_relat_1)).
% 3.32/1.58  tff(c_30, plain, (k2_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1') | k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.32/1.58  tff(c_67, plain, (k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_30])).
% 3.32/1.58  tff(c_36, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.32/1.58  tff(c_22, plain, (![A_15]: (v1_relat_1(k6_relat_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.32/1.58  tff(c_14, plain, (![A_12]: (k1_relat_1(k6_relat_1(A_12))=A_12)), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.32/1.58  tff(c_16, plain, (![A_12]: (k2_relat_1(k6_relat_1(A_12))=A_12)), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.32/1.58  tff(c_77, plain, (![A_24]: (k5_relat_1(A_24, k6_relat_1(k2_relat_1(A_24)))=A_24 | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.32/1.58  tff(c_89, plain, (![A_12]: (k5_relat_1(k6_relat_1(A_12), k6_relat_1(A_12))=k6_relat_1(A_12) | ~v1_relat_1(k6_relat_1(A_12)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_77])).
% 3.32/1.58  tff(c_93, plain, (![A_12]: (k5_relat_1(k6_relat_1(A_12), k6_relat_1(A_12))=k6_relat_1(A_12))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_89])).
% 3.32/1.58  tff(c_170, plain, (![A_28, B_29]: (r1_tarski(k1_relat_1(k5_relat_1(A_28, B_29)), k1_relat_1(A_28)) | ~v1_relat_1(B_29) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.32/1.58  tff(c_179, plain, (![A_12]: (r1_tarski(k1_relat_1(k6_relat_1(A_12)), k1_relat_1(k6_relat_1(A_12))) | ~v1_relat_1(k6_relat_1(A_12)) | ~v1_relat_1(k6_relat_1(A_12)))), inference(superposition, [status(thm), theory('equality')], [c_93, c_170])).
% 3.32/1.58  tff(c_194, plain, (![A_12]: (r1_tarski(A_12, A_12))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_14, c_14, c_179])).
% 3.32/1.58  tff(c_34, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.32/1.58  tff(c_32, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.32/1.58  tff(c_103, plain, (![A_26]: (k4_relat_1(A_26)=k2_funct_1(A_26) | ~v2_funct_1(A_26) | ~v1_funct_1(A_26) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.32/1.58  tff(c_106, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_32, c_103])).
% 3.32/1.58  tff(c_109, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_106])).
% 3.32/1.58  tff(c_2, plain, (![A_1]: (v1_relat_1(k4_relat_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.32/1.58  tff(c_131, plain, (v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_109, c_2])).
% 3.32/1.58  tff(c_139, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_131])).
% 3.32/1.58  tff(c_6, plain, (![A_2]: (k1_relat_1(k4_relat_1(A_2))=k2_relat_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.32/1.58  tff(c_125, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_109, c_6])).
% 3.32/1.58  tff(c_135, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_125])).
% 3.32/1.58  tff(c_362, plain, (![A_39, B_40]: (k1_relat_1(k5_relat_1(A_39, B_40))=k1_relat_1(A_39) | ~r1_tarski(k2_relat_1(A_39), k1_relat_1(B_40)) | ~v1_relat_1(B_40) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.32/1.58  tff(c_371, plain, (![A_39]: (k1_relat_1(k5_relat_1(A_39, k2_funct_1('#skF_1')))=k1_relat_1(A_39) | ~r1_tarski(k2_relat_1(A_39), k2_relat_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(A_39))), inference(superposition, [status(thm), theory('equality')], [c_135, c_362])).
% 3.32/1.58  tff(c_561, plain, (![A_47]: (k1_relat_1(k5_relat_1(A_47, k2_funct_1('#skF_1')))=k1_relat_1(A_47) | ~r1_tarski(k2_relat_1(A_47), k2_relat_1('#skF_1')) | ~v1_relat_1(A_47))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_371])).
% 3.32/1.58  tff(c_568, plain, (k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_194, c_561])).
% 3.32/1.58  tff(c_583, plain, (k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_568])).
% 3.32/1.58  tff(c_585, plain, $false, inference(negUnitSimplification, [status(thm)], [c_67, c_583])).
% 3.32/1.58  tff(c_586, plain, (k2_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_30])).
% 3.32/1.58  tff(c_627, plain, (![A_51]: (k4_relat_1(A_51)=k2_funct_1(A_51) | ~v2_funct_1(A_51) | ~v1_funct_1(A_51) | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.32/1.58  tff(c_630, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_32, c_627])).
% 3.32/1.58  tff(c_633, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_630])).
% 3.32/1.58  tff(c_643, plain, (v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_633, c_2])).
% 3.32/1.58  tff(c_651, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_643])).
% 3.32/1.58  tff(c_4, plain, (![A_2]: (k2_relat_1(k4_relat_1(A_2))=k1_relat_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.32/1.58  tff(c_640, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_633, c_4])).
% 3.32/1.58  tff(c_649, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_640])).
% 3.32/1.58  tff(c_601, plain, (![A_49]: (k5_relat_1(A_49, k6_relat_1(k2_relat_1(A_49)))=A_49 | ~v1_relat_1(A_49))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.32/1.58  tff(c_610, plain, (![A_2]: (k5_relat_1(k4_relat_1(A_2), k6_relat_1(k1_relat_1(A_2)))=k4_relat_1(A_2) | ~v1_relat_1(k4_relat_1(A_2)) | ~v1_relat_1(A_2))), inference(superposition, [status(thm), theory('equality')], [c_4, c_601])).
% 3.32/1.58  tff(c_715, plain, (![A_54, B_55]: (r1_tarski(k1_relat_1(k5_relat_1(A_54, B_55)), k1_relat_1(A_54)) | ~v1_relat_1(B_55) | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.32/1.58  tff(c_1218, plain, (![A_76, B_77]: (r1_tarski(k1_relat_1(k5_relat_1(k4_relat_1(A_76), B_77)), k2_relat_1(A_76)) | ~v1_relat_1(B_77) | ~v1_relat_1(k4_relat_1(A_76)) | ~v1_relat_1(A_76))), inference(superposition, [status(thm), theory('equality')], [c_6, c_715])).
% 3.32/1.58  tff(c_1236, plain, (![A_2]: (r1_tarski(k1_relat_1(k4_relat_1(A_2)), k2_relat_1(A_2)) | ~v1_relat_1(k6_relat_1(k1_relat_1(A_2))) | ~v1_relat_1(k4_relat_1(A_2)) | ~v1_relat_1(A_2) | ~v1_relat_1(k4_relat_1(A_2)) | ~v1_relat_1(A_2))), inference(superposition, [status(thm), theory('equality')], [c_610, c_1218])).
% 3.32/1.58  tff(c_1294, plain, (![A_79]: (r1_tarski(k1_relat_1(k4_relat_1(A_79)), k2_relat_1(A_79)) | ~v1_relat_1(k4_relat_1(A_79)) | ~v1_relat_1(A_79))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1236])).
% 3.32/1.58  tff(c_12, plain, (![B_11, A_9]: (k2_relat_1(k5_relat_1(B_11, A_9))=k2_relat_1(A_9) | ~r1_tarski(k1_relat_1(A_9), k2_relat_1(B_11)) | ~v1_relat_1(B_11) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.32/1.58  tff(c_1446, plain, (![A_81]: (k2_relat_1(k5_relat_1(A_81, k4_relat_1(A_81)))=k2_relat_1(k4_relat_1(A_81)) | ~v1_relat_1(k4_relat_1(A_81)) | ~v1_relat_1(A_81))), inference(resolution, [status(thm)], [c_1294, c_12])).
% 3.32/1.58  tff(c_1484, plain, (k2_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k2_relat_1(k4_relat_1('#skF_1')) | ~v1_relat_1(k4_relat_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_633, c_1446])).
% 3.32/1.58  tff(c_1500, plain, (k2_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_651, c_633, c_649, c_633, c_1484])).
% 3.32/1.58  tff(c_1502, plain, $false, inference(negUnitSimplification, [status(thm)], [c_586, c_1500])).
% 3.32/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.58  
% 3.32/1.58  Inference rules
% 3.32/1.58  ----------------------
% 3.32/1.58  #Ref     : 0
% 3.32/1.58  #Sup     : 336
% 3.32/1.58  #Fact    : 0
% 3.32/1.58  #Define  : 0
% 3.32/1.58  #Split   : 5
% 3.32/1.58  #Chain   : 0
% 3.32/1.58  #Close   : 0
% 3.32/1.58  
% 3.32/1.58  Ordering : KBO
% 3.32/1.58  
% 3.32/1.58  Simplification rules
% 3.32/1.58  ----------------------
% 3.32/1.58  #Subsume      : 11
% 3.32/1.58  #Demod        : 369
% 3.32/1.58  #Tautology    : 163
% 3.32/1.58  #SimpNegUnit  : 2
% 3.32/1.58  #BackRed      : 0
% 3.32/1.58  
% 3.32/1.58  #Partial instantiations: 0
% 3.32/1.58  #Strategies tried      : 1
% 3.32/1.58  
% 3.32/1.58  Timing (in seconds)
% 3.32/1.58  ----------------------
% 3.32/1.58  Preprocessing        : 0.32
% 3.32/1.58  Parsing              : 0.18
% 3.32/1.58  CNF conversion       : 0.02
% 3.32/1.58  Main loop            : 0.44
% 3.32/1.58  Inferencing          : 0.16
% 3.32/1.58  Reduction            : 0.16
% 3.32/1.58  Demodulation         : 0.12
% 3.32/1.58  BG Simplification    : 0.02
% 3.32/1.58  Subsumption          : 0.07
% 3.32/1.58  Abstraction          : 0.02
% 3.32/1.58  MUC search           : 0.00
% 3.32/1.58  Cooper               : 0.00
% 3.32/1.58  Total                : 0.79
% 3.32/1.58  Index Insertion      : 0.00
% 3.32/1.58  Index Deletion       : 0.00
% 3.32/1.58  Index Matching       : 0.00
% 3.32/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
