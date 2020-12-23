%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:34 EST 2020

% Result     : Theorem 8.51s
% Output     : CNFRefutation 8.51s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 178 expanded)
%              Number of leaves         :   40 (  76 expanded)
%              Depth                    :   12
%              Number of atoms          :  100 ( 253 expanded)
%              Number of equality atoms :   57 ( 108 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_77,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_99,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_88,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_45,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_50,plain,(
    ! [A_34] : k2_subset_1(A_34) = A_34 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_60,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) != k2_subset_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_63,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_60])).

tff(c_62,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_56,plain,(
    ! [A_39] : ~ v1_xboole_0(k1_zfmisc_1(A_39)) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_252,plain,(
    ! [B_73,A_74] :
      ( r2_hidden(B_73,A_74)
      | ~ m1_subset_1(B_73,A_74)
      | v1_xboole_0(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_28,plain,(
    ! [C_29,A_25] :
      ( r1_tarski(C_29,A_25)
      | ~ r2_hidden(C_29,k1_zfmisc_1(A_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_256,plain,(
    ! [B_73,A_25] :
      ( r1_tarski(B_73,A_25)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(A_25))
      | v1_xboole_0(k1_zfmisc_1(A_25)) ) ),
    inference(resolution,[status(thm)],[c_252,c_28])).

tff(c_260,plain,(
    ! [B_75,A_76] :
      ( r1_tarski(B_75,A_76)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(A_76)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_256])).

tff(c_269,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_260])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( k3_xboole_0(A_9,B_10) = A_9
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_273,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_269,c_14])).

tff(c_85,plain,(
    ! [B_48,A_49] : k3_xboole_0(B_48,A_49) = k3_xboole_0(A_49,B_48) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_7,B_8] : k2_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_100,plain,(
    ! [A_49,B_48] : k2_xboole_0(A_49,k3_xboole_0(B_48,A_49)) = A_49 ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_12])).

tff(c_298,plain,(
    k2_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_273,c_100])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_166,plain,(
    ! [A_56,B_57] :
      ( k3_xboole_0(A_56,B_57) = A_56
      | ~ r1_tarski(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_170,plain,(
    ! [B_4] : k3_xboole_0(B_4,B_4) = B_4 ),
    inference(resolution,[status(thm)],[c_8,c_166])).

tff(c_225,plain,(
    ! [A_70,B_71] : k5_xboole_0(A_70,k3_xboole_0(A_70,B_71)) = k4_xboole_0(A_70,B_71) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_234,plain,(
    ! [B_4] : k5_xboole_0(B_4,B_4) = k4_xboole_0(B_4,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_225])).

tff(c_10,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_295,plain,(
    k5_xboole_0('#skF_4','#skF_4') = k4_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_273,c_10])).

tff(c_304,plain,(
    k4_xboole_0('#skF_4','#skF_3') = k4_xboole_0('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_234,c_295])).

tff(c_22,plain,(
    ! [A_18,B_19] : k5_xboole_0(A_18,k4_xboole_0(B_19,A_18)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_317,plain,(
    k5_xboole_0('#skF_3',k4_xboole_0('#skF_4','#skF_4')) = k2_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_304,c_22])).

tff(c_321,plain,(
    k5_xboole_0('#skF_3',k4_xboole_0('#skF_4','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_298,c_317])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_796,plain,(
    ! [A_112,B_113] :
      ( k4_xboole_0(A_112,B_113) = k3_subset_1(A_112,B_113)
      | ~ m1_subset_1(B_113,k1_zfmisc_1(A_112)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_813,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_796])).

tff(c_515,plain,(
    ! [A_98,B_99,C_100] : k4_xboole_0(k3_xboole_0(A_98,B_99),C_100) = k3_xboole_0(A_98,k4_xboole_0(B_99,C_100)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_560,plain,(
    ! [B_101,C_102] : k3_xboole_0(B_101,k4_xboole_0(B_101,C_102)) = k4_xboole_0(B_101,C_102) ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_515])).

tff(c_581,plain,(
    ! [B_101,C_102] : k2_xboole_0(B_101,k4_xboole_0(B_101,C_102)) = B_101 ),
    inference(superposition,[status(thm),theory(equality)],[c_560,c_12])).

tff(c_549,plain,(
    ! [B_4,C_100] : k3_xboole_0(B_4,k4_xboole_0(B_4,C_100)) = k4_xboole_0(B_4,C_100) ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_515])).

tff(c_16,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k4_xboole_0(A_11,B_12)) = k3_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_575,plain,(
    ! [B_101,C_102] : k5_xboole_0(B_101,k4_xboole_0(B_101,C_102)) = k4_xboole_0(B_101,k4_xboole_0(B_101,C_102)) ),
    inference(superposition,[status(thm),theory(equality)],[c_560,c_10])).

tff(c_653,plain,(
    ! [B_106,C_107] : k5_xboole_0(B_106,k4_xboole_0(B_106,C_107)) = k3_xboole_0(B_106,C_107) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_575])).

tff(c_20,plain,(
    ! [A_16,B_17] : k5_xboole_0(k5_xboole_0(A_16,B_17),k3_xboole_0(A_16,B_17)) = k2_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_659,plain,(
    ! [B_106,C_107] : k5_xboole_0(k3_xboole_0(B_106,C_107),k3_xboole_0(B_106,k4_xboole_0(B_106,C_107))) = k2_xboole_0(B_106,k4_xboole_0(B_106,C_107)) ),
    inference(superposition,[status(thm),theory(equality)],[c_653,c_20])).

tff(c_681,plain,(
    ! [B_106,C_107] : k5_xboole_0(k3_xboole_0(B_106,C_107),k4_xboole_0(B_106,C_107)) = B_106 ),
    inference(demodulation,[status(thm),theory(equality)],[c_581,c_549,c_659])).

tff(c_819,plain,(
    k5_xboole_0(k3_xboole_0('#skF_3','#skF_4'),k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_813,c_681])).

tff(c_840,plain,(
    k5_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_273,c_2,c_819])).

tff(c_542,plain,(
    ! [C_100] : k3_xboole_0('#skF_4',k4_xboole_0('#skF_3',C_100)) = k4_xboole_0('#skF_4',C_100) ),
    inference(superposition,[status(thm),theory(equality)],[c_273,c_515])).

tff(c_828,plain,(
    k3_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = k4_xboole_0('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_813,c_542])).

tff(c_1002,plain,(
    k5_xboole_0(k5_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')),k4_xboole_0('#skF_4','#skF_4')) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_828,c_20])).

tff(c_1019,plain,(
    k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_321,c_840,c_1002])).

tff(c_54,plain,(
    ! [A_37,B_38] :
      ( m1_subset_1(k3_subset_1(A_37,B_38),k1_zfmisc_1(A_37))
      | ~ m1_subset_1(B_38,k1_zfmisc_1(A_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2062,plain,(
    ! [A_145,B_146,C_147] :
      ( k4_subset_1(A_145,B_146,C_147) = k2_xboole_0(B_146,C_147)
      | ~ m1_subset_1(C_147,k1_zfmisc_1(A_145))
      | ~ m1_subset_1(B_146,k1_zfmisc_1(A_145)) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_14559,plain,(
    ! [A_317,B_318,B_319] :
      ( k4_subset_1(A_317,B_318,k3_subset_1(A_317,B_319)) = k2_xboole_0(B_318,k3_subset_1(A_317,B_319))
      | ~ m1_subset_1(B_318,k1_zfmisc_1(A_317))
      | ~ m1_subset_1(B_319,k1_zfmisc_1(A_317)) ) ),
    inference(resolution,[status(thm)],[c_54,c_2062])).

tff(c_14902,plain,(
    ! [B_322] :
      ( k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3',B_322)) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3',B_322))
      | ~ m1_subset_1(B_322,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_62,c_14559])).

tff(c_14921,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_62,c_14902])).

tff(c_14929,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1019,c_14921])).

tff(c_14931,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_14929])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:46:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.51/3.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.51/3.18  
% 8.51/3.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.51/3.18  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 8.51/3.18  
% 8.51/3.18  %Foreground sorts:
% 8.51/3.18  
% 8.51/3.18  
% 8.51/3.18  %Background operators:
% 8.51/3.18  
% 8.51/3.18  
% 8.51/3.18  %Foreground operators:
% 8.51/3.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.51/3.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.51/3.18  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.51/3.18  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.51/3.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.51/3.18  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.51/3.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.51/3.18  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 8.51/3.18  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 8.51/3.18  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.51/3.18  tff('#skF_3', type, '#skF_3': $i).
% 8.51/3.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.51/3.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.51/3.18  tff(k3_tarski, type, k3_tarski: $i > $i).
% 8.51/3.18  tff('#skF_4', type, '#skF_4': $i).
% 8.51/3.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.51/3.18  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.51/3.18  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.51/3.18  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.51/3.18  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.51/3.18  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 8.51/3.18  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.51/3.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.51/3.18  
% 8.51/3.19  tff(f_77, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 8.51/3.19  tff(f_99, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_subset_1)).
% 8.51/3.19  tff(f_88, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 8.51/3.19  tff(f_75, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 8.51/3.19  tff(f_60, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 8.51/3.19  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 8.51/3.19  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 8.51/3.19  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 8.51/3.19  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.51/3.19  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 8.51/3.19  tff(f_49, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 8.51/3.19  tff(f_81, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 8.51/3.19  tff(f_45, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 8.51/3.19  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 8.51/3.19  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 8.51/3.19  tff(f_85, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 8.51/3.19  tff(f_94, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 8.51/3.19  tff(c_50, plain, (![A_34]: (k2_subset_1(A_34)=A_34)), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.51/3.19  tff(c_60, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))!=k2_subset_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 8.51/3.19  tff(c_63, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_60])).
% 8.51/3.19  tff(c_62, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 8.51/3.19  tff(c_56, plain, (![A_39]: (~v1_xboole_0(k1_zfmisc_1(A_39)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 8.51/3.19  tff(c_252, plain, (![B_73, A_74]: (r2_hidden(B_73, A_74) | ~m1_subset_1(B_73, A_74) | v1_xboole_0(A_74))), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.51/3.19  tff(c_28, plain, (![C_29, A_25]: (r1_tarski(C_29, A_25) | ~r2_hidden(C_29, k1_zfmisc_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.51/3.19  tff(c_256, plain, (![B_73, A_25]: (r1_tarski(B_73, A_25) | ~m1_subset_1(B_73, k1_zfmisc_1(A_25)) | v1_xboole_0(k1_zfmisc_1(A_25)))), inference(resolution, [status(thm)], [c_252, c_28])).
% 8.51/3.19  tff(c_260, plain, (![B_75, A_76]: (r1_tarski(B_75, A_76) | ~m1_subset_1(B_75, k1_zfmisc_1(A_76)))), inference(negUnitSimplification, [status(thm)], [c_56, c_256])).
% 8.51/3.19  tff(c_269, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_62, c_260])).
% 8.51/3.19  tff(c_14, plain, (![A_9, B_10]: (k3_xboole_0(A_9, B_10)=A_9 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.51/3.19  tff(c_273, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_269, c_14])).
% 8.51/3.19  tff(c_85, plain, (![B_48, A_49]: (k3_xboole_0(B_48, A_49)=k3_xboole_0(A_49, B_48))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.51/3.19  tff(c_12, plain, (![A_7, B_8]: (k2_xboole_0(A_7, k3_xboole_0(A_7, B_8))=A_7)), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.51/3.19  tff(c_100, plain, (![A_49, B_48]: (k2_xboole_0(A_49, k3_xboole_0(B_48, A_49))=A_49)), inference(superposition, [status(thm), theory('equality')], [c_85, c_12])).
% 8.51/3.19  tff(c_298, plain, (k2_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_273, c_100])).
% 8.51/3.19  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.51/3.19  tff(c_166, plain, (![A_56, B_57]: (k3_xboole_0(A_56, B_57)=A_56 | ~r1_tarski(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.51/3.19  tff(c_170, plain, (![B_4]: (k3_xboole_0(B_4, B_4)=B_4)), inference(resolution, [status(thm)], [c_8, c_166])).
% 8.51/3.19  tff(c_225, plain, (![A_70, B_71]: (k5_xboole_0(A_70, k3_xboole_0(A_70, B_71))=k4_xboole_0(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.51/3.19  tff(c_234, plain, (![B_4]: (k5_xboole_0(B_4, B_4)=k4_xboole_0(B_4, B_4))), inference(superposition, [status(thm), theory('equality')], [c_170, c_225])).
% 8.51/3.19  tff(c_10, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.51/3.19  tff(c_295, plain, (k5_xboole_0('#skF_4', '#skF_4')=k4_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_273, c_10])).
% 8.51/3.19  tff(c_304, plain, (k4_xboole_0('#skF_4', '#skF_3')=k4_xboole_0('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_234, c_295])).
% 8.51/3.19  tff(c_22, plain, (![A_18, B_19]: (k5_xboole_0(A_18, k4_xboole_0(B_19, A_18))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.51/3.19  tff(c_317, plain, (k5_xboole_0('#skF_3', k4_xboole_0('#skF_4', '#skF_4'))=k2_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_304, c_22])).
% 8.51/3.19  tff(c_321, plain, (k5_xboole_0('#skF_3', k4_xboole_0('#skF_4', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_298, c_317])).
% 8.51/3.19  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.51/3.19  tff(c_796, plain, (![A_112, B_113]: (k4_xboole_0(A_112, B_113)=k3_subset_1(A_112, B_113) | ~m1_subset_1(B_113, k1_zfmisc_1(A_112)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.51/3.19  tff(c_813, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_62, c_796])).
% 8.51/3.19  tff(c_515, plain, (![A_98, B_99, C_100]: (k4_xboole_0(k3_xboole_0(A_98, B_99), C_100)=k3_xboole_0(A_98, k4_xboole_0(B_99, C_100)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.51/3.19  tff(c_560, plain, (![B_101, C_102]: (k3_xboole_0(B_101, k4_xboole_0(B_101, C_102))=k4_xboole_0(B_101, C_102))), inference(superposition, [status(thm), theory('equality')], [c_170, c_515])).
% 8.51/3.19  tff(c_581, plain, (![B_101, C_102]: (k2_xboole_0(B_101, k4_xboole_0(B_101, C_102))=B_101)), inference(superposition, [status(thm), theory('equality')], [c_560, c_12])).
% 8.51/3.19  tff(c_549, plain, (![B_4, C_100]: (k3_xboole_0(B_4, k4_xboole_0(B_4, C_100))=k4_xboole_0(B_4, C_100))), inference(superposition, [status(thm), theory('equality')], [c_170, c_515])).
% 8.51/3.19  tff(c_16, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k4_xboole_0(A_11, B_12))=k3_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.51/3.19  tff(c_575, plain, (![B_101, C_102]: (k5_xboole_0(B_101, k4_xboole_0(B_101, C_102))=k4_xboole_0(B_101, k4_xboole_0(B_101, C_102)))), inference(superposition, [status(thm), theory('equality')], [c_560, c_10])).
% 8.51/3.19  tff(c_653, plain, (![B_106, C_107]: (k5_xboole_0(B_106, k4_xboole_0(B_106, C_107))=k3_xboole_0(B_106, C_107))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_575])).
% 8.51/3.19  tff(c_20, plain, (![A_16, B_17]: (k5_xboole_0(k5_xboole_0(A_16, B_17), k3_xboole_0(A_16, B_17))=k2_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.51/3.19  tff(c_659, plain, (![B_106, C_107]: (k5_xboole_0(k3_xboole_0(B_106, C_107), k3_xboole_0(B_106, k4_xboole_0(B_106, C_107)))=k2_xboole_0(B_106, k4_xboole_0(B_106, C_107)))), inference(superposition, [status(thm), theory('equality')], [c_653, c_20])).
% 8.51/3.19  tff(c_681, plain, (![B_106, C_107]: (k5_xboole_0(k3_xboole_0(B_106, C_107), k4_xboole_0(B_106, C_107))=B_106)), inference(demodulation, [status(thm), theory('equality')], [c_581, c_549, c_659])).
% 8.51/3.19  tff(c_819, plain, (k5_xboole_0(k3_xboole_0('#skF_3', '#skF_4'), k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_813, c_681])).
% 8.51/3.19  tff(c_840, plain, (k5_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_273, c_2, c_819])).
% 8.51/3.19  tff(c_542, plain, (![C_100]: (k3_xboole_0('#skF_4', k4_xboole_0('#skF_3', C_100))=k4_xboole_0('#skF_4', C_100))), inference(superposition, [status(thm), theory('equality')], [c_273, c_515])).
% 8.51/3.19  tff(c_828, plain, (k3_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k4_xboole_0('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_813, c_542])).
% 8.51/3.19  tff(c_1002, plain, (k5_xboole_0(k5_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4')), k4_xboole_0('#skF_4', '#skF_4'))=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_828, c_20])).
% 8.51/3.19  tff(c_1019, plain, (k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_321, c_840, c_1002])).
% 8.51/3.19  tff(c_54, plain, (![A_37, B_38]: (m1_subset_1(k3_subset_1(A_37, B_38), k1_zfmisc_1(A_37)) | ~m1_subset_1(B_38, k1_zfmisc_1(A_37)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 8.51/3.19  tff(c_2062, plain, (![A_145, B_146, C_147]: (k4_subset_1(A_145, B_146, C_147)=k2_xboole_0(B_146, C_147) | ~m1_subset_1(C_147, k1_zfmisc_1(A_145)) | ~m1_subset_1(B_146, k1_zfmisc_1(A_145)))), inference(cnfTransformation, [status(thm)], [f_94])).
% 8.51/3.19  tff(c_14559, plain, (![A_317, B_318, B_319]: (k4_subset_1(A_317, B_318, k3_subset_1(A_317, B_319))=k2_xboole_0(B_318, k3_subset_1(A_317, B_319)) | ~m1_subset_1(B_318, k1_zfmisc_1(A_317)) | ~m1_subset_1(B_319, k1_zfmisc_1(A_317)))), inference(resolution, [status(thm)], [c_54, c_2062])).
% 8.51/3.19  tff(c_14902, plain, (![B_322]: (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', B_322))=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', B_322)) | ~m1_subset_1(B_322, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_62, c_14559])).
% 8.51/3.19  tff(c_14921, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_62, c_14902])).
% 8.51/3.19  tff(c_14929, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1019, c_14921])).
% 8.51/3.19  tff(c_14931, plain, $false, inference(negUnitSimplification, [status(thm)], [c_63, c_14929])).
% 8.51/3.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.51/3.19  
% 8.51/3.19  Inference rules
% 8.51/3.19  ----------------------
% 8.51/3.19  #Ref     : 0
% 8.51/3.19  #Sup     : 3681
% 8.51/3.19  #Fact    : 0
% 8.51/3.19  #Define  : 0
% 8.51/3.19  #Split   : 1
% 8.51/3.19  #Chain   : 0
% 8.51/3.19  #Close   : 0
% 8.51/3.19  
% 8.51/3.19  Ordering : KBO
% 8.51/3.19  
% 8.51/3.19  Simplification rules
% 8.51/3.19  ----------------------
% 8.51/3.19  #Subsume      : 49
% 8.51/3.19  #Demod        : 3584
% 8.51/3.19  #Tautology    : 2246
% 8.51/3.19  #SimpNegUnit  : 14
% 8.51/3.19  #BackRed      : 33
% 8.51/3.19  
% 8.51/3.19  #Partial instantiations: 0
% 8.51/3.19  #Strategies tried      : 1
% 8.51/3.19  
% 8.51/3.19  Timing (in seconds)
% 8.51/3.19  ----------------------
% 8.51/3.20  Preprocessing        : 0.35
% 8.51/3.20  Parsing              : 0.18
% 8.51/3.20  CNF conversion       : 0.02
% 8.51/3.20  Main loop            : 2.08
% 8.51/3.20  Inferencing          : 0.54
% 8.51/3.20  Reduction            : 1.03
% 8.51/3.20  Demodulation         : 0.87
% 8.51/3.20  BG Simplification    : 0.07
% 8.51/3.20  Subsumption          : 0.34
% 8.51/3.20  Abstraction          : 0.09
% 8.51/3.20  MUC search           : 0.00
% 8.51/3.20  Cooper               : 0.00
% 8.51/3.20  Total                : 2.46
% 8.51/3.20  Index Insertion      : 0.00
% 8.51/3.20  Index Deletion       : 0.00
% 8.51/3.20  Index Matching       : 0.00
% 8.51/3.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
