%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:49 EST 2020

% Result     : Theorem 7.79s
% Output     : CNFRefutation 8.03s
% Verified   : 
% Statistics : Number of formulae       :   74 (  96 expanded)
%              Number of leaves         :   33 (  45 expanded)
%              Depth                    :   11
%              Number of atoms          :   91 ( 126 expanded)
%              Number of equality atoms :   52 (  72 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > k7_subset_1 > k1_enumset1 > k7_setfam_1 > k6_setfam_1 > k5_setfam_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k7_setfam_1,type,(
    k7_setfam_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k6_setfam_1,type,(
    k6_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_37,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_39,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_84,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ( B != k1_xboole_0
         => k5_setfam_1(A,k7_setfam_1(A,B)) = k7_subset_1(A,k2_subset_1(A),k6_setfam_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_setfam_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ~ ( B != k1_xboole_0
          & k7_setfam_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_setfam_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k7_setfam_1(A,k7_setfam_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k7_setfam_1(A,B),k1_zfmisc_1(k1_zfmisc_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_setfam_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( B != k1_xboole_0
       => k7_subset_1(A,k2_subset_1(A),k5_setfam_1(A,B)) = k6_setfam_1(A,k7_setfam_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_setfam_1)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_57,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k5_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_setfam_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(c_10,plain,(
    ! [A_9] : k2_subset_1(A_9) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_12,plain,(
    ! [A_10] : m1_subset_1(k2_subset_1(A_10),k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_37,plain,(
    ! [A_10] : m1_subset_1(A_10,k1_zfmisc_1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12])).

tff(c_346,plain,(
    ! [A_60,B_61,C_62] :
      ( k7_subset_1(A_60,B_61,C_62) = k4_xboole_0(B_61,C_62)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(A_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_355,plain,(
    ! [A_10,C_62] : k7_subset_1(A_10,A_10,C_62) = k4_xboole_0(A_10,C_62) ),
    inference(resolution,[status(thm)],[c_37,c_346])).

tff(c_32,plain,(
    k7_subset_1('#skF_1',k2_subset_1('#skF_1'),k6_setfam_1('#skF_1','#skF_2')) != k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_39,plain,(
    k7_subset_1('#skF_1','#skF_1',k6_setfam_1('#skF_1','#skF_2')) != k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_32])).

tff(c_356,plain,(
    k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) != k4_xboole_0('#skF_1',k6_setfam_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_355,c_39])).

tff(c_34,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_36,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_305,plain,(
    ! [A_55,B_56] :
      ( k7_setfam_1(A_55,B_56) != k1_xboole_0
      | k1_xboole_0 = B_56
      | ~ m1_subset_1(B_56,k1_zfmisc_1(k1_zfmisc_1(A_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_312,plain,
    ( k7_setfam_1('#skF_1','#skF_2') != k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_305])).

tff(c_320,plain,(
    k7_setfam_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_312])).

tff(c_468,plain,(
    ! [A_74,B_75] :
      ( k7_setfam_1(A_74,k7_setfam_1(A_74,B_75)) = B_75
      | ~ m1_subset_1(B_75,k1_zfmisc_1(k1_zfmisc_1(A_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_482,plain,(
    k7_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_468])).

tff(c_18,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(k7_setfam_1(A_16,B_17),k1_zfmisc_1(k1_zfmisc_1(A_16)))
      | ~ m1_subset_1(B_17,k1_zfmisc_1(k1_zfmisc_1(A_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_30,plain,(
    ! [A_26,B_27] :
      ( k7_subset_1(A_26,k2_subset_1(A_26),k5_setfam_1(A_26,B_27)) = k6_setfam_1(A_26,k7_setfam_1(A_26,B_27))
      | k1_xboole_0 = B_27
      | ~ m1_subset_1(B_27,k1_zfmisc_1(k1_zfmisc_1(A_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_38,plain,(
    ! [A_26,B_27] :
      ( k7_subset_1(A_26,A_26,k5_setfam_1(A_26,B_27)) = k6_setfam_1(A_26,k7_setfam_1(A_26,B_27))
      | k1_xboole_0 = B_27
      | ~ m1_subset_1(B_27,k1_zfmisc_1(k1_zfmisc_1(A_26))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_30])).

tff(c_883,plain,(
    ! [A_98,B_99] :
      ( k6_setfam_1(A_98,k7_setfam_1(A_98,B_99)) = k4_xboole_0(A_98,k5_setfam_1(A_98,B_99))
      | k1_xboole_0 = B_99
      | ~ m1_subset_1(B_99,k1_zfmisc_1(k1_zfmisc_1(A_98))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_355,c_38])).

tff(c_6991,plain,(
    ! [A_270,B_271] :
      ( k6_setfam_1(A_270,k7_setfam_1(A_270,k7_setfam_1(A_270,B_271))) = k4_xboole_0(A_270,k5_setfam_1(A_270,k7_setfam_1(A_270,B_271)))
      | k7_setfam_1(A_270,B_271) = k1_xboole_0
      | ~ m1_subset_1(B_271,k1_zfmisc_1(k1_zfmisc_1(A_270))) ) ),
    inference(resolution,[status(thm)],[c_18,c_883])).

tff(c_7010,plain,
    ( k6_setfam_1('#skF_1',k7_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2'))) = k4_xboole_0('#skF_1',k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')))
    | k7_setfam_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_6991])).

tff(c_7022,plain,
    ( k4_xboole_0('#skF_1',k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2'))) = k6_setfam_1('#skF_1','#skF_2')
    | k7_setfam_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_482,c_7010])).

tff(c_7023,plain,(
    k4_xboole_0('#skF_1',k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2'))) = k6_setfam_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_320,c_7022])).

tff(c_4,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k4_xboole_0(A_3,B_4)) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_7041,plain,(
    k3_xboole_0('#skF_1',k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2'))) = k4_xboole_0('#skF_1',k6_setfam_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_7023,c_4])).

tff(c_6,plain,(
    ! [B_6,A_5] : k2_tarski(B_6,A_5) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_129,plain,(
    ! [A_42,B_43] : k1_setfam_1(k2_tarski(A_42,B_43)) = k3_xboole_0(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_144,plain,(
    ! [B_44,A_45] : k1_setfam_1(k2_tarski(B_44,A_45)) = k3_xboole_0(A_45,B_44) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_129])).

tff(c_22,plain,(
    ! [A_20,B_21] : k1_setfam_1(k2_tarski(A_20,B_21)) = k3_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_150,plain,(
    ! [B_44,A_45] : k3_xboole_0(B_44,A_45) = k3_xboole_0(A_45,B_44) ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_22])).

tff(c_584,plain,(
    ! [A_84,B_85] :
      ( m1_subset_1(k7_setfam_1(A_84,B_85),k1_zfmisc_1(k1_zfmisc_1(A_84)))
      | ~ m1_subset_1(B_85,k1_zfmisc_1(k1_zfmisc_1(A_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_384,plain,(
    ! [A_69,B_70] :
      ( m1_subset_1(k5_setfam_1(A_69,B_70),k1_zfmisc_1(A_69))
      | ~ m1_subset_1(B_70,k1_zfmisc_1(k1_zfmisc_1(A_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_24,plain,(
    ! [A_22,B_23] :
      ( r1_tarski(A_22,B_23)
      | ~ m1_subset_1(A_22,k1_zfmisc_1(B_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_396,plain,(
    ! [A_69,B_70] :
      ( r1_tarski(k5_setfam_1(A_69,B_70),A_69)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(k1_zfmisc_1(A_69))) ) ),
    inference(resolution,[status(thm)],[c_384,c_24])).

tff(c_698,plain,(
    ! [A_90,B_91] :
      ( r1_tarski(k5_setfam_1(A_90,k7_setfam_1(A_90,B_91)),A_90)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(k1_zfmisc_1(A_90))) ) ),
    inference(resolution,[status(thm)],[c_584,c_396])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_710,plain,(
    ! [A_90,B_91] :
      ( k3_xboole_0(k5_setfam_1(A_90,k7_setfam_1(A_90,B_91)),A_90) = k5_setfam_1(A_90,k7_setfam_1(A_90,B_91))
      | ~ m1_subset_1(B_91,k1_zfmisc_1(k1_zfmisc_1(A_90))) ) ),
    inference(resolution,[status(thm)],[c_698,c_2])).

tff(c_7158,plain,(
    ! [A_273,B_274] :
      ( k3_xboole_0(A_273,k5_setfam_1(A_273,k7_setfam_1(A_273,B_274))) = k5_setfam_1(A_273,k7_setfam_1(A_273,B_274))
      | ~ m1_subset_1(B_274,k1_zfmisc_1(k1_zfmisc_1(A_273))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_710])).

tff(c_7177,plain,(
    k3_xboole_0('#skF_1',k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2'))) = k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_36,c_7158])).

tff(c_7189,plain,(
    k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) = k4_xboole_0('#skF_1',k6_setfam_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7041,c_7177])).

tff(c_7191,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_356,c_7189])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:53:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.79/2.66  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.79/2.66  
% 7.79/2.66  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.79/2.66  %$ r1_tarski > m1_subset_1 > k7_subset_1 > k1_enumset1 > k7_setfam_1 > k6_setfam_1 > k5_setfam_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 7.79/2.66  
% 7.79/2.66  %Foreground sorts:
% 7.79/2.66  
% 7.79/2.66  
% 7.79/2.66  %Background operators:
% 7.79/2.66  
% 7.79/2.66  
% 7.79/2.66  %Foreground operators:
% 7.79/2.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.79/2.66  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.79/2.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.79/2.66  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 7.79/2.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.79/2.66  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.79/2.66  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.79/2.66  tff('#skF_2', type, '#skF_2': $i).
% 7.79/2.66  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 7.79/2.66  tff('#skF_1', type, '#skF_1': $i).
% 7.79/2.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.79/2.66  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 7.79/2.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.79/2.66  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 7.79/2.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.79/2.66  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.79/2.66  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 7.79/2.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.79/2.66  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 7.79/2.66  
% 8.03/2.68  tff(f_37, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 8.03/2.68  tff(f_39, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 8.03/2.68  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 8.03/2.68  tff(f_84, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (~(B = k1_xboole_0) => (k5_setfam_1(A, k7_setfam_1(A, B)) = k7_subset_1(A, k2_subset_1(A), k6_setfam_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_setfam_1)).
% 8.03/2.68  tff(f_69, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ~(~(B = k1_xboole_0) & (k7_setfam_1(A, B) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_setfam_1)).
% 8.03/2.68  tff(f_55, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k7_setfam_1(A, k7_setfam_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k7_setfam_1)).
% 8.03/2.68  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k7_setfam_1(A, B), k1_zfmisc_1(k1_zfmisc_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_setfam_1)).
% 8.03/2.68  tff(f_76, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (~(B = k1_xboole_0) => (k7_subset_1(A, k2_subset_1(A), k5_setfam_1(A, B)) = k6_setfam_1(A, k7_setfam_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_setfam_1)).
% 8.03/2.68  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 8.03/2.68  tff(f_33, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 8.03/2.68  tff(f_57, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 8.03/2.68  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k5_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_setfam_1)).
% 8.03/2.68  tff(f_61, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 8.03/2.68  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 8.03/2.68  tff(c_10, plain, (![A_9]: (k2_subset_1(A_9)=A_9)), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.03/2.68  tff(c_12, plain, (![A_10]: (m1_subset_1(k2_subset_1(A_10), k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.03/2.68  tff(c_37, plain, (![A_10]: (m1_subset_1(A_10, k1_zfmisc_1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_12])).
% 8.03/2.68  tff(c_346, plain, (![A_60, B_61, C_62]: (k7_subset_1(A_60, B_61, C_62)=k4_xboole_0(B_61, C_62) | ~m1_subset_1(B_61, k1_zfmisc_1(A_60)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.03/2.68  tff(c_355, plain, (![A_10, C_62]: (k7_subset_1(A_10, A_10, C_62)=k4_xboole_0(A_10, C_62))), inference(resolution, [status(thm)], [c_37, c_346])).
% 8.03/2.68  tff(c_32, plain, (k7_subset_1('#skF_1', k2_subset_1('#skF_1'), k6_setfam_1('#skF_1', '#skF_2'))!=k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 8.03/2.68  tff(c_39, plain, (k7_subset_1('#skF_1', '#skF_1', k6_setfam_1('#skF_1', '#skF_2'))!=k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_32])).
% 8.03/2.68  tff(c_356, plain, (k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))!=k4_xboole_0('#skF_1', k6_setfam_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_355, c_39])).
% 8.03/2.68  tff(c_34, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_84])).
% 8.03/2.68  tff(c_36, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_84])).
% 8.03/2.68  tff(c_305, plain, (![A_55, B_56]: (k7_setfam_1(A_55, B_56)!=k1_xboole_0 | k1_xboole_0=B_56 | ~m1_subset_1(B_56, k1_zfmisc_1(k1_zfmisc_1(A_55))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.03/2.68  tff(c_312, plain, (k7_setfam_1('#skF_1', '#skF_2')!=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_305])).
% 8.03/2.68  tff(c_320, plain, (k7_setfam_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_34, c_312])).
% 8.03/2.68  tff(c_468, plain, (![A_74, B_75]: (k7_setfam_1(A_74, k7_setfam_1(A_74, B_75))=B_75 | ~m1_subset_1(B_75, k1_zfmisc_1(k1_zfmisc_1(A_74))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.03/2.68  tff(c_482, plain, (k7_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_36, c_468])).
% 8.03/2.68  tff(c_18, plain, (![A_16, B_17]: (m1_subset_1(k7_setfam_1(A_16, B_17), k1_zfmisc_1(k1_zfmisc_1(A_16))) | ~m1_subset_1(B_17, k1_zfmisc_1(k1_zfmisc_1(A_16))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.03/2.68  tff(c_30, plain, (![A_26, B_27]: (k7_subset_1(A_26, k2_subset_1(A_26), k5_setfam_1(A_26, B_27))=k6_setfam_1(A_26, k7_setfam_1(A_26, B_27)) | k1_xboole_0=B_27 | ~m1_subset_1(B_27, k1_zfmisc_1(k1_zfmisc_1(A_26))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.03/2.68  tff(c_38, plain, (![A_26, B_27]: (k7_subset_1(A_26, A_26, k5_setfam_1(A_26, B_27))=k6_setfam_1(A_26, k7_setfam_1(A_26, B_27)) | k1_xboole_0=B_27 | ~m1_subset_1(B_27, k1_zfmisc_1(k1_zfmisc_1(A_26))))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_30])).
% 8.03/2.68  tff(c_883, plain, (![A_98, B_99]: (k6_setfam_1(A_98, k7_setfam_1(A_98, B_99))=k4_xboole_0(A_98, k5_setfam_1(A_98, B_99)) | k1_xboole_0=B_99 | ~m1_subset_1(B_99, k1_zfmisc_1(k1_zfmisc_1(A_98))))), inference(demodulation, [status(thm), theory('equality')], [c_355, c_38])).
% 8.03/2.68  tff(c_6991, plain, (![A_270, B_271]: (k6_setfam_1(A_270, k7_setfam_1(A_270, k7_setfam_1(A_270, B_271)))=k4_xboole_0(A_270, k5_setfam_1(A_270, k7_setfam_1(A_270, B_271))) | k7_setfam_1(A_270, B_271)=k1_xboole_0 | ~m1_subset_1(B_271, k1_zfmisc_1(k1_zfmisc_1(A_270))))), inference(resolution, [status(thm)], [c_18, c_883])).
% 8.03/2.68  tff(c_7010, plain, (k6_setfam_1('#skF_1', k7_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2')))=k4_xboole_0('#skF_1', k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))) | k7_setfam_1('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_6991])).
% 8.03/2.68  tff(c_7022, plain, (k4_xboole_0('#skF_1', k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2')))=k6_setfam_1('#skF_1', '#skF_2') | k7_setfam_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_482, c_7010])).
% 8.03/2.68  tff(c_7023, plain, (k4_xboole_0('#skF_1', k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2')))=k6_setfam_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_320, c_7022])).
% 8.03/2.68  tff(c_4, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k4_xboole_0(A_3, B_4))=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.03/2.68  tff(c_7041, plain, (k3_xboole_0('#skF_1', k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2')))=k4_xboole_0('#skF_1', k6_setfam_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_7023, c_4])).
% 8.03/2.68  tff(c_6, plain, (![B_6, A_5]: (k2_tarski(B_6, A_5)=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.03/2.68  tff(c_129, plain, (![A_42, B_43]: (k1_setfam_1(k2_tarski(A_42, B_43))=k3_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.03/2.68  tff(c_144, plain, (![B_44, A_45]: (k1_setfam_1(k2_tarski(B_44, A_45))=k3_xboole_0(A_45, B_44))), inference(superposition, [status(thm), theory('equality')], [c_6, c_129])).
% 8.03/2.68  tff(c_22, plain, (![A_20, B_21]: (k1_setfam_1(k2_tarski(A_20, B_21))=k3_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.03/2.68  tff(c_150, plain, (![B_44, A_45]: (k3_xboole_0(B_44, A_45)=k3_xboole_0(A_45, B_44))), inference(superposition, [status(thm), theory('equality')], [c_144, c_22])).
% 8.03/2.68  tff(c_584, plain, (![A_84, B_85]: (m1_subset_1(k7_setfam_1(A_84, B_85), k1_zfmisc_1(k1_zfmisc_1(A_84))) | ~m1_subset_1(B_85, k1_zfmisc_1(k1_zfmisc_1(A_84))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.03/2.68  tff(c_384, plain, (![A_69, B_70]: (m1_subset_1(k5_setfam_1(A_69, B_70), k1_zfmisc_1(A_69)) | ~m1_subset_1(B_70, k1_zfmisc_1(k1_zfmisc_1(A_69))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.03/2.68  tff(c_24, plain, (![A_22, B_23]: (r1_tarski(A_22, B_23) | ~m1_subset_1(A_22, k1_zfmisc_1(B_23)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.03/2.68  tff(c_396, plain, (![A_69, B_70]: (r1_tarski(k5_setfam_1(A_69, B_70), A_69) | ~m1_subset_1(B_70, k1_zfmisc_1(k1_zfmisc_1(A_69))))), inference(resolution, [status(thm)], [c_384, c_24])).
% 8.03/2.68  tff(c_698, plain, (![A_90, B_91]: (r1_tarski(k5_setfam_1(A_90, k7_setfam_1(A_90, B_91)), A_90) | ~m1_subset_1(B_91, k1_zfmisc_1(k1_zfmisc_1(A_90))))), inference(resolution, [status(thm)], [c_584, c_396])).
% 8.03/2.68  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.03/2.68  tff(c_710, plain, (![A_90, B_91]: (k3_xboole_0(k5_setfam_1(A_90, k7_setfam_1(A_90, B_91)), A_90)=k5_setfam_1(A_90, k7_setfam_1(A_90, B_91)) | ~m1_subset_1(B_91, k1_zfmisc_1(k1_zfmisc_1(A_90))))), inference(resolution, [status(thm)], [c_698, c_2])).
% 8.03/2.68  tff(c_7158, plain, (![A_273, B_274]: (k3_xboole_0(A_273, k5_setfam_1(A_273, k7_setfam_1(A_273, B_274)))=k5_setfam_1(A_273, k7_setfam_1(A_273, B_274)) | ~m1_subset_1(B_274, k1_zfmisc_1(k1_zfmisc_1(A_273))))), inference(demodulation, [status(thm), theory('equality')], [c_150, c_710])).
% 8.03/2.68  tff(c_7177, plain, (k3_xboole_0('#skF_1', k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2')))=k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_36, c_7158])).
% 8.03/2.68  tff(c_7189, plain, (k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))=k4_xboole_0('#skF_1', k6_setfam_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_7041, c_7177])).
% 8.03/2.68  tff(c_7191, plain, $false, inference(negUnitSimplification, [status(thm)], [c_356, c_7189])).
% 8.03/2.68  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.03/2.68  
% 8.03/2.68  Inference rules
% 8.03/2.68  ----------------------
% 8.03/2.68  #Ref     : 0
% 8.03/2.68  #Sup     : 1883
% 8.03/2.68  #Fact    : 0
% 8.03/2.68  #Define  : 0
% 8.03/2.68  #Split   : 1
% 8.03/2.68  #Chain   : 0
% 8.03/2.68  #Close   : 0
% 8.03/2.68  
% 8.03/2.68  Ordering : KBO
% 8.03/2.68  
% 8.03/2.68  Simplification rules
% 8.03/2.68  ----------------------
% 8.03/2.68  #Subsume      : 378
% 8.03/2.68  #Demod        : 1354
% 8.03/2.68  #Tautology    : 675
% 8.03/2.68  #SimpNegUnit  : 8
% 8.03/2.68  #BackRed      : 1
% 8.03/2.68  
% 8.03/2.68  #Partial instantiations: 0
% 8.03/2.68  #Strategies tried      : 1
% 8.03/2.68  
% 8.03/2.68  Timing (in seconds)
% 8.03/2.68  ----------------------
% 8.03/2.68  Preprocessing        : 0.30
% 8.03/2.68  Parsing              : 0.16
% 8.03/2.68  CNF conversion       : 0.02
% 8.03/2.68  Main loop            : 1.61
% 8.03/2.68  Inferencing          : 0.51
% 8.03/2.68  Reduction            : 0.67
% 8.03/2.68  Demodulation         : 0.53
% 8.03/2.68  BG Simplification    : 0.06
% 8.03/2.68  Subsumption          : 0.28
% 8.03/2.68  Abstraction          : 0.08
% 8.03/2.68  MUC search           : 0.00
% 8.03/2.68  Cooper               : 0.00
% 8.03/2.68  Total                : 1.94
% 8.03/2.68  Index Insertion      : 0.00
% 8.03/2.68  Index Deletion       : 0.00
% 8.03/2.68  Index Matching       : 0.00
% 8.03/2.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
