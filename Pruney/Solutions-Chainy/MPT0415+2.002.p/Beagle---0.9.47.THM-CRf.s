%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:45 EST 2020

% Result     : Theorem 10.57s
% Output     : CNFRefutation 10.57s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 167 expanded)
%              Number of leaves         :   32 (  71 expanded)
%              Depth                    :   12
%              Number of atoms          :  128 ( 291 expanded)
%              Number of equality atoms :   34 ( 107 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k7_setfam_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k7_setfam_1,type,(
    k7_setfam_1: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_106,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ~ ( B != k1_xboole_0
            & k7_setfam_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_setfam_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
         => ( C = k7_setfam_1(A,B)
          <=> ! [D] :
                ( m1_subset_1(D,k1_zfmisc_1(A))
               => ( r2_hidden(D,C)
                <=> r2_hidden(k3_subset_1(A,D),B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_setfam_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_67,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_61,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_57,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(c_50,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_52,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_48,plain,(
    k7_setfam_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_946,plain,(
    ! [A_101,B_102,C_103] :
      ( m1_subset_1('#skF_3'(A_101,B_102,C_103),k1_zfmisc_1(A_101))
      | k7_setfam_1(A_101,B_102) = C_103
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k1_zfmisc_1(A_101)))
      | ~ m1_subset_1(B_102,k1_zfmisc_1(k1_zfmisc_1(A_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_42,plain,(
    ! [A_37,B_38] :
      ( r1_tarski(A_37,B_38)
      | ~ m1_subset_1(A_37,k1_zfmisc_1(B_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_4958,plain,(
    ! [A_209,B_210,C_211] :
      ( r1_tarski('#skF_3'(A_209,B_210,C_211),A_209)
      | k7_setfam_1(A_209,B_210) = C_211
      | ~ m1_subset_1(C_211,k1_zfmisc_1(k1_zfmisc_1(A_209)))
      | ~ m1_subset_1(B_210,k1_zfmisc_1(k1_zfmisc_1(A_209))) ) ),
    inference(resolution,[status(thm)],[c_946,c_42])).

tff(c_5007,plain,(
    ! [B_212] :
      ( r1_tarski('#skF_3'('#skF_4',B_212,'#skF_5'),'#skF_4')
      | k7_setfam_1('#skF_4',B_212) = '#skF_5'
      | ~ m1_subset_1(B_212,k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_52,c_4958])).

tff(c_5053,plain,
    ( r1_tarski('#skF_3'('#skF_4','#skF_5','#skF_5'),'#skF_4')
    | k7_setfam_1('#skF_4','#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_52,c_5007])).

tff(c_5066,plain,
    ( r1_tarski('#skF_3'('#skF_4','#skF_5','#skF_5'),'#skF_4')
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_5053])).

tff(c_5067,plain,(
    r1_tarski('#skF_3'('#skF_4','#skF_5','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_5066])).

tff(c_12,plain,(
    ! [A_12,B_13] :
      ( k3_xboole_0(A_12,B_13) = A_12
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_5075,plain,(
    k3_xboole_0('#skF_3'('#skF_4','#skF_5','#skF_5'),'#skF_4') = '#skF_3'('#skF_4','#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_5067,c_12])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_341,plain,(
    ! [A_72,B_73] : k4_xboole_0(A_72,k4_xboole_0(A_72,B_73)) = k3_xboole_0(A_72,B_73) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_24,plain,(
    ! [A_22,B_23] : k6_subset_1(A_22,B_23) = k4_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_22,plain,(
    ! [A_20,B_21] : m1_subset_1(k6_subset_1(A_20,B_21),k1_zfmisc_1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_53,plain,(
    ! [A_20,B_21] : m1_subset_1(k4_xboole_0(A_20,B_21),k1_zfmisc_1(A_20)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22])).

tff(c_698,plain,(
    ! [A_89,B_90] : m1_subset_1(k3_xboole_0(A_89,B_90),k1_zfmisc_1(A_89)) ),
    inference(superposition,[status(thm),theory(equality)],[c_341,c_53])).

tff(c_721,plain,(
    ! [A_1,B_2] : m1_subset_1(k3_xboole_0(A_1,B_2),k1_zfmisc_1(B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_698])).

tff(c_7367,plain,(
    m1_subset_1('#skF_3'('#skF_4','#skF_5','#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5075,c_721])).

tff(c_18,plain,(
    ! [A_17] : r1_xboole_0(A_17,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_14,plain,(
    ! [A_14] : k3_xboole_0(A_14,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_285,plain,(
    ! [A_66,B_67,C_68] :
      ( ~ r1_xboole_0(A_66,B_67)
      | ~ r2_hidden(C_68,k3_xboole_0(A_66,B_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_304,plain,(
    ! [A_14,C_68] :
      ( ~ r1_xboole_0(A_14,k1_xboole_0)
      | ~ r2_hidden(C_68,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_285])).

tff(c_307,plain,(
    ! [C_68] : ~ r2_hidden(C_68,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_304])).

tff(c_724,plain,(
    ! [A_14] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_14)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_698])).

tff(c_1260,plain,(
    ! [A_118,B_119,C_120] :
      ( r2_hidden('#skF_3'(A_118,B_119,C_120),C_120)
      | r2_hidden(k3_subset_1(A_118,'#skF_3'(A_118,B_119,C_120)),B_119)
      | k7_setfam_1(A_118,B_119) = C_120
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k1_zfmisc_1(A_118)))
      | ~ m1_subset_1(B_119,k1_zfmisc_1(k1_zfmisc_1(A_118))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_36,plain,(
    ! [D_34,A_24,B_25] :
      ( r2_hidden(D_34,k7_setfam_1(A_24,B_25))
      | ~ r2_hidden(k3_subset_1(A_24,D_34),B_25)
      | ~ m1_subset_1(D_34,k1_zfmisc_1(A_24))
      | ~ m1_subset_1(k7_setfam_1(A_24,B_25),k1_zfmisc_1(k1_zfmisc_1(A_24)))
      | ~ m1_subset_1(B_25,k1_zfmisc_1(k1_zfmisc_1(A_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_8252,plain,(
    ! [A_267,B_268,C_269] :
      ( r2_hidden('#skF_3'(A_267,B_268,C_269),k7_setfam_1(A_267,B_268))
      | ~ m1_subset_1('#skF_3'(A_267,B_268,C_269),k1_zfmisc_1(A_267))
      | ~ m1_subset_1(k7_setfam_1(A_267,B_268),k1_zfmisc_1(k1_zfmisc_1(A_267)))
      | r2_hidden('#skF_3'(A_267,B_268,C_269),C_269)
      | k7_setfam_1(A_267,B_268) = C_269
      | ~ m1_subset_1(C_269,k1_zfmisc_1(k1_zfmisc_1(A_267)))
      | ~ m1_subset_1(B_268,k1_zfmisc_1(k1_zfmisc_1(A_267))) ) ),
    inference(resolution,[status(thm)],[c_1260,c_36])).

tff(c_8259,plain,(
    ! [C_269] :
      ( r2_hidden('#skF_3'('#skF_4','#skF_5',C_269),k7_setfam_1('#skF_4','#skF_5'))
      | ~ m1_subset_1('#skF_3'('#skF_4','#skF_5',C_269),k1_zfmisc_1('#skF_4'))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1('#skF_4')))
      | r2_hidden('#skF_3'('#skF_4','#skF_5',C_269),C_269)
      | k7_setfam_1('#skF_4','#skF_5') = C_269
      | ~ m1_subset_1(C_269,k1_zfmisc_1(k1_zfmisc_1('#skF_4')))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_8252])).

tff(c_8263,plain,(
    ! [C_269] :
      ( r2_hidden('#skF_3'('#skF_4','#skF_5',C_269),k1_xboole_0)
      | ~ m1_subset_1('#skF_3'('#skF_4','#skF_5',C_269),k1_zfmisc_1('#skF_4'))
      | r2_hidden('#skF_3'('#skF_4','#skF_5',C_269),C_269)
      | k1_xboole_0 = C_269
      | ~ m1_subset_1(C_269,k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_724,c_48,c_8259])).

tff(c_17014,plain,(
    ! [C_405] :
      ( ~ m1_subset_1('#skF_3'('#skF_4','#skF_5',C_405),k1_zfmisc_1('#skF_4'))
      | r2_hidden('#skF_3'('#skF_4','#skF_5',C_405),C_405)
      | k1_xboole_0 = C_405
      | ~ m1_subset_1(C_405,k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_307,c_8263])).

tff(c_17016,plain,
    ( r2_hidden('#skF_3'('#skF_4','#skF_5','#skF_5'),'#skF_5')
    | k1_xboole_0 = '#skF_5'
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_7367,c_17014])).

tff(c_17028,plain,
    ( r2_hidden('#skF_3'('#skF_4','#skF_5','#skF_5'),'#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_17016])).

tff(c_17029,plain,(
    r2_hidden('#skF_3'('#skF_4','#skF_5','#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_17028])).

tff(c_7398,plain,(
    k3_xboole_0('#skF_4','#skF_3'('#skF_4','#skF_5','#skF_5')) = '#skF_3'('#skF_4','#skF_5','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_5075])).

tff(c_16,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k4_xboole_0(A_15,B_16)) = k3_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_496,plain,(
    ! [A_75,B_76] :
      ( k4_xboole_0(A_75,B_76) = k3_subset_1(A_75,B_76)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(A_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_505,plain,(
    ! [A_20,B_21] : k4_xboole_0(A_20,k4_xboole_0(A_20,B_21)) = k3_subset_1(A_20,k4_xboole_0(A_20,B_21)) ),
    inference(resolution,[status(thm)],[c_53,c_496])).

tff(c_1457,plain,(
    ! [A_134,B_135] : k3_subset_1(A_134,k4_xboole_0(A_134,B_135)) = k3_xboole_0(A_134,B_135) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_505])).

tff(c_1462,plain,(
    ! [A_134,B_135,B_25] :
      ( r2_hidden(k4_xboole_0(A_134,B_135),k7_setfam_1(A_134,B_25))
      | ~ r2_hidden(k3_xboole_0(A_134,B_135),B_25)
      | ~ m1_subset_1(k4_xboole_0(A_134,B_135),k1_zfmisc_1(A_134))
      | ~ m1_subset_1(k7_setfam_1(A_134,B_25),k1_zfmisc_1(k1_zfmisc_1(A_134)))
      | ~ m1_subset_1(B_25,k1_zfmisc_1(k1_zfmisc_1(A_134))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1457,c_36])).

tff(c_18622,plain,(
    ! [A_435,B_436,B_437] :
      ( r2_hidden(k4_xboole_0(A_435,B_436),k7_setfam_1(A_435,B_437))
      | ~ r2_hidden(k3_xboole_0(A_435,B_436),B_437)
      | ~ m1_subset_1(k7_setfam_1(A_435,B_437),k1_zfmisc_1(k1_zfmisc_1(A_435)))
      | ~ m1_subset_1(B_437,k1_zfmisc_1(k1_zfmisc_1(A_435))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_1462])).

tff(c_18635,plain,(
    ! [B_436] :
      ( r2_hidden(k4_xboole_0('#skF_4',B_436),k7_setfam_1('#skF_4','#skF_5'))
      | ~ r2_hidden(k3_xboole_0('#skF_4',B_436),'#skF_5')
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1('#skF_4')))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_18622])).

tff(c_18646,plain,(
    ! [B_436] :
      ( r2_hidden(k4_xboole_0('#skF_4',B_436),k1_xboole_0)
      | ~ r2_hidden(k3_xboole_0('#skF_4',B_436),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_724,c_48,c_18635])).

tff(c_18648,plain,(
    ! [B_438] : ~ r2_hidden(k3_xboole_0('#skF_4',B_438),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_307,c_18646])).

tff(c_18650,plain,(
    ~ r2_hidden('#skF_3'('#skF_4','#skF_5','#skF_5'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_7398,c_18648])).

tff(c_18694,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_17029,c_18650])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:15:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.57/4.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.57/4.41  
% 10.57/4.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.57/4.42  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k7_setfam_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_4 > #skF_3 > #skF_1
% 10.57/4.42  
% 10.57/4.42  %Foreground sorts:
% 10.57/4.42  
% 10.57/4.42  
% 10.57/4.42  %Background operators:
% 10.57/4.42  
% 10.57/4.42  
% 10.57/4.42  %Foreground operators:
% 10.57/4.42  tff('#skF_2', type, '#skF_2': $i > $i).
% 10.57/4.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.57/4.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.57/4.42  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.57/4.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.57/4.42  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 10.57/4.42  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 10.57/4.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.57/4.42  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 10.57/4.42  tff('#skF_5', type, '#skF_5': $i).
% 10.57/4.42  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 10.57/4.42  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 10.57/4.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.57/4.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.57/4.42  tff('#skF_4', type, '#skF_4': $i).
% 10.57/4.42  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 10.57/4.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.57/4.42  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.57/4.42  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 10.57/4.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.57/4.42  
% 10.57/4.43  tff(f_106, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ~(~(B = k1_xboole_0) & (k7_setfam_1(A, B) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_setfam_1)).
% 10.57/4.43  tff(f_83, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => ((C = k7_setfam_1(A, B)) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (r2_hidden(D, C) <=> r2_hidden(k3_subset_1(A, D), B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_setfam_1)).
% 10.57/4.43  tff(f_91, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 10.57/4.43  tff(f_55, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 10.57/4.43  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 10.57/4.43  tff(f_59, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 10.57/4.43  tff(f_69, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 10.57/4.43  tff(f_67, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 10.57/4.43  tff(f_61, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 10.57/4.43  tff(f_57, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 10.57/4.43  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 10.57/4.43  tff(f_65, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 10.57/4.43  tff(c_50, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_106])).
% 10.57/4.43  tff(c_52, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_106])).
% 10.57/4.43  tff(c_48, plain, (k7_setfam_1('#skF_4', '#skF_5')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_106])).
% 10.57/4.43  tff(c_946, plain, (![A_101, B_102, C_103]: (m1_subset_1('#skF_3'(A_101, B_102, C_103), k1_zfmisc_1(A_101)) | k7_setfam_1(A_101, B_102)=C_103 | ~m1_subset_1(C_103, k1_zfmisc_1(k1_zfmisc_1(A_101))) | ~m1_subset_1(B_102, k1_zfmisc_1(k1_zfmisc_1(A_101))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 10.57/4.43  tff(c_42, plain, (![A_37, B_38]: (r1_tarski(A_37, B_38) | ~m1_subset_1(A_37, k1_zfmisc_1(B_38)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.57/4.43  tff(c_4958, plain, (![A_209, B_210, C_211]: (r1_tarski('#skF_3'(A_209, B_210, C_211), A_209) | k7_setfam_1(A_209, B_210)=C_211 | ~m1_subset_1(C_211, k1_zfmisc_1(k1_zfmisc_1(A_209))) | ~m1_subset_1(B_210, k1_zfmisc_1(k1_zfmisc_1(A_209))))), inference(resolution, [status(thm)], [c_946, c_42])).
% 10.57/4.43  tff(c_5007, plain, (![B_212]: (r1_tarski('#skF_3'('#skF_4', B_212, '#skF_5'), '#skF_4') | k7_setfam_1('#skF_4', B_212)='#skF_5' | ~m1_subset_1(B_212, k1_zfmisc_1(k1_zfmisc_1('#skF_4'))))), inference(resolution, [status(thm)], [c_52, c_4958])).
% 10.57/4.43  tff(c_5053, plain, (r1_tarski('#skF_3'('#skF_4', '#skF_5', '#skF_5'), '#skF_4') | k7_setfam_1('#skF_4', '#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_52, c_5007])).
% 10.57/4.43  tff(c_5066, plain, (r1_tarski('#skF_3'('#skF_4', '#skF_5', '#skF_5'), '#skF_4') | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_5053])).
% 10.57/4.43  tff(c_5067, plain, (r1_tarski('#skF_3'('#skF_4', '#skF_5', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_50, c_5066])).
% 10.57/4.43  tff(c_12, plain, (![A_12, B_13]: (k3_xboole_0(A_12, B_13)=A_12 | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_55])).
% 10.57/4.43  tff(c_5075, plain, (k3_xboole_0('#skF_3'('#skF_4', '#skF_5', '#skF_5'), '#skF_4')='#skF_3'('#skF_4', '#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_5067, c_12])).
% 10.57/4.43  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.57/4.43  tff(c_341, plain, (![A_72, B_73]: (k4_xboole_0(A_72, k4_xboole_0(A_72, B_73))=k3_xboole_0(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_59])).
% 10.57/4.43  tff(c_24, plain, (![A_22, B_23]: (k6_subset_1(A_22, B_23)=k4_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_69])).
% 10.57/4.43  tff(c_22, plain, (![A_20, B_21]: (m1_subset_1(k6_subset_1(A_20, B_21), k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 10.57/4.43  tff(c_53, plain, (![A_20, B_21]: (m1_subset_1(k4_xboole_0(A_20, B_21), k1_zfmisc_1(A_20)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22])).
% 10.57/4.43  tff(c_698, plain, (![A_89, B_90]: (m1_subset_1(k3_xboole_0(A_89, B_90), k1_zfmisc_1(A_89)))), inference(superposition, [status(thm), theory('equality')], [c_341, c_53])).
% 10.57/4.43  tff(c_721, plain, (![A_1, B_2]: (m1_subset_1(k3_xboole_0(A_1, B_2), k1_zfmisc_1(B_2)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_698])).
% 10.57/4.43  tff(c_7367, plain, (m1_subset_1('#skF_3'('#skF_4', '#skF_5', '#skF_5'), k1_zfmisc_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_5075, c_721])).
% 10.57/4.43  tff(c_18, plain, (![A_17]: (r1_xboole_0(A_17, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.57/4.43  tff(c_14, plain, (![A_14]: (k3_xboole_0(A_14, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_57])).
% 10.57/4.43  tff(c_285, plain, (![A_66, B_67, C_68]: (~r1_xboole_0(A_66, B_67) | ~r2_hidden(C_68, k3_xboole_0(A_66, B_67)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.57/4.43  tff(c_304, plain, (![A_14, C_68]: (~r1_xboole_0(A_14, k1_xboole_0) | ~r2_hidden(C_68, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_285])).
% 10.57/4.43  tff(c_307, plain, (![C_68]: (~r2_hidden(C_68, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_304])).
% 10.57/4.43  tff(c_724, plain, (![A_14]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_14)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_698])).
% 10.57/4.43  tff(c_1260, plain, (![A_118, B_119, C_120]: (r2_hidden('#skF_3'(A_118, B_119, C_120), C_120) | r2_hidden(k3_subset_1(A_118, '#skF_3'(A_118, B_119, C_120)), B_119) | k7_setfam_1(A_118, B_119)=C_120 | ~m1_subset_1(C_120, k1_zfmisc_1(k1_zfmisc_1(A_118))) | ~m1_subset_1(B_119, k1_zfmisc_1(k1_zfmisc_1(A_118))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 10.57/4.43  tff(c_36, plain, (![D_34, A_24, B_25]: (r2_hidden(D_34, k7_setfam_1(A_24, B_25)) | ~r2_hidden(k3_subset_1(A_24, D_34), B_25) | ~m1_subset_1(D_34, k1_zfmisc_1(A_24)) | ~m1_subset_1(k7_setfam_1(A_24, B_25), k1_zfmisc_1(k1_zfmisc_1(A_24))) | ~m1_subset_1(B_25, k1_zfmisc_1(k1_zfmisc_1(A_24))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 10.57/4.43  tff(c_8252, plain, (![A_267, B_268, C_269]: (r2_hidden('#skF_3'(A_267, B_268, C_269), k7_setfam_1(A_267, B_268)) | ~m1_subset_1('#skF_3'(A_267, B_268, C_269), k1_zfmisc_1(A_267)) | ~m1_subset_1(k7_setfam_1(A_267, B_268), k1_zfmisc_1(k1_zfmisc_1(A_267))) | r2_hidden('#skF_3'(A_267, B_268, C_269), C_269) | k7_setfam_1(A_267, B_268)=C_269 | ~m1_subset_1(C_269, k1_zfmisc_1(k1_zfmisc_1(A_267))) | ~m1_subset_1(B_268, k1_zfmisc_1(k1_zfmisc_1(A_267))))), inference(resolution, [status(thm)], [c_1260, c_36])).
% 10.57/4.43  tff(c_8259, plain, (![C_269]: (r2_hidden('#skF_3'('#skF_4', '#skF_5', C_269), k7_setfam_1('#skF_4', '#skF_5')) | ~m1_subset_1('#skF_3'('#skF_4', '#skF_5', C_269), k1_zfmisc_1('#skF_4')) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) | r2_hidden('#skF_3'('#skF_4', '#skF_5', C_269), C_269) | k7_setfam_1('#skF_4', '#skF_5')=C_269 | ~m1_subset_1(C_269, k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1('#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_48, c_8252])).
% 10.57/4.43  tff(c_8263, plain, (![C_269]: (r2_hidden('#skF_3'('#skF_4', '#skF_5', C_269), k1_xboole_0) | ~m1_subset_1('#skF_3'('#skF_4', '#skF_5', C_269), k1_zfmisc_1('#skF_4')) | r2_hidden('#skF_3'('#skF_4', '#skF_5', C_269), C_269) | k1_xboole_0=C_269 | ~m1_subset_1(C_269, k1_zfmisc_1(k1_zfmisc_1('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_724, c_48, c_8259])).
% 10.57/4.43  tff(c_17014, plain, (![C_405]: (~m1_subset_1('#skF_3'('#skF_4', '#skF_5', C_405), k1_zfmisc_1('#skF_4')) | r2_hidden('#skF_3'('#skF_4', '#skF_5', C_405), C_405) | k1_xboole_0=C_405 | ~m1_subset_1(C_405, k1_zfmisc_1(k1_zfmisc_1('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_307, c_8263])).
% 10.57/4.43  tff(c_17016, plain, (r2_hidden('#skF_3'('#skF_4', '#skF_5', '#skF_5'), '#skF_5') | k1_xboole_0='#skF_5' | ~m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1('#skF_4')))), inference(resolution, [status(thm)], [c_7367, c_17014])).
% 10.57/4.43  tff(c_17028, plain, (r2_hidden('#skF_3'('#skF_4', '#skF_5', '#skF_5'), '#skF_5') | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_17016])).
% 10.57/4.43  tff(c_17029, plain, (r2_hidden('#skF_3'('#skF_4', '#skF_5', '#skF_5'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_50, c_17028])).
% 10.57/4.43  tff(c_7398, plain, (k3_xboole_0('#skF_4', '#skF_3'('#skF_4', '#skF_5', '#skF_5'))='#skF_3'('#skF_4', '#skF_5', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2, c_5075])).
% 10.57/4.43  tff(c_16, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k4_xboole_0(A_15, B_16))=k3_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_59])).
% 10.57/4.43  tff(c_496, plain, (![A_75, B_76]: (k4_xboole_0(A_75, B_76)=k3_subset_1(A_75, B_76) | ~m1_subset_1(B_76, k1_zfmisc_1(A_75)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 10.57/4.43  tff(c_505, plain, (![A_20, B_21]: (k4_xboole_0(A_20, k4_xboole_0(A_20, B_21))=k3_subset_1(A_20, k4_xboole_0(A_20, B_21)))), inference(resolution, [status(thm)], [c_53, c_496])).
% 10.57/4.43  tff(c_1457, plain, (![A_134, B_135]: (k3_subset_1(A_134, k4_xboole_0(A_134, B_135))=k3_xboole_0(A_134, B_135))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_505])).
% 10.57/4.43  tff(c_1462, plain, (![A_134, B_135, B_25]: (r2_hidden(k4_xboole_0(A_134, B_135), k7_setfam_1(A_134, B_25)) | ~r2_hidden(k3_xboole_0(A_134, B_135), B_25) | ~m1_subset_1(k4_xboole_0(A_134, B_135), k1_zfmisc_1(A_134)) | ~m1_subset_1(k7_setfam_1(A_134, B_25), k1_zfmisc_1(k1_zfmisc_1(A_134))) | ~m1_subset_1(B_25, k1_zfmisc_1(k1_zfmisc_1(A_134))))), inference(superposition, [status(thm), theory('equality')], [c_1457, c_36])).
% 10.57/4.43  tff(c_18622, plain, (![A_435, B_436, B_437]: (r2_hidden(k4_xboole_0(A_435, B_436), k7_setfam_1(A_435, B_437)) | ~r2_hidden(k3_xboole_0(A_435, B_436), B_437) | ~m1_subset_1(k7_setfam_1(A_435, B_437), k1_zfmisc_1(k1_zfmisc_1(A_435))) | ~m1_subset_1(B_437, k1_zfmisc_1(k1_zfmisc_1(A_435))))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_1462])).
% 10.57/4.43  tff(c_18635, plain, (![B_436]: (r2_hidden(k4_xboole_0('#skF_4', B_436), k7_setfam_1('#skF_4', '#skF_5')) | ~r2_hidden(k3_xboole_0('#skF_4', B_436), '#skF_5') | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1('#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_48, c_18622])).
% 10.57/4.43  tff(c_18646, plain, (![B_436]: (r2_hidden(k4_xboole_0('#skF_4', B_436), k1_xboole_0) | ~r2_hidden(k3_xboole_0('#skF_4', B_436), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_724, c_48, c_18635])).
% 10.57/4.43  tff(c_18648, plain, (![B_438]: (~r2_hidden(k3_xboole_0('#skF_4', B_438), '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_307, c_18646])).
% 10.57/4.43  tff(c_18650, plain, (~r2_hidden('#skF_3'('#skF_4', '#skF_5', '#skF_5'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_7398, c_18648])).
% 10.57/4.43  tff(c_18694, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_17029, c_18650])).
% 10.57/4.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.57/4.43  
% 10.57/4.43  Inference rules
% 10.57/4.43  ----------------------
% 10.57/4.43  #Ref     : 0
% 10.57/4.43  #Sup     : 4739
% 10.57/4.43  #Fact    : 0
% 10.57/4.43  #Define  : 0
% 10.57/4.43  #Split   : 15
% 10.57/4.43  #Chain   : 0
% 10.57/4.43  #Close   : 0
% 10.57/4.43  
% 10.57/4.43  Ordering : KBO
% 10.57/4.43  
% 10.57/4.43  Simplification rules
% 10.57/4.43  ----------------------
% 10.57/4.43  #Subsume      : 591
% 10.57/4.43  #Demod        : 4465
% 10.57/4.43  #Tautology    : 1922
% 10.57/4.43  #SimpNegUnit  : 116
% 10.57/4.43  #BackRed      : 66
% 10.57/4.43  
% 10.57/4.43  #Partial instantiations: 0
% 10.57/4.43  #Strategies tried      : 1
% 10.57/4.43  
% 10.57/4.43  Timing (in seconds)
% 10.57/4.43  ----------------------
% 10.57/4.43  Preprocessing        : 0.33
% 10.57/4.43  Parsing              : 0.17
% 10.57/4.43  CNF conversion       : 0.03
% 10.57/4.43  Main loop            : 3.27
% 10.57/4.43  Inferencing          : 0.67
% 10.57/4.43  Reduction            : 1.67
% 10.57/4.43  Demodulation         : 1.41
% 10.57/4.43  BG Simplification    : 0.08
% 10.57/4.43  Subsumption          : 0.64
% 10.57/4.43  Abstraction          : 0.12
% 10.57/4.43  MUC search           : 0.00
% 10.57/4.43  Cooper               : 0.00
% 10.57/4.43  Total                : 3.63
% 10.57/4.43  Index Insertion      : 0.00
% 10.57/4.44  Index Deletion       : 0.00
% 10.57/4.44  Index Matching       : 0.00
% 10.57/4.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
