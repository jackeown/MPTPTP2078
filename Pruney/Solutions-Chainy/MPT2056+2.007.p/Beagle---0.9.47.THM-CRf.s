%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:26 EST 2020

% Result     : Theorem 5.98s
% Output     : CNFRefutation 6.13s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 284 expanded)
%              Number of leaves         :   49 ( 124 expanded)
%              Depth                    :   16
%              Number of atoms          :  204 ( 695 expanded)
%              Number of equality atoms :   39 ( 166 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_yellow19 > #nlpp > u1_struct_0 > k9_setfam_1 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_lattice3 > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_lattice3,type,(
    k3_lattice3: $i > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_yellow_1,type,(
    k3_yellow_1: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_waybel_0,type,(
    v2_waybel_0: ( $i * $i ) > $o )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k9_setfam_1,type,(
    k9_setfam_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_lattice3,type,(
    k1_lattice3: $i > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k2_yellow19,type,(
    k2_yellow19: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_yellow19,type,(
    k3_yellow19: ( $i * $i * $i ) > $i )).

tff(v13_waybel_0,type,(
    v13_waybel_0: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_161,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_struct_0(A) )
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & v1_subset_1(B,u1_struct_0(k3_yellow_1(k2_struct_0(A))))
              & v2_waybel_0(B,k3_yellow_1(k2_struct_0(A)))
              & v13_waybel_0(B,k3_yellow_1(k2_struct_0(A)))
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))))) )
           => B = k2_yellow19(A,k3_yellow19(A,k2_struct_0(A),B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_yellow19)).

tff(f_91,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_99,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_87,axiom,(
    ! [A] : k9_setfam_1(A) = k1_zfmisc_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

tff(f_103,axiom,(
    ! [A] : u1_struct_0(k3_yellow_1(A)) = k9_setfam_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_waybel_7)).

tff(f_63,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_61,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_71,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_120,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v2_waybel_0(B,k3_yellow_1(k2_struct_0(A)))
            & v13_waybel_0(B,k3_yellow_1(k2_struct_0(A)))
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))))) )
         => k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))),B,k1_tarski(k1_xboole_0)) = k2_yellow19(A,k3_yellow19(A,k2_struct_0(A),B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow19)).

tff(f_81,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_141,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_subset_1(B,u1_struct_0(k3_yellow_1(A)))
            & v2_waybel_0(B,k3_yellow_1(A))
            & v13_waybel_0(B,k3_yellow_1(A))
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A)))) )
         => ! [C] :
              ~ ( r2_hidden(C,B)
                & v1_xboole_0(C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_yellow19)).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_68,plain,(
    l1_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_186,plain,(
    ! [A_60] :
      ( u1_struct_0(A_60) = k2_struct_0(A_60)
      | ~ l1_struct_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_190,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_186])).

tff(c_195,plain,(
    ! [A_61] :
      ( ~ v1_xboole_0(u1_struct_0(A_61))
      | ~ l1_struct_0(A_61)
      | v2_struct_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_198,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_3'))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_195])).

tff(c_203,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_3'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_198])).

tff(c_204,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_203])).

tff(c_42,plain,(
    ! [A_31] : k9_setfam_1(A_31) = k1_zfmisc_1(A_31) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_50,plain,(
    ! [A_35] : u1_struct_0(k3_yellow_1(A_35)) = k9_setfam_1(A_35) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_64,plain,(
    v1_subset_1('#skF_4',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_71,plain,(
    v1_subset_1('#skF_4',k9_setfam_1(k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_64])).

tff(c_76,plain,(
    v1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_71])).

tff(c_62,plain,(
    v2_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_60,plain,(
    v13_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_58,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_72,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k9_setfam_1(k2_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_58])).

tff(c_77,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_72])).

tff(c_66,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_26,plain,(
    ! [A_18] : k4_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_120,plain,(
    ! [A_50,B_51] : r1_tarski(k4_xboole_0(A_50,B_51),A_50) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_123,plain,(
    ! [A_18] : r1_tarski(A_18,A_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_120])).

tff(c_211,plain,(
    ! [A_66,B_67] :
      ( k4_xboole_0(A_66,B_67) = k1_xboole_0
      | ~ r1_tarski(A_66,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_218,plain,(
    ! [A_18] : k4_xboole_0(A_18,A_18) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_123,c_211])).

tff(c_6,plain,(
    ! [A_3] :
      ( v1_xboole_0(A_3)
      | r2_hidden('#skF_1'(A_3),A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_34,plain,(
    ! [A_22,B_23] :
      ( r1_xboole_0(A_22,B_23)
      | k4_xboole_0(A_22,B_23) != A_22 ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_562,plain,(
    ! [A_100,B_101,C_102] :
      ( ~ r1_xboole_0(A_100,B_101)
      | ~ r2_hidden(C_102,B_101)
      | ~ r2_hidden(C_102,A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_3005,plain,(
    ! [C_180,B_181,A_182] :
      ( ~ r2_hidden(C_180,B_181)
      | ~ r2_hidden(C_180,A_182)
      | k4_xboole_0(A_182,B_181) != A_182 ) ),
    inference(resolution,[status(thm)],[c_34,c_562])).

tff(c_3895,plain,(
    ! [A_214,A_215] :
      ( ~ r2_hidden('#skF_1'(A_214),A_215)
      | k4_xboole_0(A_215,A_214) != A_215
      | v1_xboole_0(A_214) ) ),
    inference(resolution,[status(thm)],[c_6,c_3005])).

tff(c_3907,plain,(
    ! [A_3] :
      ( k4_xboole_0(A_3,A_3) != A_3
      | v1_xboole_0(A_3) ) ),
    inference(resolution,[status(thm)],[c_6,c_3895])).

tff(c_3911,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_3907])).

tff(c_624,plain,(
    ! [A_107,B_108,C_109] :
      ( k7_subset_1(A_107,B_108,C_109) = k4_xboole_0(B_108,C_109)
      | ~ m1_subset_1(B_108,k1_zfmisc_1(A_107)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_627,plain,(
    ! [C_109] : k7_subset_1(k1_zfmisc_1(k2_struct_0('#skF_3')),'#skF_4',C_109) = k4_xboole_0('#skF_4',C_109) ),
    inference(resolution,[status(thm)],[c_77,c_624])).

tff(c_52,plain,(
    ! [A_36,B_38] :
      ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_36))),B_38,k1_tarski(k1_xboole_0)) = k2_yellow19(A_36,k3_yellow19(A_36,k2_struct_0(A_36),B_38))
      | ~ m1_subset_1(B_38,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_36)))))
      | ~ v13_waybel_0(B_38,k3_yellow_1(k2_struct_0(A_36)))
      | ~ v2_waybel_0(B_38,k3_yellow_1(k2_struct_0(A_36)))
      | v1_xboole_0(B_38)
      | ~ l1_struct_0(A_36)
      | v2_struct_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_74,plain,(
    ! [A_36,B_38] :
      ( k7_subset_1(k9_setfam_1(k2_struct_0(A_36)),B_38,k1_tarski(k1_xboole_0)) = k2_yellow19(A_36,k3_yellow19(A_36,k2_struct_0(A_36),B_38))
      | ~ m1_subset_1(B_38,k1_zfmisc_1(k9_setfam_1(k2_struct_0(A_36))))
      | ~ v13_waybel_0(B_38,k3_yellow_1(k2_struct_0(A_36)))
      | ~ v2_waybel_0(B_38,k3_yellow_1(k2_struct_0(A_36)))
      | v1_xboole_0(B_38)
      | ~ l1_struct_0(A_36)
      | v2_struct_0(A_36) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_50,c_52])).

tff(c_994,plain,(
    ! [A_131,B_132] :
      ( k7_subset_1(k1_zfmisc_1(k2_struct_0(A_131)),B_132,k1_tarski(k1_xboole_0)) = k2_yellow19(A_131,k3_yellow19(A_131,k2_struct_0(A_131),B_132))
      | ~ m1_subset_1(B_132,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(A_131))))
      | ~ v13_waybel_0(B_132,k3_yellow_1(k2_struct_0(A_131)))
      | ~ v2_waybel_0(B_132,k3_yellow_1(k2_struct_0(A_131)))
      | v1_xboole_0(B_132)
      | ~ l1_struct_0(A_131)
      | v2_struct_0(A_131) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_42,c_74])).

tff(c_996,plain,
    ( k7_subset_1(k1_zfmisc_1(k2_struct_0('#skF_3')),'#skF_4',k1_tarski(k1_xboole_0)) = k2_yellow19('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
    | ~ v13_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ v2_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
    | v1_xboole_0('#skF_4')
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_77,c_994])).

tff(c_999,plain,
    ( k2_yellow19('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')) = k4_xboole_0('#skF_4',k1_tarski(k1_xboole_0))
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_62,c_60,c_627,c_996])).

tff(c_1000,plain,(
    k2_yellow19('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')) = k4_xboole_0('#skF_4',k1_tarski(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_66,c_999])).

tff(c_56,plain,(
    k2_yellow19('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')) != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_1077,plain,(
    k4_xboole_0('#skF_4',k1_tarski(k1_xboole_0)) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1000,c_56])).

tff(c_321,plain,(
    ! [A_80,B_81] :
      ( r2_hidden('#skF_2'(A_80,B_81),B_81)
      | r1_xboole_0(A_80,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_38,plain,(
    ! [A_26,B_27] :
      ( r1_xboole_0(k1_tarski(A_26),k1_tarski(B_27))
      | B_27 = A_26 ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_248,plain,(
    ! [A_69,B_70] :
      ( ~ r2_hidden(A_69,B_70)
      | ~ r1_xboole_0(k1_tarski(A_69),B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_252,plain,(
    ! [A_26,B_27] :
      ( ~ r2_hidden(A_26,k1_tarski(B_27))
      | B_27 = A_26 ) ),
    inference(resolution,[status(thm)],[c_38,c_248])).

tff(c_3015,plain,(
    ! [A_183,B_184] :
      ( '#skF_2'(A_183,k1_tarski(B_184)) = B_184
      | r1_xboole_0(A_183,k1_tarski(B_184)) ) ),
    inference(resolution,[status(thm)],[c_321,c_252])).

tff(c_32,plain,(
    ! [A_22,B_23] :
      ( k4_xboole_0(A_22,B_23) = A_22
      | ~ r1_xboole_0(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_5925,plain,(
    ! [A_277,B_278] :
      ( k4_xboole_0(A_277,k1_tarski(B_278)) = A_277
      | '#skF_2'(A_277,k1_tarski(B_278)) = B_278 ) ),
    inference(resolution,[status(thm)],[c_3015,c_32])).

tff(c_6065,plain,(
    '#skF_2'('#skF_4',k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_5925,c_1077])).

tff(c_16,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_2'(A_7,B_8),A_7)
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_6095,plain,
    ( r2_hidden(k1_xboole_0,'#skF_4')
    | r1_xboole_0('#skF_4',k1_tarski(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6065,c_16])).

tff(c_6109,plain,(
    r1_xboole_0('#skF_4',k1_tarski(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_6095])).

tff(c_6114,plain,(
    k4_xboole_0('#skF_4',k1_tarski(k1_xboole_0)) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_6109,c_32])).

tff(c_6119,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1077,c_6114])).

tff(c_6120,plain,(
    r2_hidden(k1_xboole_0,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_6095])).

tff(c_54,plain,(
    ! [C_45,B_43,A_39] :
      ( ~ v1_xboole_0(C_45)
      | ~ r2_hidden(C_45,B_43)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_39))))
      | ~ v13_waybel_0(B_43,k3_yellow_1(A_39))
      | ~ v2_waybel_0(B_43,k3_yellow_1(A_39))
      | ~ v1_subset_1(B_43,u1_struct_0(k3_yellow_1(A_39)))
      | v1_xboole_0(B_43)
      | v1_xboole_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_73,plain,(
    ! [C_45,B_43,A_39] :
      ( ~ v1_xboole_0(C_45)
      | ~ r2_hidden(C_45,B_43)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(k9_setfam_1(A_39)))
      | ~ v13_waybel_0(B_43,k3_yellow_1(A_39))
      | ~ v2_waybel_0(B_43,k3_yellow_1(A_39))
      | ~ v1_subset_1(B_43,k9_setfam_1(A_39))
      | v1_xboole_0(B_43)
      | v1_xboole_0(A_39) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_50,c_54])).

tff(c_78,plain,(
    ! [C_45,B_43,A_39] :
      ( ~ v1_xboole_0(C_45)
      | ~ r2_hidden(C_45,B_43)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(k1_zfmisc_1(A_39)))
      | ~ v13_waybel_0(B_43,k3_yellow_1(A_39))
      | ~ v2_waybel_0(B_43,k3_yellow_1(A_39))
      | ~ v1_subset_1(B_43,k1_zfmisc_1(A_39))
      | v1_xboole_0(B_43)
      | v1_xboole_0(A_39) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_42,c_73])).

tff(c_6199,plain,(
    ! [A_39] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(A_39)))
      | ~ v13_waybel_0('#skF_4',k3_yellow_1(A_39))
      | ~ v2_waybel_0('#skF_4',k3_yellow_1(A_39))
      | ~ v1_subset_1('#skF_4',k1_zfmisc_1(A_39))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_39) ) ),
    inference(resolution,[status(thm)],[c_6120,c_78])).

tff(c_6212,plain,(
    ! [A_39] :
      ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(A_39)))
      | ~ v13_waybel_0('#skF_4',k3_yellow_1(A_39))
      | ~ v2_waybel_0('#skF_4',k3_yellow_1(A_39))
      | ~ v1_subset_1('#skF_4',k1_zfmisc_1(A_39))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_39) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3911,c_6199])).

tff(c_6434,plain,(
    ! [A_282] :
      ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(A_282)))
      | ~ v13_waybel_0('#skF_4',k3_yellow_1(A_282))
      | ~ v2_waybel_0('#skF_4',k3_yellow_1(A_282))
      | ~ v1_subset_1('#skF_4',k1_zfmisc_1(A_282))
      | v1_xboole_0(A_282) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_6212])).

tff(c_6437,plain,
    ( ~ v13_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ v2_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ v1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_3')))
    | v1_xboole_0(k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_77,c_6434])).

tff(c_6440,plain,(
    v1_xboole_0(k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_62,c_60,c_6437])).

tff(c_6442,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_204,c_6440])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:00:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.98/2.12  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.98/2.13  
% 5.98/2.13  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.98/2.13  %$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_yellow19 > #nlpp > u1_struct_0 > k9_setfam_1 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_lattice3 > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 5.98/2.13  
% 5.98/2.13  %Foreground sorts:
% 5.98/2.13  
% 5.98/2.13  
% 5.98/2.13  %Background operators:
% 5.98/2.13  
% 5.98/2.13  
% 5.98/2.13  %Foreground operators:
% 5.98/2.13  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.98/2.13  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 5.98/2.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.98/2.13  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 5.98/2.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.98/2.13  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 5.98/2.13  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.98/2.13  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 5.98/2.13  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.98/2.13  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.98/2.13  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.98/2.13  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 5.98/2.13  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.98/2.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.98/2.13  tff(k9_setfam_1, type, k9_setfam_1: $i > $i).
% 5.98/2.13  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.98/2.13  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 5.98/2.13  tff('#skF_3', type, '#skF_3': $i).
% 5.98/2.13  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 5.98/2.13  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.98/2.13  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.98/2.13  tff(k2_yellow19, type, k2_yellow19: ($i * $i) > $i).
% 5.98/2.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.98/2.13  tff('#skF_4', type, '#skF_4': $i).
% 5.98/2.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.98/2.13  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.98/2.13  tff(k3_yellow19, type, k3_yellow19: ($i * $i * $i) > $i).
% 5.98/2.13  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 5.98/2.13  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.98/2.13  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.98/2.13  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 5.98/2.13  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.98/2.13  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.98/2.13  
% 6.13/2.15  tff(f_161, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (B = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_yellow19)).
% 6.13/2.15  tff(f_91, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 6.13/2.15  tff(f_99, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 6.13/2.15  tff(f_87, axiom, (![A]: (k9_setfam_1(A) = k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_setfam_1)).
% 6.13/2.15  tff(f_103, axiom, (![A]: (u1_struct_0(k3_yellow_1(A)) = k9_setfam_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_waybel_7)).
% 6.13/2.15  tff(f_63, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 6.13/2.15  tff(f_61, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 6.13/2.15  tff(f_57, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 6.13/2.15  tff(f_33, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 6.13/2.15  tff(f_71, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 6.13/2.15  tff(f_53, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 6.13/2.15  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 6.13/2.15  tff(f_120, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))), B, k1_tarski(k1_xboole_0)) = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_yellow19)).
% 6.13/2.15  tff(f_81, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 6.13/2.15  tff(f_76, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 6.13/2.15  tff(f_141, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(A)))) & v2_waybel_0(B, k3_yellow_1(A))) & v13_waybel_0(B, k3_yellow_1(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A))))) => (![C]: ~(r2_hidden(C, B) & v1_xboole_0(C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_yellow19)).
% 6.13/2.15  tff(c_70, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_161])).
% 6.13/2.15  tff(c_68, plain, (l1_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_161])).
% 6.13/2.15  tff(c_186, plain, (![A_60]: (u1_struct_0(A_60)=k2_struct_0(A_60) | ~l1_struct_0(A_60))), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.13/2.15  tff(c_190, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_68, c_186])).
% 6.13/2.15  tff(c_195, plain, (![A_61]: (~v1_xboole_0(u1_struct_0(A_61)) | ~l1_struct_0(A_61) | v2_struct_0(A_61))), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.13/2.15  tff(c_198, plain, (~v1_xboole_0(k2_struct_0('#skF_3')) | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_190, c_195])).
% 6.13/2.15  tff(c_203, plain, (~v1_xboole_0(k2_struct_0('#skF_3')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_198])).
% 6.13/2.15  tff(c_204, plain, (~v1_xboole_0(k2_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_70, c_203])).
% 6.13/2.15  tff(c_42, plain, (![A_31]: (k9_setfam_1(A_31)=k1_zfmisc_1(A_31))), inference(cnfTransformation, [status(thm)], [f_87])).
% 6.13/2.15  tff(c_50, plain, (![A_35]: (u1_struct_0(k3_yellow_1(A_35))=k9_setfam_1(A_35))), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.13/2.15  tff(c_64, plain, (v1_subset_1('#skF_4', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_161])).
% 6.13/2.15  tff(c_71, plain, (v1_subset_1('#skF_4', k9_setfam_1(k2_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_64])).
% 6.13/2.15  tff(c_76, plain, (v1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_71])).
% 6.13/2.15  tff(c_62, plain, (v2_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_161])).
% 6.13/2.15  tff(c_60, plain, (v13_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_161])).
% 6.13/2.15  tff(c_58, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))))), inference(cnfTransformation, [status(thm)], [f_161])).
% 6.13/2.15  tff(c_72, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k9_setfam_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_58])).
% 6.13/2.15  tff(c_77, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_72])).
% 6.13/2.15  tff(c_66, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_161])).
% 6.13/2.15  tff(c_26, plain, (![A_18]: (k4_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.13/2.15  tff(c_120, plain, (![A_50, B_51]: (r1_tarski(k4_xboole_0(A_50, B_51), A_50))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.13/2.15  tff(c_123, plain, (![A_18]: (r1_tarski(A_18, A_18))), inference(superposition, [status(thm), theory('equality')], [c_26, c_120])).
% 6.13/2.15  tff(c_211, plain, (![A_66, B_67]: (k4_xboole_0(A_66, B_67)=k1_xboole_0 | ~r1_tarski(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.13/2.15  tff(c_218, plain, (![A_18]: (k4_xboole_0(A_18, A_18)=k1_xboole_0)), inference(resolution, [status(thm)], [c_123, c_211])).
% 6.13/2.15  tff(c_6, plain, (![A_3]: (v1_xboole_0(A_3) | r2_hidden('#skF_1'(A_3), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.13/2.15  tff(c_34, plain, (![A_22, B_23]: (r1_xboole_0(A_22, B_23) | k4_xboole_0(A_22, B_23)!=A_22)), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.13/2.15  tff(c_562, plain, (![A_100, B_101, C_102]: (~r1_xboole_0(A_100, B_101) | ~r2_hidden(C_102, B_101) | ~r2_hidden(C_102, A_100))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.13/2.15  tff(c_3005, plain, (![C_180, B_181, A_182]: (~r2_hidden(C_180, B_181) | ~r2_hidden(C_180, A_182) | k4_xboole_0(A_182, B_181)!=A_182)), inference(resolution, [status(thm)], [c_34, c_562])).
% 6.13/2.15  tff(c_3895, plain, (![A_214, A_215]: (~r2_hidden('#skF_1'(A_214), A_215) | k4_xboole_0(A_215, A_214)!=A_215 | v1_xboole_0(A_214))), inference(resolution, [status(thm)], [c_6, c_3005])).
% 6.13/2.15  tff(c_3907, plain, (![A_3]: (k4_xboole_0(A_3, A_3)!=A_3 | v1_xboole_0(A_3))), inference(resolution, [status(thm)], [c_6, c_3895])).
% 6.13/2.15  tff(c_3911, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_218, c_3907])).
% 6.13/2.15  tff(c_624, plain, (![A_107, B_108, C_109]: (k7_subset_1(A_107, B_108, C_109)=k4_xboole_0(B_108, C_109) | ~m1_subset_1(B_108, k1_zfmisc_1(A_107)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.13/2.15  tff(c_627, plain, (![C_109]: (k7_subset_1(k1_zfmisc_1(k2_struct_0('#skF_3')), '#skF_4', C_109)=k4_xboole_0('#skF_4', C_109))), inference(resolution, [status(thm)], [c_77, c_624])).
% 6.13/2.15  tff(c_52, plain, (![A_36, B_38]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_36))), B_38, k1_tarski(k1_xboole_0))=k2_yellow19(A_36, k3_yellow19(A_36, k2_struct_0(A_36), B_38)) | ~m1_subset_1(B_38, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_36))))) | ~v13_waybel_0(B_38, k3_yellow_1(k2_struct_0(A_36))) | ~v2_waybel_0(B_38, k3_yellow_1(k2_struct_0(A_36))) | v1_xboole_0(B_38) | ~l1_struct_0(A_36) | v2_struct_0(A_36))), inference(cnfTransformation, [status(thm)], [f_120])).
% 6.13/2.15  tff(c_74, plain, (![A_36, B_38]: (k7_subset_1(k9_setfam_1(k2_struct_0(A_36)), B_38, k1_tarski(k1_xboole_0))=k2_yellow19(A_36, k3_yellow19(A_36, k2_struct_0(A_36), B_38)) | ~m1_subset_1(B_38, k1_zfmisc_1(k9_setfam_1(k2_struct_0(A_36)))) | ~v13_waybel_0(B_38, k3_yellow_1(k2_struct_0(A_36))) | ~v2_waybel_0(B_38, k3_yellow_1(k2_struct_0(A_36))) | v1_xboole_0(B_38) | ~l1_struct_0(A_36) | v2_struct_0(A_36))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_50, c_52])).
% 6.13/2.15  tff(c_994, plain, (![A_131, B_132]: (k7_subset_1(k1_zfmisc_1(k2_struct_0(A_131)), B_132, k1_tarski(k1_xboole_0))=k2_yellow19(A_131, k3_yellow19(A_131, k2_struct_0(A_131), B_132)) | ~m1_subset_1(B_132, k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(A_131)))) | ~v13_waybel_0(B_132, k3_yellow_1(k2_struct_0(A_131))) | ~v2_waybel_0(B_132, k3_yellow_1(k2_struct_0(A_131))) | v1_xboole_0(B_132) | ~l1_struct_0(A_131) | v2_struct_0(A_131))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_42, c_74])).
% 6.13/2.15  tff(c_996, plain, (k7_subset_1(k1_zfmisc_1(k2_struct_0('#skF_3')), '#skF_4', k1_tarski(k1_xboole_0))=k2_yellow19('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | ~v13_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | ~v2_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | v1_xboole_0('#skF_4') | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_77, c_994])).
% 6.13/2.15  tff(c_999, plain, (k2_yellow19('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))=k4_xboole_0('#skF_4', k1_tarski(k1_xboole_0)) | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_62, c_60, c_627, c_996])).
% 6.13/2.15  tff(c_1000, plain, (k2_yellow19('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))=k4_xboole_0('#skF_4', k1_tarski(k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_70, c_66, c_999])).
% 6.13/2.15  tff(c_56, plain, (k2_yellow19('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_161])).
% 6.13/2.15  tff(c_1077, plain, (k4_xboole_0('#skF_4', k1_tarski(k1_xboole_0))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1000, c_56])).
% 6.13/2.15  tff(c_321, plain, (![A_80, B_81]: (r2_hidden('#skF_2'(A_80, B_81), B_81) | r1_xboole_0(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.13/2.15  tff(c_38, plain, (![A_26, B_27]: (r1_xboole_0(k1_tarski(A_26), k1_tarski(B_27)) | B_27=A_26)), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.13/2.15  tff(c_248, plain, (![A_69, B_70]: (~r2_hidden(A_69, B_70) | ~r1_xboole_0(k1_tarski(A_69), B_70))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.13/2.15  tff(c_252, plain, (![A_26, B_27]: (~r2_hidden(A_26, k1_tarski(B_27)) | B_27=A_26)), inference(resolution, [status(thm)], [c_38, c_248])).
% 6.13/2.15  tff(c_3015, plain, (![A_183, B_184]: ('#skF_2'(A_183, k1_tarski(B_184))=B_184 | r1_xboole_0(A_183, k1_tarski(B_184)))), inference(resolution, [status(thm)], [c_321, c_252])).
% 6.13/2.15  tff(c_32, plain, (![A_22, B_23]: (k4_xboole_0(A_22, B_23)=A_22 | ~r1_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.13/2.15  tff(c_5925, plain, (![A_277, B_278]: (k4_xboole_0(A_277, k1_tarski(B_278))=A_277 | '#skF_2'(A_277, k1_tarski(B_278))=B_278)), inference(resolution, [status(thm)], [c_3015, c_32])).
% 6.13/2.15  tff(c_6065, plain, ('#skF_2'('#skF_4', k1_tarski(k1_xboole_0))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_5925, c_1077])).
% 6.13/2.15  tff(c_16, plain, (![A_7, B_8]: (r2_hidden('#skF_2'(A_7, B_8), A_7) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.13/2.15  tff(c_6095, plain, (r2_hidden(k1_xboole_0, '#skF_4') | r1_xboole_0('#skF_4', k1_tarski(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6065, c_16])).
% 6.13/2.15  tff(c_6109, plain, (r1_xboole_0('#skF_4', k1_tarski(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_6095])).
% 6.13/2.15  tff(c_6114, plain, (k4_xboole_0('#skF_4', k1_tarski(k1_xboole_0))='#skF_4'), inference(resolution, [status(thm)], [c_6109, c_32])).
% 6.13/2.15  tff(c_6119, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1077, c_6114])).
% 6.13/2.15  tff(c_6120, plain, (r2_hidden(k1_xboole_0, '#skF_4')), inference(splitRight, [status(thm)], [c_6095])).
% 6.13/2.15  tff(c_54, plain, (![C_45, B_43, A_39]: (~v1_xboole_0(C_45) | ~r2_hidden(C_45, B_43) | ~m1_subset_1(B_43, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_39)))) | ~v13_waybel_0(B_43, k3_yellow_1(A_39)) | ~v2_waybel_0(B_43, k3_yellow_1(A_39)) | ~v1_subset_1(B_43, u1_struct_0(k3_yellow_1(A_39))) | v1_xboole_0(B_43) | v1_xboole_0(A_39))), inference(cnfTransformation, [status(thm)], [f_141])).
% 6.13/2.15  tff(c_73, plain, (![C_45, B_43, A_39]: (~v1_xboole_0(C_45) | ~r2_hidden(C_45, B_43) | ~m1_subset_1(B_43, k1_zfmisc_1(k9_setfam_1(A_39))) | ~v13_waybel_0(B_43, k3_yellow_1(A_39)) | ~v2_waybel_0(B_43, k3_yellow_1(A_39)) | ~v1_subset_1(B_43, k9_setfam_1(A_39)) | v1_xboole_0(B_43) | v1_xboole_0(A_39))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_50, c_54])).
% 6.13/2.15  tff(c_78, plain, (![C_45, B_43, A_39]: (~v1_xboole_0(C_45) | ~r2_hidden(C_45, B_43) | ~m1_subset_1(B_43, k1_zfmisc_1(k1_zfmisc_1(A_39))) | ~v13_waybel_0(B_43, k3_yellow_1(A_39)) | ~v2_waybel_0(B_43, k3_yellow_1(A_39)) | ~v1_subset_1(B_43, k1_zfmisc_1(A_39)) | v1_xboole_0(B_43) | v1_xboole_0(A_39))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_42, c_73])).
% 6.13/2.15  tff(c_6199, plain, (![A_39]: (~v1_xboole_0(k1_xboole_0) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(A_39))) | ~v13_waybel_0('#skF_4', k3_yellow_1(A_39)) | ~v2_waybel_0('#skF_4', k3_yellow_1(A_39)) | ~v1_subset_1('#skF_4', k1_zfmisc_1(A_39)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_39))), inference(resolution, [status(thm)], [c_6120, c_78])).
% 6.13/2.15  tff(c_6212, plain, (![A_39]: (~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(A_39))) | ~v13_waybel_0('#skF_4', k3_yellow_1(A_39)) | ~v2_waybel_0('#skF_4', k3_yellow_1(A_39)) | ~v1_subset_1('#skF_4', k1_zfmisc_1(A_39)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_39))), inference(demodulation, [status(thm), theory('equality')], [c_3911, c_6199])).
% 6.13/2.15  tff(c_6434, plain, (![A_282]: (~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(A_282))) | ~v13_waybel_0('#skF_4', k3_yellow_1(A_282)) | ~v2_waybel_0('#skF_4', k3_yellow_1(A_282)) | ~v1_subset_1('#skF_4', k1_zfmisc_1(A_282)) | v1_xboole_0(A_282))), inference(negUnitSimplification, [status(thm)], [c_66, c_6212])).
% 6.13/2.15  tff(c_6437, plain, (~v13_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | ~v2_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | ~v1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_3'))) | v1_xboole_0(k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_77, c_6434])).
% 6.13/2.15  tff(c_6440, plain, (v1_xboole_0(k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_62, c_60, c_6437])).
% 6.13/2.15  tff(c_6442, plain, $false, inference(negUnitSimplification, [status(thm)], [c_204, c_6440])).
% 6.13/2.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.13/2.15  
% 6.13/2.15  Inference rules
% 6.13/2.15  ----------------------
% 6.13/2.15  #Ref     : 1
% 6.13/2.15  #Sup     : 1568
% 6.13/2.15  #Fact    : 0
% 6.13/2.15  #Define  : 0
% 6.13/2.15  #Split   : 3
% 6.13/2.15  #Chain   : 0
% 6.13/2.15  #Close   : 0
% 6.13/2.15  
% 6.13/2.15  Ordering : KBO
% 6.13/2.15  
% 6.13/2.15  Simplification rules
% 6.13/2.15  ----------------------
% 6.13/2.15  #Subsume      : 483
% 6.13/2.15  #Demod        : 1093
% 6.13/2.15  #Tautology    : 842
% 6.13/2.15  #SimpNegUnit  : 16
% 6.13/2.15  #BackRed      : 1
% 6.13/2.15  
% 6.13/2.15  #Partial instantiations: 0
% 6.13/2.15  #Strategies tried      : 1
% 6.13/2.15  
% 6.13/2.15  Timing (in seconds)
% 6.13/2.15  ----------------------
% 6.13/2.16  Preprocessing        : 0.35
% 6.13/2.16  Parsing              : 0.19
% 6.13/2.16  CNF conversion       : 0.02
% 6.13/2.16  Main loop            : 1.02
% 6.13/2.16  Inferencing          : 0.31
% 6.13/2.16  Reduction            : 0.45
% 6.13/2.16  Demodulation         : 0.35
% 6.13/2.16  BG Simplification    : 0.03
% 6.13/2.16  Subsumption          : 0.16
% 6.13/2.16  Abstraction          : 0.05
% 6.13/2.16  MUC search           : 0.00
% 6.13/2.16  Cooper               : 0.00
% 6.13/2.16  Total                : 1.41
% 6.13/2.16  Index Insertion      : 0.00
% 6.13/2.16  Index Deletion       : 0.00
% 6.13/2.16  Index Matching       : 0.00
% 6.13/2.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
