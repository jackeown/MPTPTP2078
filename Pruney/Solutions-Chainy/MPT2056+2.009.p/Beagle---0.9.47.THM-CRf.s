%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:26 EST 2020

% Result     : Theorem 2.99s
% Output     : CNFRefutation 2.99s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 161 expanded)
%              Number of leaves         :   51 (  80 expanded)
%              Depth                    :   14
%              Number of atoms          :  182 ( 342 expanded)
%              Number of equality atoms :   40 (  83 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k3_mcart_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_yellow19 > k2_xboole_0 > #nlpp > u1_struct_0 > k9_setfam_1 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_lattice3 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

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

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k9_setfam_1,type,(
    k9_setfam_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_157,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_yellow19)).

tff(f_87,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_95,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_83,axiom,(
    ! [A] : k9_setfam_1(A) = k1_zfmisc_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

tff(f_99,axiom,(
    ! [A] : u1_struct_0(k3_yellow_1(A)) = k9_setfam_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_waybel_7)).

tff(f_34,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_52,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_54,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_56,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_81,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_116,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v2_waybel_0(B,k3_yellow_1(k2_struct_0(A)))
            & v13_waybel_0(B,k3_yellow_1(k2_struct_0(A)))
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))))) )
         => k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))),B,k1_tarski(k1_xboole_0)) = k2_yellow19(A,k3_yellow19(A,k2_struct_0(A),B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_yellow19)).

tff(f_137,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_yellow19)).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_58,plain,(
    l1_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_158,plain,(
    ! [A_64] :
      ( u1_struct_0(A_64) = k2_struct_0(A_64)
      | ~ l1_struct_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_162,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_158])).

tff(c_172,plain,(
    ! [A_66] :
      ( ~ v1_xboole_0(u1_struct_0(A_66))
      | ~ l1_struct_0(A_66)
      | v2_struct_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_175,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_172])).

tff(c_180,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_175])).

tff(c_181,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_180])).

tff(c_32,plain,(
    ! [A_37] : k9_setfam_1(A_37) = k1_zfmisc_1(A_37) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_40,plain,(
    ! [A_41] : u1_struct_0(k3_yellow_1(A_41)) = k9_setfam_1(A_41) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_54,plain,(
    v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_61,plain,(
    v1_subset_1('#skF_5',k9_setfam_1(k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_54])).

tff(c_66,plain,(
    v1_subset_1('#skF_5',k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_61])).

tff(c_52,plain,(
    v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_50,plain,(
    v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_48,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))))) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_62,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k9_setfam_1(k2_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_48])).

tff(c_67,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_62])).

tff(c_56,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_16,plain,(
    ! [A_14] : k2_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_18,plain,(
    ! [A_15] : k4_xboole_0(k1_xboole_0,A_15) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_200,plain,(
    ! [A_72,B_73] : k5_xboole_0(A_72,k4_xboole_0(B_73,A_72)) = k2_xboole_0(A_72,B_73) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_209,plain,(
    ! [A_15] : k5_xboole_0(A_15,k1_xboole_0) = k2_xboole_0(A_15,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_200])).

tff(c_212,plain,(
    ! [A_15] : k5_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_209])).

tff(c_22,plain,(
    ! [A_18,B_19] :
      ( r1_xboole_0(k1_tarski(A_18),B_19)
      | r2_hidden(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_26,plain,(
    ! [A_23] :
      ( r2_hidden('#skF_3'(A_23),A_23)
      | k1_xboole_0 = A_23 ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_183,plain,(
    ! [A_69,B_70,C_71] :
      ( ~ r1_xboole_0(A_69,B_70)
      | ~ r2_hidden(C_71,k3_xboole_0(A_69,B_70)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_233,plain,(
    ! [A_77,B_78] :
      ( ~ r1_xboole_0(A_77,B_78)
      | k3_xboole_0(A_77,B_78) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_26,c_183])).

tff(c_399,plain,(
    ! [A_108,B_109] :
      ( k3_xboole_0(k1_tarski(A_108),B_109) = k1_xboole_0
      | r2_hidden(A_108,B_109) ) ),
    inference(resolution,[status(thm)],[c_22,c_233])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_238,plain,(
    ! [A_79,B_80] : k5_xboole_0(A_79,k3_xboole_0(A_79,B_80)) = k4_xboole_0(A_79,B_80) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_247,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_238])).

tff(c_405,plain,(
    ! [B_109,A_108] :
      ( k4_xboole_0(B_109,k1_tarski(A_108)) = k5_xboole_0(B_109,k1_xboole_0)
      | r2_hidden(A_108,B_109) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_399,c_247])).

tff(c_448,plain,(
    ! [B_109,A_108] :
      ( k4_xboole_0(B_109,k1_tarski(A_108)) = B_109
      | r2_hidden(A_108,B_109) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_405])).

tff(c_547,plain,(
    ! [A_114,B_115,C_116] :
      ( k7_subset_1(A_114,B_115,C_116) = k4_xboole_0(B_115,C_116)
      | ~ m1_subset_1(B_115,k1_zfmisc_1(A_114)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_550,plain,(
    ! [C_116] : k7_subset_1(k1_zfmisc_1(k2_struct_0('#skF_4')),'#skF_5',C_116) = k4_xboole_0('#skF_5',C_116) ),
    inference(resolution,[status(thm)],[c_67,c_547])).

tff(c_42,plain,(
    ! [A_42,B_44] :
      ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_42))),B_44,k1_tarski(k1_xboole_0)) = k2_yellow19(A_42,k3_yellow19(A_42,k2_struct_0(A_42),B_44))
      | ~ m1_subset_1(B_44,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_42)))))
      | ~ v13_waybel_0(B_44,k3_yellow_1(k2_struct_0(A_42)))
      | ~ v2_waybel_0(B_44,k3_yellow_1(k2_struct_0(A_42)))
      | v1_xboole_0(B_44)
      | ~ l1_struct_0(A_42)
      | v2_struct_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_64,plain,(
    ! [A_42,B_44] :
      ( k7_subset_1(k9_setfam_1(k2_struct_0(A_42)),B_44,k1_tarski(k1_xboole_0)) = k2_yellow19(A_42,k3_yellow19(A_42,k2_struct_0(A_42),B_44))
      | ~ m1_subset_1(B_44,k1_zfmisc_1(k9_setfam_1(k2_struct_0(A_42))))
      | ~ v13_waybel_0(B_44,k3_yellow_1(k2_struct_0(A_42)))
      | ~ v2_waybel_0(B_44,k3_yellow_1(k2_struct_0(A_42)))
      | v1_xboole_0(B_44)
      | ~ l1_struct_0(A_42)
      | v2_struct_0(A_42) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_40,c_42])).

tff(c_629,plain,(
    ! [A_132,B_133] :
      ( k7_subset_1(k1_zfmisc_1(k2_struct_0(A_132)),B_133,k1_tarski(k1_xboole_0)) = k2_yellow19(A_132,k3_yellow19(A_132,k2_struct_0(A_132),B_133))
      | ~ m1_subset_1(B_133,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(A_132))))
      | ~ v13_waybel_0(B_133,k3_yellow_1(k2_struct_0(A_132)))
      | ~ v2_waybel_0(B_133,k3_yellow_1(k2_struct_0(A_132)))
      | v1_xboole_0(B_133)
      | ~ l1_struct_0(A_132)
      | v2_struct_0(A_132) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_32,c_64])).

tff(c_631,plain,
    ( k7_subset_1(k1_zfmisc_1(k2_struct_0('#skF_4')),'#skF_5',k1_tarski(k1_xboole_0)) = k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
    | ~ v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | ~ v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | v1_xboole_0('#skF_5')
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_67,c_629])).

tff(c_634,plain,
    ( k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) = k4_xboole_0('#skF_5',k1_tarski(k1_xboole_0))
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_52,c_50,c_550,c_631])).

tff(c_635,plain,(
    k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) = k4_xboole_0('#skF_5',k1_tarski(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_56,c_634])).

tff(c_46,plain,(
    k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_650,plain,(
    k4_xboole_0('#skF_5',k1_tarski(k1_xboole_0)) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_635,c_46])).

tff(c_658,plain,(
    r2_hidden(k1_xboole_0,'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_448,c_650])).

tff(c_44,plain,(
    ! [C_51,B_49,A_45] :
      ( ~ v1_xboole_0(C_51)
      | ~ r2_hidden(C_51,B_49)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_45))))
      | ~ v13_waybel_0(B_49,k3_yellow_1(A_45))
      | ~ v2_waybel_0(B_49,k3_yellow_1(A_45))
      | ~ v1_subset_1(B_49,u1_struct_0(k3_yellow_1(A_45)))
      | v1_xboole_0(B_49)
      | v1_xboole_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_63,plain,(
    ! [C_51,B_49,A_45] :
      ( ~ v1_xboole_0(C_51)
      | ~ r2_hidden(C_51,B_49)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(k9_setfam_1(A_45)))
      | ~ v13_waybel_0(B_49,k3_yellow_1(A_45))
      | ~ v2_waybel_0(B_49,k3_yellow_1(A_45))
      | ~ v1_subset_1(B_49,k9_setfam_1(A_45))
      | v1_xboole_0(B_49)
      | v1_xboole_0(A_45) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_40,c_44])).

tff(c_68,plain,(
    ! [C_51,B_49,A_45] :
      ( ~ v1_xboole_0(C_51)
      | ~ r2_hidden(C_51,B_49)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(k1_zfmisc_1(A_45)))
      | ~ v13_waybel_0(B_49,k3_yellow_1(A_45))
      | ~ v2_waybel_0(B_49,k3_yellow_1(A_45))
      | ~ v1_subset_1(B_49,k1_zfmisc_1(A_45))
      | v1_xboole_0(B_49)
      | v1_xboole_0(A_45) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_32,c_63])).

tff(c_660,plain,(
    ! [A_45] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(A_45)))
      | ~ v13_waybel_0('#skF_5',k3_yellow_1(A_45))
      | ~ v2_waybel_0('#skF_5',k3_yellow_1(A_45))
      | ~ v1_subset_1('#skF_5',k1_zfmisc_1(A_45))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_45) ) ),
    inference(resolution,[status(thm)],[c_658,c_68])).

tff(c_670,plain,(
    ! [A_45] :
      ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(A_45)))
      | ~ v13_waybel_0('#skF_5',k3_yellow_1(A_45))
      | ~ v2_waybel_0('#skF_5',k3_yellow_1(A_45))
      | ~ v1_subset_1('#skF_5',k1_zfmisc_1(A_45))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_45) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_660])).

tff(c_680,plain,(
    ! [A_142] :
      ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(A_142)))
      | ~ v13_waybel_0('#skF_5',k3_yellow_1(A_142))
      | ~ v2_waybel_0('#skF_5',k3_yellow_1(A_142))
      | ~ v1_subset_1('#skF_5',k1_zfmisc_1(A_142))
      | v1_xboole_0(A_142) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_670])).

tff(c_683,plain,
    ( ~ v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | ~ v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | ~ v1_subset_1('#skF_5',k1_zfmisc_1(k2_struct_0('#skF_4')))
    | v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_67,c_680])).

tff(c_686,plain,(
    v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_52,c_50,c_683])).

tff(c_688,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_181,c_686])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n019.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 20:55:07 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.99/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.99/1.41  
% 2.99/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.99/1.41  %$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k3_mcart_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_yellow19 > k2_xboole_0 > #nlpp > u1_struct_0 > k9_setfam_1 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_lattice3 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2
% 2.99/1.41  
% 2.99/1.41  %Foreground sorts:
% 2.99/1.41  
% 2.99/1.41  
% 2.99/1.41  %Background operators:
% 2.99/1.41  
% 2.99/1.41  
% 2.99/1.41  %Foreground operators:
% 2.99/1.41  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.99/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.99/1.41  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 2.99/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.99/1.41  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.99/1.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.99/1.41  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 2.99/1.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.99/1.41  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.99/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.99/1.41  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 2.99/1.41  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 2.99/1.41  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.99/1.41  tff(k9_setfam_1, type, k9_setfam_1: $i > $i).
% 2.99/1.41  tff('#skF_5', type, '#skF_5': $i).
% 2.99/1.41  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.99/1.41  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 2.99/1.41  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 2.99/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.99/1.41  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.99/1.41  tff(k2_yellow19, type, k2_yellow19: ($i * $i) > $i).
% 2.99/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.99/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.99/1.41  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.99/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.99/1.41  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.99/1.41  tff(k3_yellow19, type, k3_yellow19: ($i * $i * $i) > $i).
% 2.99/1.41  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 2.99/1.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.99/1.41  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.99/1.41  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.99/1.41  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.99/1.41  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.99/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.99/1.41  
% 2.99/1.43  tff(f_157, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (B = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_yellow19)).
% 2.99/1.43  tff(f_87, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.99/1.43  tff(f_95, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.99/1.43  tff(f_83, axiom, (![A]: (k9_setfam_1(A) = k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_setfam_1)).
% 2.99/1.43  tff(f_99, axiom, (![A]: (u1_struct_0(k3_yellow_1(A)) = k9_setfam_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_waybel_7)).
% 2.99/1.43  tff(f_34, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.99/1.43  tff(f_52, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.99/1.43  tff(f_54, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 2.99/1.43  tff(f_56, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.99/1.43  tff(f_61, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.99/1.43  tff(f_81, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_mcart_1)).
% 2.99/1.43  tff(f_48, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.99/1.43  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.99/1.43  tff(f_50, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.99/1.43  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 2.99/1.43  tff(f_116, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))), B, k1_tarski(k1_xboole_0)) = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_yellow19)).
% 2.99/1.43  tff(f_137, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(A)))) & v2_waybel_0(B, k3_yellow_1(A))) & v13_waybel_0(B, k3_yellow_1(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A))))) => (![C]: ~(r2_hidden(C, B) & v1_xboole_0(C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_yellow19)).
% 2.99/1.43  tff(c_60, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_157])).
% 2.99/1.43  tff(c_58, plain, (l1_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_157])).
% 2.99/1.43  tff(c_158, plain, (![A_64]: (u1_struct_0(A_64)=k2_struct_0(A_64) | ~l1_struct_0(A_64))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.99/1.43  tff(c_162, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_58, c_158])).
% 2.99/1.43  tff(c_172, plain, (![A_66]: (~v1_xboole_0(u1_struct_0(A_66)) | ~l1_struct_0(A_66) | v2_struct_0(A_66))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.99/1.43  tff(c_175, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_162, c_172])).
% 2.99/1.43  tff(c_180, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_175])).
% 2.99/1.43  tff(c_181, plain, (~v1_xboole_0(k2_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_60, c_180])).
% 2.99/1.43  tff(c_32, plain, (![A_37]: (k9_setfam_1(A_37)=k1_zfmisc_1(A_37))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.99/1.43  tff(c_40, plain, (![A_41]: (u1_struct_0(k3_yellow_1(A_41))=k9_setfam_1(A_41))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.99/1.43  tff(c_54, plain, (v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_157])).
% 2.99/1.43  tff(c_61, plain, (v1_subset_1('#skF_5', k9_setfam_1(k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_54])).
% 2.99/1.43  tff(c_66, plain, (v1_subset_1('#skF_5', k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_61])).
% 2.99/1.43  tff(c_52, plain, (v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_157])).
% 2.99/1.43  tff(c_50, plain, (v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_157])).
% 2.99/1.43  tff(c_48, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4')))))), inference(cnfTransformation, [status(thm)], [f_157])).
% 2.99/1.43  tff(c_62, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k9_setfam_1(k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_48])).
% 2.99/1.43  tff(c_67, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_62])).
% 2.99/1.43  tff(c_56, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_157])).
% 2.99/1.43  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.99/1.43  tff(c_16, plain, (![A_14]: (k2_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.99/1.43  tff(c_18, plain, (![A_15]: (k4_xboole_0(k1_xboole_0, A_15)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.99/1.43  tff(c_200, plain, (![A_72, B_73]: (k5_xboole_0(A_72, k4_xboole_0(B_73, A_72))=k2_xboole_0(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.99/1.43  tff(c_209, plain, (![A_15]: (k5_xboole_0(A_15, k1_xboole_0)=k2_xboole_0(A_15, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_200])).
% 2.99/1.43  tff(c_212, plain, (![A_15]: (k5_xboole_0(A_15, k1_xboole_0)=A_15)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_209])).
% 2.99/1.43  tff(c_22, plain, (![A_18, B_19]: (r1_xboole_0(k1_tarski(A_18), B_19) | r2_hidden(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.99/1.43  tff(c_26, plain, (![A_23]: (r2_hidden('#skF_3'(A_23), A_23) | k1_xboole_0=A_23)), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.99/1.43  tff(c_183, plain, (![A_69, B_70, C_71]: (~r1_xboole_0(A_69, B_70) | ~r2_hidden(C_71, k3_xboole_0(A_69, B_70)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.99/1.43  tff(c_233, plain, (![A_77, B_78]: (~r1_xboole_0(A_77, B_78) | k3_xboole_0(A_77, B_78)=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_183])).
% 2.99/1.43  tff(c_399, plain, (![A_108, B_109]: (k3_xboole_0(k1_tarski(A_108), B_109)=k1_xboole_0 | r2_hidden(A_108, B_109))), inference(resolution, [status(thm)], [c_22, c_233])).
% 2.99/1.43  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.99/1.43  tff(c_238, plain, (![A_79, B_80]: (k5_xboole_0(A_79, k3_xboole_0(A_79, B_80))=k4_xboole_0(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.99/1.43  tff(c_247, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_238])).
% 2.99/1.43  tff(c_405, plain, (![B_109, A_108]: (k4_xboole_0(B_109, k1_tarski(A_108))=k5_xboole_0(B_109, k1_xboole_0) | r2_hidden(A_108, B_109))), inference(superposition, [status(thm), theory('equality')], [c_399, c_247])).
% 2.99/1.43  tff(c_448, plain, (![B_109, A_108]: (k4_xboole_0(B_109, k1_tarski(A_108))=B_109 | r2_hidden(A_108, B_109))), inference(demodulation, [status(thm), theory('equality')], [c_212, c_405])).
% 2.99/1.43  tff(c_547, plain, (![A_114, B_115, C_116]: (k7_subset_1(A_114, B_115, C_116)=k4_xboole_0(B_115, C_116) | ~m1_subset_1(B_115, k1_zfmisc_1(A_114)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.99/1.43  tff(c_550, plain, (![C_116]: (k7_subset_1(k1_zfmisc_1(k2_struct_0('#skF_4')), '#skF_5', C_116)=k4_xboole_0('#skF_5', C_116))), inference(resolution, [status(thm)], [c_67, c_547])).
% 2.99/1.43  tff(c_42, plain, (![A_42, B_44]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_42))), B_44, k1_tarski(k1_xboole_0))=k2_yellow19(A_42, k3_yellow19(A_42, k2_struct_0(A_42), B_44)) | ~m1_subset_1(B_44, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_42))))) | ~v13_waybel_0(B_44, k3_yellow_1(k2_struct_0(A_42))) | ~v2_waybel_0(B_44, k3_yellow_1(k2_struct_0(A_42))) | v1_xboole_0(B_44) | ~l1_struct_0(A_42) | v2_struct_0(A_42))), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.99/1.43  tff(c_64, plain, (![A_42, B_44]: (k7_subset_1(k9_setfam_1(k2_struct_0(A_42)), B_44, k1_tarski(k1_xboole_0))=k2_yellow19(A_42, k3_yellow19(A_42, k2_struct_0(A_42), B_44)) | ~m1_subset_1(B_44, k1_zfmisc_1(k9_setfam_1(k2_struct_0(A_42)))) | ~v13_waybel_0(B_44, k3_yellow_1(k2_struct_0(A_42))) | ~v2_waybel_0(B_44, k3_yellow_1(k2_struct_0(A_42))) | v1_xboole_0(B_44) | ~l1_struct_0(A_42) | v2_struct_0(A_42))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_40, c_42])).
% 2.99/1.43  tff(c_629, plain, (![A_132, B_133]: (k7_subset_1(k1_zfmisc_1(k2_struct_0(A_132)), B_133, k1_tarski(k1_xboole_0))=k2_yellow19(A_132, k3_yellow19(A_132, k2_struct_0(A_132), B_133)) | ~m1_subset_1(B_133, k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(A_132)))) | ~v13_waybel_0(B_133, k3_yellow_1(k2_struct_0(A_132))) | ~v2_waybel_0(B_133, k3_yellow_1(k2_struct_0(A_132))) | v1_xboole_0(B_133) | ~l1_struct_0(A_132) | v2_struct_0(A_132))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_32, c_64])).
% 2.99/1.43  tff(c_631, plain, (k7_subset_1(k1_zfmisc_1(k2_struct_0('#skF_4')), '#skF_5', k1_tarski(k1_xboole_0))=k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | ~v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | v1_xboole_0('#skF_5') | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_67, c_629])).
% 2.99/1.43  tff(c_634, plain, (k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))=k4_xboole_0('#skF_5', k1_tarski(k1_xboole_0)) | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_52, c_50, c_550, c_631])).
% 2.99/1.43  tff(c_635, plain, (k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))=k4_xboole_0('#skF_5', k1_tarski(k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_60, c_56, c_634])).
% 2.99/1.43  tff(c_46, plain, (k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_157])).
% 2.99/1.43  tff(c_650, plain, (k4_xboole_0('#skF_5', k1_tarski(k1_xboole_0))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_635, c_46])).
% 2.99/1.43  tff(c_658, plain, (r2_hidden(k1_xboole_0, '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_448, c_650])).
% 2.99/1.43  tff(c_44, plain, (![C_51, B_49, A_45]: (~v1_xboole_0(C_51) | ~r2_hidden(C_51, B_49) | ~m1_subset_1(B_49, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_45)))) | ~v13_waybel_0(B_49, k3_yellow_1(A_45)) | ~v2_waybel_0(B_49, k3_yellow_1(A_45)) | ~v1_subset_1(B_49, u1_struct_0(k3_yellow_1(A_45))) | v1_xboole_0(B_49) | v1_xboole_0(A_45))), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.99/1.43  tff(c_63, plain, (![C_51, B_49, A_45]: (~v1_xboole_0(C_51) | ~r2_hidden(C_51, B_49) | ~m1_subset_1(B_49, k1_zfmisc_1(k9_setfam_1(A_45))) | ~v13_waybel_0(B_49, k3_yellow_1(A_45)) | ~v2_waybel_0(B_49, k3_yellow_1(A_45)) | ~v1_subset_1(B_49, k9_setfam_1(A_45)) | v1_xboole_0(B_49) | v1_xboole_0(A_45))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_40, c_44])).
% 2.99/1.43  tff(c_68, plain, (![C_51, B_49, A_45]: (~v1_xboole_0(C_51) | ~r2_hidden(C_51, B_49) | ~m1_subset_1(B_49, k1_zfmisc_1(k1_zfmisc_1(A_45))) | ~v13_waybel_0(B_49, k3_yellow_1(A_45)) | ~v2_waybel_0(B_49, k3_yellow_1(A_45)) | ~v1_subset_1(B_49, k1_zfmisc_1(A_45)) | v1_xboole_0(B_49) | v1_xboole_0(A_45))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_32, c_63])).
% 2.99/1.43  tff(c_660, plain, (![A_45]: (~v1_xboole_0(k1_xboole_0) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1(A_45))) | ~v13_waybel_0('#skF_5', k3_yellow_1(A_45)) | ~v2_waybel_0('#skF_5', k3_yellow_1(A_45)) | ~v1_subset_1('#skF_5', k1_zfmisc_1(A_45)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_45))), inference(resolution, [status(thm)], [c_658, c_68])).
% 2.99/1.43  tff(c_670, plain, (![A_45]: (~m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1(A_45))) | ~v13_waybel_0('#skF_5', k3_yellow_1(A_45)) | ~v2_waybel_0('#skF_5', k3_yellow_1(A_45)) | ~v1_subset_1('#skF_5', k1_zfmisc_1(A_45)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_45))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_660])).
% 2.99/1.43  tff(c_680, plain, (![A_142]: (~m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1(A_142))) | ~v13_waybel_0('#skF_5', k3_yellow_1(A_142)) | ~v2_waybel_0('#skF_5', k3_yellow_1(A_142)) | ~v1_subset_1('#skF_5', k1_zfmisc_1(A_142)) | v1_xboole_0(A_142))), inference(negUnitSimplification, [status(thm)], [c_56, c_670])).
% 2.99/1.43  tff(c_683, plain, (~v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v1_subset_1('#skF_5', k1_zfmisc_1(k2_struct_0('#skF_4'))) | v1_xboole_0(k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_67, c_680])).
% 2.99/1.43  tff(c_686, plain, (v1_xboole_0(k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_52, c_50, c_683])).
% 2.99/1.43  tff(c_688, plain, $false, inference(negUnitSimplification, [status(thm)], [c_181, c_686])).
% 2.99/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.99/1.43  
% 2.99/1.43  Inference rules
% 2.99/1.43  ----------------------
% 2.99/1.43  #Ref     : 0
% 2.99/1.43  #Sup     : 149
% 2.99/1.43  #Fact    : 0
% 2.99/1.43  #Define  : 0
% 2.99/1.43  #Split   : 3
% 2.99/1.43  #Chain   : 0
% 2.99/1.43  #Close   : 0
% 2.99/1.43  
% 2.99/1.43  Ordering : KBO
% 2.99/1.43  
% 2.99/1.43  Simplification rules
% 2.99/1.43  ----------------------
% 2.99/1.43  #Subsume      : 44
% 2.99/1.43  #Demod        : 40
% 2.99/1.43  #Tautology    : 63
% 2.99/1.43  #SimpNegUnit  : 4
% 2.99/1.43  #BackRed      : 1
% 2.99/1.43  
% 2.99/1.43  #Partial instantiations: 0
% 2.99/1.43  #Strategies tried      : 1
% 2.99/1.43  
% 2.99/1.43  Timing (in seconds)
% 2.99/1.43  ----------------------
% 2.99/1.43  Preprocessing        : 0.35
% 2.99/1.43  Parsing              : 0.18
% 2.99/1.43  CNF conversion       : 0.02
% 2.99/1.43  Main loop            : 0.33
% 2.99/1.43  Inferencing          : 0.11
% 2.99/1.43  Reduction            : 0.11
% 2.99/1.43  Demodulation         : 0.08
% 2.99/1.43  BG Simplification    : 0.02
% 2.99/1.43  Subsumption          : 0.06
% 2.99/1.43  Abstraction          : 0.02
% 2.99/1.43  MUC search           : 0.00
% 2.99/1.43  Cooper               : 0.00
% 2.99/1.43  Total                : 0.72
% 2.99/1.43  Index Insertion      : 0.00
% 2.99/1.43  Index Deletion       : 0.00
% 2.99/1.43  Index Matching       : 0.00
% 2.99/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
