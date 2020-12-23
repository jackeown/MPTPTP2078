%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:26 EST 2020

% Result     : Theorem 2.73s
% Output     : CNFRefutation 2.94s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 160 expanded)
%              Number of leaves         :   50 (  79 expanded)
%              Depth                    :   14
%              Number of atoms          :  180 ( 340 expanded)
%              Number of equality atoms :   39 (  82 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_yellow19 > k2_xboole_0 > #nlpp > u1_struct_0 > k9_setfam_1 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_lattice3 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2

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

tff(f_151,negated_conjecture,(
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

tff(f_81,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_89,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_77,axiom,(
    ! [A] : k9_setfam_1(A) = k1_zfmisc_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

tff(f_93,axiom,(
    ! [A] : u1_struct_0(k3_yellow_1(A)) = k9_setfam_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_waybel_7)).

tff(f_34,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_52,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_54,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_56,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_75,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_mcart_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_110,axiom,(
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

tff(f_131,axiom,(
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

tff(c_58,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_56,plain,(
    l1_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_145,plain,(
    ! [A_50] :
      ( u1_struct_0(A_50) = k2_struct_0(A_50)
      | ~ l1_struct_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_149,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_145])).

tff(c_171,plain,(
    ! [A_55] :
      ( ~ v1_xboole_0(u1_struct_0(A_55))
      | ~ l1_struct_0(A_55)
      | v2_struct_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_174,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_171])).

tff(c_179,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_174])).

tff(c_180,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_179])).

tff(c_30,plain,(
    ! [A_25] : k9_setfam_1(A_25) = k1_zfmisc_1(A_25) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_38,plain,(
    ! [A_29] : u1_struct_0(k3_yellow_1(A_29)) = k9_setfam_1(A_29) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_52,plain,(
    v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_59,plain,(
    v1_subset_1('#skF_5',k9_setfam_1(k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_52])).

tff(c_64,plain,(
    v1_subset_1('#skF_5',k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_59])).

tff(c_50,plain,(
    v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_48,plain,(
    v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_46,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))))) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_60,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k9_setfam_1(k2_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_46])).

tff(c_65,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_60])).

tff(c_54,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_16,plain,(
    ! [A_14] : k2_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_18,plain,(
    ! [A_15] : k4_xboole_0(k1_xboole_0,A_15) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_235,plain,(
    ! [A_67,B_68] : k5_xboole_0(A_67,k4_xboole_0(B_68,A_67)) = k2_xboole_0(A_67,B_68) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_244,plain,(
    ! [A_15] : k5_xboole_0(A_15,k1_xboole_0) = k2_xboole_0(A_15,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_235])).

tff(c_247,plain,(
    ! [A_15] : k5_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_244])).

tff(c_22,plain,(
    ! [A_18,B_19] :
      ( r1_xboole_0(k1_tarski(A_18),B_19)
      | r2_hidden(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_28,plain,(
    ! [A_23] :
      ( r2_hidden('#skF_3'(A_23),A_23)
      | k1_xboole_0 = A_23 ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_197,plain,(
    ! [A_60,B_61,C_62] :
      ( ~ r1_xboole_0(A_60,B_61)
      | ~ r2_hidden(C_62,k3_xboole_0(A_60,B_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_225,plain,(
    ! [A_65,B_66] :
      ( ~ r1_xboole_0(A_65,B_66)
      | k3_xboole_0(A_65,B_66) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_28,c_197])).

tff(c_494,plain,(
    ! [A_99,B_100] :
      ( k3_xboole_0(k1_tarski(A_99),B_100) = k1_xboole_0
      | r2_hidden(A_99,B_100) ) ),
    inference(resolution,[status(thm)],[c_22,c_225])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_182,plain,(
    ! [A_58,B_59] : k5_xboole_0(A_58,k3_xboole_0(A_58,B_59)) = k4_xboole_0(A_58,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_191,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_182])).

tff(c_503,plain,(
    ! [B_100,A_99] :
      ( k4_xboole_0(B_100,k1_tarski(A_99)) = k5_xboole_0(B_100,k1_xboole_0)
      | r2_hidden(A_99,B_100) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_494,c_191])).

tff(c_551,plain,(
    ! [B_100,A_99] :
      ( k4_xboole_0(B_100,k1_tarski(A_99)) = B_100
      | r2_hidden(A_99,B_100) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_247,c_503])).

tff(c_346,plain,(
    ! [A_80,B_81,C_82] :
      ( k7_subset_1(A_80,B_81,C_82) = k4_xboole_0(B_81,C_82)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(A_80)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_349,plain,(
    ! [C_82] : k7_subset_1(k1_zfmisc_1(k2_struct_0('#skF_4')),'#skF_5',C_82) = k4_xboole_0('#skF_5',C_82) ),
    inference(resolution,[status(thm)],[c_65,c_346])).

tff(c_40,plain,(
    ! [A_30,B_32] :
      ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_30))),B_32,k1_tarski(k1_xboole_0)) = k2_yellow19(A_30,k3_yellow19(A_30,k2_struct_0(A_30),B_32))
      | ~ m1_subset_1(B_32,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_30)))))
      | ~ v13_waybel_0(B_32,k3_yellow_1(k2_struct_0(A_30)))
      | ~ v2_waybel_0(B_32,k3_yellow_1(k2_struct_0(A_30)))
      | v1_xboole_0(B_32)
      | ~ l1_struct_0(A_30)
      | v2_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_62,plain,(
    ! [A_30,B_32] :
      ( k7_subset_1(k9_setfam_1(k2_struct_0(A_30)),B_32,k1_tarski(k1_xboole_0)) = k2_yellow19(A_30,k3_yellow19(A_30,k2_struct_0(A_30),B_32))
      | ~ m1_subset_1(B_32,k1_zfmisc_1(k9_setfam_1(k2_struct_0(A_30))))
      | ~ v13_waybel_0(B_32,k3_yellow_1(k2_struct_0(A_30)))
      | ~ v2_waybel_0(B_32,k3_yellow_1(k2_struct_0(A_30)))
      | v1_xboole_0(B_32)
      | ~ l1_struct_0(A_30)
      | v2_struct_0(A_30) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_38,c_40])).

tff(c_642,plain,(
    ! [A_104,B_105] :
      ( k7_subset_1(k1_zfmisc_1(k2_struct_0(A_104)),B_105,k1_tarski(k1_xboole_0)) = k2_yellow19(A_104,k3_yellow19(A_104,k2_struct_0(A_104),B_105))
      | ~ m1_subset_1(B_105,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(A_104))))
      | ~ v13_waybel_0(B_105,k3_yellow_1(k2_struct_0(A_104)))
      | ~ v2_waybel_0(B_105,k3_yellow_1(k2_struct_0(A_104)))
      | v1_xboole_0(B_105)
      | ~ l1_struct_0(A_104)
      | v2_struct_0(A_104) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_30,c_62])).

tff(c_644,plain,
    ( k7_subset_1(k1_zfmisc_1(k2_struct_0('#skF_4')),'#skF_5',k1_tarski(k1_xboole_0)) = k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
    | ~ v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | ~ v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | v1_xboole_0('#skF_5')
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_65,c_642])).

tff(c_647,plain,
    ( k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) = k4_xboole_0('#skF_5',k1_tarski(k1_xboole_0))
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_50,c_48,c_349,c_644])).

tff(c_648,plain,(
    k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) = k4_xboole_0('#skF_5',k1_tarski(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_54,c_647])).

tff(c_44,plain,(
    k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_681,plain,(
    k4_xboole_0('#skF_5',k1_tarski(k1_xboole_0)) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_648,c_44])).

tff(c_689,plain,(
    r2_hidden(k1_xboole_0,'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_551,c_681])).

tff(c_42,plain,(
    ! [C_39,B_37,A_33] :
      ( ~ v1_xboole_0(C_39)
      | ~ r2_hidden(C_39,B_37)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_33))))
      | ~ v13_waybel_0(B_37,k3_yellow_1(A_33))
      | ~ v2_waybel_0(B_37,k3_yellow_1(A_33))
      | ~ v1_subset_1(B_37,u1_struct_0(k3_yellow_1(A_33)))
      | v1_xboole_0(B_37)
      | v1_xboole_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_61,plain,(
    ! [C_39,B_37,A_33] :
      ( ~ v1_xboole_0(C_39)
      | ~ r2_hidden(C_39,B_37)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(k9_setfam_1(A_33)))
      | ~ v13_waybel_0(B_37,k3_yellow_1(A_33))
      | ~ v2_waybel_0(B_37,k3_yellow_1(A_33))
      | ~ v1_subset_1(B_37,k9_setfam_1(A_33))
      | v1_xboole_0(B_37)
      | v1_xboole_0(A_33) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_38,c_42])).

tff(c_66,plain,(
    ! [C_39,B_37,A_33] :
      ( ~ v1_xboole_0(C_39)
      | ~ r2_hidden(C_39,B_37)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(k1_zfmisc_1(A_33)))
      | ~ v13_waybel_0(B_37,k3_yellow_1(A_33))
      | ~ v2_waybel_0(B_37,k3_yellow_1(A_33))
      | ~ v1_subset_1(B_37,k1_zfmisc_1(A_33))
      | v1_xboole_0(B_37)
      | v1_xboole_0(A_33) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_30,c_61])).

tff(c_691,plain,(
    ! [A_33] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(A_33)))
      | ~ v13_waybel_0('#skF_5',k3_yellow_1(A_33))
      | ~ v2_waybel_0('#skF_5',k3_yellow_1(A_33))
      | ~ v1_subset_1('#skF_5',k1_zfmisc_1(A_33))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_33) ) ),
    inference(resolution,[status(thm)],[c_689,c_66])).

tff(c_697,plain,(
    ! [A_33] :
      ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(A_33)))
      | ~ v13_waybel_0('#skF_5',k3_yellow_1(A_33))
      | ~ v2_waybel_0('#skF_5',k3_yellow_1(A_33))
      | ~ v1_subset_1('#skF_5',k1_zfmisc_1(A_33))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_33) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_691])).

tff(c_702,plain,(
    ! [A_109] :
      ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(A_109)))
      | ~ v13_waybel_0('#skF_5',k3_yellow_1(A_109))
      | ~ v2_waybel_0('#skF_5',k3_yellow_1(A_109))
      | ~ v1_subset_1('#skF_5',k1_zfmisc_1(A_109))
      | v1_xboole_0(A_109) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_697])).

tff(c_705,plain,
    ( ~ v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | ~ v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | ~ v1_subset_1('#skF_5',k1_zfmisc_1(k2_struct_0('#skF_4')))
    | v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_65,c_702])).

tff(c_708,plain,(
    v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_50,c_48,c_705])).

tff(c_710,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_180,c_708])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:21:56 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.73/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.94/1.42  
% 2.94/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.94/1.43  %$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_yellow19 > k2_xboole_0 > #nlpp > u1_struct_0 > k9_setfam_1 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_lattice3 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2
% 2.94/1.43  
% 2.94/1.43  %Foreground sorts:
% 2.94/1.43  
% 2.94/1.43  
% 2.94/1.43  %Background operators:
% 2.94/1.43  
% 2.94/1.43  
% 2.94/1.43  %Foreground operators:
% 2.94/1.43  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.94/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.94/1.43  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 2.94/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.94/1.43  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.94/1.43  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.94/1.43  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 2.94/1.43  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.94/1.43  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.94/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.94/1.43  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 2.94/1.43  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.94/1.43  tff(k9_setfam_1, type, k9_setfam_1: $i > $i).
% 2.94/1.43  tff('#skF_5', type, '#skF_5': $i).
% 2.94/1.43  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.94/1.43  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 2.94/1.43  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 2.94/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.94/1.43  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.94/1.43  tff(k2_yellow19, type, k2_yellow19: ($i * $i) > $i).
% 2.94/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.94/1.43  tff('#skF_4', type, '#skF_4': $i).
% 2.94/1.43  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.94/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.94/1.43  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.94/1.43  tff(k3_yellow19, type, k3_yellow19: ($i * $i * $i) > $i).
% 2.94/1.43  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 2.94/1.43  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.94/1.43  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.94/1.43  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.94/1.43  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.94/1.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.94/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.94/1.43  
% 2.94/1.44  tff(f_151, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (B = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_yellow19)).
% 2.94/1.44  tff(f_81, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 2.94/1.44  tff(f_89, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.94/1.44  tff(f_77, axiom, (![A]: (k9_setfam_1(A) = k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_setfam_1)).
% 2.94/1.44  tff(f_93, axiom, (![A]: (u1_struct_0(k3_yellow_1(A)) = k9_setfam_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_waybel_7)).
% 2.94/1.44  tff(f_34, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.94/1.44  tff(f_52, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.94/1.44  tff(f_54, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 2.94/1.44  tff(f_56, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.94/1.44  tff(f_61, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.94/1.44  tff(f_75, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & r1_xboole_0(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_mcart_1)).
% 2.94/1.44  tff(f_48, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.94/1.44  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.94/1.44  tff(f_50, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.94/1.44  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 2.94/1.44  tff(f_110, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))), B, k1_tarski(k1_xboole_0)) = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_yellow19)).
% 2.94/1.44  tff(f_131, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(A)))) & v2_waybel_0(B, k3_yellow_1(A))) & v13_waybel_0(B, k3_yellow_1(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A))))) => (![C]: ~(r2_hidden(C, B) & v1_xboole_0(C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_yellow19)).
% 2.94/1.44  tff(c_58, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_151])).
% 2.94/1.44  tff(c_56, plain, (l1_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_151])).
% 2.94/1.44  tff(c_145, plain, (![A_50]: (u1_struct_0(A_50)=k2_struct_0(A_50) | ~l1_struct_0(A_50))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.94/1.44  tff(c_149, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_56, c_145])).
% 2.94/1.44  tff(c_171, plain, (![A_55]: (~v1_xboole_0(u1_struct_0(A_55)) | ~l1_struct_0(A_55) | v2_struct_0(A_55))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.94/1.44  tff(c_174, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_149, c_171])).
% 2.94/1.44  tff(c_179, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_174])).
% 2.94/1.44  tff(c_180, plain, (~v1_xboole_0(k2_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_58, c_179])).
% 2.94/1.44  tff(c_30, plain, (![A_25]: (k9_setfam_1(A_25)=k1_zfmisc_1(A_25))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.94/1.44  tff(c_38, plain, (![A_29]: (u1_struct_0(k3_yellow_1(A_29))=k9_setfam_1(A_29))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.94/1.44  tff(c_52, plain, (v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_151])).
% 2.94/1.44  tff(c_59, plain, (v1_subset_1('#skF_5', k9_setfam_1(k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_52])).
% 2.94/1.44  tff(c_64, plain, (v1_subset_1('#skF_5', k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_59])).
% 2.94/1.44  tff(c_50, plain, (v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_151])).
% 2.94/1.44  tff(c_48, plain, (v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_151])).
% 2.94/1.44  tff(c_46, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4')))))), inference(cnfTransformation, [status(thm)], [f_151])).
% 2.94/1.44  tff(c_60, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k9_setfam_1(k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_46])).
% 2.94/1.44  tff(c_65, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_60])).
% 2.94/1.44  tff(c_54, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_151])).
% 2.94/1.44  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.94/1.44  tff(c_16, plain, (![A_14]: (k2_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.94/1.44  tff(c_18, plain, (![A_15]: (k4_xboole_0(k1_xboole_0, A_15)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.94/1.44  tff(c_235, plain, (![A_67, B_68]: (k5_xboole_0(A_67, k4_xboole_0(B_68, A_67))=k2_xboole_0(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.94/1.44  tff(c_244, plain, (![A_15]: (k5_xboole_0(A_15, k1_xboole_0)=k2_xboole_0(A_15, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_235])).
% 2.94/1.44  tff(c_247, plain, (![A_15]: (k5_xboole_0(A_15, k1_xboole_0)=A_15)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_244])).
% 2.94/1.44  tff(c_22, plain, (![A_18, B_19]: (r1_xboole_0(k1_tarski(A_18), B_19) | r2_hidden(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.94/1.44  tff(c_28, plain, (![A_23]: (r2_hidden('#skF_3'(A_23), A_23) | k1_xboole_0=A_23)), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.94/1.44  tff(c_197, plain, (![A_60, B_61, C_62]: (~r1_xboole_0(A_60, B_61) | ~r2_hidden(C_62, k3_xboole_0(A_60, B_61)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.94/1.44  tff(c_225, plain, (![A_65, B_66]: (~r1_xboole_0(A_65, B_66) | k3_xboole_0(A_65, B_66)=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_197])).
% 2.94/1.44  tff(c_494, plain, (![A_99, B_100]: (k3_xboole_0(k1_tarski(A_99), B_100)=k1_xboole_0 | r2_hidden(A_99, B_100))), inference(resolution, [status(thm)], [c_22, c_225])).
% 2.94/1.44  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.94/1.44  tff(c_182, plain, (![A_58, B_59]: (k5_xboole_0(A_58, k3_xboole_0(A_58, B_59))=k4_xboole_0(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.94/1.44  tff(c_191, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_182])).
% 2.94/1.44  tff(c_503, plain, (![B_100, A_99]: (k4_xboole_0(B_100, k1_tarski(A_99))=k5_xboole_0(B_100, k1_xboole_0) | r2_hidden(A_99, B_100))), inference(superposition, [status(thm), theory('equality')], [c_494, c_191])).
% 2.94/1.44  tff(c_551, plain, (![B_100, A_99]: (k4_xboole_0(B_100, k1_tarski(A_99))=B_100 | r2_hidden(A_99, B_100))), inference(demodulation, [status(thm), theory('equality')], [c_247, c_503])).
% 2.94/1.44  tff(c_346, plain, (![A_80, B_81, C_82]: (k7_subset_1(A_80, B_81, C_82)=k4_xboole_0(B_81, C_82) | ~m1_subset_1(B_81, k1_zfmisc_1(A_80)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.94/1.44  tff(c_349, plain, (![C_82]: (k7_subset_1(k1_zfmisc_1(k2_struct_0('#skF_4')), '#skF_5', C_82)=k4_xboole_0('#skF_5', C_82))), inference(resolution, [status(thm)], [c_65, c_346])).
% 2.94/1.44  tff(c_40, plain, (![A_30, B_32]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_30))), B_32, k1_tarski(k1_xboole_0))=k2_yellow19(A_30, k3_yellow19(A_30, k2_struct_0(A_30), B_32)) | ~m1_subset_1(B_32, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_30))))) | ~v13_waybel_0(B_32, k3_yellow_1(k2_struct_0(A_30))) | ~v2_waybel_0(B_32, k3_yellow_1(k2_struct_0(A_30))) | v1_xboole_0(B_32) | ~l1_struct_0(A_30) | v2_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.94/1.44  tff(c_62, plain, (![A_30, B_32]: (k7_subset_1(k9_setfam_1(k2_struct_0(A_30)), B_32, k1_tarski(k1_xboole_0))=k2_yellow19(A_30, k3_yellow19(A_30, k2_struct_0(A_30), B_32)) | ~m1_subset_1(B_32, k1_zfmisc_1(k9_setfam_1(k2_struct_0(A_30)))) | ~v13_waybel_0(B_32, k3_yellow_1(k2_struct_0(A_30))) | ~v2_waybel_0(B_32, k3_yellow_1(k2_struct_0(A_30))) | v1_xboole_0(B_32) | ~l1_struct_0(A_30) | v2_struct_0(A_30))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_38, c_40])).
% 2.94/1.44  tff(c_642, plain, (![A_104, B_105]: (k7_subset_1(k1_zfmisc_1(k2_struct_0(A_104)), B_105, k1_tarski(k1_xboole_0))=k2_yellow19(A_104, k3_yellow19(A_104, k2_struct_0(A_104), B_105)) | ~m1_subset_1(B_105, k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(A_104)))) | ~v13_waybel_0(B_105, k3_yellow_1(k2_struct_0(A_104))) | ~v2_waybel_0(B_105, k3_yellow_1(k2_struct_0(A_104))) | v1_xboole_0(B_105) | ~l1_struct_0(A_104) | v2_struct_0(A_104))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_30, c_62])).
% 2.94/1.44  tff(c_644, plain, (k7_subset_1(k1_zfmisc_1(k2_struct_0('#skF_4')), '#skF_5', k1_tarski(k1_xboole_0))=k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | ~v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | v1_xboole_0('#skF_5') | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_65, c_642])).
% 2.94/1.44  tff(c_647, plain, (k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))=k4_xboole_0('#skF_5', k1_tarski(k1_xboole_0)) | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_50, c_48, c_349, c_644])).
% 2.94/1.44  tff(c_648, plain, (k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))=k4_xboole_0('#skF_5', k1_tarski(k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_58, c_54, c_647])).
% 2.94/1.44  tff(c_44, plain, (k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_151])).
% 2.94/1.44  tff(c_681, plain, (k4_xboole_0('#skF_5', k1_tarski(k1_xboole_0))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_648, c_44])).
% 2.94/1.44  tff(c_689, plain, (r2_hidden(k1_xboole_0, '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_551, c_681])).
% 2.94/1.44  tff(c_42, plain, (![C_39, B_37, A_33]: (~v1_xboole_0(C_39) | ~r2_hidden(C_39, B_37) | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_33)))) | ~v13_waybel_0(B_37, k3_yellow_1(A_33)) | ~v2_waybel_0(B_37, k3_yellow_1(A_33)) | ~v1_subset_1(B_37, u1_struct_0(k3_yellow_1(A_33))) | v1_xboole_0(B_37) | v1_xboole_0(A_33))), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.94/1.44  tff(c_61, plain, (![C_39, B_37, A_33]: (~v1_xboole_0(C_39) | ~r2_hidden(C_39, B_37) | ~m1_subset_1(B_37, k1_zfmisc_1(k9_setfam_1(A_33))) | ~v13_waybel_0(B_37, k3_yellow_1(A_33)) | ~v2_waybel_0(B_37, k3_yellow_1(A_33)) | ~v1_subset_1(B_37, k9_setfam_1(A_33)) | v1_xboole_0(B_37) | v1_xboole_0(A_33))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_38, c_42])).
% 2.94/1.44  tff(c_66, plain, (![C_39, B_37, A_33]: (~v1_xboole_0(C_39) | ~r2_hidden(C_39, B_37) | ~m1_subset_1(B_37, k1_zfmisc_1(k1_zfmisc_1(A_33))) | ~v13_waybel_0(B_37, k3_yellow_1(A_33)) | ~v2_waybel_0(B_37, k3_yellow_1(A_33)) | ~v1_subset_1(B_37, k1_zfmisc_1(A_33)) | v1_xboole_0(B_37) | v1_xboole_0(A_33))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_30, c_61])).
% 2.94/1.44  tff(c_691, plain, (![A_33]: (~v1_xboole_0(k1_xboole_0) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1(A_33))) | ~v13_waybel_0('#skF_5', k3_yellow_1(A_33)) | ~v2_waybel_0('#skF_5', k3_yellow_1(A_33)) | ~v1_subset_1('#skF_5', k1_zfmisc_1(A_33)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_33))), inference(resolution, [status(thm)], [c_689, c_66])).
% 2.94/1.44  tff(c_697, plain, (![A_33]: (~m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1(A_33))) | ~v13_waybel_0('#skF_5', k3_yellow_1(A_33)) | ~v2_waybel_0('#skF_5', k3_yellow_1(A_33)) | ~v1_subset_1('#skF_5', k1_zfmisc_1(A_33)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_33))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_691])).
% 2.94/1.44  tff(c_702, plain, (![A_109]: (~m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1(A_109))) | ~v13_waybel_0('#skF_5', k3_yellow_1(A_109)) | ~v2_waybel_0('#skF_5', k3_yellow_1(A_109)) | ~v1_subset_1('#skF_5', k1_zfmisc_1(A_109)) | v1_xboole_0(A_109))), inference(negUnitSimplification, [status(thm)], [c_54, c_697])).
% 2.94/1.44  tff(c_705, plain, (~v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v1_subset_1('#skF_5', k1_zfmisc_1(k2_struct_0('#skF_4'))) | v1_xboole_0(k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_65, c_702])).
% 2.94/1.44  tff(c_708, plain, (v1_xboole_0(k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_50, c_48, c_705])).
% 2.94/1.44  tff(c_710, plain, $false, inference(negUnitSimplification, [status(thm)], [c_180, c_708])).
% 2.94/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.94/1.44  
% 2.94/1.44  Inference rules
% 2.94/1.44  ----------------------
% 2.94/1.44  #Ref     : 0
% 2.94/1.44  #Sup     : 153
% 2.94/1.44  #Fact    : 0
% 2.94/1.44  #Define  : 0
% 2.94/1.44  #Split   : 1
% 2.94/1.45  #Chain   : 0
% 2.94/1.45  #Close   : 0
% 2.94/1.45  
% 2.94/1.45  Ordering : KBO
% 2.94/1.45  
% 2.94/1.45  Simplification rules
% 2.94/1.45  ----------------------
% 2.94/1.45  #Subsume      : 39
% 2.94/1.45  #Demod        : 47
% 2.94/1.45  #Tautology    : 70
% 2.94/1.45  #SimpNegUnit  : 4
% 2.94/1.45  #BackRed      : 1
% 2.94/1.45  
% 2.94/1.45  #Partial instantiations: 0
% 2.94/1.45  #Strategies tried      : 1
% 2.94/1.45  
% 2.94/1.45  Timing (in seconds)
% 2.94/1.45  ----------------------
% 3.07/1.45  Preprocessing        : 0.35
% 3.07/1.45  Parsing              : 0.20
% 3.07/1.45  CNF conversion       : 0.02
% 3.07/1.45  Main loop            : 0.29
% 3.07/1.45  Inferencing          : 0.11
% 3.07/1.45  Reduction            : 0.10
% 3.07/1.45  Demodulation         : 0.07
% 3.07/1.45  BG Simplification    : 0.02
% 3.07/1.45  Subsumption          : 0.05
% 3.07/1.45  Abstraction          : 0.02
% 3.07/1.45  MUC search           : 0.00
% 3.07/1.45  Cooper               : 0.00
% 3.07/1.45  Total                : 0.68
% 3.07/1.45  Index Insertion      : 0.00
% 3.07/1.45  Index Deletion       : 0.00
% 3.07/1.45  Index Matching       : 0.00
% 3.07/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
