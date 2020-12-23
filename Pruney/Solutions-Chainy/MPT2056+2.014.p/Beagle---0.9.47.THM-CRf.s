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
% DateTime   : Thu Dec  3 10:31:27 EST 2020

% Result     : Theorem 3.07s
% Output     : CNFRefutation 3.22s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 115 expanded)
%              Number of leaves         :   46 (  62 expanded)
%              Depth                    :   15
%              Number of atoms          :  141 ( 264 expanded)
%              Number of equality atoms :   32 (  50 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_yellow19 > k2_xboole_0 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_lattice3 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2

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

tff(f_158,negated_conjecture,(
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

tff(f_34,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_54,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_60,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_50,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_90,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F,G] :
                  ( ( r2_hidden(C,D)
                    & r2_hidden(D,E)
                    & r2_hidden(E,F)
                    & r2_hidden(F,G)
                    & r2_hidden(G,B) )
                 => r1_xboole_0(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_mcart_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_117,axiom,(
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

tff(f_138,axiom,(
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

tff(f_98,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_54,plain,(
    l1_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_50,plain,(
    v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_48,plain,(
    v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_46,plain,(
    v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))))) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_52,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_18,plain,(
    ! [A_15] : k4_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_176,plain,(
    ! [A_77,B_78] : k4_xboole_0(A_77,k4_xboole_0(A_77,B_78)) = k3_xboole_0(A_77,B_78) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_24,plain,(
    ! [A_20] : k4_xboole_0(k1_xboole_0,A_20) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_210,plain,(
    ! [B_79] : k3_xboole_0(k1_xboole_0,B_79) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_24])).

tff(c_224,plain,(
    ! [B_2] : k3_xboole_0(B_2,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_210])).

tff(c_291,plain,(
    ! [A_84,B_85] : k5_xboole_0(A_84,k3_xboole_0(A_84,B_85)) = k4_xboole_0(A_84,B_85) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_300,plain,(
    ! [B_2] : k5_xboole_0(B_2,k1_xboole_0) = k4_xboole_0(B_2,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_291])).

tff(c_312,plain,(
    ! [B_2] : k5_xboole_0(B_2,k1_xboole_0) = B_2 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_300])).

tff(c_26,plain,(
    ! [A_21,B_22] :
      ( r1_xboole_0(k1_tarski(A_21),B_22)
      | r2_hidden(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_32,plain,(
    ! [A_26] :
      ( r2_hidden('#skF_3'(A_26),A_26)
      | k1_xboole_0 = A_26 ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_233,plain,(
    ! [A_80,B_81,C_82] :
      ( ~ r1_xboole_0(A_80,B_81)
      | ~ r2_hidden(C_82,k3_xboole_0(A_80,B_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_459,plain,(
    ! [A_98,B_99] :
      ( ~ r1_xboole_0(A_98,B_99)
      | k3_xboole_0(A_98,B_99) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_32,c_233])).

tff(c_792,plain,(
    ! [A_136,B_137] :
      ( k3_xboole_0(k1_tarski(A_136),B_137) = k1_xboole_0
      | r2_hidden(A_136,B_137) ) ),
    inference(resolution,[status(thm)],[c_26,c_459])).

tff(c_306,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_291])).

tff(c_798,plain,(
    ! [B_137,A_136] :
      ( k4_xboole_0(B_137,k1_tarski(A_136)) = k5_xboole_0(B_137,k1_xboole_0)
      | r2_hidden(A_136,B_137) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_792,c_306])).

tff(c_1020,plain,(
    ! [B_143,A_144] :
      ( k4_xboole_0(B_143,k1_tarski(A_144)) = B_143
      | r2_hidden(A_144,B_143) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_312,c_798])).

tff(c_450,plain,(
    ! [A_93,B_94,C_95] :
      ( k7_subset_1(A_93,B_94,C_95) = k4_xboole_0(B_94,C_95)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(A_93)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_453,plain,(
    ! [C_95] : k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))),'#skF_5',C_95) = k4_xboole_0('#skF_5',C_95) ),
    inference(resolution,[status(thm)],[c_44,c_450])).

tff(c_703,plain,(
    ! [A_128,B_129] :
      ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_128))),B_129,k1_tarski(k1_xboole_0)) = k2_yellow19(A_128,k3_yellow19(A_128,k2_struct_0(A_128),B_129))
      | ~ m1_subset_1(B_129,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_128)))))
      | ~ v13_waybel_0(B_129,k3_yellow_1(k2_struct_0(A_128)))
      | ~ v2_waybel_0(B_129,k3_yellow_1(k2_struct_0(A_128)))
      | v1_xboole_0(B_129)
      | ~ l1_struct_0(A_128)
      | v2_struct_0(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_705,plain,
    ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))),'#skF_5',k1_tarski(k1_xboole_0)) = k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
    | ~ v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | ~ v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | v1_xboole_0('#skF_5')
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_703])).

tff(c_708,plain,
    ( k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) = k4_xboole_0('#skF_5',k1_tarski(k1_xboole_0))
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_48,c_46,c_453,c_705])).

tff(c_709,plain,(
    k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) = k4_xboole_0('#skF_5',k1_tarski(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_52,c_708])).

tff(c_42,plain,(
    k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_879,plain,(
    k4_xboole_0('#skF_5',k1_tarski(k1_xboole_0)) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_709,c_42])).

tff(c_1058,plain,(
    r2_hidden(k1_xboole_0,'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1020,c_879])).

tff(c_40,plain,(
    ! [C_59,B_57,A_53] :
      ( ~ v1_xboole_0(C_59)
      | ~ r2_hidden(C_59,B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_53))))
      | ~ v13_waybel_0(B_57,k3_yellow_1(A_53))
      | ~ v2_waybel_0(B_57,k3_yellow_1(A_53))
      | ~ v1_subset_1(B_57,u1_struct_0(k3_yellow_1(A_53)))
      | v1_xboole_0(B_57)
      | v1_xboole_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_1066,plain,(
    ! [A_53] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_53))))
      | ~ v13_waybel_0('#skF_5',k3_yellow_1(A_53))
      | ~ v2_waybel_0('#skF_5',k3_yellow_1(A_53))
      | ~ v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(A_53)))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_53) ) ),
    inference(resolution,[status(thm)],[c_1058,c_40])).

tff(c_1072,plain,(
    ! [A_53] :
      ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_53))))
      | ~ v13_waybel_0('#skF_5',k3_yellow_1(A_53))
      | ~ v2_waybel_0('#skF_5',k3_yellow_1(A_53))
      | ~ v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(A_53)))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_53) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1066])).

tff(c_1075,plain,(
    ! [A_145] :
      ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_145))))
      | ~ v13_waybel_0('#skF_5',k3_yellow_1(A_145))
      | ~ v2_waybel_0('#skF_5',k3_yellow_1(A_145))
      | ~ v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(A_145)))
      | v1_xboole_0(A_145) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1072])).

tff(c_1078,plain,
    ( ~ v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | ~ v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | ~ v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))))
    | v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_44,c_1075])).

tff(c_1081,plain,(
    v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_1078])).

tff(c_34,plain,(
    ! [A_48] :
      ( ~ v1_xboole_0(k2_struct_0(A_48))
      | ~ l1_struct_0(A_48)
      | v2_struct_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1084,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1081,c_34])).

tff(c_1090,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1084])).

tff(c_1092,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1090])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:47:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.07/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.07/1.52  
% 3.07/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.07/1.52  %$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_yellow19 > k2_xboole_0 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_lattice3 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2
% 3.07/1.52  
% 3.07/1.52  %Foreground sorts:
% 3.07/1.52  
% 3.07/1.52  
% 3.07/1.52  %Background operators:
% 3.07/1.52  
% 3.07/1.52  
% 3.07/1.52  %Foreground operators:
% 3.07/1.52  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.07/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.07/1.52  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 3.07/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.07/1.52  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.07/1.52  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.07/1.52  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 3.07/1.52  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.07/1.52  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.07/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.07/1.52  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 3.07/1.52  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.07/1.52  tff('#skF_5', type, '#skF_5': $i).
% 3.07/1.52  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.07/1.52  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 3.07/1.52  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 3.07/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.07/1.52  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.07/1.52  tff(k2_yellow19, type, k2_yellow19: ($i * $i) > $i).
% 3.07/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.07/1.52  tff('#skF_4', type, '#skF_4': $i).
% 3.07/1.52  tff('#skF_3', type, '#skF_3': $i > $i).
% 3.07/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.07/1.52  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.07/1.52  tff(k3_yellow19, type, k3_yellow19: ($i * $i * $i) > $i).
% 3.07/1.52  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 3.07/1.52  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.07/1.52  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.07/1.52  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.07/1.52  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.07/1.52  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.07/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.07/1.52  
% 3.22/1.53  tff(f_158, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (B = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_yellow19)).
% 3.22/1.53  tff(f_34, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.22/1.53  tff(f_54, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 3.22/1.53  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.22/1.53  tff(f_58, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.22/1.53  tff(f_60, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 3.22/1.53  tff(f_50, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.22/1.53  tff(f_65, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.22/1.53  tff(f_90, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F, G]: (((((r2_hidden(C, D) & r2_hidden(D, E)) & r2_hidden(E, F)) & r2_hidden(F, G)) & r2_hidden(G, B)) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_mcart_1)).
% 3.22/1.53  tff(f_48, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.22/1.53  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 3.22/1.53  tff(f_117, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))), B, k1_tarski(k1_xboole_0)) = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_yellow19)).
% 3.22/1.53  tff(f_138, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(A)))) & v2_waybel_0(B, k3_yellow_1(A))) & v13_waybel_0(B, k3_yellow_1(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A))))) => (![C]: ~(r2_hidden(C, B) & v1_xboole_0(C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_yellow19)).
% 3.22/1.53  tff(f_98, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_struct_0)).
% 3.22/1.53  tff(c_56, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_158])).
% 3.22/1.53  tff(c_54, plain, (l1_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_158])).
% 3.22/1.53  tff(c_50, plain, (v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_158])).
% 3.22/1.53  tff(c_48, plain, (v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_158])).
% 3.22/1.53  tff(c_46, plain, (v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_158])).
% 3.22/1.53  tff(c_44, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4')))))), inference(cnfTransformation, [status(thm)], [f_158])).
% 3.22/1.53  tff(c_52, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_158])).
% 3.22/1.53  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.22/1.53  tff(c_18, plain, (![A_15]: (k4_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.22/1.53  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.22/1.53  tff(c_176, plain, (![A_77, B_78]: (k4_xboole_0(A_77, k4_xboole_0(A_77, B_78))=k3_xboole_0(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.22/1.53  tff(c_24, plain, (![A_20]: (k4_xboole_0(k1_xboole_0, A_20)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.22/1.53  tff(c_210, plain, (![B_79]: (k3_xboole_0(k1_xboole_0, B_79)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_176, c_24])).
% 3.22/1.53  tff(c_224, plain, (![B_2]: (k3_xboole_0(B_2, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_210])).
% 3.22/1.53  tff(c_291, plain, (![A_84, B_85]: (k5_xboole_0(A_84, k3_xboole_0(A_84, B_85))=k4_xboole_0(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.22/1.53  tff(c_300, plain, (![B_2]: (k5_xboole_0(B_2, k1_xboole_0)=k4_xboole_0(B_2, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_224, c_291])).
% 3.22/1.53  tff(c_312, plain, (![B_2]: (k5_xboole_0(B_2, k1_xboole_0)=B_2)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_300])).
% 3.22/1.53  tff(c_26, plain, (![A_21, B_22]: (r1_xboole_0(k1_tarski(A_21), B_22) | r2_hidden(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.22/1.53  tff(c_32, plain, (![A_26]: (r2_hidden('#skF_3'(A_26), A_26) | k1_xboole_0=A_26)), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.22/1.53  tff(c_233, plain, (![A_80, B_81, C_82]: (~r1_xboole_0(A_80, B_81) | ~r2_hidden(C_82, k3_xboole_0(A_80, B_81)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.22/1.53  tff(c_459, plain, (![A_98, B_99]: (~r1_xboole_0(A_98, B_99) | k3_xboole_0(A_98, B_99)=k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_233])).
% 3.22/1.53  tff(c_792, plain, (![A_136, B_137]: (k3_xboole_0(k1_tarski(A_136), B_137)=k1_xboole_0 | r2_hidden(A_136, B_137))), inference(resolution, [status(thm)], [c_26, c_459])).
% 3.22/1.53  tff(c_306, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_291])).
% 3.22/1.53  tff(c_798, plain, (![B_137, A_136]: (k4_xboole_0(B_137, k1_tarski(A_136))=k5_xboole_0(B_137, k1_xboole_0) | r2_hidden(A_136, B_137))), inference(superposition, [status(thm), theory('equality')], [c_792, c_306])).
% 3.22/1.53  tff(c_1020, plain, (![B_143, A_144]: (k4_xboole_0(B_143, k1_tarski(A_144))=B_143 | r2_hidden(A_144, B_143))), inference(demodulation, [status(thm), theory('equality')], [c_312, c_798])).
% 3.22/1.53  tff(c_450, plain, (![A_93, B_94, C_95]: (k7_subset_1(A_93, B_94, C_95)=k4_xboole_0(B_94, C_95) | ~m1_subset_1(B_94, k1_zfmisc_1(A_93)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.22/1.53  tff(c_453, plain, (![C_95]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))), '#skF_5', C_95)=k4_xboole_0('#skF_5', C_95))), inference(resolution, [status(thm)], [c_44, c_450])).
% 3.22/1.53  tff(c_703, plain, (![A_128, B_129]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_128))), B_129, k1_tarski(k1_xboole_0))=k2_yellow19(A_128, k3_yellow19(A_128, k2_struct_0(A_128), B_129)) | ~m1_subset_1(B_129, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_128))))) | ~v13_waybel_0(B_129, k3_yellow_1(k2_struct_0(A_128))) | ~v2_waybel_0(B_129, k3_yellow_1(k2_struct_0(A_128))) | v1_xboole_0(B_129) | ~l1_struct_0(A_128) | v2_struct_0(A_128))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.22/1.53  tff(c_705, plain, (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))), '#skF_5', k1_tarski(k1_xboole_0))=k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | ~v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | v1_xboole_0('#skF_5') | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_44, c_703])).
% 3.22/1.53  tff(c_708, plain, (k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))=k4_xboole_0('#skF_5', k1_tarski(k1_xboole_0)) | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_48, c_46, c_453, c_705])).
% 3.22/1.53  tff(c_709, plain, (k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))=k4_xboole_0('#skF_5', k1_tarski(k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_56, c_52, c_708])).
% 3.22/1.53  tff(c_42, plain, (k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_158])).
% 3.22/1.53  tff(c_879, plain, (k4_xboole_0('#skF_5', k1_tarski(k1_xboole_0))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_709, c_42])).
% 3.22/1.53  tff(c_1058, plain, (r2_hidden(k1_xboole_0, '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1020, c_879])).
% 3.22/1.53  tff(c_40, plain, (![C_59, B_57, A_53]: (~v1_xboole_0(C_59) | ~r2_hidden(C_59, B_57) | ~m1_subset_1(B_57, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_53)))) | ~v13_waybel_0(B_57, k3_yellow_1(A_53)) | ~v2_waybel_0(B_57, k3_yellow_1(A_53)) | ~v1_subset_1(B_57, u1_struct_0(k3_yellow_1(A_53))) | v1_xboole_0(B_57) | v1_xboole_0(A_53))), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.22/1.53  tff(c_1066, plain, (![A_53]: (~v1_xboole_0(k1_xboole_0) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_53)))) | ~v13_waybel_0('#skF_5', k3_yellow_1(A_53)) | ~v2_waybel_0('#skF_5', k3_yellow_1(A_53)) | ~v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(A_53))) | v1_xboole_0('#skF_5') | v1_xboole_0(A_53))), inference(resolution, [status(thm)], [c_1058, c_40])).
% 3.22/1.53  tff(c_1072, plain, (![A_53]: (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_53)))) | ~v13_waybel_0('#skF_5', k3_yellow_1(A_53)) | ~v2_waybel_0('#skF_5', k3_yellow_1(A_53)) | ~v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(A_53))) | v1_xboole_0('#skF_5') | v1_xboole_0(A_53))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1066])).
% 3.22/1.53  tff(c_1075, plain, (![A_145]: (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_145)))) | ~v13_waybel_0('#skF_5', k3_yellow_1(A_145)) | ~v2_waybel_0('#skF_5', k3_yellow_1(A_145)) | ~v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(A_145))) | v1_xboole_0(A_145))), inference(negUnitSimplification, [status(thm)], [c_52, c_1072])).
% 3.22/1.53  tff(c_1078, plain, (~v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4')))) | v1_xboole_0(k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_44, c_1075])).
% 3.22/1.53  tff(c_1081, plain, (v1_xboole_0(k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_1078])).
% 3.22/1.53  tff(c_34, plain, (![A_48]: (~v1_xboole_0(k2_struct_0(A_48)) | ~l1_struct_0(A_48) | v2_struct_0(A_48))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.22/1.53  tff(c_1084, plain, (~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_1081, c_34])).
% 3.22/1.54  tff(c_1090, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1084])).
% 3.22/1.54  tff(c_1092, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_1090])).
% 3.22/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/1.54  
% 3.22/1.54  Inference rules
% 3.22/1.54  ----------------------
% 3.22/1.54  #Ref     : 0
% 3.22/1.54  #Sup     : 242
% 3.22/1.54  #Fact    : 0
% 3.22/1.54  #Define  : 0
% 3.22/1.54  #Split   : 1
% 3.22/1.54  #Chain   : 0
% 3.22/1.54  #Close   : 0
% 3.22/1.54  
% 3.22/1.54  Ordering : KBO
% 3.22/1.54  
% 3.22/1.54  Simplification rules
% 3.22/1.54  ----------------------
% 3.22/1.54  #Subsume      : 58
% 3.22/1.54  #Demod        : 90
% 3.22/1.54  #Tautology    : 123
% 3.22/1.54  #SimpNegUnit  : 17
% 3.22/1.54  #BackRed      : 1
% 3.22/1.54  
% 3.22/1.54  #Partial instantiations: 0
% 3.22/1.54  #Strategies tried      : 1
% 3.22/1.54  
% 3.22/1.54  Timing (in seconds)
% 3.22/1.54  ----------------------
% 3.22/1.54  Preprocessing        : 0.35
% 3.25/1.54  Parsing              : 0.20
% 3.25/1.54  CNF conversion       : 0.02
% 3.25/1.54  Main loop            : 0.34
% 3.25/1.54  Inferencing          : 0.13
% 3.25/1.54  Reduction            : 0.12
% 3.25/1.54  Demodulation         : 0.08
% 3.25/1.54  BG Simplification    : 0.02
% 3.25/1.54  Subsumption          : 0.05
% 3.25/1.54  Abstraction          : 0.02
% 3.25/1.54  MUC search           : 0.00
% 3.25/1.54  Cooper               : 0.00
% 3.25/1.54  Total                : 0.73
% 3.25/1.54  Index Insertion      : 0.00
% 3.25/1.54  Index Deletion       : 0.00
% 3.25/1.54  Index Matching       : 0.00
% 3.25/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
