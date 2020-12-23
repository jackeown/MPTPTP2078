%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:26 EST 2020

% Result     : Theorem 2.82s
% Output     : CNFRefutation 2.82s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 115 expanded)
%              Number of leaves         :   47 (  62 expanded)
%              Depth                    :   12
%              Number of atoms          :  147 ( 275 expanded)
%              Number of equality atoms :   33 (  48 expanded)
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

tff(f_90,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_98,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

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

tff(f_86,axiom,(
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

tff(c_54,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_52,plain,(
    l1_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_81,plain,(
    ! [A_64] :
      ( u1_struct_0(A_64) = k2_struct_0(A_64)
      | ~ l1_struct_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_85,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_81])).

tff(c_139,plain,(
    ! [A_70] :
      ( ~ v1_xboole_0(u1_struct_0(A_70))
      | ~ l1_struct_0(A_70)
      | v2_struct_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_142,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_139])).

tff(c_144,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_142])).

tff(c_145,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_144])).

tff(c_48,plain,(
    v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_46,plain,(
    v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_44,plain,(
    v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_42,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))))) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_50,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_16,plain,(
    ! [A_14] : k2_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_18,plain,(
    ! [A_15] : k4_xboole_0(k1_xboole_0,A_15) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_206,plain,(
    ! [A_84,B_85] : k5_xboole_0(A_84,k4_xboole_0(B_85,A_84)) = k2_xboole_0(A_84,B_85) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_215,plain,(
    ! [A_15] : k5_xboole_0(A_15,k1_xboole_0) = k2_xboole_0(A_15,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_206])).

tff(c_218,plain,(
    ! [A_15] : k5_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_215])).

tff(c_22,plain,(
    ! [A_18,B_19] :
      ( r1_xboole_0(k1_tarski(A_18),B_19)
      | r2_hidden(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_28,plain,(
    ! [A_23] :
      ( r2_hidden('#skF_3'(A_23),A_23)
      | k1_xboole_0 = A_23 ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_162,plain,(
    ! [A_75,B_76,C_77] :
      ( ~ r1_xboole_0(A_75,B_76)
      | ~ r2_hidden(C_77,k3_xboole_0(A_75,B_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_190,plain,(
    ! [A_80,B_81] :
      ( ~ r1_xboole_0(A_80,B_81)
      | k3_xboole_0(A_80,B_81) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_28,c_162])).

tff(c_347,plain,(
    ! [A_107,B_108] :
      ( k3_xboole_0(k1_tarski(A_107),B_108) = k1_xboole_0
      | r2_hidden(A_107,B_108) ) ),
    inference(resolution,[status(thm)],[c_22,c_190])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_147,plain,(
    ! [A_73,B_74] : k5_xboole_0(A_73,k3_xboole_0(A_73,B_74)) = k4_xboole_0(A_73,B_74) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_159,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_147])).

tff(c_362,plain,(
    ! [B_108,A_107] :
      ( k4_xboole_0(B_108,k1_tarski(A_107)) = k5_xboole_0(B_108,k1_xboole_0)
      | r2_hidden(A_107,B_108) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_347,c_159])).

tff(c_400,plain,(
    ! [B_108,A_107] :
      ( k4_xboole_0(B_108,k1_tarski(A_107)) = B_108
      | r2_hidden(A_107,B_108) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_362])).

tff(c_330,plain,(
    ! [A_102,B_103,C_104] :
      ( k7_subset_1(A_102,B_103,C_104) = k4_xboole_0(B_103,C_104)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(A_102)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_333,plain,(
    ! [C_104] : k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))),'#skF_5',C_104) = k4_xboole_0('#skF_5',C_104) ),
    inference(resolution,[status(thm)],[c_42,c_330])).

tff(c_573,plain,(
    ! [A_127,B_128] :
      ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_127))),B_128,k1_tarski(k1_xboole_0)) = k2_yellow19(A_127,k3_yellow19(A_127,k2_struct_0(A_127),B_128))
      | ~ m1_subset_1(B_128,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_127)))))
      | ~ v13_waybel_0(B_128,k3_yellow_1(k2_struct_0(A_127)))
      | ~ v2_waybel_0(B_128,k3_yellow_1(k2_struct_0(A_127)))
      | v1_xboole_0(B_128)
      | ~ l1_struct_0(A_127)
      | v2_struct_0(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_575,plain,
    ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))),'#skF_5',k1_tarski(k1_xboole_0)) = k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
    | ~ v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | ~ v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | v1_xboole_0('#skF_5')
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_573])).

tff(c_578,plain,
    ( k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) = k4_xboole_0('#skF_5',k1_tarski(k1_xboole_0))
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_46,c_44,c_333,c_575])).

tff(c_579,plain,(
    k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) = k4_xboole_0('#skF_5',k1_tarski(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_50,c_578])).

tff(c_40,plain,(
    k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_594,plain,(
    k4_xboole_0('#skF_5',k1_tarski(k1_xboole_0)) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_579,c_40])).

tff(c_602,plain,(
    r2_hidden(k1_xboole_0,'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_400,c_594])).

tff(c_38,plain,(
    ! [C_57,B_55,A_51] :
      ( ~ v1_xboole_0(C_57)
      | ~ r2_hidden(C_57,B_55)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_51))))
      | ~ v13_waybel_0(B_55,k3_yellow_1(A_51))
      | ~ v2_waybel_0(B_55,k3_yellow_1(A_51))
      | ~ v1_subset_1(B_55,u1_struct_0(k3_yellow_1(A_51)))
      | v1_xboole_0(B_55)
      | v1_xboole_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_604,plain,(
    ! [A_51] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_51))))
      | ~ v13_waybel_0('#skF_5',k3_yellow_1(A_51))
      | ~ v2_waybel_0('#skF_5',k3_yellow_1(A_51))
      | ~ v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(A_51)))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_51) ) ),
    inference(resolution,[status(thm)],[c_602,c_38])).

tff(c_610,plain,(
    ! [A_51] :
      ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_51))))
      | ~ v13_waybel_0('#skF_5',k3_yellow_1(A_51))
      | ~ v2_waybel_0('#skF_5',k3_yellow_1(A_51))
      | ~ v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(A_51)))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_51) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_604])).

tff(c_622,plain,(
    ! [A_132] :
      ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_132))))
      | ~ v13_waybel_0('#skF_5',k3_yellow_1(A_132))
      | ~ v2_waybel_0('#skF_5',k3_yellow_1(A_132))
      | ~ v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(A_132)))
      | v1_xboole_0(A_132) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_610])).

tff(c_625,plain,
    ( ~ v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | ~ v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | ~ v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))))
    | v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_42,c_622])).

tff(c_628,plain,(
    v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_625])).

tff(c_630,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_145,c_628])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:22:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.82/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.82/1.39  
% 2.82/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.82/1.39  %$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_yellow19 > k2_xboole_0 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_lattice3 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2
% 2.82/1.39  
% 2.82/1.39  %Foreground sorts:
% 2.82/1.39  
% 2.82/1.39  
% 2.82/1.39  %Background operators:
% 2.82/1.39  
% 2.82/1.39  
% 2.82/1.39  %Foreground operators:
% 2.82/1.39  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.82/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.82/1.39  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 2.82/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.82/1.39  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.82/1.39  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.82/1.39  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 2.82/1.39  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.82/1.39  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.82/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.82/1.39  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 2.82/1.39  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.82/1.39  tff('#skF_5', type, '#skF_5': $i).
% 2.82/1.39  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.82/1.39  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 2.82/1.39  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 2.82/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.82/1.39  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.82/1.39  tff(k2_yellow19, type, k2_yellow19: ($i * $i) > $i).
% 2.82/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.82/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.82/1.39  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.82/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.82/1.39  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.82/1.39  tff(k3_yellow19, type, k3_yellow19: ($i * $i * $i) > $i).
% 2.82/1.39  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 2.82/1.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.82/1.39  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.82/1.39  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.82/1.39  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.82/1.39  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.82/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.82/1.39  
% 2.82/1.40  tff(f_158, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (B = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_yellow19)).
% 2.82/1.40  tff(f_90, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 2.82/1.40  tff(f_98, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.82/1.40  tff(f_34, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.82/1.40  tff(f_52, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.82/1.40  tff(f_54, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 2.82/1.40  tff(f_56, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.82/1.40  tff(f_61, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.82/1.40  tff(f_86, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F, G]: (((((r2_hidden(C, D) & r2_hidden(D, E)) & r2_hidden(E, F)) & r2_hidden(F, G)) & r2_hidden(G, B)) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_mcart_1)).
% 2.82/1.40  tff(f_48, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.82/1.40  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.82/1.40  tff(f_50, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.82/1.40  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 2.82/1.40  tff(f_117, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))), B, k1_tarski(k1_xboole_0)) = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_yellow19)).
% 2.82/1.40  tff(f_138, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(A)))) & v2_waybel_0(B, k3_yellow_1(A))) & v13_waybel_0(B, k3_yellow_1(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A))))) => (![C]: ~(r2_hidden(C, B) & v1_xboole_0(C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_yellow19)).
% 2.82/1.40  tff(c_54, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_158])).
% 2.82/1.40  tff(c_52, plain, (l1_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_158])).
% 2.82/1.40  tff(c_81, plain, (![A_64]: (u1_struct_0(A_64)=k2_struct_0(A_64) | ~l1_struct_0(A_64))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.82/1.40  tff(c_85, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_52, c_81])).
% 2.82/1.40  tff(c_139, plain, (![A_70]: (~v1_xboole_0(u1_struct_0(A_70)) | ~l1_struct_0(A_70) | v2_struct_0(A_70))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.82/1.40  tff(c_142, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_85, c_139])).
% 2.82/1.40  tff(c_144, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_142])).
% 2.82/1.40  tff(c_145, plain, (~v1_xboole_0(k2_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_54, c_144])).
% 2.82/1.40  tff(c_48, plain, (v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_158])).
% 2.82/1.40  tff(c_46, plain, (v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_158])).
% 2.82/1.40  tff(c_44, plain, (v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_158])).
% 2.82/1.40  tff(c_42, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4')))))), inference(cnfTransformation, [status(thm)], [f_158])).
% 2.82/1.40  tff(c_50, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_158])).
% 2.82/1.40  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.82/1.40  tff(c_16, plain, (![A_14]: (k2_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.82/1.40  tff(c_18, plain, (![A_15]: (k4_xboole_0(k1_xboole_0, A_15)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.82/1.40  tff(c_206, plain, (![A_84, B_85]: (k5_xboole_0(A_84, k4_xboole_0(B_85, A_84))=k2_xboole_0(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.82/1.40  tff(c_215, plain, (![A_15]: (k5_xboole_0(A_15, k1_xboole_0)=k2_xboole_0(A_15, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_206])).
% 2.82/1.40  tff(c_218, plain, (![A_15]: (k5_xboole_0(A_15, k1_xboole_0)=A_15)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_215])).
% 2.82/1.40  tff(c_22, plain, (![A_18, B_19]: (r1_xboole_0(k1_tarski(A_18), B_19) | r2_hidden(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.82/1.40  tff(c_28, plain, (![A_23]: (r2_hidden('#skF_3'(A_23), A_23) | k1_xboole_0=A_23)), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.82/1.40  tff(c_162, plain, (![A_75, B_76, C_77]: (~r1_xboole_0(A_75, B_76) | ~r2_hidden(C_77, k3_xboole_0(A_75, B_76)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.82/1.40  tff(c_190, plain, (![A_80, B_81]: (~r1_xboole_0(A_80, B_81) | k3_xboole_0(A_80, B_81)=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_162])).
% 2.82/1.40  tff(c_347, plain, (![A_107, B_108]: (k3_xboole_0(k1_tarski(A_107), B_108)=k1_xboole_0 | r2_hidden(A_107, B_108))), inference(resolution, [status(thm)], [c_22, c_190])).
% 2.82/1.40  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.82/1.40  tff(c_147, plain, (![A_73, B_74]: (k5_xboole_0(A_73, k3_xboole_0(A_73, B_74))=k4_xboole_0(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.82/1.40  tff(c_159, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_147])).
% 2.82/1.40  tff(c_362, plain, (![B_108, A_107]: (k4_xboole_0(B_108, k1_tarski(A_107))=k5_xboole_0(B_108, k1_xboole_0) | r2_hidden(A_107, B_108))), inference(superposition, [status(thm), theory('equality')], [c_347, c_159])).
% 2.82/1.40  tff(c_400, plain, (![B_108, A_107]: (k4_xboole_0(B_108, k1_tarski(A_107))=B_108 | r2_hidden(A_107, B_108))), inference(demodulation, [status(thm), theory('equality')], [c_218, c_362])).
% 2.82/1.40  tff(c_330, plain, (![A_102, B_103, C_104]: (k7_subset_1(A_102, B_103, C_104)=k4_xboole_0(B_103, C_104) | ~m1_subset_1(B_103, k1_zfmisc_1(A_102)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.82/1.40  tff(c_333, plain, (![C_104]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))), '#skF_5', C_104)=k4_xboole_0('#skF_5', C_104))), inference(resolution, [status(thm)], [c_42, c_330])).
% 2.82/1.40  tff(c_573, plain, (![A_127, B_128]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_127))), B_128, k1_tarski(k1_xboole_0))=k2_yellow19(A_127, k3_yellow19(A_127, k2_struct_0(A_127), B_128)) | ~m1_subset_1(B_128, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_127))))) | ~v13_waybel_0(B_128, k3_yellow_1(k2_struct_0(A_127))) | ~v2_waybel_0(B_128, k3_yellow_1(k2_struct_0(A_127))) | v1_xboole_0(B_128) | ~l1_struct_0(A_127) | v2_struct_0(A_127))), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.82/1.40  tff(c_575, plain, (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))), '#skF_5', k1_tarski(k1_xboole_0))=k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | ~v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | v1_xboole_0('#skF_5') | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_42, c_573])).
% 2.82/1.40  tff(c_578, plain, (k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))=k4_xboole_0('#skF_5', k1_tarski(k1_xboole_0)) | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_46, c_44, c_333, c_575])).
% 2.82/1.40  tff(c_579, plain, (k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))=k4_xboole_0('#skF_5', k1_tarski(k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_54, c_50, c_578])).
% 2.82/1.40  tff(c_40, plain, (k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_158])).
% 2.82/1.40  tff(c_594, plain, (k4_xboole_0('#skF_5', k1_tarski(k1_xboole_0))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_579, c_40])).
% 2.82/1.40  tff(c_602, plain, (r2_hidden(k1_xboole_0, '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_400, c_594])).
% 2.82/1.40  tff(c_38, plain, (![C_57, B_55, A_51]: (~v1_xboole_0(C_57) | ~r2_hidden(C_57, B_55) | ~m1_subset_1(B_55, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_51)))) | ~v13_waybel_0(B_55, k3_yellow_1(A_51)) | ~v2_waybel_0(B_55, k3_yellow_1(A_51)) | ~v1_subset_1(B_55, u1_struct_0(k3_yellow_1(A_51))) | v1_xboole_0(B_55) | v1_xboole_0(A_51))), inference(cnfTransformation, [status(thm)], [f_138])).
% 2.82/1.40  tff(c_604, plain, (![A_51]: (~v1_xboole_0(k1_xboole_0) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_51)))) | ~v13_waybel_0('#skF_5', k3_yellow_1(A_51)) | ~v2_waybel_0('#skF_5', k3_yellow_1(A_51)) | ~v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(A_51))) | v1_xboole_0('#skF_5') | v1_xboole_0(A_51))), inference(resolution, [status(thm)], [c_602, c_38])).
% 2.82/1.40  tff(c_610, plain, (![A_51]: (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_51)))) | ~v13_waybel_0('#skF_5', k3_yellow_1(A_51)) | ~v2_waybel_0('#skF_5', k3_yellow_1(A_51)) | ~v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(A_51))) | v1_xboole_0('#skF_5') | v1_xboole_0(A_51))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_604])).
% 2.82/1.40  tff(c_622, plain, (![A_132]: (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_132)))) | ~v13_waybel_0('#skF_5', k3_yellow_1(A_132)) | ~v2_waybel_0('#skF_5', k3_yellow_1(A_132)) | ~v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(A_132))) | v1_xboole_0(A_132))), inference(negUnitSimplification, [status(thm)], [c_50, c_610])).
% 2.82/1.40  tff(c_625, plain, (~v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4')))) | v1_xboole_0(k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_42, c_622])).
% 2.82/1.40  tff(c_628, plain, (v1_xboole_0(k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_625])).
% 2.82/1.40  tff(c_630, plain, $false, inference(negUnitSimplification, [status(thm)], [c_145, c_628])).
% 2.82/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.82/1.40  
% 2.82/1.40  Inference rules
% 2.82/1.40  ----------------------
% 2.82/1.40  #Ref     : 0
% 2.82/1.40  #Sup     : 138
% 2.82/1.40  #Fact    : 0
% 2.82/1.40  #Define  : 0
% 2.82/1.40  #Split   : 1
% 2.82/1.40  #Chain   : 0
% 2.82/1.40  #Close   : 0
% 2.82/1.40  
% 2.82/1.40  Ordering : KBO
% 2.82/1.40  
% 2.82/1.40  Simplification rules
% 2.82/1.40  ----------------------
% 2.82/1.40  #Subsume      : 44
% 2.82/1.40  #Demod        : 27
% 2.82/1.40  #Tautology    : 61
% 2.82/1.40  #SimpNegUnit  : 4
% 2.82/1.40  #BackRed      : 1
% 2.82/1.40  
% 2.82/1.41  #Partial instantiations: 0
% 2.82/1.41  #Strategies tried      : 1
% 2.82/1.41  
% 2.82/1.41  Timing (in seconds)
% 2.82/1.41  ----------------------
% 2.82/1.41  Preprocessing        : 0.34
% 2.82/1.41  Parsing              : 0.19
% 2.82/1.41  CNF conversion       : 0.02
% 2.82/1.41  Main loop            : 0.30
% 2.82/1.41  Inferencing          : 0.11
% 2.82/1.41  Reduction            : 0.09
% 2.82/1.41  Demodulation         : 0.07
% 2.82/1.41  BG Simplification    : 0.02
% 2.82/1.41  Subsumption          : 0.05
% 2.82/1.41  Abstraction          : 0.02
% 2.82/1.41  MUC search           : 0.00
% 2.82/1.41  Cooper               : 0.00
% 2.82/1.41  Total                : 0.67
% 2.82/1.41  Index Insertion      : 0.00
% 2.82/1.41  Index Deletion       : 0.00
% 2.82/1.41  Index Matching       : 0.00
% 2.82/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
