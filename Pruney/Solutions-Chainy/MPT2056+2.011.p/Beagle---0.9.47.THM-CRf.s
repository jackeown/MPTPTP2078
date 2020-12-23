%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:26 EST 2020

% Result     : Theorem 3.15s
% Output     : CNFRefutation 3.23s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 121 expanded)
%              Number of leaves         :   46 (  64 expanded)
%              Depth                    :   13
%              Number of atoms          :  147 ( 294 expanded)
%              Number of equality atoms :   31 (  50 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_yellow19 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_lattice3 > k1_xboole_0 > #skF_4 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_166,negated_conjecture,(
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

tff(f_98,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_106,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_34,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_52,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_54,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_94,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_mcart_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_125,axiom,(
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

tff(f_146,axiom,(
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

tff(c_56,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_54,plain,(
    l1_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_127,plain,(
    ! [A_70] :
      ( u1_struct_0(A_70) = k2_struct_0(A_70)
      | ~ l1_struct_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_131,plain,(
    u1_struct_0('#skF_5') = k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_127])).

tff(c_141,plain,(
    ! [A_72] :
      ( ~ v1_xboole_0(u1_struct_0(A_72))
      | ~ l1_struct_0(A_72)
      | v2_struct_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_144,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_5'))
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_141])).

tff(c_146,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_5'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_144])).

tff(c_147,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_146])).

tff(c_50,plain,(
    v1_subset_1('#skF_6',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_48,plain,(
    v2_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_46,plain,(
    v13_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_44,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_52,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_16,plain,(
    ! [A_14] : k4_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_18,plain,(
    ! [A_15] : r1_xboole_0(A_15,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_30,plain,(
    ! [A_23] :
      ( r2_hidden('#skF_4'(A_23),A_23)
      | k1_xboole_0 = A_23 ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_164,plain,(
    ! [A_77,B_78,C_79] :
      ( ~ r1_xboole_0(A_77,B_78)
      | ~ r2_hidden(C_79,k3_xboole_0(A_77,B_78)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_186,plain,(
    ! [A_80,B_81] :
      ( ~ r1_xboole_0(A_80,B_81)
      | k3_xboole_0(A_80,B_81) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_30,c_164])).

tff(c_200,plain,(
    ! [A_82] : k3_xboole_0(A_82,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_186])).

tff(c_14,plain,(
    ! [A_12,B_13] : k5_xboole_0(A_12,k3_xboole_0(A_12,B_13)) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_208,plain,(
    ! [A_82] : k5_xboole_0(A_82,k1_xboole_0) = k4_xboole_0(A_82,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_14])).

tff(c_228,plain,(
    ! [A_82] : k5_xboole_0(A_82,k1_xboole_0) = A_82 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_208])).

tff(c_20,plain,(
    ! [A_16,B_17] :
      ( r1_xboole_0(k1_tarski(A_16),B_17)
      | r2_hidden(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_698,plain,(
    ! [A_127,B_128] :
      ( k3_xboole_0(k1_tarski(A_127),B_128) = k1_xboole_0
      | r2_hidden(A_127,B_128) ) ),
    inference(resolution,[status(thm)],[c_20,c_186])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_149,plain,(
    ! [A_75,B_76] : k5_xboole_0(A_75,k3_xboole_0(A_75,B_76)) = k4_xboole_0(A_75,B_76) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_158,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_149])).

tff(c_704,plain,(
    ! [B_128,A_127] :
      ( k4_xboole_0(B_128,k1_tarski(A_127)) = k5_xboole_0(B_128,k1_xboole_0)
      | r2_hidden(A_127,B_128) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_698,c_158])).

tff(c_923,plain,(
    ! [B_134,A_135] :
      ( k4_xboole_0(B_134,k1_tarski(A_135)) = B_134
      | r2_hidden(A_135,B_134) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_704])).

tff(c_329,plain,(
    ! [A_89,B_90,C_91] :
      ( k7_subset_1(A_89,B_90,C_91) = k4_xboole_0(B_90,C_91)
      | ~ m1_subset_1(B_90,k1_zfmisc_1(A_89)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_332,plain,(
    ! [C_91] : k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))),'#skF_6',C_91) = k4_xboole_0('#skF_6',C_91) ),
    inference(resolution,[status(thm)],[c_44,c_329])).

tff(c_607,plain,(
    ! [A_120,B_121] :
      ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_120))),B_121,k1_tarski(k1_xboole_0)) = k2_yellow19(A_120,k3_yellow19(A_120,k2_struct_0(A_120),B_121))
      | ~ m1_subset_1(B_121,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_120)))))
      | ~ v13_waybel_0(B_121,k3_yellow_1(k2_struct_0(A_120)))
      | ~ v2_waybel_0(B_121,k3_yellow_1(k2_struct_0(A_120)))
      | v1_xboole_0(B_121)
      | ~ l1_struct_0(A_120)
      | v2_struct_0(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_609,plain,
    ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))),'#skF_6',k1_tarski(k1_xboole_0)) = k2_yellow19('#skF_5',k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6'))
    | ~ v13_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5')))
    | ~ v2_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5')))
    | v1_xboole_0('#skF_6')
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_607])).

tff(c_612,plain,
    ( k2_yellow19('#skF_5',k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6')) = k4_xboole_0('#skF_6',k1_tarski(k1_xboole_0))
    | v1_xboole_0('#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_48,c_46,c_332,c_609])).

tff(c_613,plain,(
    k2_yellow19('#skF_5',k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6')) = k4_xboole_0('#skF_6',k1_tarski(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_52,c_612])).

tff(c_42,plain,(
    k2_yellow19('#skF_5',k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6')) != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_692,plain,(
    k4_xboole_0('#skF_6',k1_tarski(k1_xboole_0)) != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_613,c_42])).

tff(c_951,plain,(
    r2_hidden(k1_xboole_0,'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_923,c_692])).

tff(c_40,plain,(
    ! [C_57,B_55,A_51] :
      ( ~ v1_xboole_0(C_57)
      | ~ r2_hidden(C_57,B_55)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_51))))
      | ~ v13_waybel_0(B_55,k3_yellow_1(A_51))
      | ~ v2_waybel_0(B_55,k3_yellow_1(A_51))
      | ~ v1_subset_1(B_55,u1_struct_0(k3_yellow_1(A_51)))
      | v1_xboole_0(B_55)
      | v1_xboole_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_959,plain,(
    ! [A_51] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_51))))
      | ~ v13_waybel_0('#skF_6',k3_yellow_1(A_51))
      | ~ v2_waybel_0('#skF_6',k3_yellow_1(A_51))
      | ~ v1_subset_1('#skF_6',u1_struct_0(k3_yellow_1(A_51)))
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(A_51) ) ),
    inference(resolution,[status(thm)],[c_951,c_40])).

tff(c_965,plain,(
    ! [A_51] :
      ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_51))))
      | ~ v13_waybel_0('#skF_6',k3_yellow_1(A_51))
      | ~ v2_waybel_0('#skF_6',k3_yellow_1(A_51))
      | ~ v1_subset_1('#skF_6',u1_struct_0(k3_yellow_1(A_51)))
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(A_51) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_959])).

tff(c_968,plain,(
    ! [A_136] :
      ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_136))))
      | ~ v13_waybel_0('#skF_6',k3_yellow_1(A_136))
      | ~ v2_waybel_0('#skF_6',k3_yellow_1(A_136))
      | ~ v1_subset_1('#skF_6',u1_struct_0(k3_yellow_1(A_136)))
      | v1_xboole_0(A_136) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_965])).

tff(c_971,plain,
    ( ~ v13_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5')))
    | ~ v2_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5')))
    | ~ v1_subset_1('#skF_6',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))
    | v1_xboole_0(k2_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_44,c_968])).

tff(c_974,plain,(
    v1_xboole_0(k2_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_971])).

tff(c_976,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_147,c_974])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:17:45 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.15/1.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.15/1.52  
% 3.15/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.15/1.53  %$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_yellow19 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_lattice3 > k1_xboole_0 > #skF_4 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2
% 3.15/1.53  
% 3.15/1.53  %Foreground sorts:
% 3.15/1.53  
% 3.15/1.53  
% 3.15/1.53  %Background operators:
% 3.15/1.53  
% 3.15/1.53  
% 3.15/1.53  %Foreground operators:
% 3.15/1.53  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.15/1.53  tff('#skF_4', type, '#skF_4': $i > $i).
% 3.15/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.15/1.53  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 3.15/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.15/1.53  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.15/1.53  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.15/1.53  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 3.15/1.53  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.15/1.53  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.15/1.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.15/1.53  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 3.15/1.53  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.15/1.53  tff('#skF_5', type, '#skF_5': $i).
% 3.15/1.53  tff('#skF_6', type, '#skF_6': $i).
% 3.15/1.53  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.15/1.53  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 3.15/1.53  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 3.15/1.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.15/1.53  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.15/1.53  tff(k2_yellow19, type, k2_yellow19: ($i * $i) > $i).
% 3.15/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.15/1.53  tff('#skF_3', type, '#skF_3': $i > $i).
% 3.15/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.15/1.53  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.15/1.53  tff(k3_yellow19, type, k3_yellow19: ($i * $i * $i) > $i).
% 3.15/1.53  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 3.15/1.53  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.15/1.53  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.15/1.53  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.15/1.53  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.15/1.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.15/1.53  
% 3.23/1.54  tff(f_166, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (B = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_yellow19)).
% 3.23/1.54  tff(f_98, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.23/1.54  tff(f_106, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.23/1.54  tff(f_34, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.23/1.54  tff(f_52, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.23/1.54  tff(f_54, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.23/1.54  tff(f_94, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F, G]: (((((r2_hidden(C, D) & r2_hidden(D, E)) & r2_hidden(E, F)) & r2_hidden(F, G)) & r2_hidden(G, B)) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_mcart_1)).
% 3.23/1.54  tff(f_48, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.23/1.54  tff(f_50, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.23/1.54  tff(f_59, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.23/1.54  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.23/1.54  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 3.23/1.54  tff(f_125, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))), B, k1_tarski(k1_xboole_0)) = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_yellow19)).
% 3.23/1.54  tff(f_146, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(A)))) & v2_waybel_0(B, k3_yellow_1(A))) & v13_waybel_0(B, k3_yellow_1(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A))))) => (![C]: ~(r2_hidden(C, B) & v1_xboole_0(C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_yellow19)).
% 3.23/1.54  tff(c_56, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_166])).
% 3.23/1.54  tff(c_54, plain, (l1_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_166])).
% 3.23/1.54  tff(c_127, plain, (![A_70]: (u1_struct_0(A_70)=k2_struct_0(A_70) | ~l1_struct_0(A_70))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.23/1.54  tff(c_131, plain, (u1_struct_0('#skF_5')=k2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_54, c_127])).
% 3.23/1.54  tff(c_141, plain, (![A_72]: (~v1_xboole_0(u1_struct_0(A_72)) | ~l1_struct_0(A_72) | v2_struct_0(A_72))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.23/1.54  tff(c_144, plain, (~v1_xboole_0(k2_struct_0('#skF_5')) | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_131, c_141])).
% 3.23/1.54  tff(c_146, plain, (~v1_xboole_0(k2_struct_0('#skF_5')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_144])).
% 3.23/1.54  tff(c_147, plain, (~v1_xboole_0(k2_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_56, c_146])).
% 3.23/1.54  tff(c_50, plain, (v1_subset_1('#skF_6', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))), inference(cnfTransformation, [status(thm)], [f_166])).
% 3.23/1.54  tff(c_48, plain, (v2_waybel_0('#skF_6', k3_yellow_1(k2_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_166])).
% 3.23/1.54  tff(c_46, plain, (v13_waybel_0('#skF_6', k3_yellow_1(k2_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_166])).
% 3.23/1.54  tff(c_44, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))))), inference(cnfTransformation, [status(thm)], [f_166])).
% 3.23/1.54  tff(c_52, plain, (~v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_166])).
% 3.23/1.54  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.23/1.54  tff(c_16, plain, (![A_14]: (k4_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.23/1.54  tff(c_18, plain, (![A_15]: (r1_xboole_0(A_15, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.23/1.54  tff(c_30, plain, (![A_23]: (r2_hidden('#skF_4'(A_23), A_23) | k1_xboole_0=A_23)), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.23/1.54  tff(c_164, plain, (![A_77, B_78, C_79]: (~r1_xboole_0(A_77, B_78) | ~r2_hidden(C_79, k3_xboole_0(A_77, B_78)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.23/1.54  tff(c_186, plain, (![A_80, B_81]: (~r1_xboole_0(A_80, B_81) | k3_xboole_0(A_80, B_81)=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_164])).
% 3.23/1.54  tff(c_200, plain, (![A_82]: (k3_xboole_0(A_82, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_186])).
% 3.23/1.54  tff(c_14, plain, (![A_12, B_13]: (k5_xboole_0(A_12, k3_xboole_0(A_12, B_13))=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.23/1.54  tff(c_208, plain, (![A_82]: (k5_xboole_0(A_82, k1_xboole_0)=k4_xboole_0(A_82, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_200, c_14])).
% 3.23/1.54  tff(c_228, plain, (![A_82]: (k5_xboole_0(A_82, k1_xboole_0)=A_82)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_208])).
% 3.23/1.54  tff(c_20, plain, (![A_16, B_17]: (r1_xboole_0(k1_tarski(A_16), B_17) | r2_hidden(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.23/1.54  tff(c_698, plain, (![A_127, B_128]: (k3_xboole_0(k1_tarski(A_127), B_128)=k1_xboole_0 | r2_hidden(A_127, B_128))), inference(resolution, [status(thm)], [c_20, c_186])).
% 3.23/1.54  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.23/1.54  tff(c_149, plain, (![A_75, B_76]: (k5_xboole_0(A_75, k3_xboole_0(A_75, B_76))=k4_xboole_0(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.23/1.54  tff(c_158, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_149])).
% 3.23/1.54  tff(c_704, plain, (![B_128, A_127]: (k4_xboole_0(B_128, k1_tarski(A_127))=k5_xboole_0(B_128, k1_xboole_0) | r2_hidden(A_127, B_128))), inference(superposition, [status(thm), theory('equality')], [c_698, c_158])).
% 3.23/1.54  tff(c_923, plain, (![B_134, A_135]: (k4_xboole_0(B_134, k1_tarski(A_135))=B_134 | r2_hidden(A_135, B_134))), inference(demodulation, [status(thm), theory('equality')], [c_228, c_704])).
% 3.23/1.54  tff(c_329, plain, (![A_89, B_90, C_91]: (k7_subset_1(A_89, B_90, C_91)=k4_xboole_0(B_90, C_91) | ~m1_subset_1(B_90, k1_zfmisc_1(A_89)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.23/1.54  tff(c_332, plain, (![C_91]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))), '#skF_6', C_91)=k4_xboole_0('#skF_6', C_91))), inference(resolution, [status(thm)], [c_44, c_329])).
% 3.23/1.54  tff(c_607, plain, (![A_120, B_121]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_120))), B_121, k1_tarski(k1_xboole_0))=k2_yellow19(A_120, k3_yellow19(A_120, k2_struct_0(A_120), B_121)) | ~m1_subset_1(B_121, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_120))))) | ~v13_waybel_0(B_121, k3_yellow_1(k2_struct_0(A_120))) | ~v2_waybel_0(B_121, k3_yellow_1(k2_struct_0(A_120))) | v1_xboole_0(B_121) | ~l1_struct_0(A_120) | v2_struct_0(A_120))), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.23/1.54  tff(c_609, plain, (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))), '#skF_6', k1_tarski(k1_xboole_0))=k2_yellow19('#skF_5', k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6')) | ~v13_waybel_0('#skF_6', k3_yellow_1(k2_struct_0('#skF_5'))) | ~v2_waybel_0('#skF_6', k3_yellow_1(k2_struct_0('#skF_5'))) | v1_xboole_0('#skF_6') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_44, c_607])).
% 3.23/1.54  tff(c_612, plain, (k2_yellow19('#skF_5', k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6'))=k4_xboole_0('#skF_6', k1_tarski(k1_xboole_0)) | v1_xboole_0('#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_48, c_46, c_332, c_609])).
% 3.23/1.54  tff(c_613, plain, (k2_yellow19('#skF_5', k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6'))=k4_xboole_0('#skF_6', k1_tarski(k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_56, c_52, c_612])).
% 3.23/1.54  tff(c_42, plain, (k2_yellow19('#skF_5', k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6'))!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_166])).
% 3.23/1.54  tff(c_692, plain, (k4_xboole_0('#skF_6', k1_tarski(k1_xboole_0))!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_613, c_42])).
% 3.23/1.54  tff(c_951, plain, (r2_hidden(k1_xboole_0, '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_923, c_692])).
% 3.23/1.54  tff(c_40, plain, (![C_57, B_55, A_51]: (~v1_xboole_0(C_57) | ~r2_hidden(C_57, B_55) | ~m1_subset_1(B_55, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_51)))) | ~v13_waybel_0(B_55, k3_yellow_1(A_51)) | ~v2_waybel_0(B_55, k3_yellow_1(A_51)) | ~v1_subset_1(B_55, u1_struct_0(k3_yellow_1(A_51))) | v1_xboole_0(B_55) | v1_xboole_0(A_51))), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.23/1.54  tff(c_959, plain, (![A_51]: (~v1_xboole_0(k1_xboole_0) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_51)))) | ~v13_waybel_0('#skF_6', k3_yellow_1(A_51)) | ~v2_waybel_0('#skF_6', k3_yellow_1(A_51)) | ~v1_subset_1('#skF_6', u1_struct_0(k3_yellow_1(A_51))) | v1_xboole_0('#skF_6') | v1_xboole_0(A_51))), inference(resolution, [status(thm)], [c_951, c_40])).
% 3.23/1.54  tff(c_965, plain, (![A_51]: (~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_51)))) | ~v13_waybel_0('#skF_6', k3_yellow_1(A_51)) | ~v2_waybel_0('#skF_6', k3_yellow_1(A_51)) | ~v1_subset_1('#skF_6', u1_struct_0(k3_yellow_1(A_51))) | v1_xboole_0('#skF_6') | v1_xboole_0(A_51))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_959])).
% 3.23/1.54  tff(c_968, plain, (![A_136]: (~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_136)))) | ~v13_waybel_0('#skF_6', k3_yellow_1(A_136)) | ~v2_waybel_0('#skF_6', k3_yellow_1(A_136)) | ~v1_subset_1('#skF_6', u1_struct_0(k3_yellow_1(A_136))) | v1_xboole_0(A_136))), inference(negUnitSimplification, [status(thm)], [c_52, c_965])).
% 3.23/1.54  tff(c_971, plain, (~v13_waybel_0('#skF_6', k3_yellow_1(k2_struct_0('#skF_5'))) | ~v2_waybel_0('#skF_6', k3_yellow_1(k2_struct_0('#skF_5'))) | ~v1_subset_1('#skF_6', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))) | v1_xboole_0(k2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_44, c_968])).
% 3.23/1.54  tff(c_974, plain, (v1_xboole_0(k2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_971])).
% 3.23/1.54  tff(c_976, plain, $false, inference(negUnitSimplification, [status(thm)], [c_147, c_974])).
% 3.23/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.23/1.54  
% 3.23/1.54  Inference rules
% 3.23/1.54  ----------------------
% 3.23/1.54  #Ref     : 0
% 3.23/1.54  #Sup     : 211
% 3.23/1.54  #Fact    : 0
% 3.23/1.54  #Define  : 0
% 3.23/1.54  #Split   : 0
% 3.23/1.54  #Chain   : 0
% 3.23/1.54  #Close   : 0
% 3.23/1.54  
% 3.23/1.54  Ordering : KBO
% 3.23/1.54  
% 3.23/1.54  Simplification rules
% 3.23/1.54  ----------------------
% 3.23/1.54  #Subsume      : 53
% 3.23/1.54  #Demod        : 74
% 3.23/1.54  #Tautology    : 109
% 3.23/1.54  #SimpNegUnit  : 20
% 3.23/1.54  #BackRed      : 1
% 3.23/1.54  
% 3.23/1.54  #Partial instantiations: 0
% 3.23/1.54  #Strategies tried      : 1
% 3.23/1.54  
% 3.23/1.54  Timing (in seconds)
% 3.23/1.54  ----------------------
% 3.23/1.55  Preprocessing        : 0.36
% 3.23/1.55  Parsing              : 0.20
% 3.23/1.55  CNF conversion       : 0.02
% 3.23/1.55  Main loop            : 0.33
% 3.23/1.55  Inferencing          : 0.13
% 3.23/1.55  Reduction            : 0.11
% 3.23/1.55  Demodulation         : 0.08
% 3.23/1.55  BG Simplification    : 0.02
% 3.23/1.55  Subsumption          : 0.05
% 3.23/1.55  Abstraction          : 0.02
% 3.23/1.55  MUC search           : 0.00
% 3.23/1.55  Cooper               : 0.00
% 3.23/1.55  Total                : 0.73
% 3.23/1.55  Index Insertion      : 0.00
% 3.23/1.55  Index Deletion       : 0.00
% 3.23/1.55  Index Matching       : 0.00
% 3.23/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
