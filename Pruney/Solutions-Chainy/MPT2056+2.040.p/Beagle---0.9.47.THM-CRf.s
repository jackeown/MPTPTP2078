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
% DateTime   : Thu Dec  3 10:31:30 EST 2020

% Result     : Theorem 2.83s
% Output     : CNFRefutation 3.19s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 239 expanded)
%              Number of leaves         :   46 ( 105 expanded)
%              Depth                    :   15
%              Number of atoms          :  167 ( 628 expanded)
%              Number of equality atoms :   40 ( 135 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_yellow19 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_lattice3 > k1_xboole_0 > #skF_5 > #skF_4 > #skF_3 > #skF_2 > #skF_1

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_160,negated_conjecture,(
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

tff(f_92,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_100,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_119,axiom,(
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

tff(f_62,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_64,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_88,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_mcart_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_74,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_140,axiom,(
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

tff(c_54,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_52,plain,(
    l1_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_75,plain,(
    ! [A_42] :
      ( u1_struct_0(A_42) = k2_struct_0(A_42)
      | ~ l1_struct_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_79,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_75])).

tff(c_86,plain,(
    ! [A_46] :
      ( ~ v1_xboole_0(u1_struct_0(A_46))
      | ~ l1_struct_0(A_46)
      | v2_struct_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_89,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_86])).

tff(c_91,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_89])).

tff(c_92,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_91])).

tff(c_48,plain,(
    v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_46,plain,(
    v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_44,plain,(
    v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_42,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))))) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_50,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_611,plain,(
    ! [A_97,B_98,C_99] :
      ( k7_subset_1(A_97,B_98,C_99) = k4_xboole_0(B_98,C_99)
      | ~ m1_subset_1(B_98,k1_zfmisc_1(A_97)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_614,plain,(
    ! [C_99] : k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))),'#skF_5',C_99) = k4_xboole_0('#skF_5',C_99) ),
    inference(resolution,[status(thm)],[c_42,c_611])).

tff(c_937,plain,(
    ! [A_121,B_122] :
      ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_121))),B_122,k1_tarski(k1_xboole_0)) = k2_yellow19(A_121,k3_yellow19(A_121,k2_struct_0(A_121),B_122))
      | ~ m1_subset_1(B_122,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_121)))))
      | ~ v13_waybel_0(B_122,k3_yellow_1(k2_struct_0(A_121)))
      | ~ v2_waybel_0(B_122,k3_yellow_1(k2_struct_0(A_121)))
      | v1_xboole_0(B_122)
      | ~ l1_struct_0(A_121)
      | v2_struct_0(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_939,plain,
    ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))),'#skF_5',k1_tarski(k1_xboole_0)) = k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
    | ~ v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | ~ v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | v1_xboole_0('#skF_5')
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_937])).

tff(c_942,plain,
    ( k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) = k4_xboole_0('#skF_5',k1_tarski(k1_xboole_0))
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_46,c_44,c_614,c_939])).

tff(c_943,plain,(
    k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) = k4_xboole_0('#skF_5',k1_tarski(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_50,c_942])).

tff(c_40,plain,(
    k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_1133,plain,(
    k4_xboole_0('#skF_5',k1_tarski(k1_xboole_0)) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_943,c_40])).

tff(c_16,plain,(
    ! [A_13] : k4_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_18,plain,(
    ! [A_14] : r1_xboole_0(A_14,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_28,plain,(
    ! [A_22] :
      ( r2_hidden('#skF_3'(A_22),A_22)
      | k1_xboole_0 = A_22 ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_144,plain,(
    ! [A_55,B_56,C_57] :
      ( ~ r1_xboole_0(A_55,B_56)
      | ~ r2_hidden(C_57,k3_xboole_0(A_55,B_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_155,plain,(
    ! [A_58,B_59] :
      ( ~ r1_xboole_0(A_58,B_59)
      | k3_xboole_0(A_58,B_59) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_28,c_144])).

tff(c_167,plain,(
    ! [A_14] : k3_xboole_0(A_14,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_155])).

tff(c_222,plain,(
    ! [A_64,B_65] : k5_xboole_0(A_64,k3_xboole_0(A_64,B_65)) = k4_xboole_0(A_64,B_65) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_234,plain,(
    ! [A_14] : k5_xboole_0(A_14,k1_xboole_0) = k4_xboole_0(A_14,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_222])).

tff(c_237,plain,(
    ! [A_14] : k5_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_234])).

tff(c_132,plain,(
    ! [A_53,B_54] :
      ( r2_hidden('#skF_1'(A_53,B_54),B_54)
      | r1_xboole_0(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_22,plain,(
    ! [A_17,B_18] :
      ( r1_xboole_0(k1_tarski(A_17),k1_tarski(B_18))
      | B_18 = A_17 ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_93,plain,(
    ! [A_47,B_48] :
      ( ~ r2_hidden(A_47,B_48)
      | ~ r1_xboole_0(k1_tarski(A_47),B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_101,plain,(
    ! [A_17,B_18] :
      ( ~ r2_hidden(A_17,k1_tarski(B_18))
      | B_18 = A_17 ) ),
    inference(resolution,[status(thm)],[c_22,c_93])).

tff(c_423,plain,(
    ! [A_85,B_86] :
      ( '#skF_1'(A_85,k1_tarski(B_86)) = B_86
      | r1_xboole_0(A_85,k1_tarski(B_86)) ) ),
    inference(resolution,[status(thm)],[c_132,c_101])).

tff(c_154,plain,(
    ! [A_55,B_56] :
      ( ~ r1_xboole_0(A_55,B_56)
      | k3_xboole_0(A_55,B_56) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_28,c_144])).

tff(c_697,plain,(
    ! [A_110,B_111] :
      ( k3_xboole_0(A_110,k1_tarski(B_111)) = k1_xboole_0
      | '#skF_1'(A_110,k1_tarski(B_111)) = B_111 ) ),
    inference(resolution,[status(thm)],[c_423,c_154])).

tff(c_14,plain,(
    ! [A_11,B_12] : k5_xboole_0(A_11,k3_xboole_0(A_11,B_12)) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_733,plain,(
    ! [A_110,B_111] :
      ( k4_xboole_0(A_110,k1_tarski(B_111)) = k5_xboole_0(A_110,k1_xboole_0)
      | '#skF_1'(A_110,k1_tarski(B_111)) = B_111 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_697,c_14])).

tff(c_769,plain,(
    ! [A_110,B_111] :
      ( k4_xboole_0(A_110,k1_tarski(B_111)) = A_110
      | '#skF_1'(A_110,k1_tarski(B_111)) = B_111 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_237,c_733])).

tff(c_1141,plain,(
    '#skF_1'('#skF_5',k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_769,c_1133])).

tff(c_8,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1145,plain,
    ( r2_hidden(k1_xboole_0,'#skF_5')
    | r1_xboole_0('#skF_5',k1_tarski(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1141,c_8])).

tff(c_1152,plain,(
    r1_xboole_0('#skF_5',k1_tarski(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_1145])).

tff(c_1160,plain,(
    k3_xboole_0('#skF_5',k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1152,c_154])).

tff(c_1186,plain,(
    k4_xboole_0('#skF_5',k1_tarski(k1_xboole_0)) = k5_xboole_0('#skF_5',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1160,c_14])).

tff(c_1209,plain,(
    k4_xboole_0('#skF_5',k1_tarski(k1_xboole_0)) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_237,c_1186])).

tff(c_1211,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1133,c_1209])).

tff(c_1212,plain,(
    r2_hidden(k1_xboole_0,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_1145])).

tff(c_38,plain,(
    ! [C_36,B_34,A_30] :
      ( ~ v1_xboole_0(C_36)
      | ~ r2_hidden(C_36,B_34)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_30))))
      | ~ v13_waybel_0(B_34,k3_yellow_1(A_30))
      | ~ v2_waybel_0(B_34,k3_yellow_1(A_30))
      | ~ v1_subset_1(B_34,u1_struct_0(k3_yellow_1(A_30)))
      | v1_xboole_0(B_34)
      | v1_xboole_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_1215,plain,(
    ! [A_30] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_30))))
      | ~ v13_waybel_0('#skF_5',k3_yellow_1(A_30))
      | ~ v2_waybel_0('#skF_5',k3_yellow_1(A_30))
      | ~ v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(A_30)))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_30) ) ),
    inference(resolution,[status(thm)],[c_1212,c_38])).

tff(c_1218,plain,(
    ! [A_30] :
      ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_30))))
      | ~ v13_waybel_0('#skF_5',k3_yellow_1(A_30))
      | ~ v2_waybel_0('#skF_5',k3_yellow_1(A_30))
      | ~ v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(A_30)))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_30) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1215])).

tff(c_1248,plain,(
    ! [A_132] :
      ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_132))))
      | ~ v13_waybel_0('#skF_5',k3_yellow_1(A_132))
      | ~ v2_waybel_0('#skF_5',k3_yellow_1(A_132))
      | ~ v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(A_132)))
      | v1_xboole_0(A_132) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1218])).

tff(c_1251,plain,
    ( ~ v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | ~ v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | ~ v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))))
    | v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_42,c_1248])).

tff(c_1254,plain,(
    v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_1251])).

tff(c_1256,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_1254])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n016.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:43:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.83/1.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.45  
% 2.83/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.45  %$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_yellow19 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_lattice3 > k1_xboole_0 > #skF_5 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 2.83/1.45  
% 2.83/1.45  %Foreground sorts:
% 2.83/1.45  
% 2.83/1.45  
% 2.83/1.45  %Background operators:
% 2.83/1.45  
% 2.83/1.45  
% 2.83/1.45  %Foreground operators:
% 2.83/1.45  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.83/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.83/1.45  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 2.83/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.83/1.45  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.83/1.45  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.83/1.45  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 2.83/1.45  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.83/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.83/1.45  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 2.83/1.45  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.83/1.45  tff('#skF_5', type, '#skF_5': $i).
% 2.83/1.45  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.83/1.45  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 2.83/1.45  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 2.83/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.83/1.45  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.83/1.45  tff(k2_yellow19, type, k2_yellow19: ($i * $i) > $i).
% 2.83/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.83/1.45  tff('#skF_4', type, '#skF_4': $i).
% 2.83/1.45  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.83/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.83/1.45  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.83/1.45  tff(k3_yellow19, type, k3_yellow19: ($i * $i * $i) > $i).
% 2.83/1.45  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 2.83/1.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.83/1.45  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.83/1.45  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.83/1.45  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.83/1.45  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.83/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.83/1.45  
% 3.19/1.47  tff(f_160, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (B = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_yellow19)).
% 3.19/1.47  tff(f_92, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.19/1.47  tff(f_100, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.19/1.47  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.19/1.47  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 3.19/1.47  tff(f_119, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))), B, k1_tarski(k1_xboole_0)) = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_yellow19)).
% 3.19/1.47  tff(f_62, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.19/1.47  tff(f_64, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.19/1.47  tff(f_88, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & r1_xboole_0(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_mcart_1)).
% 3.19/1.47  tff(f_58, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.19/1.47  tff(f_60, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.19/1.47  tff(f_44, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.19/1.47  tff(f_74, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 3.19/1.47  tff(f_69, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 3.19/1.47  tff(f_140, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(A)))) & v2_waybel_0(B, k3_yellow_1(A))) & v13_waybel_0(B, k3_yellow_1(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A))))) => (![C]: ~(r2_hidden(C, B) & v1_xboole_0(C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_yellow19)).
% 3.19/1.47  tff(c_54, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_160])).
% 3.19/1.47  tff(c_52, plain, (l1_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_160])).
% 3.19/1.47  tff(c_75, plain, (![A_42]: (u1_struct_0(A_42)=k2_struct_0(A_42) | ~l1_struct_0(A_42))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.19/1.47  tff(c_79, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_52, c_75])).
% 3.19/1.47  tff(c_86, plain, (![A_46]: (~v1_xboole_0(u1_struct_0(A_46)) | ~l1_struct_0(A_46) | v2_struct_0(A_46))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.19/1.47  tff(c_89, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_79, c_86])).
% 3.19/1.47  tff(c_91, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_89])).
% 3.19/1.47  tff(c_92, plain, (~v1_xboole_0(k2_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_54, c_91])).
% 3.19/1.47  tff(c_48, plain, (v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_160])).
% 3.19/1.47  tff(c_46, plain, (v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_160])).
% 3.19/1.47  tff(c_44, plain, (v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_160])).
% 3.19/1.47  tff(c_42, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4')))))), inference(cnfTransformation, [status(thm)], [f_160])).
% 3.19/1.47  tff(c_50, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_160])).
% 3.19/1.47  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.19/1.47  tff(c_611, plain, (![A_97, B_98, C_99]: (k7_subset_1(A_97, B_98, C_99)=k4_xboole_0(B_98, C_99) | ~m1_subset_1(B_98, k1_zfmisc_1(A_97)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.19/1.47  tff(c_614, plain, (![C_99]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))), '#skF_5', C_99)=k4_xboole_0('#skF_5', C_99))), inference(resolution, [status(thm)], [c_42, c_611])).
% 3.19/1.47  tff(c_937, plain, (![A_121, B_122]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_121))), B_122, k1_tarski(k1_xboole_0))=k2_yellow19(A_121, k3_yellow19(A_121, k2_struct_0(A_121), B_122)) | ~m1_subset_1(B_122, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_121))))) | ~v13_waybel_0(B_122, k3_yellow_1(k2_struct_0(A_121))) | ~v2_waybel_0(B_122, k3_yellow_1(k2_struct_0(A_121))) | v1_xboole_0(B_122) | ~l1_struct_0(A_121) | v2_struct_0(A_121))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.19/1.47  tff(c_939, plain, (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))), '#skF_5', k1_tarski(k1_xboole_0))=k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | ~v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | v1_xboole_0('#skF_5') | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_42, c_937])).
% 3.19/1.47  tff(c_942, plain, (k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))=k4_xboole_0('#skF_5', k1_tarski(k1_xboole_0)) | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_46, c_44, c_614, c_939])).
% 3.19/1.47  tff(c_943, plain, (k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))=k4_xboole_0('#skF_5', k1_tarski(k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_54, c_50, c_942])).
% 3.19/1.47  tff(c_40, plain, (k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_160])).
% 3.19/1.47  tff(c_1133, plain, (k4_xboole_0('#skF_5', k1_tarski(k1_xboole_0))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_943, c_40])).
% 3.19/1.47  tff(c_16, plain, (![A_13]: (k4_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.19/1.47  tff(c_18, plain, (![A_14]: (r1_xboole_0(A_14, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.19/1.47  tff(c_28, plain, (![A_22]: (r2_hidden('#skF_3'(A_22), A_22) | k1_xboole_0=A_22)), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.19/1.47  tff(c_144, plain, (![A_55, B_56, C_57]: (~r1_xboole_0(A_55, B_56) | ~r2_hidden(C_57, k3_xboole_0(A_55, B_56)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.19/1.47  tff(c_155, plain, (![A_58, B_59]: (~r1_xboole_0(A_58, B_59) | k3_xboole_0(A_58, B_59)=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_144])).
% 3.19/1.47  tff(c_167, plain, (![A_14]: (k3_xboole_0(A_14, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_155])).
% 3.19/1.47  tff(c_222, plain, (![A_64, B_65]: (k5_xboole_0(A_64, k3_xboole_0(A_64, B_65))=k4_xboole_0(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.19/1.47  tff(c_234, plain, (![A_14]: (k5_xboole_0(A_14, k1_xboole_0)=k4_xboole_0(A_14, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_167, c_222])).
% 3.19/1.47  tff(c_237, plain, (![A_14]: (k5_xboole_0(A_14, k1_xboole_0)=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_234])).
% 3.19/1.47  tff(c_132, plain, (![A_53, B_54]: (r2_hidden('#skF_1'(A_53, B_54), B_54) | r1_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.19/1.47  tff(c_22, plain, (![A_17, B_18]: (r1_xboole_0(k1_tarski(A_17), k1_tarski(B_18)) | B_18=A_17)), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.19/1.47  tff(c_93, plain, (![A_47, B_48]: (~r2_hidden(A_47, B_48) | ~r1_xboole_0(k1_tarski(A_47), B_48))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.19/1.47  tff(c_101, plain, (![A_17, B_18]: (~r2_hidden(A_17, k1_tarski(B_18)) | B_18=A_17)), inference(resolution, [status(thm)], [c_22, c_93])).
% 3.19/1.47  tff(c_423, plain, (![A_85, B_86]: ('#skF_1'(A_85, k1_tarski(B_86))=B_86 | r1_xboole_0(A_85, k1_tarski(B_86)))), inference(resolution, [status(thm)], [c_132, c_101])).
% 3.19/1.47  tff(c_154, plain, (![A_55, B_56]: (~r1_xboole_0(A_55, B_56) | k3_xboole_0(A_55, B_56)=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_144])).
% 3.19/1.47  tff(c_697, plain, (![A_110, B_111]: (k3_xboole_0(A_110, k1_tarski(B_111))=k1_xboole_0 | '#skF_1'(A_110, k1_tarski(B_111))=B_111)), inference(resolution, [status(thm)], [c_423, c_154])).
% 3.19/1.47  tff(c_14, plain, (![A_11, B_12]: (k5_xboole_0(A_11, k3_xboole_0(A_11, B_12))=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.19/1.47  tff(c_733, plain, (![A_110, B_111]: (k4_xboole_0(A_110, k1_tarski(B_111))=k5_xboole_0(A_110, k1_xboole_0) | '#skF_1'(A_110, k1_tarski(B_111))=B_111)), inference(superposition, [status(thm), theory('equality')], [c_697, c_14])).
% 3.19/1.47  tff(c_769, plain, (![A_110, B_111]: (k4_xboole_0(A_110, k1_tarski(B_111))=A_110 | '#skF_1'(A_110, k1_tarski(B_111))=B_111)), inference(demodulation, [status(thm), theory('equality')], [c_237, c_733])).
% 3.19/1.47  tff(c_1141, plain, ('#skF_1'('#skF_5', k1_tarski(k1_xboole_0))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_769, c_1133])).
% 3.19/1.47  tff(c_8, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.19/1.47  tff(c_1145, plain, (r2_hidden(k1_xboole_0, '#skF_5') | r1_xboole_0('#skF_5', k1_tarski(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1141, c_8])).
% 3.19/1.47  tff(c_1152, plain, (r1_xboole_0('#skF_5', k1_tarski(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_1145])).
% 3.19/1.47  tff(c_1160, plain, (k3_xboole_0('#skF_5', k1_tarski(k1_xboole_0))=k1_xboole_0), inference(resolution, [status(thm)], [c_1152, c_154])).
% 3.19/1.47  tff(c_1186, plain, (k4_xboole_0('#skF_5', k1_tarski(k1_xboole_0))=k5_xboole_0('#skF_5', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1160, c_14])).
% 3.19/1.47  tff(c_1209, plain, (k4_xboole_0('#skF_5', k1_tarski(k1_xboole_0))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_237, c_1186])).
% 3.19/1.47  tff(c_1211, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1133, c_1209])).
% 3.19/1.47  tff(c_1212, plain, (r2_hidden(k1_xboole_0, '#skF_5')), inference(splitRight, [status(thm)], [c_1145])).
% 3.19/1.47  tff(c_38, plain, (![C_36, B_34, A_30]: (~v1_xboole_0(C_36) | ~r2_hidden(C_36, B_34) | ~m1_subset_1(B_34, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_30)))) | ~v13_waybel_0(B_34, k3_yellow_1(A_30)) | ~v2_waybel_0(B_34, k3_yellow_1(A_30)) | ~v1_subset_1(B_34, u1_struct_0(k3_yellow_1(A_30))) | v1_xboole_0(B_34) | v1_xboole_0(A_30))), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.19/1.47  tff(c_1215, plain, (![A_30]: (~v1_xboole_0(k1_xboole_0) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_30)))) | ~v13_waybel_0('#skF_5', k3_yellow_1(A_30)) | ~v2_waybel_0('#skF_5', k3_yellow_1(A_30)) | ~v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(A_30))) | v1_xboole_0('#skF_5') | v1_xboole_0(A_30))), inference(resolution, [status(thm)], [c_1212, c_38])).
% 3.19/1.47  tff(c_1218, plain, (![A_30]: (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_30)))) | ~v13_waybel_0('#skF_5', k3_yellow_1(A_30)) | ~v2_waybel_0('#skF_5', k3_yellow_1(A_30)) | ~v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(A_30))) | v1_xboole_0('#skF_5') | v1_xboole_0(A_30))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1215])).
% 3.19/1.47  tff(c_1248, plain, (![A_132]: (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_132)))) | ~v13_waybel_0('#skF_5', k3_yellow_1(A_132)) | ~v2_waybel_0('#skF_5', k3_yellow_1(A_132)) | ~v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(A_132))) | v1_xboole_0(A_132))), inference(negUnitSimplification, [status(thm)], [c_50, c_1218])).
% 3.19/1.47  tff(c_1251, plain, (~v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4')))) | v1_xboole_0(k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_42, c_1248])).
% 3.19/1.47  tff(c_1254, plain, (v1_xboole_0(k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_1251])).
% 3.19/1.47  tff(c_1256, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_1254])).
% 3.19/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.19/1.47  
% 3.19/1.47  Inference rules
% 3.19/1.47  ----------------------
% 3.19/1.47  #Ref     : 0
% 3.19/1.47  #Sup     : 274
% 3.19/1.47  #Fact    : 0
% 3.19/1.47  #Define  : 0
% 3.19/1.47  #Split   : 3
% 3.19/1.47  #Chain   : 0
% 3.19/1.47  #Close   : 0
% 3.19/1.47  
% 3.19/1.47  Ordering : KBO
% 3.19/1.47  
% 3.19/1.47  Simplification rules
% 3.19/1.47  ----------------------
% 3.19/1.47  #Subsume      : 33
% 3.19/1.47  #Demod        : 100
% 3.19/1.47  #Tautology    : 169
% 3.19/1.47  #SimpNegUnit  : 17
% 3.19/1.47  #BackRed      : 1
% 3.19/1.47  
% 3.19/1.47  #Partial instantiations: 0
% 3.19/1.47  #Strategies tried      : 1
% 3.19/1.47  
% 3.19/1.47  Timing (in seconds)
% 3.19/1.47  ----------------------
% 3.19/1.47  Preprocessing        : 0.33
% 3.19/1.47  Parsing              : 0.17
% 3.19/1.47  CNF conversion       : 0.02
% 3.19/1.47  Main loop            : 0.37
% 3.19/1.47  Inferencing          : 0.15
% 3.19/1.47  Reduction            : 0.11
% 3.19/1.47  Demodulation         : 0.08
% 3.19/1.47  BG Simplification    : 0.02
% 3.19/1.47  Subsumption          : 0.06
% 3.19/1.47  Abstraction          : 0.02
% 3.19/1.47  MUC search           : 0.00
% 3.19/1.47  Cooper               : 0.00
% 3.19/1.47  Total                : 0.73
% 3.19/1.47  Index Insertion      : 0.00
% 3.19/1.47  Index Deletion       : 0.00
% 3.19/1.47  Index Matching       : 0.00
% 3.19/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
