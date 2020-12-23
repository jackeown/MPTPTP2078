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
% DateTime   : Thu Dec  3 10:31:31 EST 2020

% Result     : Theorem 11.56s
% Output     : CNFRefutation 11.75s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 327 expanded)
%              Number of leaves         :   47 ( 136 expanded)
%              Depth                    :   18
%              Number of atoms          :  209 ( 892 expanded)
%              Number of equality atoms :   45 ( 177 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_yellow19 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_lattice3 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

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

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

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

tff(f_100,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).

tff(f_36,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_92,axiom,(
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

tff(f_72,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_78,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_76,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_83,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_70,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_54,axiom,(
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

tff(f_88,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_68,plain,(
    l1_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_66,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_64,plain,(
    v1_subset_1('#skF_6',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_62,plain,(
    v2_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_60,plain,(
    v13_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_58,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_18,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),A_1)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1630,plain,(
    ! [C_176,B_177,A_178] :
      ( ~ v1_xboole_0(C_176)
      | ~ r2_hidden(C_176,B_177)
      | ~ m1_subset_1(B_177,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_178))))
      | ~ v13_waybel_0(B_177,k3_yellow_1(A_178))
      | ~ v2_waybel_0(B_177,k3_yellow_1(A_178))
      | ~ v1_subset_1(B_177,u1_struct_0(k3_yellow_1(A_178)))
      | v1_xboole_0(B_177)
      | v1_xboole_0(A_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_29891,plain,(
    ! [A_649,B_650,C_651,A_652] :
      ( ~ v1_xboole_0('#skF_2'(A_649,B_650,C_651))
      | ~ m1_subset_1(C_651,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_652))))
      | ~ v13_waybel_0(C_651,k3_yellow_1(A_652))
      | ~ v2_waybel_0(C_651,k3_yellow_1(A_652))
      | ~ v1_subset_1(C_651,u1_struct_0(k3_yellow_1(A_652)))
      | v1_xboole_0(C_651)
      | v1_xboole_0(A_652)
      | r2_hidden('#skF_1'(A_649,B_650,C_651),A_649)
      | k4_xboole_0(A_649,B_650) = C_651 ) ),
    inference(resolution,[status(thm)],[c_18,c_1630])).

tff(c_29893,plain,(
    ! [A_649,B_650] :
      ( ~ v1_xboole_0('#skF_2'(A_649,B_650,'#skF_6'))
      | ~ v13_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v2_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v1_subset_1('#skF_6',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(k2_struct_0('#skF_5'))
      | r2_hidden('#skF_1'(A_649,B_650,'#skF_6'),A_649)
      | k4_xboole_0(A_649,B_650) = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_58,c_29891])).

tff(c_29896,plain,(
    ! [A_649,B_650] :
      ( ~ v1_xboole_0('#skF_2'(A_649,B_650,'#skF_6'))
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(k2_struct_0('#skF_5'))
      | r2_hidden('#skF_1'(A_649,B_650,'#skF_6'),A_649)
      | k4_xboole_0(A_649,B_650) = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_29893])).

tff(c_29897,plain,(
    ! [A_649,B_650] :
      ( ~ v1_xboole_0('#skF_2'(A_649,B_650,'#skF_6'))
      | v1_xboole_0(k2_struct_0('#skF_5'))
      | r2_hidden('#skF_1'(A_649,B_650,'#skF_6'),A_649)
      | k4_xboole_0(A_649,B_650) = '#skF_6' ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_29896])).

tff(c_30623,plain,(
    v1_xboole_0(k2_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_29897])).

tff(c_48,plain,(
    ! [A_31] :
      ( ~ v1_xboole_0(k2_struct_0(A_31))
      | ~ l1_struct_0(A_31)
      | v2_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_30626,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_30623,c_48])).

tff(c_30629,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_30626])).

tff(c_30631,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_30629])).

tff(c_30633,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_29897])).

tff(c_20,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_624,plain,(
    ! [A_116,B_117,C_118] :
      ( k7_subset_1(A_116,B_117,C_118) = k4_xboole_0(B_117,C_118)
      | ~ m1_subset_1(B_117,k1_zfmisc_1(A_116)) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_627,plain,(
    ! [C_118] : k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))),'#skF_6',C_118) = k4_xboole_0('#skF_6',C_118) ),
    inference(resolution,[status(thm)],[c_58,c_624])).

tff(c_1834,plain,(
    ! [A_186,B_187] :
      ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_186))),B_187,k1_tarski(k1_xboole_0)) = k2_yellow19(A_186,k3_yellow19(A_186,k2_struct_0(A_186),B_187))
      | ~ m1_subset_1(B_187,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_186)))))
      | ~ v13_waybel_0(B_187,k3_yellow_1(k2_struct_0(A_186)))
      | ~ v2_waybel_0(B_187,k3_yellow_1(k2_struct_0(A_186)))
      | v1_xboole_0(B_187)
      | ~ l1_struct_0(A_186)
      | v2_struct_0(A_186) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_1836,plain,
    ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))),'#skF_6',k1_tarski(k1_xboole_0)) = k2_yellow19('#skF_5',k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6'))
    | ~ v13_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5')))
    | ~ v2_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5')))
    | v1_xboole_0('#skF_6')
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_1834])).

tff(c_1839,plain,
    ( k2_yellow19('#skF_5',k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6')) = k4_xboole_0('#skF_6',k1_tarski(k1_xboole_0))
    | v1_xboole_0('#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_62,c_60,c_627,c_1836])).

tff(c_1840,plain,(
    k2_yellow19('#skF_5',k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6')) = k4_xboole_0('#skF_6',k1_tarski(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_66,c_1839])).

tff(c_56,plain,(
    k2_yellow19('#skF_5',k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6')) != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_2214,plain,(
    k4_xboole_0('#skF_6',k1_tarski(k1_xboole_0)) != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1840,c_56])).

tff(c_34,plain,(
    ! [A_19] : k4_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_40,plain,(
    ! [A_23] : r1_xboole_0(A_23,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_38,plain,(
    ! [A_22] : k4_xboole_0(k1_xboole_0,A_22) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_846,plain,(
    ! [A_142,B_143,C_144] :
      ( r2_hidden('#skF_1'(A_142,B_143,C_144),A_142)
      | r2_hidden('#skF_2'(A_142,B_143,C_144),C_144)
      | k4_xboole_0(A_142,B_143) = C_144 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_108,plain,(
    ! [A_49,B_50] :
      ( ~ r2_hidden(A_49,B_50)
      | ~ r1_xboole_0(k1_tarski(A_49),B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_113,plain,(
    ! [A_49] : ~ r2_hidden(A_49,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_40,c_108])).

tff(c_897,plain,(
    ! [B_143,C_144] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_143,C_144),C_144)
      | k4_xboole_0(k1_xboole_0,B_143) = C_144 ) ),
    inference(resolution,[status(thm)],[c_846,c_113])).

tff(c_967,plain,(
    ! [B_145,C_146] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_145,C_146),C_146)
      | k1_xboole_0 = C_146 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_897])).

tff(c_30,plain,(
    ! [A_12,B_13,C_16] :
      ( ~ r1_xboole_0(A_12,B_13)
      | ~ r2_hidden(C_16,k3_xboole_0(A_12,B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1025,plain,(
    ! [A_147,B_148] :
      ( ~ r1_xboole_0(A_147,B_148)
      | k3_xboole_0(A_147,B_148) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_967,c_30])).

tff(c_1065,plain,(
    ! [A_149] : k3_xboole_0(A_149,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_1025])).

tff(c_32,plain,(
    ! [A_17,B_18] : k5_xboole_0(A_17,k3_xboole_0(A_17,B_18)) = k4_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1088,plain,(
    ! [A_149] : k5_xboole_0(A_149,k1_xboole_0) = k4_xboole_0(A_149,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1065,c_32])).

tff(c_1109,plain,(
    ! [A_149] : k5_xboole_0(A_149,k1_xboole_0) = A_149 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1088])).

tff(c_267,plain,(
    ! [A_74,B_75] :
      ( r2_hidden('#skF_3'(A_74,B_75),B_75)
      | r1_xboole_0(A_74,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_115,plain,(
    ! [A_52,B_53] :
      ( r1_xboole_0(k1_tarski(A_52),k1_tarski(B_53))
      | B_53 = A_52 ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_42,plain,(
    ! [A_24,B_25] :
      ( ~ r2_hidden(A_24,B_25)
      | ~ r1_xboole_0(k1_tarski(A_24),B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_119,plain,(
    ! [A_52,B_53] :
      ( ~ r2_hidden(A_52,k1_tarski(B_53))
      | B_53 = A_52 ) ),
    inference(resolution,[status(thm)],[c_115,c_42])).

tff(c_291,plain,(
    ! [A_74,B_53] :
      ( '#skF_3'(A_74,k1_tarski(B_53)) = B_53
      | r1_xboole_0(A_74,k1_tarski(B_53)) ) ),
    inference(resolution,[status(thm)],[c_267,c_119])).

tff(c_23163,plain,(
    ! [A_607,B_608] :
      ( k3_xboole_0(A_607,k1_tarski(B_608)) = k1_xboole_0
      | '#skF_3'(A_607,k1_tarski(B_608)) = B_608 ) ),
    inference(resolution,[status(thm)],[c_291,c_1025])).

tff(c_23503,plain,(
    ! [A_607,B_608] :
      ( k4_xboole_0(A_607,k1_tarski(B_608)) = k5_xboole_0(A_607,k1_xboole_0)
      | '#skF_3'(A_607,k1_tarski(B_608)) = B_608 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_23163,c_32])).

tff(c_31531,plain,(
    ! [A_665,B_666] :
      ( k4_xboole_0(A_665,k1_tarski(B_666)) = A_665
      | '#skF_3'(A_665,k1_tarski(B_666)) = B_666 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1109,c_23503])).

tff(c_32198,plain,(
    '#skF_3'('#skF_6',k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_31531,c_2214])).

tff(c_26,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_3'(A_7,B_8),A_7)
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_32226,plain,
    ( r2_hidden(k1_xboole_0,'#skF_6')
    | r1_xboole_0('#skF_6',k1_tarski(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_32198,c_26])).

tff(c_32242,plain,(
    r1_xboole_0('#skF_6',k1_tarski(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_32226])).

tff(c_1021,plain,(
    ! [A_12,B_13] :
      ( ~ r1_xboole_0(A_12,B_13)
      | k3_xboole_0(A_12,B_13) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_967,c_30])).

tff(c_32359,plain,(
    k3_xboole_0('#skF_6',k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32242,c_1021])).

tff(c_32552,plain,(
    k4_xboole_0('#skF_6',k1_tarski(k1_xboole_0)) = k5_xboole_0('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_32359,c_32])).

tff(c_32639,plain,(
    k4_xboole_0('#skF_6',k1_tarski(k1_xboole_0)) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1109,c_32552])).

tff(c_32641,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2214,c_32639])).

tff(c_32642,plain,(
    r2_hidden(k1_xboole_0,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_32226])).

tff(c_54,plain,(
    ! [C_42,B_40,A_36] :
      ( ~ v1_xboole_0(C_42)
      | ~ r2_hidden(C_42,B_40)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_36))))
      | ~ v13_waybel_0(B_40,k3_yellow_1(A_36))
      | ~ v2_waybel_0(B_40,k3_yellow_1(A_36))
      | ~ v1_subset_1(B_40,u1_struct_0(k3_yellow_1(A_36)))
      | v1_xboole_0(B_40)
      | v1_xboole_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_32663,plain,(
    ! [A_36] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_36))))
      | ~ v13_waybel_0('#skF_6',k3_yellow_1(A_36))
      | ~ v2_waybel_0('#skF_6',k3_yellow_1(A_36))
      | ~ v1_subset_1('#skF_6',u1_struct_0(k3_yellow_1(A_36)))
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(A_36) ) ),
    inference(resolution,[status(thm)],[c_32642,c_54])).

tff(c_32668,plain,(
    ! [A_36] :
      ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_36))))
      | ~ v13_waybel_0('#skF_6',k3_yellow_1(A_36))
      | ~ v2_waybel_0('#skF_6',k3_yellow_1(A_36))
      | ~ v1_subset_1('#skF_6',u1_struct_0(k3_yellow_1(A_36)))
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(A_36) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_32663])).

tff(c_32802,plain,(
    ! [A_675] :
      ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_675))))
      | ~ v13_waybel_0('#skF_6',k3_yellow_1(A_675))
      | ~ v2_waybel_0('#skF_6',k3_yellow_1(A_675))
      | ~ v1_subset_1('#skF_6',u1_struct_0(k3_yellow_1(A_675)))
      | v1_xboole_0(A_675) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_32668])).

tff(c_32805,plain,
    ( ~ v13_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5')))
    | ~ v2_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5')))
    | ~ v1_subset_1('#skF_6',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))
    | v1_xboole_0(k2_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_58,c_32802])).

tff(c_32808,plain,(
    v1_xboole_0(k2_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_32805])).

tff(c_32810,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30633,c_32808])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:30:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.56/4.63  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.56/4.64  
% 11.56/4.64  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.56/4.64  %$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_yellow19 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_lattice3 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 11.56/4.64  
% 11.56/4.64  %Foreground sorts:
% 11.56/4.64  
% 11.56/4.64  
% 11.56/4.64  %Background operators:
% 11.56/4.64  
% 11.56/4.64  
% 11.56/4.64  %Foreground operators:
% 11.56/4.64  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 11.56/4.64  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 11.56/4.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.56/4.64  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 11.56/4.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.56/4.64  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 11.56/4.64  tff(k1_tarski, type, k1_tarski: $i > $i).
% 11.56/4.64  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 11.56/4.64  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.56/4.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.56/4.64  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 11.56/4.64  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 11.56/4.64  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 11.56/4.64  tff('#skF_5', type, '#skF_5': $i).
% 11.56/4.64  tff('#skF_6', type, '#skF_6': $i).
% 11.56/4.64  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 11.56/4.64  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 11.56/4.64  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 11.56/4.64  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 11.56/4.64  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.56/4.64  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 11.56/4.64  tff(k2_yellow19, type, k2_yellow19: ($i * $i) > $i).
% 11.56/4.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.56/4.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.56/4.64  tff(k3_yellow19, type, k3_yellow19: ($i * $i * $i) > $i).
% 11.56/4.64  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 11.56/4.64  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.56/4.64  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 11.56/4.64  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 11.56/4.64  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 11.56/4.64  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 11.56/4.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.56/4.64  
% 11.75/4.66  tff(f_160, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (B = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_yellow19)).
% 11.75/4.66  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 11.75/4.66  tff(f_140, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(A)))) & v2_waybel_0(B, k3_yellow_1(A))) & v13_waybel_0(B, k3_yellow_1(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A))))) => (![C]: ~(r2_hidden(C, B) & v1_xboole_0(C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_yellow19)).
% 11.75/4.66  tff(f_100, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_struct_0)).
% 11.75/4.66  tff(f_36, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 11.75/4.66  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 11.75/4.66  tff(f_119, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))), B, k1_tarski(k1_xboole_0)) = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_yellow19)).
% 11.75/4.66  tff(f_72, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 11.75/4.66  tff(f_78, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 11.75/4.66  tff(f_76, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 11.75/4.66  tff(f_83, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 11.75/4.66  tff(f_68, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 11.75/4.66  tff(f_70, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 11.75/4.66  tff(f_54, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 11.75/4.66  tff(f_88, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 11.75/4.66  tff(c_70, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_160])).
% 11.75/4.66  tff(c_68, plain, (l1_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_160])).
% 11.75/4.66  tff(c_66, plain, (~v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_160])).
% 11.75/4.66  tff(c_64, plain, (v1_subset_1('#skF_6', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))), inference(cnfTransformation, [status(thm)], [f_160])).
% 11.75/4.66  tff(c_62, plain, (v2_waybel_0('#skF_6', k3_yellow_1(k2_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_160])).
% 11.75/4.66  tff(c_60, plain, (v13_waybel_0('#skF_6', k3_yellow_1(k2_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_160])).
% 11.75/4.66  tff(c_58, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))))), inference(cnfTransformation, [status(thm)], [f_160])).
% 11.75/4.66  tff(c_18, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), A_1) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.75/4.66  tff(c_1630, plain, (![C_176, B_177, A_178]: (~v1_xboole_0(C_176) | ~r2_hidden(C_176, B_177) | ~m1_subset_1(B_177, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_178)))) | ~v13_waybel_0(B_177, k3_yellow_1(A_178)) | ~v2_waybel_0(B_177, k3_yellow_1(A_178)) | ~v1_subset_1(B_177, u1_struct_0(k3_yellow_1(A_178))) | v1_xboole_0(B_177) | v1_xboole_0(A_178))), inference(cnfTransformation, [status(thm)], [f_140])).
% 11.75/4.66  tff(c_29891, plain, (![A_649, B_650, C_651, A_652]: (~v1_xboole_0('#skF_2'(A_649, B_650, C_651)) | ~m1_subset_1(C_651, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_652)))) | ~v13_waybel_0(C_651, k3_yellow_1(A_652)) | ~v2_waybel_0(C_651, k3_yellow_1(A_652)) | ~v1_subset_1(C_651, u1_struct_0(k3_yellow_1(A_652))) | v1_xboole_0(C_651) | v1_xboole_0(A_652) | r2_hidden('#skF_1'(A_649, B_650, C_651), A_649) | k4_xboole_0(A_649, B_650)=C_651)), inference(resolution, [status(thm)], [c_18, c_1630])).
% 11.75/4.66  tff(c_29893, plain, (![A_649, B_650]: (~v1_xboole_0('#skF_2'(A_649, B_650, '#skF_6')) | ~v13_waybel_0('#skF_6', k3_yellow_1(k2_struct_0('#skF_5'))) | ~v2_waybel_0('#skF_6', k3_yellow_1(k2_struct_0('#skF_5'))) | ~v1_subset_1('#skF_6', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))) | v1_xboole_0('#skF_6') | v1_xboole_0(k2_struct_0('#skF_5')) | r2_hidden('#skF_1'(A_649, B_650, '#skF_6'), A_649) | k4_xboole_0(A_649, B_650)='#skF_6')), inference(resolution, [status(thm)], [c_58, c_29891])).
% 11.75/4.66  tff(c_29896, plain, (![A_649, B_650]: (~v1_xboole_0('#skF_2'(A_649, B_650, '#skF_6')) | v1_xboole_0('#skF_6') | v1_xboole_0(k2_struct_0('#skF_5')) | r2_hidden('#skF_1'(A_649, B_650, '#skF_6'), A_649) | k4_xboole_0(A_649, B_650)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_29893])).
% 11.75/4.66  tff(c_29897, plain, (![A_649, B_650]: (~v1_xboole_0('#skF_2'(A_649, B_650, '#skF_6')) | v1_xboole_0(k2_struct_0('#skF_5')) | r2_hidden('#skF_1'(A_649, B_650, '#skF_6'), A_649) | k4_xboole_0(A_649, B_650)='#skF_6')), inference(negUnitSimplification, [status(thm)], [c_66, c_29896])).
% 11.75/4.66  tff(c_30623, plain, (v1_xboole_0(k2_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_29897])).
% 11.75/4.66  tff(c_48, plain, (![A_31]: (~v1_xboole_0(k2_struct_0(A_31)) | ~l1_struct_0(A_31) | v2_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_100])).
% 11.75/4.66  tff(c_30626, plain, (~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_30623, c_48])).
% 11.75/4.66  tff(c_30629, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_30626])).
% 11.75/4.66  tff(c_30631, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_30629])).
% 11.75/4.66  tff(c_30633, plain, (~v1_xboole_0(k2_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_29897])).
% 11.75/4.66  tff(c_20, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 11.75/4.66  tff(c_624, plain, (![A_116, B_117, C_118]: (k7_subset_1(A_116, B_117, C_118)=k4_xboole_0(B_117, C_118) | ~m1_subset_1(B_117, k1_zfmisc_1(A_116)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 11.75/4.66  tff(c_627, plain, (![C_118]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))), '#skF_6', C_118)=k4_xboole_0('#skF_6', C_118))), inference(resolution, [status(thm)], [c_58, c_624])).
% 11.75/4.66  tff(c_1834, plain, (![A_186, B_187]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_186))), B_187, k1_tarski(k1_xboole_0))=k2_yellow19(A_186, k3_yellow19(A_186, k2_struct_0(A_186), B_187)) | ~m1_subset_1(B_187, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_186))))) | ~v13_waybel_0(B_187, k3_yellow_1(k2_struct_0(A_186))) | ~v2_waybel_0(B_187, k3_yellow_1(k2_struct_0(A_186))) | v1_xboole_0(B_187) | ~l1_struct_0(A_186) | v2_struct_0(A_186))), inference(cnfTransformation, [status(thm)], [f_119])).
% 11.75/4.66  tff(c_1836, plain, (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))), '#skF_6', k1_tarski(k1_xboole_0))=k2_yellow19('#skF_5', k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6')) | ~v13_waybel_0('#skF_6', k3_yellow_1(k2_struct_0('#skF_5'))) | ~v2_waybel_0('#skF_6', k3_yellow_1(k2_struct_0('#skF_5'))) | v1_xboole_0('#skF_6') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_58, c_1834])).
% 11.75/4.66  tff(c_1839, plain, (k2_yellow19('#skF_5', k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6'))=k4_xboole_0('#skF_6', k1_tarski(k1_xboole_0)) | v1_xboole_0('#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_62, c_60, c_627, c_1836])).
% 11.75/4.66  tff(c_1840, plain, (k2_yellow19('#skF_5', k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6'))=k4_xboole_0('#skF_6', k1_tarski(k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_70, c_66, c_1839])).
% 11.75/4.66  tff(c_56, plain, (k2_yellow19('#skF_5', k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6'))!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_160])).
% 11.75/4.66  tff(c_2214, plain, (k4_xboole_0('#skF_6', k1_tarski(k1_xboole_0))!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1840, c_56])).
% 11.75/4.66  tff(c_34, plain, (![A_19]: (k4_xboole_0(A_19, k1_xboole_0)=A_19)), inference(cnfTransformation, [status(thm)], [f_72])).
% 11.75/4.66  tff(c_40, plain, (![A_23]: (r1_xboole_0(A_23, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_78])).
% 11.75/4.66  tff(c_38, plain, (![A_22]: (k4_xboole_0(k1_xboole_0, A_22)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_76])).
% 11.75/4.66  tff(c_846, plain, (![A_142, B_143, C_144]: (r2_hidden('#skF_1'(A_142, B_143, C_144), A_142) | r2_hidden('#skF_2'(A_142, B_143, C_144), C_144) | k4_xboole_0(A_142, B_143)=C_144)), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.75/4.66  tff(c_108, plain, (![A_49, B_50]: (~r2_hidden(A_49, B_50) | ~r1_xboole_0(k1_tarski(A_49), B_50))), inference(cnfTransformation, [status(thm)], [f_83])).
% 11.75/4.66  tff(c_113, plain, (![A_49]: (~r2_hidden(A_49, k1_xboole_0))), inference(resolution, [status(thm)], [c_40, c_108])).
% 11.75/4.66  tff(c_897, plain, (![B_143, C_144]: (r2_hidden('#skF_2'(k1_xboole_0, B_143, C_144), C_144) | k4_xboole_0(k1_xboole_0, B_143)=C_144)), inference(resolution, [status(thm)], [c_846, c_113])).
% 11.75/4.66  tff(c_967, plain, (![B_145, C_146]: (r2_hidden('#skF_2'(k1_xboole_0, B_145, C_146), C_146) | k1_xboole_0=C_146)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_897])).
% 11.75/4.66  tff(c_30, plain, (![A_12, B_13, C_16]: (~r1_xboole_0(A_12, B_13) | ~r2_hidden(C_16, k3_xboole_0(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 11.75/4.66  tff(c_1025, plain, (![A_147, B_148]: (~r1_xboole_0(A_147, B_148) | k3_xboole_0(A_147, B_148)=k1_xboole_0)), inference(resolution, [status(thm)], [c_967, c_30])).
% 11.75/4.66  tff(c_1065, plain, (![A_149]: (k3_xboole_0(A_149, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_1025])).
% 11.75/4.66  tff(c_32, plain, (![A_17, B_18]: (k5_xboole_0(A_17, k3_xboole_0(A_17, B_18))=k4_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_70])).
% 11.75/4.66  tff(c_1088, plain, (![A_149]: (k5_xboole_0(A_149, k1_xboole_0)=k4_xboole_0(A_149, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1065, c_32])).
% 11.75/4.66  tff(c_1109, plain, (![A_149]: (k5_xboole_0(A_149, k1_xboole_0)=A_149)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1088])).
% 11.75/4.66  tff(c_267, plain, (![A_74, B_75]: (r2_hidden('#skF_3'(A_74, B_75), B_75) | r1_xboole_0(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_54])).
% 11.75/4.66  tff(c_115, plain, (![A_52, B_53]: (r1_xboole_0(k1_tarski(A_52), k1_tarski(B_53)) | B_53=A_52)), inference(cnfTransformation, [status(thm)], [f_88])).
% 11.75/4.66  tff(c_42, plain, (![A_24, B_25]: (~r2_hidden(A_24, B_25) | ~r1_xboole_0(k1_tarski(A_24), B_25))), inference(cnfTransformation, [status(thm)], [f_83])).
% 11.75/4.66  tff(c_119, plain, (![A_52, B_53]: (~r2_hidden(A_52, k1_tarski(B_53)) | B_53=A_52)), inference(resolution, [status(thm)], [c_115, c_42])).
% 11.75/4.66  tff(c_291, plain, (![A_74, B_53]: ('#skF_3'(A_74, k1_tarski(B_53))=B_53 | r1_xboole_0(A_74, k1_tarski(B_53)))), inference(resolution, [status(thm)], [c_267, c_119])).
% 11.75/4.66  tff(c_23163, plain, (![A_607, B_608]: (k3_xboole_0(A_607, k1_tarski(B_608))=k1_xboole_0 | '#skF_3'(A_607, k1_tarski(B_608))=B_608)), inference(resolution, [status(thm)], [c_291, c_1025])).
% 11.75/4.66  tff(c_23503, plain, (![A_607, B_608]: (k4_xboole_0(A_607, k1_tarski(B_608))=k5_xboole_0(A_607, k1_xboole_0) | '#skF_3'(A_607, k1_tarski(B_608))=B_608)), inference(superposition, [status(thm), theory('equality')], [c_23163, c_32])).
% 11.75/4.66  tff(c_31531, plain, (![A_665, B_666]: (k4_xboole_0(A_665, k1_tarski(B_666))=A_665 | '#skF_3'(A_665, k1_tarski(B_666))=B_666)), inference(demodulation, [status(thm), theory('equality')], [c_1109, c_23503])).
% 11.75/4.66  tff(c_32198, plain, ('#skF_3'('#skF_6', k1_tarski(k1_xboole_0))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_31531, c_2214])).
% 11.75/4.66  tff(c_26, plain, (![A_7, B_8]: (r2_hidden('#skF_3'(A_7, B_8), A_7) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_54])).
% 11.75/4.66  tff(c_32226, plain, (r2_hidden(k1_xboole_0, '#skF_6') | r1_xboole_0('#skF_6', k1_tarski(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_32198, c_26])).
% 11.75/4.66  tff(c_32242, plain, (r1_xboole_0('#skF_6', k1_tarski(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_32226])).
% 11.75/4.66  tff(c_1021, plain, (![A_12, B_13]: (~r1_xboole_0(A_12, B_13) | k3_xboole_0(A_12, B_13)=k1_xboole_0)), inference(resolution, [status(thm)], [c_967, c_30])).
% 11.75/4.66  tff(c_32359, plain, (k3_xboole_0('#skF_6', k1_tarski(k1_xboole_0))=k1_xboole_0), inference(resolution, [status(thm)], [c_32242, c_1021])).
% 11.75/4.66  tff(c_32552, plain, (k4_xboole_0('#skF_6', k1_tarski(k1_xboole_0))=k5_xboole_0('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_32359, c_32])).
% 11.75/4.66  tff(c_32639, plain, (k4_xboole_0('#skF_6', k1_tarski(k1_xboole_0))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1109, c_32552])).
% 11.75/4.66  tff(c_32641, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2214, c_32639])).
% 11.75/4.66  tff(c_32642, plain, (r2_hidden(k1_xboole_0, '#skF_6')), inference(splitRight, [status(thm)], [c_32226])).
% 11.75/4.66  tff(c_54, plain, (![C_42, B_40, A_36]: (~v1_xboole_0(C_42) | ~r2_hidden(C_42, B_40) | ~m1_subset_1(B_40, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_36)))) | ~v13_waybel_0(B_40, k3_yellow_1(A_36)) | ~v2_waybel_0(B_40, k3_yellow_1(A_36)) | ~v1_subset_1(B_40, u1_struct_0(k3_yellow_1(A_36))) | v1_xboole_0(B_40) | v1_xboole_0(A_36))), inference(cnfTransformation, [status(thm)], [f_140])).
% 11.75/4.66  tff(c_32663, plain, (![A_36]: (~v1_xboole_0(k1_xboole_0) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_36)))) | ~v13_waybel_0('#skF_6', k3_yellow_1(A_36)) | ~v2_waybel_0('#skF_6', k3_yellow_1(A_36)) | ~v1_subset_1('#skF_6', u1_struct_0(k3_yellow_1(A_36))) | v1_xboole_0('#skF_6') | v1_xboole_0(A_36))), inference(resolution, [status(thm)], [c_32642, c_54])).
% 11.75/4.66  tff(c_32668, plain, (![A_36]: (~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_36)))) | ~v13_waybel_0('#skF_6', k3_yellow_1(A_36)) | ~v2_waybel_0('#skF_6', k3_yellow_1(A_36)) | ~v1_subset_1('#skF_6', u1_struct_0(k3_yellow_1(A_36))) | v1_xboole_0('#skF_6') | v1_xboole_0(A_36))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_32663])).
% 11.75/4.66  tff(c_32802, plain, (![A_675]: (~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_675)))) | ~v13_waybel_0('#skF_6', k3_yellow_1(A_675)) | ~v2_waybel_0('#skF_6', k3_yellow_1(A_675)) | ~v1_subset_1('#skF_6', u1_struct_0(k3_yellow_1(A_675))) | v1_xboole_0(A_675))), inference(negUnitSimplification, [status(thm)], [c_66, c_32668])).
% 11.75/4.66  tff(c_32805, plain, (~v13_waybel_0('#skF_6', k3_yellow_1(k2_struct_0('#skF_5'))) | ~v2_waybel_0('#skF_6', k3_yellow_1(k2_struct_0('#skF_5'))) | ~v1_subset_1('#skF_6', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))) | v1_xboole_0(k2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_58, c_32802])).
% 11.75/4.66  tff(c_32808, plain, (v1_xboole_0(k2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_32805])).
% 11.75/4.66  tff(c_32810, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30633, c_32808])).
% 11.75/4.66  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.75/4.66  
% 11.75/4.66  Inference rules
% 11.75/4.66  ----------------------
% 11.75/4.66  #Ref     : 0
% 11.75/4.66  #Sup     : 8166
% 11.75/4.66  #Fact    : 0
% 11.75/4.66  #Define  : 0
% 11.75/4.66  #Split   : 3
% 11.75/4.66  #Chain   : 0
% 11.75/4.66  #Close   : 0
% 11.75/4.66  
% 11.75/4.66  Ordering : KBO
% 11.75/4.66  
% 11.75/4.66  Simplification rules
% 11.75/4.66  ----------------------
% 11.75/4.66  #Subsume      : 1201
% 11.75/4.66  #Demod        : 8560
% 11.75/4.66  #Tautology    : 4904
% 11.75/4.66  #SimpNegUnit  : 119
% 11.75/4.66  #BackRed      : 6
% 11.75/4.66  
% 11.75/4.66  #Partial instantiations: 0
% 11.75/4.66  #Strategies tried      : 1
% 11.75/4.66  
% 11.75/4.66  Timing (in seconds)
% 11.75/4.66  ----------------------
% 11.75/4.66  Preprocessing        : 0.36
% 11.75/4.66  Parsing              : 0.20
% 11.75/4.66  CNF conversion       : 0.03
% 11.75/4.66  Main loop            : 3.48
% 11.75/4.66  Inferencing          : 0.75
% 11.75/4.66  Reduction            : 1.58
% 11.75/4.66  Demodulation         : 1.31
% 11.75/4.66  BG Simplification    : 0.08
% 11.75/4.66  Subsumption          : 0.88
% 11.75/4.66  Abstraction          : 0.14
% 11.75/4.66  MUC search           : 0.00
% 11.75/4.66  Cooper               : 0.00
% 11.75/4.66  Total                : 3.88
% 11.75/4.66  Index Insertion      : 0.00
% 11.75/4.66  Index Deletion       : 0.00
% 11.75/4.66  Index Matching       : 0.00
% 11.75/4.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
