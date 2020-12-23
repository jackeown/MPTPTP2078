%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:22 EST 2020

% Result     : Theorem 5.85s
% Output     : CNFRefutation 6.15s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 880 expanded)
%              Number of leaves         :   41 ( 322 expanded)
%              Depth                    :   18
%              Number of atoms          :  333 (2209 expanded)
%              Number of equality atoms :   24 ( 563 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r1_orders_2 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > v1_xboole_0 > v1_orders_2 > l1_orders_2 > k11_lattice3 > k3_xboole_0 > k2_zfmisc_1 > g1_orders_2 > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k1_zfmisc_1 > k1_yellow_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_orders_2,type,(
    v1_orders_2: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(r3_orders_2,type,(
    r3_orders_2: ( $i * $i * $i ) > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k11_lattice3,type,(
    k11_lattice3: ( $i * $i * $i ) > $i )).

tff(g1_orders_2,type,(
    g1_orders_2: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k1_yellow_1,type,(
    k1_yellow_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v2_lattice3,type,(
    v2_lattice3: $i > $o )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_119,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(u1_orders_2(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

tff(f_127,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & v3_orders_2(k2_yellow_1(A))
      & v4_orders_2(k2_yellow_1(A))
      & v5_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow_1)).

tff(f_37,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_orders_2(A)
       => A = g1_orders_2(u1_struct_0(A),u1_orders_2(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_orders_2)).

tff(f_115,axiom,(
    ! [A] : k2_yellow_1(A) = g1_orders_2(A,k1_yellow_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_yellow_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
     => ! [C,D] :
          ( g1_orders_2(A,B) = g1_orders_2(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_orders_2)).

tff(f_154,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ( v2_lattice3(k2_yellow_1(A))
         => ! [B] :
              ( m1_subset_1(B,u1_struct_0(k2_yellow_1(A)))
             => ! [C] :
                  ( m1_subset_1(C,u1_struct_0(k2_yellow_1(A)))
                 => r1_tarski(k11_lattice3(k2_yellow_1(A),B,C),k3_xboole_0(B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_yellow_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( ( l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k11_lattice3(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k11_lattice3)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v2_lattice3(A)
       => ~ v2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_lattice3)).

tff(f_113,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( D = k11_lattice3(A,B,C)
                  <=> ( r1_orders_2(A,D,B)
                      & r1_orders_2(A,D,C)
                      & ! [E] :
                          ( m1_subset_1(E,u1_struct_0(A))
                         => ( ( r1_orders_2(A,E,B)
                              & r1_orders_2(A,E,C) )
                           => r1_orders_2(A,E,D) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l28_lattice3)).

tff(f_140,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(k2_yellow_1(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(k2_yellow_1(A)))
             => ( r3_orders_2(k2_yellow_1(A),B,C)
              <=> r1_tarski(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_yellow_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_38,plain,(
    ! [A_66] : l1_orders_2(k2_yellow_1(A_66)) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_6,plain,(
    ! [A_5] :
      ( m1_subset_1(u1_orders_2(A_5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_5),u1_struct_0(A_5))))
      | ~ l1_orders_2(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_40,plain,(
    ! [A_67] : v1_orders_2(k2_yellow_1(A_67)) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_4,plain,(
    ! [A_4] :
      ( g1_orders_2(u1_struct_0(A_4),u1_orders_2(A_4)) = A_4
      | ~ v1_orders_2(A_4)
      | ~ l1_orders_2(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_34,plain,(
    ! [A_65] : g1_orders_2(A_65,k1_yellow_1(A_65)) = k2_yellow_1(A_65) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_109,plain,(
    ! [C_95,A_96,D_97,B_98] :
      ( C_95 = A_96
      | g1_orders_2(C_95,D_97) != g1_orders_2(A_96,B_98)
      | ~ m1_subset_1(B_98,k1_zfmisc_1(k2_zfmisc_1(A_96,A_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_118,plain,(
    ! [A_99,A_100,B_101] :
      ( A_99 = A_100
      | k2_yellow_1(A_100) != g1_orders_2(A_99,B_101)
      | ~ m1_subset_1(B_101,k1_zfmisc_1(k2_zfmisc_1(A_99,A_99))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_109])).

tff(c_120,plain,(
    ! [A_4,A_100] :
      ( u1_struct_0(A_4) = A_100
      | k2_yellow_1(A_100) != A_4
      | ~ m1_subset_1(u1_orders_2(A_4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_4),u1_struct_0(A_4))))
      | ~ v1_orders_2(A_4)
      | ~ l1_orders_2(A_4) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_118])).

tff(c_2508,plain,(
    ! [A_100] :
      ( u1_struct_0(k2_yellow_1(A_100)) = A_100
      | ~ m1_subset_1(u1_orders_2(k2_yellow_1(A_100)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k2_yellow_1(A_100)),u1_struct_0(k2_yellow_1(A_100)))))
      | ~ v1_orders_2(k2_yellow_1(A_100))
      | ~ l1_orders_2(k2_yellow_1(A_100)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_120])).

tff(c_2512,plain,(
    ! [A_460] :
      ( u1_struct_0(k2_yellow_1(A_460)) = A_460
      | ~ m1_subset_1(u1_orders_2(k2_yellow_1(A_460)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k2_yellow_1(A_460)),u1_struct_0(k2_yellow_1(A_460))))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_40,c_2508])).

tff(c_2515,plain,(
    ! [A_460] :
      ( u1_struct_0(k2_yellow_1(A_460)) = A_460
      | ~ l1_orders_2(k2_yellow_1(A_460)) ) ),
    inference(resolution,[status(thm)],[c_6,c_2512])).

tff(c_2518,plain,(
    ! [A_460] : u1_struct_0(k2_yellow_1(A_460)) = A_460 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_2515])).

tff(c_56,plain,(
    m1_subset_1('#skF_3',u1_struct_0(k2_yellow_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_2529,plain,(
    m1_subset_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2518,c_56])).

tff(c_54,plain,(
    m1_subset_1('#skF_4',u1_struct_0(k2_yellow_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_2528,plain,(
    m1_subset_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2518,c_54])).

tff(c_2530,plain,(
    ! [A_461] : u1_struct_0(k2_yellow_1(A_461)) = A_461 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_2515])).

tff(c_18,plain,(
    ! [A_16,B_17,C_18] :
      ( m1_subset_1(k11_lattice3(A_16,B_17,C_18),u1_struct_0(A_16))
      | ~ m1_subset_1(C_18,u1_struct_0(A_16))
      | ~ m1_subset_1(B_17,u1_struct_0(A_16))
      | ~ l1_orders_2(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2540,plain,(
    ! [A_461,B_17,C_18] :
      ( m1_subset_1(k11_lattice3(k2_yellow_1(A_461),B_17,C_18),A_461)
      | ~ m1_subset_1(C_18,u1_struct_0(k2_yellow_1(A_461)))
      | ~ m1_subset_1(B_17,u1_struct_0(k2_yellow_1(A_461)))
      | ~ l1_orders_2(k2_yellow_1(A_461)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2530,c_18])).

tff(c_2559,plain,(
    ! [A_461,B_17,C_18] :
      ( m1_subset_1(k11_lattice3(k2_yellow_1(A_461),B_17,C_18),A_461)
      | ~ m1_subset_1(C_18,A_461)
      | ~ m1_subset_1(B_17,A_461) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_2518,c_2518,c_2540])).

tff(c_58,plain,(
    v2_lattice3(k2_yellow_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_42,plain,(
    ! [A_67] : v3_orders_2(k2_yellow_1(A_67)) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_2441,plain,(
    ! [A_450,B_451,C_452] :
      ( r3_orders_2(A_450,B_451,C_452)
      | ~ r1_orders_2(A_450,B_451,C_452)
      | ~ m1_subset_1(C_452,u1_struct_0(A_450))
      | ~ m1_subset_1(B_451,u1_struct_0(A_450))
      | ~ l1_orders_2(A_450)
      | ~ v3_orders_2(A_450)
      | v2_struct_0(A_450) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2445,plain,(
    ! [B_451] :
      ( r3_orders_2(k2_yellow_1('#skF_2'),B_451,'#skF_4')
      | ~ r1_orders_2(k2_yellow_1('#skF_2'),B_451,'#skF_4')
      | ~ m1_subset_1(B_451,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ v3_orders_2(k2_yellow_1('#skF_2'))
      | v2_struct_0(k2_yellow_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_54,c_2441])).

tff(c_2451,plain,(
    ! [B_451] :
      ( r3_orders_2(k2_yellow_1('#skF_2'),B_451,'#skF_4')
      | ~ r1_orders_2(k2_yellow_1('#skF_2'),B_451,'#skF_4')
      | ~ m1_subset_1(B_451,u1_struct_0(k2_yellow_1('#skF_2')))
      | v2_struct_0(k2_yellow_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_2445])).

tff(c_2455,plain,(
    v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_2451])).

tff(c_16,plain,(
    ! [A_15] :
      ( ~ v2_struct_0(A_15)
      | ~ v2_lattice3(A_15)
      | ~ l1_orders_2(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2458,plain,
    ( ~ v2_lattice3(k2_yellow_1('#skF_2'))
    | ~ l1_orders_2(k2_yellow_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_2455,c_16])).

tff(c_2462,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_58,c_2458])).

tff(c_2464,plain,(
    ~ v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_2451])).

tff(c_46,plain,(
    ! [A_67] : v5_orders_2(k2_yellow_1(A_67)) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_2500,plain,(
    ! [A_455,B_456,C_457] :
      ( r1_orders_2(A_455,k11_lattice3(A_455,B_456,C_457),C_457)
      | ~ m1_subset_1(k11_lattice3(A_455,B_456,C_457),u1_struct_0(A_455))
      | ~ m1_subset_1(C_457,u1_struct_0(A_455))
      | ~ m1_subset_1(B_456,u1_struct_0(A_455))
      | ~ l1_orders_2(A_455)
      | ~ v2_lattice3(A_455)
      | ~ v5_orders_2(A_455)
      | v2_struct_0(A_455) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_3223,plain,(
    ! [A_586,B_587,C_588] :
      ( r1_orders_2(A_586,k11_lattice3(A_586,B_587,C_588),C_588)
      | ~ v2_lattice3(A_586)
      | ~ v5_orders_2(A_586)
      | v2_struct_0(A_586)
      | ~ m1_subset_1(C_588,u1_struct_0(A_586))
      | ~ m1_subset_1(B_587,u1_struct_0(A_586))
      | ~ l1_orders_2(A_586) ) ),
    inference(resolution,[status(thm)],[c_18,c_2500])).

tff(c_60,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_2463,plain,(
    ! [B_451] :
      ( r3_orders_2(k2_yellow_1('#skF_2'),B_451,'#skF_4')
      | ~ r1_orders_2(k2_yellow_1('#skF_2'),B_451,'#skF_4')
      | ~ m1_subset_1(B_451,u1_struct_0(k2_yellow_1('#skF_2'))) ) ),
    inference(splitRight,[status(thm)],[c_2451])).

tff(c_2520,plain,(
    ! [B_451] :
      ( r3_orders_2(k2_yellow_1('#skF_2'),B_451,'#skF_4')
      | ~ r1_orders_2(k2_yellow_1('#skF_2'),B_451,'#skF_4')
      | ~ m1_subset_1(B_451,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2518,c_2463])).

tff(c_50,plain,(
    ! [B_72,C_74,A_68] :
      ( r1_tarski(B_72,C_74)
      | ~ r3_orders_2(k2_yellow_1(A_68),B_72,C_74)
      | ~ m1_subset_1(C_74,u1_struct_0(k2_yellow_1(A_68)))
      | ~ m1_subset_1(B_72,u1_struct_0(k2_yellow_1(A_68)))
      | v1_xboole_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_2885,plain,(
    ! [B_520,C_521,A_522] :
      ( r1_tarski(B_520,C_521)
      | ~ r3_orders_2(k2_yellow_1(A_522),B_520,C_521)
      | ~ m1_subset_1(C_521,A_522)
      | ~ m1_subset_1(B_520,A_522)
      | v1_xboole_0(A_522) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2518,c_2518,c_50])).

tff(c_2897,plain,(
    ! [B_451] :
      ( r1_tarski(B_451,'#skF_4')
      | ~ m1_subset_1('#skF_4','#skF_2')
      | v1_xboole_0('#skF_2')
      | ~ r1_orders_2(k2_yellow_1('#skF_2'),B_451,'#skF_4')
      | ~ m1_subset_1(B_451,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_2520,c_2885])).

tff(c_2918,plain,(
    ! [B_451] :
      ( r1_tarski(B_451,'#skF_4')
      | v1_xboole_0('#skF_2')
      | ~ r1_orders_2(k2_yellow_1('#skF_2'),B_451,'#skF_4')
      | ~ m1_subset_1(B_451,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2528,c_2897])).

tff(c_2919,plain,(
    ! [B_451] :
      ( r1_tarski(B_451,'#skF_4')
      | ~ r1_orders_2(k2_yellow_1('#skF_2'),B_451,'#skF_4')
      | ~ m1_subset_1(B_451,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_2918])).

tff(c_3227,plain,(
    ! [B_587] :
      ( r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),B_587,'#skF_4'),'#skF_4')
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),B_587,'#skF_4'),'#skF_2')
      | ~ v2_lattice3(k2_yellow_1('#skF_2'))
      | ~ v5_orders_2(k2_yellow_1('#skF_2'))
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1('#skF_4',u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ m1_subset_1(B_587,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_3223,c_2919])).

tff(c_3234,plain,(
    ! [B_587] :
      ( r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),B_587,'#skF_4'),'#skF_4')
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),B_587,'#skF_4'),'#skF_2')
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(B_587,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_2518,c_2528,c_2518,c_46,c_58,c_3227])).

tff(c_3240,plain,(
    ! [B_589] :
      ( r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),B_589,'#skF_4'),'#skF_4')
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),B_589,'#skF_4'),'#skF_2')
      | ~ m1_subset_1(B_589,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_2464,c_3234])).

tff(c_263,plain,(
    ! [A_100] :
      ( u1_struct_0(k2_yellow_1(A_100)) = A_100
      | ~ m1_subset_1(u1_orders_2(k2_yellow_1(A_100)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k2_yellow_1(A_100)),u1_struct_0(k2_yellow_1(A_100)))))
      | ~ v1_orders_2(k2_yellow_1(A_100))
      | ~ l1_orders_2(k2_yellow_1(A_100)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_120])).

tff(c_267,plain,(
    ! [A_147] :
      ( u1_struct_0(k2_yellow_1(A_147)) = A_147
      | ~ m1_subset_1(u1_orders_2(k2_yellow_1(A_147)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k2_yellow_1(A_147)),u1_struct_0(k2_yellow_1(A_147))))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_40,c_263])).

tff(c_270,plain,(
    ! [A_147] :
      ( u1_struct_0(k2_yellow_1(A_147)) = A_147
      | ~ l1_orders_2(k2_yellow_1(A_147)) ) ),
    inference(resolution,[status(thm)],[c_6,c_267])).

tff(c_273,plain,(
    ! [A_147] : u1_struct_0(k2_yellow_1(A_147)) = A_147 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_270])).

tff(c_282,plain,(
    m1_subset_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_273,c_56])).

tff(c_189,plain,(
    ! [A_133,B_134,C_135] :
      ( r3_orders_2(k2_yellow_1(A_133),B_134,C_135)
      | ~ r1_tarski(B_134,C_135)
      | ~ m1_subset_1(C_135,u1_struct_0(k2_yellow_1(A_133)))
      | ~ m1_subset_1(B_134,u1_struct_0(k2_yellow_1(A_133)))
      | v1_xboole_0(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_196,plain,(
    ! [B_134] :
      ( r3_orders_2(k2_yellow_1('#skF_2'),B_134,'#skF_3')
      | ~ r1_tarski(B_134,'#skF_3')
      | ~ m1_subset_1(B_134,u1_struct_0(k2_yellow_1('#skF_2')))
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_56,c_189])).

tff(c_205,plain,(
    ! [B_134] :
      ( r3_orders_2(k2_yellow_1('#skF_2'),B_134,'#skF_3')
      | ~ r1_tarski(B_134,'#skF_3')
      | ~ m1_subset_1(B_134,u1_struct_0(k2_yellow_1('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_196])).

tff(c_357,plain,(
    ! [B_154] :
      ( r3_orders_2(k2_yellow_1('#skF_2'),B_154,'#skF_3')
      | ~ r1_tarski(B_154,'#skF_3')
      | ~ m1_subset_1(B_154,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_273,c_205])).

tff(c_14,plain,(
    ! [A_12,B_13,C_14] :
      ( r1_orders_2(A_12,B_13,C_14)
      | ~ r3_orders_2(A_12,B_13,C_14)
      | ~ m1_subset_1(C_14,u1_struct_0(A_12))
      | ~ m1_subset_1(B_13,u1_struct_0(A_12))
      | ~ l1_orders_2(A_12)
      | ~ v3_orders_2(A_12)
      | v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_359,plain,(
    ! [B_154] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),B_154,'#skF_3')
      | ~ m1_subset_1('#skF_3',u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ m1_subset_1(B_154,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ v3_orders_2(k2_yellow_1('#skF_2'))
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ r1_tarski(B_154,'#skF_3')
      | ~ m1_subset_1(B_154,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_357,c_14])).

tff(c_362,plain,(
    ! [B_154] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),B_154,'#skF_3')
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ r1_tarski(B_154,'#skF_3')
      | ~ m1_subset_1(B_154,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_273,c_282,c_273,c_359])).

tff(c_379,plain,(
    v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_362])).

tff(c_382,plain,
    ( ~ v2_lattice3(k2_yellow_1('#skF_2'))
    | ~ l1_orders_2(k2_yellow_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_379,c_16])).

tff(c_386,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_58,c_382])).

tff(c_388,plain,(
    ~ v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_362])).

tff(c_281,plain,(
    m1_subset_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_273,c_54])).

tff(c_283,plain,(
    ! [A_148] : u1_struct_0(k2_yellow_1(A_148)) = A_148 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_270])).

tff(c_289,plain,(
    ! [A_148,B_17,C_18] :
      ( m1_subset_1(k11_lattice3(k2_yellow_1(A_148),B_17,C_18),A_148)
      | ~ m1_subset_1(C_18,u1_struct_0(k2_yellow_1(A_148)))
      | ~ m1_subset_1(B_17,u1_struct_0(k2_yellow_1(A_148)))
      | ~ l1_orders_2(k2_yellow_1(A_148)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_283,c_18])).

tff(c_304,plain,(
    ! [A_148,B_17,C_18] :
      ( m1_subset_1(k11_lattice3(k2_yellow_1(A_148),B_17,C_18),A_148)
      | ~ m1_subset_1(C_18,A_148)
      | ~ m1_subset_1(B_17,A_148) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_273,c_273,c_289])).

tff(c_559,plain,(
    ! [A_180,B_181,C_182] :
      ( r1_orders_2(A_180,k11_lattice3(A_180,B_181,C_182),B_181)
      | ~ m1_subset_1(k11_lattice3(A_180,B_181,C_182),u1_struct_0(A_180))
      | ~ m1_subset_1(C_182,u1_struct_0(A_180))
      | ~ m1_subset_1(B_181,u1_struct_0(A_180))
      | ~ l1_orders_2(A_180)
      | ~ v2_lattice3(A_180)
      | ~ v5_orders_2(A_180)
      | v2_struct_0(A_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_561,plain,(
    ! [A_147,B_181,C_182] :
      ( r1_orders_2(k2_yellow_1(A_147),k11_lattice3(k2_yellow_1(A_147),B_181,C_182),B_181)
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1(A_147),B_181,C_182),A_147)
      | ~ m1_subset_1(C_182,u1_struct_0(k2_yellow_1(A_147)))
      | ~ m1_subset_1(B_181,u1_struct_0(k2_yellow_1(A_147)))
      | ~ l1_orders_2(k2_yellow_1(A_147))
      | ~ v2_lattice3(k2_yellow_1(A_147))
      | ~ v5_orders_2(k2_yellow_1(A_147))
      | v2_struct_0(k2_yellow_1(A_147)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_273,c_559])).

tff(c_2174,plain,(
    ! [A_375,B_376,C_377] :
      ( r1_orders_2(k2_yellow_1(A_375),k11_lattice3(k2_yellow_1(A_375),B_376,C_377),B_376)
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1(A_375),B_376,C_377),A_375)
      | ~ m1_subset_1(C_377,A_375)
      | ~ m1_subset_1(B_376,A_375)
      | ~ v2_lattice3(k2_yellow_1(A_375))
      | v2_struct_0(k2_yellow_1(A_375)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_38,c_273,c_273,c_561])).

tff(c_312,plain,(
    ! [A_149,B_150,C_151] :
      ( r3_orders_2(A_149,B_150,C_151)
      | ~ r1_orders_2(A_149,B_150,C_151)
      | ~ m1_subset_1(C_151,u1_struct_0(A_149))
      | ~ m1_subset_1(B_150,u1_struct_0(A_149))
      | ~ l1_orders_2(A_149)
      | ~ v3_orders_2(A_149)
      | v2_struct_0(A_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_314,plain,(
    ! [A_147,B_150,C_151] :
      ( r3_orders_2(k2_yellow_1(A_147),B_150,C_151)
      | ~ r1_orders_2(k2_yellow_1(A_147),B_150,C_151)
      | ~ m1_subset_1(C_151,A_147)
      | ~ m1_subset_1(B_150,u1_struct_0(k2_yellow_1(A_147)))
      | ~ l1_orders_2(k2_yellow_1(A_147))
      | ~ v3_orders_2(k2_yellow_1(A_147))
      | v2_struct_0(k2_yellow_1(A_147)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_273,c_312])).

tff(c_862,plain,(
    ! [A_261,B_262,C_263] :
      ( r3_orders_2(k2_yellow_1(A_261),B_262,C_263)
      | ~ r1_orders_2(k2_yellow_1(A_261),B_262,C_263)
      | ~ m1_subset_1(C_263,A_261)
      | ~ m1_subset_1(B_262,A_261)
      | v2_struct_0(k2_yellow_1(A_261)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_273,c_314])).

tff(c_280,plain,(
    ! [B_72,C_74,A_68] :
      ( r1_tarski(B_72,C_74)
      | ~ r3_orders_2(k2_yellow_1(A_68),B_72,C_74)
      | ~ m1_subset_1(C_74,A_68)
      | ~ m1_subset_1(B_72,A_68)
      | v1_xboole_0(A_68) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_273,c_273,c_50])).

tff(c_868,plain,(
    ! [B_262,C_263,A_261] :
      ( r1_tarski(B_262,C_263)
      | v1_xboole_0(A_261)
      | ~ r1_orders_2(k2_yellow_1(A_261),B_262,C_263)
      | ~ m1_subset_1(C_263,A_261)
      | ~ m1_subset_1(B_262,A_261)
      | v2_struct_0(k2_yellow_1(A_261)) ) ),
    inference(resolution,[status(thm)],[c_862,c_280])).

tff(c_2302,plain,(
    ! [A_405,B_406,C_407] :
      ( r1_tarski(k11_lattice3(k2_yellow_1(A_405),B_406,C_407),B_406)
      | v1_xboole_0(A_405)
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1(A_405),B_406,C_407),A_405)
      | ~ m1_subset_1(C_407,A_405)
      | ~ m1_subset_1(B_406,A_405)
      | ~ v2_lattice3(k2_yellow_1(A_405))
      | v2_struct_0(k2_yellow_1(A_405)) ) ),
    inference(resolution,[status(thm)],[c_2174,c_868])).

tff(c_2306,plain,(
    ! [A_408,B_409,C_410] :
      ( r1_tarski(k11_lattice3(k2_yellow_1(A_408),B_409,C_410),B_409)
      | v1_xboole_0(A_408)
      | ~ v2_lattice3(k2_yellow_1(A_408))
      | v2_struct_0(k2_yellow_1(A_408))
      | ~ m1_subset_1(C_410,A_408)
      | ~ m1_subset_1(B_409,A_408) ) ),
    inference(resolution,[status(thm)],[c_304,c_2302])).

tff(c_87,plain,(
    ! [A_88,B_89,C_90] :
      ( r1_tarski(A_88,k3_xboole_0(B_89,C_90))
      | ~ r1_tarski(A_88,C_90)
      | ~ r1_tarski(A_88,B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_52,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),k3_xboole_0('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_91,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_4')
    | ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_87,c_52])).

tff(c_128,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_91])).

tff(c_2309,plain,
    ( v1_xboole_0('#skF_2')
    | ~ v2_lattice3(k2_yellow_1('#skF_2'))
    | v2_struct_0(k2_yellow_1('#skF_2'))
    | ~ m1_subset_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_2306,c_128])).

tff(c_2312,plain,
    ( v1_xboole_0('#skF_2')
    | v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_282,c_281,c_58,c_2309])).

tff(c_2314,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_388,c_60,c_2312])).

tff(c_2315,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_91])).

tff(c_3243,plain,
    ( ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_3240,c_2315])).

tff(c_3246,plain,(
    ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2529,c_3243])).

tff(c_3249,plain,
    ( ~ m1_subset_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_2559,c_3246])).

tff(c_3253,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2529,c_2528,c_3249])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:46:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.85/2.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.85/2.15  
% 5.85/2.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.85/2.15  %$ r3_orders_2 > r1_orders_2 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > v1_xboole_0 > v1_orders_2 > l1_orders_2 > k11_lattice3 > k3_xboole_0 > k2_zfmisc_1 > g1_orders_2 > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k1_zfmisc_1 > k1_yellow_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 5.85/2.15  
% 5.85/2.15  %Foreground sorts:
% 5.85/2.15  
% 5.85/2.15  
% 5.85/2.15  %Background operators:
% 5.85/2.15  
% 5.85/2.15  
% 5.85/2.15  %Foreground operators:
% 5.85/2.15  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 5.85/2.15  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.85/2.15  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 5.85/2.15  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 5.85/2.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.85/2.15  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 5.85/2.15  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 5.85/2.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.85/2.15  tff(k11_lattice3, type, k11_lattice3: ($i * $i * $i) > $i).
% 5.85/2.15  tff(g1_orders_2, type, g1_orders_2: ($i * $i) > $i).
% 5.85/2.15  tff('#skF_2', type, '#skF_2': $i).
% 5.85/2.15  tff('#skF_3', type, '#skF_3': $i).
% 5.85/2.15  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 5.85/2.15  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 5.85/2.15  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.85/2.15  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 5.85/2.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.85/2.15  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.85/2.15  tff('#skF_4', type, '#skF_4': $i).
% 5.85/2.15  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 5.85/2.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.85/2.15  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.85/2.15  tff(v2_lattice3, type, v2_lattice3: $i > $o).
% 5.85/2.15  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 5.85/2.15  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 5.85/2.15  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.85/2.15  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.85/2.15  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.85/2.15  
% 6.15/2.17  tff(f_119, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 6.15/2.17  tff(f_41, axiom, (![A]: (l1_orders_2(A) => m1_subset_1(u1_orders_2(A), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_orders_2)).
% 6.15/2.17  tff(f_127, axiom, (![A]: (((v1_orders_2(k2_yellow_1(A)) & v3_orders_2(k2_yellow_1(A))) & v4_orders_2(k2_yellow_1(A))) & v5_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_yellow_1)).
% 6.15/2.17  tff(f_37, axiom, (![A]: (l1_orders_2(A) => (v1_orders_2(A) => (A = g1_orders_2(u1_struct_0(A), u1_orders_2(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', abstractness_v1_orders_2)).
% 6.15/2.17  tff(f_115, axiom, (![A]: (k2_yellow_1(A) = g1_orders_2(A, k1_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_yellow_1)).
% 6.15/2.17  tff(f_50, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A))) => (![C, D]: ((g1_orders_2(A, B) = g1_orders_2(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', free_g1_orders_2)).
% 6.15/2.17  tff(f_154, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (v2_lattice3(k2_yellow_1(A)) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => r1_tarski(k11_lattice3(k2_yellow_1(A), B, C), k3_xboole_0(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_yellow_1)).
% 6.15/2.17  tff(f_80, axiom, (![A, B, C]: (((l1_orders_2(A) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k11_lattice3(A, B, C), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k11_lattice3)).
% 6.15/2.17  tff(f_65, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 6.15/2.17  tff(f_72, axiom, (![A]: (l1_orders_2(A) => (v2_lattice3(A) => ~v2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_lattice3)).
% 6.15/2.17  tff(f_113, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((D = k11_lattice3(A, B, C)) <=> ((r1_orders_2(A, D, B) & r1_orders_2(A, D, C)) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((r1_orders_2(A, E, B) & r1_orders_2(A, E, C)) => r1_orders_2(A, E, D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l28_lattice3)).
% 6.15/2.17  tff(f_140, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => (r3_orders_2(k2_yellow_1(A), B, C) <=> r1_tarski(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_yellow_1)).
% 6.15/2.17  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 6.15/2.17  tff(c_38, plain, (![A_66]: (l1_orders_2(k2_yellow_1(A_66)))), inference(cnfTransformation, [status(thm)], [f_119])).
% 6.15/2.17  tff(c_6, plain, (![A_5]: (m1_subset_1(u1_orders_2(A_5), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_5), u1_struct_0(A_5)))) | ~l1_orders_2(A_5))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.15/2.17  tff(c_40, plain, (![A_67]: (v1_orders_2(k2_yellow_1(A_67)))), inference(cnfTransformation, [status(thm)], [f_127])).
% 6.15/2.17  tff(c_4, plain, (![A_4]: (g1_orders_2(u1_struct_0(A_4), u1_orders_2(A_4))=A_4 | ~v1_orders_2(A_4) | ~l1_orders_2(A_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.15/2.17  tff(c_34, plain, (![A_65]: (g1_orders_2(A_65, k1_yellow_1(A_65))=k2_yellow_1(A_65))), inference(cnfTransformation, [status(thm)], [f_115])).
% 6.15/2.17  tff(c_109, plain, (![C_95, A_96, D_97, B_98]: (C_95=A_96 | g1_orders_2(C_95, D_97)!=g1_orders_2(A_96, B_98) | ~m1_subset_1(B_98, k1_zfmisc_1(k2_zfmisc_1(A_96, A_96))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.15/2.18  tff(c_118, plain, (![A_99, A_100, B_101]: (A_99=A_100 | k2_yellow_1(A_100)!=g1_orders_2(A_99, B_101) | ~m1_subset_1(B_101, k1_zfmisc_1(k2_zfmisc_1(A_99, A_99))))), inference(superposition, [status(thm), theory('equality')], [c_34, c_109])).
% 6.15/2.18  tff(c_120, plain, (![A_4, A_100]: (u1_struct_0(A_4)=A_100 | k2_yellow_1(A_100)!=A_4 | ~m1_subset_1(u1_orders_2(A_4), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_4), u1_struct_0(A_4)))) | ~v1_orders_2(A_4) | ~l1_orders_2(A_4))), inference(superposition, [status(thm), theory('equality')], [c_4, c_118])).
% 6.15/2.18  tff(c_2508, plain, (![A_100]: (u1_struct_0(k2_yellow_1(A_100))=A_100 | ~m1_subset_1(u1_orders_2(k2_yellow_1(A_100)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k2_yellow_1(A_100)), u1_struct_0(k2_yellow_1(A_100))))) | ~v1_orders_2(k2_yellow_1(A_100)) | ~l1_orders_2(k2_yellow_1(A_100)))), inference(reflexivity, [status(thm), theory('equality')], [c_120])).
% 6.15/2.18  tff(c_2512, plain, (![A_460]: (u1_struct_0(k2_yellow_1(A_460))=A_460 | ~m1_subset_1(u1_orders_2(k2_yellow_1(A_460)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k2_yellow_1(A_460)), u1_struct_0(k2_yellow_1(A_460))))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_40, c_2508])).
% 6.15/2.18  tff(c_2515, plain, (![A_460]: (u1_struct_0(k2_yellow_1(A_460))=A_460 | ~l1_orders_2(k2_yellow_1(A_460)))), inference(resolution, [status(thm)], [c_6, c_2512])).
% 6.15/2.18  tff(c_2518, plain, (![A_460]: (u1_struct_0(k2_yellow_1(A_460))=A_460)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_2515])).
% 6.15/2.18  tff(c_56, plain, (m1_subset_1('#skF_3', u1_struct_0(k2_yellow_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_154])).
% 6.15/2.18  tff(c_2529, plain, (m1_subset_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2518, c_56])).
% 6.15/2.18  tff(c_54, plain, (m1_subset_1('#skF_4', u1_struct_0(k2_yellow_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_154])).
% 6.15/2.18  tff(c_2528, plain, (m1_subset_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2518, c_54])).
% 6.15/2.18  tff(c_2530, plain, (![A_461]: (u1_struct_0(k2_yellow_1(A_461))=A_461)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_2515])).
% 6.15/2.18  tff(c_18, plain, (![A_16, B_17, C_18]: (m1_subset_1(k11_lattice3(A_16, B_17, C_18), u1_struct_0(A_16)) | ~m1_subset_1(C_18, u1_struct_0(A_16)) | ~m1_subset_1(B_17, u1_struct_0(A_16)) | ~l1_orders_2(A_16))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.15/2.18  tff(c_2540, plain, (![A_461, B_17, C_18]: (m1_subset_1(k11_lattice3(k2_yellow_1(A_461), B_17, C_18), A_461) | ~m1_subset_1(C_18, u1_struct_0(k2_yellow_1(A_461))) | ~m1_subset_1(B_17, u1_struct_0(k2_yellow_1(A_461))) | ~l1_orders_2(k2_yellow_1(A_461)))), inference(superposition, [status(thm), theory('equality')], [c_2530, c_18])).
% 6.15/2.18  tff(c_2559, plain, (![A_461, B_17, C_18]: (m1_subset_1(k11_lattice3(k2_yellow_1(A_461), B_17, C_18), A_461) | ~m1_subset_1(C_18, A_461) | ~m1_subset_1(B_17, A_461))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_2518, c_2518, c_2540])).
% 6.15/2.18  tff(c_58, plain, (v2_lattice3(k2_yellow_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_154])).
% 6.15/2.18  tff(c_42, plain, (![A_67]: (v3_orders_2(k2_yellow_1(A_67)))), inference(cnfTransformation, [status(thm)], [f_127])).
% 6.15/2.18  tff(c_2441, plain, (![A_450, B_451, C_452]: (r3_orders_2(A_450, B_451, C_452) | ~r1_orders_2(A_450, B_451, C_452) | ~m1_subset_1(C_452, u1_struct_0(A_450)) | ~m1_subset_1(B_451, u1_struct_0(A_450)) | ~l1_orders_2(A_450) | ~v3_orders_2(A_450) | v2_struct_0(A_450))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.15/2.18  tff(c_2445, plain, (![B_451]: (r3_orders_2(k2_yellow_1('#skF_2'), B_451, '#skF_4') | ~r1_orders_2(k2_yellow_1('#skF_2'), B_451, '#skF_4') | ~m1_subset_1(B_451, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v3_orders_2(k2_yellow_1('#skF_2')) | v2_struct_0(k2_yellow_1('#skF_2')))), inference(resolution, [status(thm)], [c_54, c_2441])).
% 6.15/2.18  tff(c_2451, plain, (![B_451]: (r3_orders_2(k2_yellow_1('#skF_2'), B_451, '#skF_4') | ~r1_orders_2(k2_yellow_1('#skF_2'), B_451, '#skF_4') | ~m1_subset_1(B_451, u1_struct_0(k2_yellow_1('#skF_2'))) | v2_struct_0(k2_yellow_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_2445])).
% 6.15/2.18  tff(c_2455, plain, (v2_struct_0(k2_yellow_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_2451])).
% 6.15/2.18  tff(c_16, plain, (![A_15]: (~v2_struct_0(A_15) | ~v2_lattice3(A_15) | ~l1_orders_2(A_15))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.15/2.18  tff(c_2458, plain, (~v2_lattice3(k2_yellow_1('#skF_2')) | ~l1_orders_2(k2_yellow_1('#skF_2'))), inference(resolution, [status(thm)], [c_2455, c_16])).
% 6.15/2.18  tff(c_2462, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_58, c_2458])).
% 6.15/2.18  tff(c_2464, plain, (~v2_struct_0(k2_yellow_1('#skF_2'))), inference(splitRight, [status(thm)], [c_2451])).
% 6.15/2.18  tff(c_46, plain, (![A_67]: (v5_orders_2(k2_yellow_1(A_67)))), inference(cnfTransformation, [status(thm)], [f_127])).
% 6.15/2.18  tff(c_2500, plain, (![A_455, B_456, C_457]: (r1_orders_2(A_455, k11_lattice3(A_455, B_456, C_457), C_457) | ~m1_subset_1(k11_lattice3(A_455, B_456, C_457), u1_struct_0(A_455)) | ~m1_subset_1(C_457, u1_struct_0(A_455)) | ~m1_subset_1(B_456, u1_struct_0(A_455)) | ~l1_orders_2(A_455) | ~v2_lattice3(A_455) | ~v5_orders_2(A_455) | v2_struct_0(A_455))), inference(cnfTransformation, [status(thm)], [f_113])).
% 6.15/2.18  tff(c_3223, plain, (![A_586, B_587, C_588]: (r1_orders_2(A_586, k11_lattice3(A_586, B_587, C_588), C_588) | ~v2_lattice3(A_586) | ~v5_orders_2(A_586) | v2_struct_0(A_586) | ~m1_subset_1(C_588, u1_struct_0(A_586)) | ~m1_subset_1(B_587, u1_struct_0(A_586)) | ~l1_orders_2(A_586))), inference(resolution, [status(thm)], [c_18, c_2500])).
% 6.15/2.18  tff(c_60, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_154])).
% 6.15/2.18  tff(c_2463, plain, (![B_451]: (r3_orders_2(k2_yellow_1('#skF_2'), B_451, '#skF_4') | ~r1_orders_2(k2_yellow_1('#skF_2'), B_451, '#skF_4') | ~m1_subset_1(B_451, u1_struct_0(k2_yellow_1('#skF_2'))))), inference(splitRight, [status(thm)], [c_2451])).
% 6.15/2.18  tff(c_2520, plain, (![B_451]: (r3_orders_2(k2_yellow_1('#skF_2'), B_451, '#skF_4') | ~r1_orders_2(k2_yellow_1('#skF_2'), B_451, '#skF_4') | ~m1_subset_1(B_451, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2518, c_2463])).
% 6.15/2.18  tff(c_50, plain, (![B_72, C_74, A_68]: (r1_tarski(B_72, C_74) | ~r3_orders_2(k2_yellow_1(A_68), B_72, C_74) | ~m1_subset_1(C_74, u1_struct_0(k2_yellow_1(A_68))) | ~m1_subset_1(B_72, u1_struct_0(k2_yellow_1(A_68))) | v1_xboole_0(A_68))), inference(cnfTransformation, [status(thm)], [f_140])).
% 6.15/2.18  tff(c_2885, plain, (![B_520, C_521, A_522]: (r1_tarski(B_520, C_521) | ~r3_orders_2(k2_yellow_1(A_522), B_520, C_521) | ~m1_subset_1(C_521, A_522) | ~m1_subset_1(B_520, A_522) | v1_xboole_0(A_522))), inference(demodulation, [status(thm), theory('equality')], [c_2518, c_2518, c_50])).
% 6.15/2.18  tff(c_2897, plain, (![B_451]: (r1_tarski(B_451, '#skF_4') | ~m1_subset_1('#skF_4', '#skF_2') | v1_xboole_0('#skF_2') | ~r1_orders_2(k2_yellow_1('#skF_2'), B_451, '#skF_4') | ~m1_subset_1(B_451, '#skF_2'))), inference(resolution, [status(thm)], [c_2520, c_2885])).
% 6.15/2.18  tff(c_2918, plain, (![B_451]: (r1_tarski(B_451, '#skF_4') | v1_xboole_0('#skF_2') | ~r1_orders_2(k2_yellow_1('#skF_2'), B_451, '#skF_4') | ~m1_subset_1(B_451, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2528, c_2897])).
% 6.15/2.18  tff(c_2919, plain, (![B_451]: (r1_tarski(B_451, '#skF_4') | ~r1_orders_2(k2_yellow_1('#skF_2'), B_451, '#skF_4') | ~m1_subset_1(B_451, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_60, c_2918])).
% 6.15/2.18  tff(c_3227, plain, (![B_587]: (r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), B_587, '#skF_4'), '#skF_4') | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), B_587, '#skF_4'), '#skF_2') | ~v2_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2')) | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1('#skF_4', u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1(B_587, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')))), inference(resolution, [status(thm)], [c_3223, c_2919])).
% 6.15/2.18  tff(c_3234, plain, (![B_587]: (r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), B_587, '#skF_4'), '#skF_4') | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), B_587, '#skF_4'), '#skF_2') | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(B_587, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_2518, c_2528, c_2518, c_46, c_58, c_3227])).
% 6.15/2.18  tff(c_3240, plain, (![B_589]: (r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), B_589, '#skF_4'), '#skF_4') | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), B_589, '#skF_4'), '#skF_2') | ~m1_subset_1(B_589, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_2464, c_3234])).
% 6.15/2.18  tff(c_263, plain, (![A_100]: (u1_struct_0(k2_yellow_1(A_100))=A_100 | ~m1_subset_1(u1_orders_2(k2_yellow_1(A_100)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k2_yellow_1(A_100)), u1_struct_0(k2_yellow_1(A_100))))) | ~v1_orders_2(k2_yellow_1(A_100)) | ~l1_orders_2(k2_yellow_1(A_100)))), inference(reflexivity, [status(thm), theory('equality')], [c_120])).
% 6.15/2.18  tff(c_267, plain, (![A_147]: (u1_struct_0(k2_yellow_1(A_147))=A_147 | ~m1_subset_1(u1_orders_2(k2_yellow_1(A_147)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k2_yellow_1(A_147)), u1_struct_0(k2_yellow_1(A_147))))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_40, c_263])).
% 6.15/2.18  tff(c_270, plain, (![A_147]: (u1_struct_0(k2_yellow_1(A_147))=A_147 | ~l1_orders_2(k2_yellow_1(A_147)))), inference(resolution, [status(thm)], [c_6, c_267])).
% 6.15/2.18  tff(c_273, plain, (![A_147]: (u1_struct_0(k2_yellow_1(A_147))=A_147)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_270])).
% 6.15/2.18  tff(c_282, plain, (m1_subset_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_273, c_56])).
% 6.15/2.18  tff(c_189, plain, (![A_133, B_134, C_135]: (r3_orders_2(k2_yellow_1(A_133), B_134, C_135) | ~r1_tarski(B_134, C_135) | ~m1_subset_1(C_135, u1_struct_0(k2_yellow_1(A_133))) | ~m1_subset_1(B_134, u1_struct_0(k2_yellow_1(A_133))) | v1_xboole_0(A_133))), inference(cnfTransformation, [status(thm)], [f_140])).
% 6.15/2.18  tff(c_196, plain, (![B_134]: (r3_orders_2(k2_yellow_1('#skF_2'), B_134, '#skF_3') | ~r1_tarski(B_134, '#skF_3') | ~m1_subset_1(B_134, u1_struct_0(k2_yellow_1('#skF_2'))) | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_56, c_189])).
% 6.15/2.18  tff(c_205, plain, (![B_134]: (r3_orders_2(k2_yellow_1('#skF_2'), B_134, '#skF_3') | ~r1_tarski(B_134, '#skF_3') | ~m1_subset_1(B_134, u1_struct_0(k2_yellow_1('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_60, c_196])).
% 6.15/2.18  tff(c_357, plain, (![B_154]: (r3_orders_2(k2_yellow_1('#skF_2'), B_154, '#skF_3') | ~r1_tarski(B_154, '#skF_3') | ~m1_subset_1(B_154, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_273, c_205])).
% 6.15/2.18  tff(c_14, plain, (![A_12, B_13, C_14]: (r1_orders_2(A_12, B_13, C_14) | ~r3_orders_2(A_12, B_13, C_14) | ~m1_subset_1(C_14, u1_struct_0(A_12)) | ~m1_subset_1(B_13, u1_struct_0(A_12)) | ~l1_orders_2(A_12) | ~v3_orders_2(A_12) | v2_struct_0(A_12))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.15/2.18  tff(c_359, plain, (![B_154]: (r1_orders_2(k2_yellow_1('#skF_2'), B_154, '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1(B_154, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v3_orders_2(k2_yellow_1('#skF_2')) | v2_struct_0(k2_yellow_1('#skF_2')) | ~r1_tarski(B_154, '#skF_3') | ~m1_subset_1(B_154, '#skF_2'))), inference(resolution, [status(thm)], [c_357, c_14])).
% 6.15/2.18  tff(c_362, plain, (![B_154]: (r1_orders_2(k2_yellow_1('#skF_2'), B_154, '#skF_3') | v2_struct_0(k2_yellow_1('#skF_2')) | ~r1_tarski(B_154, '#skF_3') | ~m1_subset_1(B_154, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_273, c_282, c_273, c_359])).
% 6.15/2.18  tff(c_379, plain, (v2_struct_0(k2_yellow_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_362])).
% 6.15/2.18  tff(c_382, plain, (~v2_lattice3(k2_yellow_1('#skF_2')) | ~l1_orders_2(k2_yellow_1('#skF_2'))), inference(resolution, [status(thm)], [c_379, c_16])).
% 6.15/2.18  tff(c_386, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_58, c_382])).
% 6.15/2.18  tff(c_388, plain, (~v2_struct_0(k2_yellow_1('#skF_2'))), inference(splitRight, [status(thm)], [c_362])).
% 6.15/2.18  tff(c_281, plain, (m1_subset_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_273, c_54])).
% 6.15/2.18  tff(c_283, plain, (![A_148]: (u1_struct_0(k2_yellow_1(A_148))=A_148)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_270])).
% 6.15/2.18  tff(c_289, plain, (![A_148, B_17, C_18]: (m1_subset_1(k11_lattice3(k2_yellow_1(A_148), B_17, C_18), A_148) | ~m1_subset_1(C_18, u1_struct_0(k2_yellow_1(A_148))) | ~m1_subset_1(B_17, u1_struct_0(k2_yellow_1(A_148))) | ~l1_orders_2(k2_yellow_1(A_148)))), inference(superposition, [status(thm), theory('equality')], [c_283, c_18])).
% 6.15/2.18  tff(c_304, plain, (![A_148, B_17, C_18]: (m1_subset_1(k11_lattice3(k2_yellow_1(A_148), B_17, C_18), A_148) | ~m1_subset_1(C_18, A_148) | ~m1_subset_1(B_17, A_148))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_273, c_273, c_289])).
% 6.15/2.18  tff(c_559, plain, (![A_180, B_181, C_182]: (r1_orders_2(A_180, k11_lattice3(A_180, B_181, C_182), B_181) | ~m1_subset_1(k11_lattice3(A_180, B_181, C_182), u1_struct_0(A_180)) | ~m1_subset_1(C_182, u1_struct_0(A_180)) | ~m1_subset_1(B_181, u1_struct_0(A_180)) | ~l1_orders_2(A_180) | ~v2_lattice3(A_180) | ~v5_orders_2(A_180) | v2_struct_0(A_180))), inference(cnfTransformation, [status(thm)], [f_113])).
% 6.15/2.18  tff(c_561, plain, (![A_147, B_181, C_182]: (r1_orders_2(k2_yellow_1(A_147), k11_lattice3(k2_yellow_1(A_147), B_181, C_182), B_181) | ~m1_subset_1(k11_lattice3(k2_yellow_1(A_147), B_181, C_182), A_147) | ~m1_subset_1(C_182, u1_struct_0(k2_yellow_1(A_147))) | ~m1_subset_1(B_181, u1_struct_0(k2_yellow_1(A_147))) | ~l1_orders_2(k2_yellow_1(A_147)) | ~v2_lattice3(k2_yellow_1(A_147)) | ~v5_orders_2(k2_yellow_1(A_147)) | v2_struct_0(k2_yellow_1(A_147)))), inference(superposition, [status(thm), theory('equality')], [c_273, c_559])).
% 6.15/2.18  tff(c_2174, plain, (![A_375, B_376, C_377]: (r1_orders_2(k2_yellow_1(A_375), k11_lattice3(k2_yellow_1(A_375), B_376, C_377), B_376) | ~m1_subset_1(k11_lattice3(k2_yellow_1(A_375), B_376, C_377), A_375) | ~m1_subset_1(C_377, A_375) | ~m1_subset_1(B_376, A_375) | ~v2_lattice3(k2_yellow_1(A_375)) | v2_struct_0(k2_yellow_1(A_375)))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_38, c_273, c_273, c_561])).
% 6.15/2.18  tff(c_312, plain, (![A_149, B_150, C_151]: (r3_orders_2(A_149, B_150, C_151) | ~r1_orders_2(A_149, B_150, C_151) | ~m1_subset_1(C_151, u1_struct_0(A_149)) | ~m1_subset_1(B_150, u1_struct_0(A_149)) | ~l1_orders_2(A_149) | ~v3_orders_2(A_149) | v2_struct_0(A_149))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.15/2.18  tff(c_314, plain, (![A_147, B_150, C_151]: (r3_orders_2(k2_yellow_1(A_147), B_150, C_151) | ~r1_orders_2(k2_yellow_1(A_147), B_150, C_151) | ~m1_subset_1(C_151, A_147) | ~m1_subset_1(B_150, u1_struct_0(k2_yellow_1(A_147))) | ~l1_orders_2(k2_yellow_1(A_147)) | ~v3_orders_2(k2_yellow_1(A_147)) | v2_struct_0(k2_yellow_1(A_147)))), inference(superposition, [status(thm), theory('equality')], [c_273, c_312])).
% 6.15/2.18  tff(c_862, plain, (![A_261, B_262, C_263]: (r3_orders_2(k2_yellow_1(A_261), B_262, C_263) | ~r1_orders_2(k2_yellow_1(A_261), B_262, C_263) | ~m1_subset_1(C_263, A_261) | ~m1_subset_1(B_262, A_261) | v2_struct_0(k2_yellow_1(A_261)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_273, c_314])).
% 6.15/2.18  tff(c_280, plain, (![B_72, C_74, A_68]: (r1_tarski(B_72, C_74) | ~r3_orders_2(k2_yellow_1(A_68), B_72, C_74) | ~m1_subset_1(C_74, A_68) | ~m1_subset_1(B_72, A_68) | v1_xboole_0(A_68))), inference(demodulation, [status(thm), theory('equality')], [c_273, c_273, c_50])).
% 6.15/2.18  tff(c_868, plain, (![B_262, C_263, A_261]: (r1_tarski(B_262, C_263) | v1_xboole_0(A_261) | ~r1_orders_2(k2_yellow_1(A_261), B_262, C_263) | ~m1_subset_1(C_263, A_261) | ~m1_subset_1(B_262, A_261) | v2_struct_0(k2_yellow_1(A_261)))), inference(resolution, [status(thm)], [c_862, c_280])).
% 6.15/2.18  tff(c_2302, plain, (![A_405, B_406, C_407]: (r1_tarski(k11_lattice3(k2_yellow_1(A_405), B_406, C_407), B_406) | v1_xboole_0(A_405) | ~m1_subset_1(k11_lattice3(k2_yellow_1(A_405), B_406, C_407), A_405) | ~m1_subset_1(C_407, A_405) | ~m1_subset_1(B_406, A_405) | ~v2_lattice3(k2_yellow_1(A_405)) | v2_struct_0(k2_yellow_1(A_405)))), inference(resolution, [status(thm)], [c_2174, c_868])).
% 6.15/2.18  tff(c_2306, plain, (![A_408, B_409, C_410]: (r1_tarski(k11_lattice3(k2_yellow_1(A_408), B_409, C_410), B_409) | v1_xboole_0(A_408) | ~v2_lattice3(k2_yellow_1(A_408)) | v2_struct_0(k2_yellow_1(A_408)) | ~m1_subset_1(C_410, A_408) | ~m1_subset_1(B_409, A_408))), inference(resolution, [status(thm)], [c_304, c_2302])).
% 6.15/2.18  tff(c_87, plain, (![A_88, B_89, C_90]: (r1_tarski(A_88, k3_xboole_0(B_89, C_90)) | ~r1_tarski(A_88, C_90) | ~r1_tarski(A_88, B_89))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.15/2.18  tff(c_52, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), k3_xboole_0('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_154])).
% 6.15/2.18  tff(c_91, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_4') | ~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_87, c_52])).
% 6.15/2.18  tff(c_128, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_91])).
% 6.15/2.18  tff(c_2309, plain, (v1_xboole_0('#skF_2') | ~v2_lattice3(k2_yellow_1('#skF_2')) | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_2306, c_128])).
% 6.15/2.18  tff(c_2312, plain, (v1_xboole_0('#skF_2') | v2_struct_0(k2_yellow_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_282, c_281, c_58, c_2309])).
% 6.15/2.18  tff(c_2314, plain, $false, inference(negUnitSimplification, [status(thm)], [c_388, c_60, c_2312])).
% 6.15/2.18  tff(c_2315, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_91])).
% 6.15/2.18  tff(c_3243, plain, (~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_2') | ~m1_subset_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_3240, c_2315])).
% 6.15/2.18  tff(c_3246, plain, (~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2529, c_3243])).
% 6.15/2.18  tff(c_3249, plain, (~m1_subset_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_2559, c_3246])).
% 6.15/2.18  tff(c_3253, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2529, c_2528, c_3249])).
% 6.15/2.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.15/2.18  
% 6.15/2.18  Inference rules
% 6.15/2.18  ----------------------
% 6.15/2.18  #Ref     : 46
% 6.15/2.18  #Sup     : 684
% 6.15/2.18  #Fact    : 0
% 6.15/2.18  #Define  : 0
% 6.15/2.18  #Split   : 15
% 6.15/2.18  #Chain   : 0
% 6.15/2.18  #Close   : 0
% 6.15/2.18  
% 6.15/2.18  Ordering : KBO
% 6.15/2.18  
% 6.15/2.18  Simplification rules
% 6.15/2.18  ----------------------
% 6.15/2.18  #Subsume      : 238
% 6.15/2.18  #Demod        : 1027
% 6.15/2.18  #Tautology    : 179
% 6.15/2.18  #SimpNegUnit  : 52
% 6.15/2.18  #BackRed      : 42
% 6.15/2.18  
% 6.15/2.18  #Partial instantiations: 0
% 6.15/2.18  #Strategies tried      : 1
% 6.15/2.18  
% 6.15/2.18  Timing (in seconds)
% 6.15/2.18  ----------------------
% 6.15/2.18  Preprocessing        : 0.34
% 6.15/2.18  Parsing              : 0.19
% 6.15/2.18  CNF conversion       : 0.03
% 6.15/2.18  Main loop            : 1.02
% 6.15/2.18  Inferencing          : 0.36
% 6.15/2.18  Reduction            : 0.33
% 6.15/2.18  Demodulation         : 0.23
% 6.15/2.18  BG Simplification    : 0.05
% 6.15/2.18  Subsumption          : 0.22
% 6.15/2.18  Abstraction          : 0.05
% 6.15/2.18  MUC search           : 0.00
% 6.15/2.18  Cooper               : 0.00
% 6.15/2.18  Total                : 1.41
% 6.15/2.18  Index Insertion      : 0.00
% 6.15/2.18  Index Deletion       : 0.00
% 6.15/2.18  Index Matching       : 0.00
% 6.15/2.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
