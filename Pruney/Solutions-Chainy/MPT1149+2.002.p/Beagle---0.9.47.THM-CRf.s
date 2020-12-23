%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:23 EST 2020

% Result     : Theorem 14.20s
% Output     : CNFRefutation 14.20s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 178 expanded)
%              Number of leaves         :   36 (  81 expanded)
%              Depth                    :   14
%              Number of atoms          :  192 ( 517 expanded)
%              Number of equality atoms :   18 (  62 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k1_orders_2 > a_2_0_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff(k1_orders_2,type,(
    k1_orders_2: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(a_2_0_orders_2,type,(
    a_2_0_orders_2: ( $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(r2_orders_2,type,(
    r2_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_struct_0,type,(
    k1_struct_0: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_151,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => k1_orders_2(A,k1_struct_0(A)) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_orders_2)).

tff(f_40,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_91,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_orders_2(A,B) = a_2_0_orders_2(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_orders_2)).

tff(f_106,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_orders_2(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_orders_2)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( ! [D] :
                ( m1_subset_1(D,A)
               => ( r2_hidden(D,B)
                 => r2_hidden(D,C) ) )
           => r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_subset_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_137,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(B)
        & v3_orders_2(B)
        & v4_orders_2(B)
        & v5_orders_2(B)
        & l1_orders_2(B)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B))) )
     => ( r2_hidden(A,a_2_0_orders_2(B,C))
      <=> ? [D] :
            ( m1_subset_1(D,u1_struct_0(B))
            & A = D
            & ! [E] :
                ( m1_subset_1(E,u1_struct_0(B))
               => ( r2_hidden(E,C)
                 => r2_orders_2(B,E,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_0_orders_2)).

tff(f_110,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_75,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k1_struct_0(A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_struct_0)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_8,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_22,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(A_14,k1_zfmisc_1(B_15))
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_56,plain,(
    v3_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_54,plain,(
    v4_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_52,plain,(
    v5_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_50,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_12,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_249,plain,(
    ! [A_94,B_95] :
      ( k1_orders_2(A_94,B_95) = a_2_0_orders_2(A_94,B_95)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ l1_orders_2(A_94)
      | ~ v5_orders_2(A_94)
      | ~ v4_orders_2(A_94)
      | ~ v3_orders_2(A_94)
      | v2_struct_0(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_350,plain,(
    ! [A_113] :
      ( k1_orders_2(A_113,k1_xboole_0) = a_2_0_orders_2(A_113,k1_xboole_0)
      | ~ l1_orders_2(A_113)
      | ~ v5_orders_2(A_113)
      | ~ v4_orders_2(A_113)
      | ~ v3_orders_2(A_113)
      | v2_struct_0(A_113) ) ),
    inference(resolution,[status(thm)],[c_12,c_249])).

tff(c_353,plain,
    ( k1_orders_2('#skF_4',k1_xboole_0) = a_2_0_orders_2('#skF_4',k1_xboole_0)
    | ~ l1_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_350])).

tff(c_356,plain,
    ( k1_orders_2('#skF_4',k1_xboole_0) = a_2_0_orders_2('#skF_4',k1_xboole_0)
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_50,c_353])).

tff(c_357,plain,(
    k1_orders_2('#skF_4',k1_xboole_0) = a_2_0_orders_2('#skF_4',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_356])).

tff(c_32,plain,(
    ! [A_26,B_27] :
      ( m1_subset_1(k1_orders_2(A_26,B_27),k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ m1_subset_1(B_27,k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ l1_orders_2(A_26)
      | ~ v5_orders_2(A_26)
      | ~ v4_orders_2(A_26)
      | ~ v3_orders_2(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_362,plain,
    ( m1_subset_1(a_2_0_orders_2('#skF_4',k1_xboole_0),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_357,c_32])).

tff(c_366,plain,
    ( m1_subset_1(a_2_0_orders_2('#skF_4',k1_xboole_0),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_12,c_362])).

tff(c_367,plain,(
    m1_subset_1(a_2_0_orders_2('#skF_4',k1_xboole_0),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_366])).

tff(c_18,plain,(
    ! [A_7,B_8,C_12] :
      ( m1_subset_1('#skF_1'(A_7,B_8,C_12),A_7)
      | r1_tarski(B_8,C_12)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(A_7))
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_130,plain,(
    ! [C_60,B_61,A_62] :
      ( ~ v1_xboole_0(C_60)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(C_60))
      | ~ r2_hidden(A_62,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_136,plain,(
    ! [A_6,A_62] :
      ( ~ v1_xboole_0(A_6)
      | ~ r2_hidden(A_62,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_130])).

tff(c_137,plain,(
    ! [A_62] : ~ r2_hidden(A_62,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_136])).

tff(c_523,plain,(
    ! [D_121,B_122,C_123] :
      ( r2_hidden('#skF_3'(D_121,B_122,C_123,D_121),C_123)
      | r2_hidden(D_121,a_2_0_orders_2(B_122,C_123))
      | ~ m1_subset_1(D_121,u1_struct_0(B_122))
      | ~ m1_subset_1(C_123,k1_zfmisc_1(u1_struct_0(B_122)))
      | ~ l1_orders_2(B_122)
      | ~ v5_orders_2(B_122)
      | ~ v4_orders_2(B_122)
      | ~ v3_orders_2(B_122)
      | v2_struct_0(B_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_540,plain,(
    ! [D_121,B_122] :
      ( r2_hidden('#skF_3'(D_121,B_122,k1_xboole_0,D_121),k1_xboole_0)
      | r2_hidden(D_121,a_2_0_orders_2(B_122,k1_xboole_0))
      | ~ m1_subset_1(D_121,u1_struct_0(B_122))
      | ~ l1_orders_2(B_122)
      | ~ v5_orders_2(B_122)
      | ~ v4_orders_2(B_122)
      | ~ v3_orders_2(B_122)
      | v2_struct_0(B_122) ) ),
    inference(resolution,[status(thm)],[c_12,c_523])).

tff(c_672,plain,(
    ! [D_131,B_132] :
      ( r2_hidden(D_131,a_2_0_orders_2(B_132,k1_xboole_0))
      | ~ m1_subset_1(D_131,u1_struct_0(B_132))
      | ~ l1_orders_2(B_132)
      | ~ v5_orders_2(B_132)
      | ~ v4_orders_2(B_132)
      | ~ v3_orders_2(B_132)
      | v2_struct_0(B_132) ) ),
    inference(negUnitSimplification,[status(thm)],[c_137,c_540])).

tff(c_14,plain,(
    ! [A_7,B_8,C_12] :
      ( ~ r2_hidden('#skF_1'(A_7,B_8,C_12),C_12)
      | r1_tarski(B_8,C_12)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(A_7))
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_10583,plain,(
    ! [B_533,B_534,A_535] :
      ( r1_tarski(B_533,a_2_0_orders_2(B_534,k1_xboole_0))
      | ~ m1_subset_1(a_2_0_orders_2(B_534,k1_xboole_0),k1_zfmisc_1(A_535))
      | ~ m1_subset_1(B_533,k1_zfmisc_1(A_535))
      | ~ m1_subset_1('#skF_1'(A_535,B_533,a_2_0_orders_2(B_534,k1_xboole_0)),u1_struct_0(B_534))
      | ~ l1_orders_2(B_534)
      | ~ v5_orders_2(B_534)
      | ~ v4_orders_2(B_534)
      | ~ v3_orders_2(B_534)
      | v2_struct_0(B_534) ) ),
    inference(resolution,[status(thm)],[c_672,c_14])).

tff(c_23232,plain,(
    ! [B_911,B_912] :
      ( ~ l1_orders_2(B_911)
      | ~ v5_orders_2(B_911)
      | ~ v4_orders_2(B_911)
      | ~ v3_orders_2(B_911)
      | v2_struct_0(B_911)
      | r1_tarski(B_912,a_2_0_orders_2(B_911,k1_xboole_0))
      | ~ m1_subset_1(a_2_0_orders_2(B_911,k1_xboole_0),k1_zfmisc_1(u1_struct_0(B_911)))
      | ~ m1_subset_1(B_912,k1_zfmisc_1(u1_struct_0(B_911))) ) ),
    inference(resolution,[status(thm)],[c_18,c_10583])).

tff(c_23234,plain,(
    ! [B_912] :
      ( ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4')
      | r1_tarski(B_912,a_2_0_orders_2('#skF_4',k1_xboole_0))
      | ~ m1_subset_1(B_912,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_367,c_23232])).

tff(c_23240,plain,(
    ! [B_912] :
      ( v2_struct_0('#skF_4')
      | r1_tarski(B_912,a_2_0_orders_2('#skF_4',k1_xboole_0))
      | ~ m1_subset_1(B_912,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_23234])).

tff(c_23243,plain,(
    ! [B_913] :
      ( r1_tarski(B_913,a_2_0_orders_2('#skF_4',k1_xboole_0))
      | ~ m1_subset_1(B_913,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_23240])).

tff(c_23364,plain,(
    ! [A_914] :
      ( r1_tarski(A_914,a_2_0_orders_2('#skF_4',k1_xboole_0))
      | ~ r1_tarski(A_914,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_22,c_23243])).

tff(c_34,plain,(
    ! [A_28] :
      ( l1_struct_0(A_28)
      | ~ l1_orders_2(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_63,plain,(
    ! [A_45] :
      ( k1_struct_0(A_45) = k1_xboole_0
      | ~ l1_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_68,plain,(
    ! [A_46] :
      ( k1_struct_0(A_46) = k1_xboole_0
      | ~ l1_orders_2(A_46) ) ),
    inference(resolution,[status(thm)],[c_34,c_63])).

tff(c_72,plain,(
    k1_struct_0('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_50,c_68])).

tff(c_48,plain,(
    k1_orders_2('#skF_4',k1_struct_0('#skF_4')) != u1_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_73,plain,(
    k1_orders_2('#skF_4',k1_xboole_0) != u1_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_48])).

tff(c_358,plain,(
    a_2_0_orders_2('#skF_4',k1_xboole_0) != u1_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_357,c_73])).

tff(c_20,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,B_15)
      | ~ m1_subset_1(A_14,k1_zfmisc_1(B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_385,plain,(
    r1_tarski(a_2_0_orders_2('#skF_4',k1_xboole_0),u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_367,c_20])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_394,plain,
    ( a_2_0_orders_2('#skF_4',k1_xboole_0) = u1_struct_0('#skF_4')
    | ~ r1_tarski(u1_struct_0('#skF_4'),a_2_0_orders_2('#skF_4',k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_385,c_4])).

tff(c_402,plain,(
    ~ r1_tarski(u1_struct_0('#skF_4'),a_2_0_orders_2('#skF_4',k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_358,c_394])).

tff(c_23439,plain,(
    ~ r1_tarski(u1_struct_0('#skF_4'),u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_23364,c_402])).

tff(c_23487,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_23439])).

tff(c_23488,plain,(
    ! [A_6] : ~ v1_xboole_0(A_6) ),
    inference(splitRight,[status(thm)],[c_136])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_23490,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_23488,c_2])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:27:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.20/6.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.20/6.45  
% 14.20/6.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.20/6.46  %$ r2_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k1_orders_2 > a_2_0_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_4 > #skF_3
% 14.20/6.46  
% 14.20/6.46  %Foreground sorts:
% 14.20/6.46  
% 14.20/6.46  
% 14.20/6.46  %Background operators:
% 14.20/6.46  
% 14.20/6.46  
% 14.20/6.46  %Foreground operators:
% 14.20/6.46  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 14.20/6.46  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 14.20/6.46  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 14.20/6.46  tff(k1_orders_2, type, k1_orders_2: ($i * $i) > $i).
% 14.20/6.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.20/6.46  tff(a_2_0_orders_2, type, a_2_0_orders_2: ($i * $i) > $i).
% 14.20/6.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 14.20/6.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 14.20/6.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.20/6.46  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 14.20/6.46  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 14.20/6.46  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 14.20/6.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 14.20/6.46  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 14.20/6.46  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 14.20/6.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.20/6.46  tff('#skF_4', type, '#skF_4': $i).
% 14.20/6.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.20/6.46  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 14.20/6.46  tff(k1_struct_0, type, k1_struct_0: $i > $i).
% 14.20/6.46  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 14.20/6.46  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 14.20/6.46  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 14.20/6.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 14.20/6.46  
% 14.20/6.47  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 14.20/6.47  tff(f_58, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 14.20/6.47  tff(f_151, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (k1_orders_2(A, k1_struct_0(A)) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_orders_2)).
% 14.20/6.47  tff(f_40, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 14.20/6.47  tff(f_91, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_orders_2(A, B) = a_2_0_orders_2(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_orders_2)).
% 14.20/6.47  tff(f_106, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_orders_2(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_orders_2)).
% 14.20/6.47  tff(f_54, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) => r2_hidden(D, C)))) => r1_tarski(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_subset_1)).
% 14.20/6.47  tff(f_71, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 14.20/6.47  tff(f_137, axiom, (![A, B, C]: ((((((~v2_struct_0(B) & v3_orders_2(B)) & v4_orders_2(B)) & v5_orders_2(B)) & l1_orders_2(B)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B)))) => (r2_hidden(A, a_2_0_orders_2(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r2_hidden(E, C) => r2_orders_2(B, E, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fraenkel_a_2_0_orders_2)).
% 14.20/6.47  tff(f_110, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 14.20/6.47  tff(f_75, axiom, (![A]: (l1_struct_0(A) => (k1_struct_0(A) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_struct_0)).
% 14.20/6.47  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 14.20/6.47  tff(c_8, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 14.20/6.47  tff(c_22, plain, (![A_14, B_15]: (m1_subset_1(A_14, k1_zfmisc_1(B_15)) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_58])).
% 14.20/6.47  tff(c_58, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_151])).
% 14.20/6.47  tff(c_56, plain, (v3_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_151])).
% 14.20/6.47  tff(c_54, plain, (v4_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_151])).
% 14.20/6.47  tff(c_52, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_151])).
% 14.20/6.47  tff(c_50, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_151])).
% 14.20/6.47  tff(c_12, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 14.20/6.47  tff(c_249, plain, (![A_94, B_95]: (k1_orders_2(A_94, B_95)=a_2_0_orders_2(A_94, B_95) | ~m1_subset_1(B_95, k1_zfmisc_1(u1_struct_0(A_94))) | ~l1_orders_2(A_94) | ~v5_orders_2(A_94) | ~v4_orders_2(A_94) | ~v3_orders_2(A_94) | v2_struct_0(A_94))), inference(cnfTransformation, [status(thm)], [f_91])).
% 14.20/6.47  tff(c_350, plain, (![A_113]: (k1_orders_2(A_113, k1_xboole_0)=a_2_0_orders_2(A_113, k1_xboole_0) | ~l1_orders_2(A_113) | ~v5_orders_2(A_113) | ~v4_orders_2(A_113) | ~v3_orders_2(A_113) | v2_struct_0(A_113))), inference(resolution, [status(thm)], [c_12, c_249])).
% 14.20/6.47  tff(c_353, plain, (k1_orders_2('#skF_4', k1_xboole_0)=a_2_0_orders_2('#skF_4', k1_xboole_0) | ~l1_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_52, c_350])).
% 14.20/6.47  tff(c_356, plain, (k1_orders_2('#skF_4', k1_xboole_0)=a_2_0_orders_2('#skF_4', k1_xboole_0) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_50, c_353])).
% 14.20/6.47  tff(c_357, plain, (k1_orders_2('#skF_4', k1_xboole_0)=a_2_0_orders_2('#skF_4', k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_58, c_356])).
% 14.20/6.47  tff(c_32, plain, (![A_26, B_27]: (m1_subset_1(k1_orders_2(A_26, B_27), k1_zfmisc_1(u1_struct_0(A_26))) | ~m1_subset_1(B_27, k1_zfmisc_1(u1_struct_0(A_26))) | ~l1_orders_2(A_26) | ~v5_orders_2(A_26) | ~v4_orders_2(A_26) | ~v3_orders_2(A_26) | v2_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_106])).
% 14.20/6.47  tff(c_362, plain, (m1_subset_1(a_2_0_orders_2('#skF_4', k1_xboole_0), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_357, c_32])).
% 14.20/6.47  tff(c_366, plain, (m1_subset_1(a_2_0_orders_2('#skF_4', k1_xboole_0), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_12, c_362])).
% 14.20/6.47  tff(c_367, plain, (m1_subset_1(a_2_0_orders_2('#skF_4', k1_xboole_0), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_58, c_366])).
% 14.20/6.47  tff(c_18, plain, (![A_7, B_8, C_12]: (m1_subset_1('#skF_1'(A_7, B_8, C_12), A_7) | r1_tarski(B_8, C_12) | ~m1_subset_1(C_12, k1_zfmisc_1(A_7)) | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 14.20/6.47  tff(c_130, plain, (![C_60, B_61, A_62]: (~v1_xboole_0(C_60) | ~m1_subset_1(B_61, k1_zfmisc_1(C_60)) | ~r2_hidden(A_62, B_61))), inference(cnfTransformation, [status(thm)], [f_71])).
% 14.20/6.47  tff(c_136, plain, (![A_6, A_62]: (~v1_xboole_0(A_6) | ~r2_hidden(A_62, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_130])).
% 14.20/6.47  tff(c_137, plain, (![A_62]: (~r2_hidden(A_62, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_136])).
% 14.20/6.47  tff(c_523, plain, (![D_121, B_122, C_123]: (r2_hidden('#skF_3'(D_121, B_122, C_123, D_121), C_123) | r2_hidden(D_121, a_2_0_orders_2(B_122, C_123)) | ~m1_subset_1(D_121, u1_struct_0(B_122)) | ~m1_subset_1(C_123, k1_zfmisc_1(u1_struct_0(B_122))) | ~l1_orders_2(B_122) | ~v5_orders_2(B_122) | ~v4_orders_2(B_122) | ~v3_orders_2(B_122) | v2_struct_0(B_122))), inference(cnfTransformation, [status(thm)], [f_137])).
% 14.20/6.47  tff(c_540, plain, (![D_121, B_122]: (r2_hidden('#skF_3'(D_121, B_122, k1_xboole_0, D_121), k1_xboole_0) | r2_hidden(D_121, a_2_0_orders_2(B_122, k1_xboole_0)) | ~m1_subset_1(D_121, u1_struct_0(B_122)) | ~l1_orders_2(B_122) | ~v5_orders_2(B_122) | ~v4_orders_2(B_122) | ~v3_orders_2(B_122) | v2_struct_0(B_122))), inference(resolution, [status(thm)], [c_12, c_523])).
% 14.20/6.47  tff(c_672, plain, (![D_131, B_132]: (r2_hidden(D_131, a_2_0_orders_2(B_132, k1_xboole_0)) | ~m1_subset_1(D_131, u1_struct_0(B_132)) | ~l1_orders_2(B_132) | ~v5_orders_2(B_132) | ~v4_orders_2(B_132) | ~v3_orders_2(B_132) | v2_struct_0(B_132))), inference(negUnitSimplification, [status(thm)], [c_137, c_540])).
% 14.20/6.47  tff(c_14, plain, (![A_7, B_8, C_12]: (~r2_hidden('#skF_1'(A_7, B_8, C_12), C_12) | r1_tarski(B_8, C_12) | ~m1_subset_1(C_12, k1_zfmisc_1(A_7)) | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 14.20/6.47  tff(c_10583, plain, (![B_533, B_534, A_535]: (r1_tarski(B_533, a_2_0_orders_2(B_534, k1_xboole_0)) | ~m1_subset_1(a_2_0_orders_2(B_534, k1_xboole_0), k1_zfmisc_1(A_535)) | ~m1_subset_1(B_533, k1_zfmisc_1(A_535)) | ~m1_subset_1('#skF_1'(A_535, B_533, a_2_0_orders_2(B_534, k1_xboole_0)), u1_struct_0(B_534)) | ~l1_orders_2(B_534) | ~v5_orders_2(B_534) | ~v4_orders_2(B_534) | ~v3_orders_2(B_534) | v2_struct_0(B_534))), inference(resolution, [status(thm)], [c_672, c_14])).
% 14.20/6.47  tff(c_23232, plain, (![B_911, B_912]: (~l1_orders_2(B_911) | ~v5_orders_2(B_911) | ~v4_orders_2(B_911) | ~v3_orders_2(B_911) | v2_struct_0(B_911) | r1_tarski(B_912, a_2_0_orders_2(B_911, k1_xboole_0)) | ~m1_subset_1(a_2_0_orders_2(B_911, k1_xboole_0), k1_zfmisc_1(u1_struct_0(B_911))) | ~m1_subset_1(B_912, k1_zfmisc_1(u1_struct_0(B_911))))), inference(resolution, [status(thm)], [c_18, c_10583])).
% 14.20/6.47  tff(c_23234, plain, (![B_912]: (~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4') | r1_tarski(B_912, a_2_0_orders_2('#skF_4', k1_xboole_0)) | ~m1_subset_1(B_912, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_367, c_23232])).
% 14.20/6.47  tff(c_23240, plain, (![B_912]: (v2_struct_0('#skF_4') | r1_tarski(B_912, a_2_0_orders_2('#skF_4', k1_xboole_0)) | ~m1_subset_1(B_912, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_23234])).
% 14.20/6.47  tff(c_23243, plain, (![B_913]: (r1_tarski(B_913, a_2_0_orders_2('#skF_4', k1_xboole_0)) | ~m1_subset_1(B_913, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_58, c_23240])).
% 14.20/6.47  tff(c_23364, plain, (![A_914]: (r1_tarski(A_914, a_2_0_orders_2('#skF_4', k1_xboole_0)) | ~r1_tarski(A_914, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_22, c_23243])).
% 14.20/6.47  tff(c_34, plain, (![A_28]: (l1_struct_0(A_28) | ~l1_orders_2(A_28))), inference(cnfTransformation, [status(thm)], [f_110])).
% 14.20/6.47  tff(c_63, plain, (![A_45]: (k1_struct_0(A_45)=k1_xboole_0 | ~l1_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_75])).
% 14.20/6.47  tff(c_68, plain, (![A_46]: (k1_struct_0(A_46)=k1_xboole_0 | ~l1_orders_2(A_46))), inference(resolution, [status(thm)], [c_34, c_63])).
% 14.20/6.47  tff(c_72, plain, (k1_struct_0('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_50, c_68])).
% 14.20/6.47  tff(c_48, plain, (k1_orders_2('#skF_4', k1_struct_0('#skF_4'))!=u1_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_151])).
% 14.20/6.47  tff(c_73, plain, (k1_orders_2('#skF_4', k1_xboole_0)!=u1_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_48])).
% 14.20/6.47  tff(c_358, plain, (a_2_0_orders_2('#skF_4', k1_xboole_0)!=u1_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_357, c_73])).
% 14.20/6.47  tff(c_20, plain, (![A_14, B_15]: (r1_tarski(A_14, B_15) | ~m1_subset_1(A_14, k1_zfmisc_1(B_15)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 14.20/6.47  tff(c_385, plain, (r1_tarski(a_2_0_orders_2('#skF_4', k1_xboole_0), u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_367, c_20])).
% 14.20/6.47  tff(c_4, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 14.20/6.47  tff(c_394, plain, (a_2_0_orders_2('#skF_4', k1_xboole_0)=u1_struct_0('#skF_4') | ~r1_tarski(u1_struct_0('#skF_4'), a_2_0_orders_2('#skF_4', k1_xboole_0))), inference(resolution, [status(thm)], [c_385, c_4])).
% 14.20/6.47  tff(c_402, plain, (~r1_tarski(u1_struct_0('#skF_4'), a_2_0_orders_2('#skF_4', k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_358, c_394])).
% 14.20/6.47  tff(c_23439, plain, (~r1_tarski(u1_struct_0('#skF_4'), u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_23364, c_402])).
% 14.20/6.47  tff(c_23487, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_23439])).
% 14.20/6.47  tff(c_23488, plain, (![A_6]: (~v1_xboole_0(A_6))), inference(splitRight, [status(thm)], [c_136])).
% 14.20/6.47  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 14.20/6.47  tff(c_23490, plain, $false, inference(negUnitSimplification, [status(thm)], [c_23488, c_2])).
% 14.20/6.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.20/6.47  
% 14.20/6.47  Inference rules
% 14.20/6.47  ----------------------
% 14.20/6.47  #Ref     : 0
% 14.20/6.47  #Sup     : 5492
% 14.20/6.47  #Fact    : 16
% 14.20/6.47  #Define  : 0
% 14.20/6.47  #Split   : 22
% 14.20/6.47  #Chain   : 0
% 14.20/6.47  #Close   : 0
% 14.20/6.47  
% 14.20/6.47  Ordering : KBO
% 14.20/6.47  
% 14.20/6.47  Simplification rules
% 14.20/6.47  ----------------------
% 14.20/6.47  #Subsume      : 2662
% 14.20/6.47  #Demod        : 4194
% 14.20/6.47  #Tautology    : 561
% 14.20/6.47  #SimpNegUnit  : 514
% 14.20/6.47  #BackRed      : 6
% 14.20/6.47  
% 14.20/6.47  #Partial instantiations: 0
% 14.20/6.47  #Strategies tried      : 1
% 14.20/6.47  
% 14.20/6.47  Timing (in seconds)
% 14.20/6.47  ----------------------
% 14.20/6.48  Preprocessing        : 0.34
% 14.20/6.48  Parsing              : 0.18
% 14.20/6.48  CNF conversion       : 0.02
% 14.20/6.48  Main loop            : 5.36
% 14.20/6.48  Inferencing          : 1.08
% 14.20/6.48  Reduction            : 1.46
% 14.20/6.48  Demodulation         : 1.04
% 14.20/6.48  BG Simplification    : 0.10
% 14.20/6.48  Subsumption          : 2.46
% 14.20/6.48  Abstraction          : 0.20
% 14.20/6.48  MUC search           : 0.00
% 14.20/6.48  Cooper               : 0.00
% 14.20/6.48  Total                : 5.74
% 14.20/6.48  Index Insertion      : 0.00
% 14.20/6.48  Index Deletion       : 0.00
% 14.20/6.48  Index Matching       : 0.00
% 14.20/6.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
