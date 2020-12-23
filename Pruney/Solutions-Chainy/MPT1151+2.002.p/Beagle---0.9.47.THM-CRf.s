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
% DateTime   : Thu Dec  3 10:19:27 EST 2020

% Result     : Theorem 5.86s
% Output     : CNFRefutation 6.02s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 223 expanded)
%              Number of leaves         :   35 (  96 expanded)
%              Depth                    :   19
%              Number of atoms          :  186 ( 685 expanded)
%              Number of equality atoms :   19 (  82 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_struct_0 > l1_orders_2 > k2_orders_2 > a_2_1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(a_2_1_orders_2,type,(
    a_2_1_orders_2: ( $i * $i ) > $i )).

tff(k2_orders_2,type,(
    k2_orders_2: ( $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_135,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => k2_orders_2(A,k1_struct_0(A)) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_orders_2)).

tff(f_75,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_orders_2(A,B) = a_2_1_orders_2(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_orders_2)).

tff(f_90,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_orders_2(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_orders_2)).

tff(f_121,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(B)
        & v3_orders_2(B)
        & v4_orders_2(B)
        & v5_orders_2(B)
        & l1_orders_2(B)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B))) )
     => ( r2_hidden(A,a_2_1_orders_2(B,C))
      <=> ? [D] :
            ( m1_subset_1(D,u1_struct_0(B))
            & A = D
            & ! [E] :
                ( m1_subset_1(E,u1_struct_0(B))
               => ( r2_hidden(E,C)
                 => r2_orders_2(B,D,E) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).

tff(f_55,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_94,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k1_struct_0(A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_struct_0)).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_18,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,k1_zfmisc_1(B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_127,plain,(
    ! [A_59,C_60,B_61] :
      ( m1_subset_1(A_59,C_60)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(C_60))
      | ~ r2_hidden(A_59,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_131,plain,(
    ! [A_62,B_63,A_64] :
      ( m1_subset_1(A_62,B_63)
      | ~ r2_hidden(A_62,A_64)
      | ~ r1_tarski(A_64,B_63) ) ),
    inference(resolution,[status(thm)],[c_18,c_127])).

tff(c_134,plain,(
    ! [A_1,B_2,B_63] :
      ( m1_subset_1('#skF_1'(A_1,B_2),B_63)
      | ~ r1_tarski(A_1,B_63)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_131])).

tff(c_14,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_52,plain,(
    v3_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_50,plain,(
    v4_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_48,plain,(
    v5_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_46,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_151,plain,(
    ! [A_68,B_69] :
      ( k2_orders_2(A_68,B_69) = a_2_1_orders_2(A_68,B_69)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ l1_orders_2(A_68)
      | ~ v5_orders_2(A_68)
      | ~ v4_orders_2(A_68)
      | ~ v3_orders_2(A_68)
      | v2_struct_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_536,plain,(
    ! [A_119,A_120] :
      ( k2_orders_2(A_119,A_120) = a_2_1_orders_2(A_119,A_120)
      | ~ l1_orders_2(A_119)
      | ~ v5_orders_2(A_119)
      | ~ v4_orders_2(A_119)
      | ~ v3_orders_2(A_119)
      | v2_struct_0(A_119)
      | ~ r1_tarski(A_120,u1_struct_0(A_119)) ) ),
    inference(resolution,[status(thm)],[c_18,c_151])).

tff(c_2762,plain,(
    ! [A_217] :
      ( k2_orders_2(A_217,k1_xboole_0) = a_2_1_orders_2(A_217,k1_xboole_0)
      | ~ l1_orders_2(A_217)
      | ~ v5_orders_2(A_217)
      | ~ v4_orders_2(A_217)
      | ~ v3_orders_2(A_217)
      | v2_struct_0(A_217) ) ),
    inference(resolution,[status(thm)],[c_14,c_536])).

tff(c_2765,plain,
    ( k2_orders_2('#skF_4',k1_xboole_0) = a_2_1_orders_2('#skF_4',k1_xboole_0)
    | ~ l1_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_2762])).

tff(c_2768,plain,
    ( k2_orders_2('#skF_4',k1_xboole_0) = a_2_1_orders_2('#skF_4',k1_xboole_0)
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_46,c_2765])).

tff(c_2769,plain,(
    k2_orders_2('#skF_4',k1_xboole_0) = a_2_1_orders_2('#skF_4',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_2768])).

tff(c_194,plain,(
    ! [A_78,B_79] :
      ( m1_subset_1(k2_orders_2(A_78,B_79),k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ l1_orders_2(A_78)
      | ~ v5_orders_2(A_78)
      | ~ v4_orders_2(A_78)
      | ~ v3_orders_2(A_78)
      | v2_struct_0(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( r1_tarski(A_9,B_10)
      | ~ m1_subset_1(A_9,k1_zfmisc_1(B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_205,plain,(
    ! [A_78,B_79] :
      ( r1_tarski(k2_orders_2(A_78,B_79),u1_struct_0(A_78))
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ l1_orders_2(A_78)
      | ~ v5_orders_2(A_78)
      | ~ v4_orders_2(A_78)
      | ~ v3_orders_2(A_78)
      | v2_struct_0(A_78) ) ),
    inference(resolution,[status(thm)],[c_194,c_16])).

tff(c_2776,plain,
    ( r1_tarski(a_2_1_orders_2('#skF_4',k1_xboole_0),u1_struct_0('#skF_4'))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2769,c_205])).

tff(c_2786,plain,
    ( r1_tarski(a_2_1_orders_2('#skF_4',k1_xboole_0),u1_struct_0('#skF_4'))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_2776])).

tff(c_2787,plain,
    ( r1_tarski(a_2_1_orders_2('#skF_4',k1_xboole_0),u1_struct_0('#skF_4'))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_2786])).

tff(c_2797,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_2787])).

tff(c_2800,plain,(
    ~ r1_tarski(k1_xboole_0,u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_18,c_2797])).

tff(c_2804,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_2800])).

tff(c_2806,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_2787])).

tff(c_34,plain,(
    ! [D_34,B_24,C_25] :
      ( r2_hidden('#skF_3'(D_34,B_24,C_25,D_34),C_25)
      | r2_hidden(D_34,a_2_1_orders_2(B_24,C_25))
      | ~ m1_subset_1(D_34,u1_struct_0(B_24))
      | ~ m1_subset_1(C_25,k1_zfmisc_1(u1_struct_0(B_24)))
      | ~ l1_orders_2(B_24)
      | ~ v5_orders_2(B_24)
      | ~ v4_orders_2(B_24)
      | ~ v3_orders_2(B_24)
      | v2_struct_0(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_2858,plain,(
    ! [D_34] :
      ( r2_hidden('#skF_3'(D_34,'#skF_4',k1_xboole_0,D_34),k1_xboole_0)
      | r2_hidden(D_34,a_2_1_orders_2('#skF_4',k1_xboole_0))
      | ~ m1_subset_1(D_34,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2806,c_34])).

tff(c_2881,plain,(
    ! [D_34] :
      ( r2_hidden('#skF_3'(D_34,'#skF_4',k1_xboole_0,D_34),k1_xboole_0)
      | r2_hidden(D_34,a_2_1_orders_2('#skF_4',k1_xboole_0))
      | ~ m1_subset_1(D_34,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_2858])).

tff(c_3642,plain,(
    ! [D_246] :
      ( r2_hidden('#skF_3'(D_246,'#skF_4',k1_xboole_0,D_246),k1_xboole_0)
      | r2_hidden(D_246,a_2_1_orders_2('#skF_4',k1_xboole_0))
      | ~ m1_subset_1(D_246,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_2881])).

tff(c_22,plain,(
    ! [B_15,A_14] :
      ( ~ r1_tarski(B_15,A_14)
      | ~ r2_hidden(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_3655,plain,(
    ! [D_246] :
      ( ~ r1_tarski(k1_xboole_0,'#skF_3'(D_246,'#skF_4',k1_xboole_0,D_246))
      | r2_hidden(D_246,a_2_1_orders_2('#skF_4',k1_xboole_0))
      | ~ m1_subset_1(D_246,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_3642,c_22])).

tff(c_3669,plain,(
    ! [D_247] :
      ( r2_hidden(D_247,a_2_1_orders_2('#skF_4',k1_xboole_0))
      | ~ m1_subset_1(D_247,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_3655])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4169,plain,(
    ! [A_271] :
      ( r1_tarski(A_271,a_2_1_orders_2('#skF_4',k1_xboole_0))
      | ~ m1_subset_1('#skF_1'(A_271,a_2_1_orders_2('#skF_4',k1_xboole_0)),u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_3669,c_4])).

tff(c_4230,plain,(
    ! [A_272] :
      ( ~ r1_tarski(A_272,u1_struct_0('#skF_4'))
      | r1_tarski(A_272,a_2_1_orders_2('#skF_4',k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_134,c_4169])).

tff(c_30,plain,(
    ! [A_22] :
      ( l1_struct_0(A_22)
      | ~ l1_orders_2(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_59,plain,(
    ! [A_39] :
      ( k1_struct_0(A_39) = k1_xboole_0
      | ~ l1_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_64,plain,(
    ! [A_40] :
      ( k1_struct_0(A_40) = k1_xboole_0
      | ~ l1_orders_2(A_40) ) ),
    inference(resolution,[status(thm)],[c_30,c_59])).

tff(c_68,plain,(
    k1_struct_0('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_46,c_64])).

tff(c_44,plain,(
    k2_orders_2('#skF_4',k1_struct_0('#skF_4')) != u1_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_69,plain,(
    k2_orders_2('#skF_4',k1_xboole_0) != u1_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_44])).

tff(c_2770,plain,(
    a_2_1_orders_2('#skF_4',k1_xboole_0) != u1_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2769,c_69])).

tff(c_2805,plain,(
    r1_tarski(a_2_1_orders_2('#skF_4',k1_xboole_0),u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_2787])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2904,plain,
    ( a_2_1_orders_2('#skF_4',k1_xboole_0) = u1_struct_0('#skF_4')
    | ~ r1_tarski(u1_struct_0('#skF_4'),a_2_1_orders_2('#skF_4',k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_2805,c_8])).

tff(c_2917,plain,(
    ~ r1_tarski(u1_struct_0('#skF_4'),a_2_1_orders_2('#skF_4',k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_2770,c_2904])).

tff(c_4256,plain,(
    ~ r1_tarski(u1_struct_0('#skF_4'),u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_4230,c_2917])).

tff(c_4290,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_4256])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:12:46 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.86/2.09  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.86/2.09  
% 5.86/2.09  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.86/2.10  %$ r2_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_struct_0 > l1_orders_2 > k2_orders_2 > a_2_1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 5.86/2.10  
% 5.86/2.10  %Foreground sorts:
% 5.86/2.10  
% 5.86/2.10  
% 5.86/2.10  %Background operators:
% 5.86/2.10  
% 5.86/2.10  
% 5.86/2.10  %Foreground operators:
% 5.86/2.10  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.86/2.10  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 5.86/2.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.86/2.10  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.86/2.10  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.86/2.10  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.86/2.10  tff(a_2_1_orders_2, type, a_2_1_orders_2: ($i * $i) > $i).
% 5.86/2.10  tff(k2_orders_2, type, k2_orders_2: ($i * $i) > $i).
% 5.86/2.10  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.86/2.10  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 5.86/2.10  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 5.86/2.10  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.86/2.10  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.86/2.10  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 5.86/2.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.86/2.10  tff('#skF_4', type, '#skF_4': $i).
% 5.86/2.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.86/2.10  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 5.86/2.10  tff(k1_struct_0, type, k1_struct_0: $i > $i).
% 5.86/2.10  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 5.86/2.10  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.86/2.10  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.86/2.10  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.86/2.10  
% 6.02/2.11  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.02/2.11  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 6.02/2.11  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 6.02/2.11  tff(f_50, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 6.02/2.11  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.02/2.11  tff(f_135, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (k2_orders_2(A, k1_struct_0(A)) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_orders_2)).
% 6.02/2.11  tff(f_75, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_orders_2(A, B) = a_2_1_orders_2(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_orders_2)).
% 6.02/2.11  tff(f_90, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_orders_2(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_orders_2)).
% 6.02/2.11  tff(f_121, axiom, (![A, B, C]: ((((((~v2_struct_0(B) & v3_orders_2(B)) & v4_orders_2(B)) & v5_orders_2(B)) & l1_orders_2(B)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B)))) => (r2_hidden(A, a_2_1_orders_2(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r2_hidden(E, C) => r2_orders_2(B, D, E))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fraenkel_a_2_1_orders_2)).
% 6.02/2.11  tff(f_55, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 6.02/2.11  tff(f_94, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 6.02/2.11  tff(f_59, axiom, (![A]: (l1_struct_0(A) => (k1_struct_0(A) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_struct_0)).
% 6.02/2.11  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.02/2.11  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.02/2.11  tff(c_18, plain, (![A_9, B_10]: (m1_subset_1(A_9, k1_zfmisc_1(B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.02/2.11  tff(c_127, plain, (![A_59, C_60, B_61]: (m1_subset_1(A_59, C_60) | ~m1_subset_1(B_61, k1_zfmisc_1(C_60)) | ~r2_hidden(A_59, B_61))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.02/2.11  tff(c_131, plain, (![A_62, B_63, A_64]: (m1_subset_1(A_62, B_63) | ~r2_hidden(A_62, A_64) | ~r1_tarski(A_64, B_63))), inference(resolution, [status(thm)], [c_18, c_127])).
% 6.02/2.11  tff(c_134, plain, (![A_1, B_2, B_63]: (m1_subset_1('#skF_1'(A_1, B_2), B_63) | ~r1_tarski(A_1, B_63) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_131])).
% 6.02/2.11  tff(c_14, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.02/2.11  tff(c_54, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_135])).
% 6.02/2.11  tff(c_52, plain, (v3_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_135])).
% 6.02/2.11  tff(c_50, plain, (v4_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_135])).
% 6.02/2.11  tff(c_48, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_135])).
% 6.02/2.11  tff(c_46, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_135])).
% 6.02/2.11  tff(c_151, plain, (![A_68, B_69]: (k2_orders_2(A_68, B_69)=a_2_1_orders_2(A_68, B_69) | ~m1_subset_1(B_69, k1_zfmisc_1(u1_struct_0(A_68))) | ~l1_orders_2(A_68) | ~v5_orders_2(A_68) | ~v4_orders_2(A_68) | ~v3_orders_2(A_68) | v2_struct_0(A_68))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.02/2.11  tff(c_536, plain, (![A_119, A_120]: (k2_orders_2(A_119, A_120)=a_2_1_orders_2(A_119, A_120) | ~l1_orders_2(A_119) | ~v5_orders_2(A_119) | ~v4_orders_2(A_119) | ~v3_orders_2(A_119) | v2_struct_0(A_119) | ~r1_tarski(A_120, u1_struct_0(A_119)))), inference(resolution, [status(thm)], [c_18, c_151])).
% 6.02/2.11  tff(c_2762, plain, (![A_217]: (k2_orders_2(A_217, k1_xboole_0)=a_2_1_orders_2(A_217, k1_xboole_0) | ~l1_orders_2(A_217) | ~v5_orders_2(A_217) | ~v4_orders_2(A_217) | ~v3_orders_2(A_217) | v2_struct_0(A_217))), inference(resolution, [status(thm)], [c_14, c_536])).
% 6.02/2.11  tff(c_2765, plain, (k2_orders_2('#skF_4', k1_xboole_0)=a_2_1_orders_2('#skF_4', k1_xboole_0) | ~l1_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_48, c_2762])).
% 6.02/2.11  tff(c_2768, plain, (k2_orders_2('#skF_4', k1_xboole_0)=a_2_1_orders_2('#skF_4', k1_xboole_0) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_46, c_2765])).
% 6.02/2.11  tff(c_2769, plain, (k2_orders_2('#skF_4', k1_xboole_0)=a_2_1_orders_2('#skF_4', k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_54, c_2768])).
% 6.02/2.11  tff(c_194, plain, (![A_78, B_79]: (m1_subset_1(k2_orders_2(A_78, B_79), k1_zfmisc_1(u1_struct_0(A_78))) | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0(A_78))) | ~l1_orders_2(A_78) | ~v5_orders_2(A_78) | ~v4_orders_2(A_78) | ~v3_orders_2(A_78) | v2_struct_0(A_78))), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.02/2.11  tff(c_16, plain, (![A_9, B_10]: (r1_tarski(A_9, B_10) | ~m1_subset_1(A_9, k1_zfmisc_1(B_10)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.02/2.11  tff(c_205, plain, (![A_78, B_79]: (r1_tarski(k2_orders_2(A_78, B_79), u1_struct_0(A_78)) | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0(A_78))) | ~l1_orders_2(A_78) | ~v5_orders_2(A_78) | ~v4_orders_2(A_78) | ~v3_orders_2(A_78) | v2_struct_0(A_78))), inference(resolution, [status(thm)], [c_194, c_16])).
% 6.02/2.11  tff(c_2776, plain, (r1_tarski(a_2_1_orders_2('#skF_4', k1_xboole_0), u1_struct_0('#skF_4')) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2769, c_205])).
% 6.02/2.11  tff(c_2786, plain, (r1_tarski(a_2_1_orders_2('#skF_4', k1_xboole_0), u1_struct_0('#skF_4')) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_2776])).
% 6.02/2.11  tff(c_2787, plain, (r1_tarski(a_2_1_orders_2('#skF_4', k1_xboole_0), u1_struct_0('#skF_4')) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_54, c_2786])).
% 6.02/2.11  tff(c_2797, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_2787])).
% 6.02/2.11  tff(c_2800, plain, (~r1_tarski(k1_xboole_0, u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_18, c_2797])).
% 6.02/2.11  tff(c_2804, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_2800])).
% 6.02/2.11  tff(c_2806, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_2787])).
% 6.02/2.11  tff(c_34, plain, (![D_34, B_24, C_25]: (r2_hidden('#skF_3'(D_34, B_24, C_25, D_34), C_25) | r2_hidden(D_34, a_2_1_orders_2(B_24, C_25)) | ~m1_subset_1(D_34, u1_struct_0(B_24)) | ~m1_subset_1(C_25, k1_zfmisc_1(u1_struct_0(B_24))) | ~l1_orders_2(B_24) | ~v5_orders_2(B_24) | ~v4_orders_2(B_24) | ~v3_orders_2(B_24) | v2_struct_0(B_24))), inference(cnfTransformation, [status(thm)], [f_121])).
% 6.02/2.11  tff(c_2858, plain, (![D_34]: (r2_hidden('#skF_3'(D_34, '#skF_4', k1_xboole_0, D_34), k1_xboole_0) | r2_hidden(D_34, a_2_1_orders_2('#skF_4', k1_xboole_0)) | ~m1_subset_1(D_34, u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_2806, c_34])).
% 6.02/2.11  tff(c_2881, plain, (![D_34]: (r2_hidden('#skF_3'(D_34, '#skF_4', k1_xboole_0, D_34), k1_xboole_0) | r2_hidden(D_34, a_2_1_orders_2('#skF_4', k1_xboole_0)) | ~m1_subset_1(D_34, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_2858])).
% 6.02/2.11  tff(c_3642, plain, (![D_246]: (r2_hidden('#skF_3'(D_246, '#skF_4', k1_xboole_0, D_246), k1_xboole_0) | r2_hidden(D_246, a_2_1_orders_2('#skF_4', k1_xboole_0)) | ~m1_subset_1(D_246, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_54, c_2881])).
% 6.02/2.11  tff(c_22, plain, (![B_15, A_14]: (~r1_tarski(B_15, A_14) | ~r2_hidden(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.02/2.11  tff(c_3655, plain, (![D_246]: (~r1_tarski(k1_xboole_0, '#skF_3'(D_246, '#skF_4', k1_xboole_0, D_246)) | r2_hidden(D_246, a_2_1_orders_2('#skF_4', k1_xboole_0)) | ~m1_subset_1(D_246, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_3642, c_22])).
% 6.02/2.11  tff(c_3669, plain, (![D_247]: (r2_hidden(D_247, a_2_1_orders_2('#skF_4', k1_xboole_0)) | ~m1_subset_1(D_247, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_3655])).
% 6.02/2.11  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.02/2.11  tff(c_4169, plain, (![A_271]: (r1_tarski(A_271, a_2_1_orders_2('#skF_4', k1_xboole_0)) | ~m1_subset_1('#skF_1'(A_271, a_2_1_orders_2('#skF_4', k1_xboole_0)), u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_3669, c_4])).
% 6.02/2.11  tff(c_4230, plain, (![A_272]: (~r1_tarski(A_272, u1_struct_0('#skF_4')) | r1_tarski(A_272, a_2_1_orders_2('#skF_4', k1_xboole_0)))), inference(resolution, [status(thm)], [c_134, c_4169])).
% 6.02/2.11  tff(c_30, plain, (![A_22]: (l1_struct_0(A_22) | ~l1_orders_2(A_22))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.02/2.11  tff(c_59, plain, (![A_39]: (k1_struct_0(A_39)=k1_xboole_0 | ~l1_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.02/2.11  tff(c_64, plain, (![A_40]: (k1_struct_0(A_40)=k1_xboole_0 | ~l1_orders_2(A_40))), inference(resolution, [status(thm)], [c_30, c_59])).
% 6.02/2.11  tff(c_68, plain, (k1_struct_0('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_46, c_64])).
% 6.02/2.11  tff(c_44, plain, (k2_orders_2('#skF_4', k1_struct_0('#skF_4'))!=u1_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_135])).
% 6.02/2.11  tff(c_69, plain, (k2_orders_2('#skF_4', k1_xboole_0)!=u1_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_44])).
% 6.02/2.11  tff(c_2770, plain, (a_2_1_orders_2('#skF_4', k1_xboole_0)!=u1_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2769, c_69])).
% 6.02/2.11  tff(c_2805, plain, (r1_tarski(a_2_1_orders_2('#skF_4', k1_xboole_0), u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_2787])).
% 6.02/2.11  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.02/2.11  tff(c_2904, plain, (a_2_1_orders_2('#skF_4', k1_xboole_0)=u1_struct_0('#skF_4') | ~r1_tarski(u1_struct_0('#skF_4'), a_2_1_orders_2('#skF_4', k1_xboole_0))), inference(resolution, [status(thm)], [c_2805, c_8])).
% 6.02/2.11  tff(c_2917, plain, (~r1_tarski(u1_struct_0('#skF_4'), a_2_1_orders_2('#skF_4', k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_2770, c_2904])).
% 6.02/2.11  tff(c_4256, plain, (~r1_tarski(u1_struct_0('#skF_4'), u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_4230, c_2917])).
% 6.02/2.11  tff(c_4290, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_4256])).
% 6.02/2.11  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.02/2.11  
% 6.02/2.11  Inference rules
% 6.02/2.11  ----------------------
% 6.02/2.11  #Ref     : 0
% 6.02/2.11  #Sup     : 1002
% 6.02/2.11  #Fact    : 0
% 6.02/2.11  #Define  : 0
% 6.02/2.11  #Split   : 7
% 6.02/2.11  #Chain   : 0
% 6.02/2.11  #Close   : 0
% 6.02/2.11  
% 6.02/2.11  Ordering : KBO
% 6.02/2.11  
% 6.02/2.11  Simplification rules
% 6.02/2.11  ----------------------
% 6.02/2.11  #Subsume      : 337
% 6.02/2.11  #Demod        : 671
% 6.02/2.11  #Tautology    : 192
% 6.02/2.11  #SimpNegUnit  : 84
% 6.02/2.11  #BackRed      : 6
% 6.02/2.11  
% 6.02/2.11  #Partial instantiations: 0
% 6.02/2.11  #Strategies tried      : 1
% 6.02/2.11  
% 6.02/2.11  Timing (in seconds)
% 6.02/2.11  ----------------------
% 6.02/2.12  Preprocessing        : 0.33
% 6.02/2.12  Parsing              : 0.17
% 6.02/2.12  CNF conversion       : 0.02
% 6.02/2.12  Main loop            : 1.02
% 6.02/2.12  Inferencing          : 0.31
% 6.02/2.12  Reduction            : 0.27
% 6.02/2.12  Demodulation         : 0.18
% 6.02/2.12  BG Simplification    : 0.04
% 6.02/2.12  Subsumption          : 0.32
% 6.02/2.12  Abstraction          : 0.05
% 6.02/2.12  MUC search           : 0.00
% 6.02/2.12  Cooper               : 0.00
% 6.02/2.12  Total                : 1.38
% 6.02/2.12  Index Insertion      : 0.00
% 6.02/2.12  Index Deletion       : 0.00
% 6.02/2.12  Index Matching       : 0.00
% 6.02/2.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
