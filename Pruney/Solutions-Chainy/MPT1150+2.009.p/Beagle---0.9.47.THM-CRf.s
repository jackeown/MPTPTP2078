%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:25 EST 2020

% Result     : Theorem 14.24s
% Output     : CNFRefutation 14.43s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 977 expanded)
%              Number of leaves         :   43 ( 382 expanded)
%              Depth                    :   27
%              Number of atoms          :  388 (2877 expanded)
%              Number of equality atoms :   45 ( 514 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r1_orders_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_struct_0 > l1_orders_2 > k1_orders_2 > a_2_0_orders_2 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff(k1_orders_2,type,(
    k1_orders_2: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(a_2_0_orders_2,type,(
    a_2_0_orders_2: ( $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(r2_orders_2,type,(
    r2_orders_2: ( $i * $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_36,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_38,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_167,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => k1_orders_2(A,k2_struct_0(A)) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_orders_2)).

tff(f_126,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_76,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_107,axiom,(
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

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_72,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ( ( r2_hidden(C,D)
                    & r2_hidden(D,E)
                    & r2_hidden(E,B) )
                 => r1_xboole_0(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_mcart_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_122,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_orders_2(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_orders_2)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_153,axiom,(
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

tff(f_40,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_91,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r2_orders_2(A,B,C)
              <=> ( r1_orders_2(A,B,C)
                  & B != C ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_orders_2)).

tff(c_10,plain,(
    ! [A_7] : k2_subset_1(A_7) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_12,plain,(
    ! [A_8] : m1_subset_1(k2_subset_1(A_8),k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_65,plain,(
    ! [A_8] : m1_subset_1(A_8,k1_zfmisc_1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_62,plain,(
    v3_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_60,plain,(
    v4_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_58,plain,(
    v5_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_56,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_40,plain,(
    ! [A_44] :
      ( l1_struct_0(A_44)
      | ~ l1_orders_2(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_85,plain,(
    ! [A_66] :
      ( u1_struct_0(A_66) = k2_struct_0(A_66)
      | ~ l1_struct_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_98,plain,(
    ! [A_70] :
      ( u1_struct_0(A_70) = k2_struct_0(A_70)
      | ~ l1_orders_2(A_70) ) ),
    inference(resolution,[status(thm)],[c_40,c_85])).

tff(c_102,plain,(
    u1_struct_0('#skF_5') = k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_98])).

tff(c_356,plain,(
    ! [A_117,B_118] :
      ( k1_orders_2(A_117,B_118) = a_2_0_orders_2(A_117,B_118)
      | ~ m1_subset_1(B_118,k1_zfmisc_1(u1_struct_0(A_117)))
      | ~ l1_orders_2(A_117)
      | ~ v5_orders_2(A_117)
      | ~ v4_orders_2(A_117)
      | ~ v3_orders_2(A_117)
      | v2_struct_0(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_367,plain,(
    ! [B_118] :
      ( k1_orders_2('#skF_5',B_118) = a_2_0_orders_2('#skF_5',B_118)
      | ~ m1_subset_1(B_118,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_356])).

tff(c_383,plain,(
    ! [B_118] :
      ( k1_orders_2('#skF_5',B_118) = a_2_0_orders_2('#skF_5',B_118)
      | ~ m1_subset_1(B_118,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_56,c_367])).

tff(c_425,plain,(
    ! [B_123] :
      ( k1_orders_2('#skF_5',B_123) = a_2_0_orders_2('#skF_5',B_123)
      | ~ m1_subset_1(B_123,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_383])).

tff(c_455,plain,(
    k1_orders_2('#skF_5',k2_struct_0('#skF_5')) = a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_65,c_425])).

tff(c_54,plain,(
    k1_orders_2('#skF_5',k2_struct_0('#skF_5')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_460,plain,(
    a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_455,c_54])).

tff(c_107,plain,(
    ! [A_71,B_72] :
      ( r1_tarski(A_71,B_72)
      | ~ m1_subset_1(A_71,k1_zfmisc_1(B_72)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_120,plain,(
    ! [A_8] : r1_tarski(A_8,A_8) ),
    inference(resolution,[status(thm)],[c_65,c_107])).

tff(c_26,plain,(
    ! [A_17] :
      ( r2_hidden('#skF_2'(A_17),A_17)
      | k1_xboole_0 = A_17 ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_141,plain,(
    ! [C_80,B_81,A_82] :
      ( r2_hidden(C_80,B_81)
      | ~ r2_hidden(C_80,A_82)
      | ~ r1_tarski(A_82,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_147,plain,(
    ! [A_17,B_81] :
      ( r2_hidden('#skF_2'(A_17),B_81)
      | ~ r1_tarski(A_17,B_81)
      | k1_xboole_0 = A_17 ) ),
    inference(resolution,[status(thm)],[c_26,c_141])).

tff(c_515,plain,(
    ! [A_128,B_129] :
      ( m1_subset_1(k1_orders_2(A_128,B_129),k1_zfmisc_1(u1_struct_0(A_128)))
      | ~ m1_subset_1(B_129,k1_zfmisc_1(u1_struct_0(A_128)))
      | ~ l1_orders_2(A_128)
      | ~ v5_orders_2(A_128)
      | ~ v4_orders_2(A_128)
      | ~ v3_orders_2(A_128)
      | v2_struct_0(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_526,plain,
    ( m1_subset_1(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_455,c_515])).

tff(c_537,plain,
    ( m1_subset_1(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')),k1_zfmisc_1(k2_struct_0('#skF_5')))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_56,c_65,c_102,c_102,c_526])).

tff(c_538,plain,(
    m1_subset_1(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')),k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_537])).

tff(c_20,plain,(
    ! [A_12,C_14,B_13] :
      ( m1_subset_1(A_12,C_14)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(C_14))
      | ~ r2_hidden(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_641,plain,(
    ! [A_133] :
      ( m1_subset_1(A_133,k2_struct_0('#skF_5'))
      | ~ r2_hidden(A_133,a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_538,c_20])).

tff(c_653,plain,
    ( m1_subset_1('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),k2_struct_0('#skF_5'))
    | a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_641])).

tff(c_658,plain,(
    m1_subset_1('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),k2_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_460,c_653])).

tff(c_659,plain,(
    ! [A_134,B_135,C_136] :
      ( '#skF_3'(A_134,B_135,C_136) = A_134
      | ~ r2_hidden(A_134,a_2_0_orders_2(B_135,C_136))
      | ~ m1_subset_1(C_136,k1_zfmisc_1(u1_struct_0(B_135)))
      | ~ l1_orders_2(B_135)
      | ~ v5_orders_2(B_135)
      | ~ v4_orders_2(B_135)
      | ~ v3_orders_2(B_135)
      | v2_struct_0(B_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_10345,plain,(
    ! [B_520,C_521] :
      ( '#skF_3'('#skF_2'(a_2_0_orders_2(B_520,C_521)),B_520,C_521) = '#skF_2'(a_2_0_orders_2(B_520,C_521))
      | ~ m1_subset_1(C_521,k1_zfmisc_1(u1_struct_0(B_520)))
      | ~ l1_orders_2(B_520)
      | ~ v5_orders_2(B_520)
      | ~ v4_orders_2(B_520)
      | ~ v3_orders_2(B_520)
      | v2_struct_0(B_520)
      | a_2_0_orders_2(B_520,C_521) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_26,c_659])).

tff(c_10367,plain,(
    ! [C_521] :
      ( '#skF_3'('#skF_2'(a_2_0_orders_2('#skF_5',C_521)),'#skF_5',C_521) = '#skF_2'(a_2_0_orders_2('#skF_5',C_521))
      | ~ m1_subset_1(C_521,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5')
      | a_2_0_orders_2('#skF_5',C_521) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_10345])).

tff(c_10385,plain,(
    ! [C_521] :
      ( '#skF_3'('#skF_2'(a_2_0_orders_2('#skF_5',C_521)),'#skF_5',C_521) = '#skF_2'(a_2_0_orders_2('#skF_5',C_521))
      | ~ m1_subset_1(C_521,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | v2_struct_0('#skF_5')
      | a_2_0_orders_2('#skF_5',C_521) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_56,c_10367])).

tff(c_12690,plain,(
    ! [C_586] :
      ( '#skF_3'('#skF_2'(a_2_0_orders_2('#skF_5',C_586)),'#skF_5',C_586) = '#skF_2'(a_2_0_orders_2('#skF_5',C_586))
      | ~ m1_subset_1(C_586,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | a_2_0_orders_2('#skF_5',C_586) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_10385])).

tff(c_12736,plain,
    ( '#skF_3'('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),'#skF_5',k2_struct_0('#skF_5')) = '#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')))
    | a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_65,c_12690])).

tff(c_12760,plain,(
    '#skF_3'('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),'#skF_5',k2_struct_0('#skF_5')) = '#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_460,c_12736])).

tff(c_14,plain,(
    ! [A_9] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_454,plain,(
    k1_orders_2('#skF_5',k1_xboole_0) = a_2_0_orders_2('#skF_5',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_425])).

tff(c_529,plain,
    ( m1_subset_1(a_2_0_orders_2('#skF_5',k1_xboole_0),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_454,c_515])).

tff(c_540,plain,
    ( m1_subset_1(a_2_0_orders_2('#skF_5',k1_xboole_0),k1_zfmisc_1(k2_struct_0('#skF_5')))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_56,c_14,c_102,c_529])).

tff(c_541,plain,(
    m1_subset_1(a_2_0_orders_2('#skF_5',k1_xboole_0),k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_540])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | ~ m1_subset_1(A_10,k1_zfmisc_1(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_555,plain,(
    r1_tarski(a_2_0_orders_2('#skF_5',k1_xboole_0),k2_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_541,c_16])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1055,plain,(
    ! [D_165,B_166,C_167] :
      ( r2_hidden('#skF_4'(D_165,B_166,C_167,D_165),C_167)
      | r2_hidden(D_165,a_2_0_orders_2(B_166,C_167))
      | ~ m1_subset_1(D_165,u1_struct_0(B_166))
      | ~ m1_subset_1(C_167,k1_zfmisc_1(u1_struct_0(B_166)))
      | ~ l1_orders_2(B_166)
      | ~ v5_orders_2(B_166)
      | ~ v4_orders_2(B_166)
      | ~ v3_orders_2(B_166)
      | v2_struct_0(B_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_9053,plain,(
    ! [D_480,B_481] :
      ( r2_hidden('#skF_4'(D_480,B_481,k1_xboole_0,D_480),k1_xboole_0)
      | r2_hidden(D_480,a_2_0_orders_2(B_481,k1_xboole_0))
      | ~ m1_subset_1(D_480,u1_struct_0(B_481))
      | ~ l1_orders_2(B_481)
      | ~ v5_orders_2(B_481)
      | ~ v4_orders_2(B_481)
      | ~ v3_orders_2(B_481)
      | v2_struct_0(B_481) ) ),
    inference(resolution,[status(thm)],[c_14,c_1055])).

tff(c_22,plain,(
    ! [B_16,A_15] :
      ( ~ r1_tarski(B_16,A_15)
      | ~ r2_hidden(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_9068,plain,(
    ! [D_480,B_481] :
      ( ~ r1_tarski(k1_xboole_0,'#skF_4'(D_480,B_481,k1_xboole_0,D_480))
      | r2_hidden(D_480,a_2_0_orders_2(B_481,k1_xboole_0))
      | ~ m1_subset_1(D_480,u1_struct_0(B_481))
      | ~ l1_orders_2(B_481)
      | ~ v5_orders_2(B_481)
      | ~ v4_orders_2(B_481)
      | ~ v3_orders_2(B_481)
      | v2_struct_0(B_481) ) ),
    inference(resolution,[status(thm)],[c_9053,c_22])).

tff(c_9082,plain,(
    ! [D_480,B_481] :
      ( r2_hidden(D_480,a_2_0_orders_2(B_481,k1_xboole_0))
      | ~ m1_subset_1(D_480,u1_struct_0(B_481))
      | ~ l1_orders_2(B_481)
      | ~ v5_orders_2(B_481)
      | ~ v4_orders_2(B_481)
      | ~ v3_orders_2(B_481)
      | v2_struct_0(B_481) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_9068])).

tff(c_1071,plain,(
    ! [D_165,C_167] :
      ( r2_hidden('#skF_4'(D_165,'#skF_5',C_167,D_165),C_167)
      | r2_hidden(D_165,a_2_0_orders_2('#skF_5',C_167))
      | ~ m1_subset_1(D_165,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(C_167,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_1055])).

tff(c_1087,plain,(
    ! [D_165,C_167] :
      ( r2_hidden('#skF_4'(D_165,'#skF_5',C_167,D_165),C_167)
      | r2_hidden(D_165,a_2_0_orders_2('#skF_5',C_167))
      | ~ m1_subset_1(D_165,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(C_167,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_56,c_102,c_1071])).

tff(c_1135,plain,(
    ! [D_169,C_170] :
      ( r2_hidden('#skF_4'(D_169,'#skF_5',C_170,D_169),C_170)
      | r2_hidden(D_169,a_2_0_orders_2('#skF_5',C_170))
      | ~ m1_subset_1(D_169,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(C_170,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1087])).

tff(c_8336,plain,(
    ! [D_451] :
      ( r2_hidden('#skF_4'(D_451,'#skF_5',k1_xboole_0,D_451),k1_xboole_0)
      | r2_hidden(D_451,a_2_0_orders_2('#skF_5',k1_xboole_0))
      | ~ m1_subset_1(D_451,k2_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_14,c_1135])).

tff(c_8351,plain,(
    ! [D_451] :
      ( ~ r1_tarski(k1_xboole_0,'#skF_4'(D_451,'#skF_5',k1_xboole_0,D_451))
      | r2_hidden(D_451,a_2_0_orders_2('#skF_5',k1_xboole_0))
      | ~ m1_subset_1(D_451,k2_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_8336,c_22])).

tff(c_8366,plain,(
    ! [D_452] :
      ( r2_hidden(D_452,a_2_0_orders_2('#skF_5',k1_xboole_0))
      | ~ m1_subset_1(D_452,k2_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_8351])).

tff(c_50,plain,(
    ! [A_45,B_46,C_47] :
      ( '#skF_3'(A_45,B_46,C_47) = A_45
      | ~ r2_hidden(A_45,a_2_0_orders_2(B_46,C_47))
      | ~ m1_subset_1(C_47,k1_zfmisc_1(u1_struct_0(B_46)))
      | ~ l1_orders_2(B_46)
      | ~ v5_orders_2(B_46)
      | ~ v4_orders_2(B_46)
      | ~ v3_orders_2(B_46)
      | v2_struct_0(B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_8368,plain,(
    ! [D_452] :
      ( '#skF_3'(D_452,'#skF_5',k1_xboole_0) = D_452
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ m1_subset_1(D_452,k2_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_8366,c_50])).

tff(c_8391,plain,(
    ! [D_452] :
      ( '#skF_3'(D_452,'#skF_5',k1_xboole_0) = D_452
      | v2_struct_0('#skF_5')
      | ~ m1_subset_1(D_452,k2_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_56,c_14,c_102,c_8368])).

tff(c_8400,plain,(
    ! [D_453] :
      ( '#skF_3'(D_453,'#skF_5',k1_xboole_0) = D_453
      | ~ m1_subset_1(D_453,k2_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_8391])).

tff(c_8446,plain,(
    '#skF_3'('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),'#skF_5',k1_xboole_0) = '#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_658,c_8400])).

tff(c_6867,plain,(
    ! [B_384,E_385,A_386,C_387] :
      ( r2_orders_2(B_384,E_385,'#skF_3'(A_386,B_384,C_387))
      | ~ r2_hidden(E_385,C_387)
      | ~ m1_subset_1(E_385,u1_struct_0(B_384))
      | ~ r2_hidden(A_386,a_2_0_orders_2(B_384,C_387))
      | ~ m1_subset_1(C_387,k1_zfmisc_1(u1_struct_0(B_384)))
      | ~ l1_orders_2(B_384)
      | ~ v5_orders_2(B_384)
      | ~ v4_orders_2(B_384)
      | ~ v3_orders_2(B_384)
      | v2_struct_0(B_384) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_10053,plain,(
    ! [B_512,E_513,A_514] :
      ( r2_orders_2(B_512,E_513,'#skF_3'(A_514,B_512,k1_xboole_0))
      | ~ r2_hidden(E_513,k1_xboole_0)
      | ~ m1_subset_1(E_513,u1_struct_0(B_512))
      | ~ r2_hidden(A_514,a_2_0_orders_2(B_512,k1_xboole_0))
      | ~ l1_orders_2(B_512)
      | ~ v5_orders_2(B_512)
      | ~ v4_orders_2(B_512)
      | ~ v3_orders_2(B_512)
      | v2_struct_0(B_512) ) ),
    inference(resolution,[status(thm)],[c_14,c_6867])).

tff(c_10064,plain,(
    ! [E_513] :
      ( r2_orders_2('#skF_5',E_513,'#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))))
      | ~ r2_hidden(E_513,k1_xboole_0)
      | ~ m1_subset_1(E_513,u1_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),a_2_0_orders_2('#skF_5',k1_xboole_0))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8446,c_10053])).

tff(c_10075,plain,(
    ! [E_513] :
      ( r2_orders_2('#skF_5',E_513,'#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))))
      | ~ r2_hidden(E_513,k1_xboole_0)
      | ~ m1_subset_1(E_513,k2_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),a_2_0_orders_2('#skF_5',k1_xboole_0))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_56,c_102,c_10064])).

tff(c_10076,plain,(
    ! [E_513] :
      ( r2_orders_2('#skF_5',E_513,'#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))))
      | ~ r2_hidden(E_513,k1_xboole_0)
      | ~ m1_subset_1(E_513,k2_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),a_2_0_orders_2('#skF_5',k1_xboole_0)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_10075])).

tff(c_17700,plain,(
    ~ r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),a_2_0_orders_2('#skF_5',k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_10076])).

tff(c_17703,plain,
    ( ~ m1_subset_1('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_9082,c_17700])).

tff(c_17715,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_56,c_658,c_102,c_17703])).

tff(c_17717,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_17715])).

tff(c_17719,plain,(
    r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),a_2_0_orders_2('#skF_5',k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_10076])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_17889,plain,(
    ! [B_701] :
      ( r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),B_701)
      | ~ r1_tarski(a_2_0_orders_2('#skF_5',k1_xboole_0),B_701) ) ),
    inference(resolution,[status(thm)],[c_17719,c_2])).

tff(c_23557,plain,(
    ! [B_809,B_810] :
      ( r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),B_809)
      | ~ r1_tarski(B_810,B_809)
      | ~ r1_tarski(a_2_0_orders_2('#skF_5',k1_xboole_0),B_810) ) ),
    inference(resolution,[status(thm)],[c_17889,c_2])).

tff(c_23615,plain,
    ( r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),k2_struct_0('#skF_5'))
    | ~ r1_tarski(a_2_0_orders_2('#skF_5',k1_xboole_0),a_2_0_orders_2('#skF_5',k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_555,c_23557])).

tff(c_23660,plain,(
    r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),k2_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_23615])).

tff(c_18,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_10387,plain,(
    ! [B_520,A_10] :
      ( '#skF_3'('#skF_2'(a_2_0_orders_2(B_520,A_10)),B_520,A_10) = '#skF_2'(a_2_0_orders_2(B_520,A_10))
      | ~ l1_orders_2(B_520)
      | ~ v5_orders_2(B_520)
      | ~ v4_orders_2(B_520)
      | ~ v3_orders_2(B_520)
      | v2_struct_0(B_520)
      | a_2_0_orders_2(B_520,A_10) = k1_xboole_0
      | ~ r1_tarski(A_10,u1_struct_0(B_520)) ) ),
    inference(resolution,[status(thm)],[c_18,c_10345])).

tff(c_11012,plain,(
    ! [B_546,E_547,A_548] :
      ( r2_orders_2(B_546,E_547,'#skF_3'(A_548,B_546,u1_struct_0(B_546)))
      | ~ r2_hidden(E_547,u1_struct_0(B_546))
      | ~ m1_subset_1(E_547,u1_struct_0(B_546))
      | ~ r2_hidden(A_548,a_2_0_orders_2(B_546,u1_struct_0(B_546)))
      | ~ l1_orders_2(B_546)
      | ~ v5_orders_2(B_546)
      | ~ v4_orders_2(B_546)
      | ~ v3_orders_2(B_546)
      | v2_struct_0(B_546) ) ),
    inference(resolution,[status(thm)],[c_65,c_6867])).

tff(c_32,plain,(
    ! [A_32,C_38] :
      ( ~ r2_orders_2(A_32,C_38,C_38)
      | ~ m1_subset_1(C_38,u1_struct_0(A_32))
      | ~ l1_orders_2(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_30185,plain,(
    ! [A_954,B_955] :
      ( ~ r2_hidden('#skF_3'(A_954,B_955,u1_struct_0(B_955)),u1_struct_0(B_955))
      | ~ m1_subset_1('#skF_3'(A_954,B_955,u1_struct_0(B_955)),u1_struct_0(B_955))
      | ~ r2_hidden(A_954,a_2_0_orders_2(B_955,u1_struct_0(B_955)))
      | ~ l1_orders_2(B_955)
      | ~ v5_orders_2(B_955)
      | ~ v4_orders_2(B_955)
      | ~ v3_orders_2(B_955)
      | v2_struct_0(B_955) ) ),
    inference(resolution,[status(thm)],[c_11012,c_32])).

tff(c_30199,plain,(
    ! [A_954] :
      ( ~ r2_hidden('#skF_3'(A_954,'#skF_5',k2_struct_0('#skF_5')),u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_3'(A_954,'#skF_5',u1_struct_0('#skF_5')),u1_struct_0('#skF_5'))
      | ~ r2_hidden(A_954,a_2_0_orders_2('#skF_5',u1_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_30185])).

tff(c_30208,plain,(
    ! [A_954] :
      ( ~ r2_hidden('#skF_3'(A_954,'#skF_5',k2_struct_0('#skF_5')),k2_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_3'(A_954,'#skF_5',k2_struct_0('#skF_5')),k2_struct_0('#skF_5'))
      | ~ r2_hidden(A_954,a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_56,c_102,c_102,c_102,c_102,c_30199])).

tff(c_30252,plain,(
    ! [A_958] :
      ( ~ r2_hidden('#skF_3'(A_958,'#skF_5',k2_struct_0('#skF_5')),k2_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_3'(A_958,'#skF_5',k2_struct_0('#skF_5')),k2_struct_0('#skF_5'))
      | ~ r2_hidden(A_958,a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_30208])).

tff(c_30260,plain,
    ( ~ r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),k2_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_3'('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),'#skF_5',k2_struct_0('#skF_5')),k2_struct_0('#skF_5'))
    | ~ r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5')
    | a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')) = k1_xboole_0
    | ~ r1_tarski(k2_struct_0('#skF_5'),u1_struct_0('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_10387,c_30252])).

tff(c_30271,plain,
    ( ~ r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')))
    | v2_struct_0('#skF_5')
    | a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_102,c_62,c_60,c_58,c_56,c_658,c_12760,c_23660,c_30260])).

tff(c_30272,plain,(
    ~ r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_460,c_64,c_30271])).

tff(c_30292,plain,
    ( ~ r1_tarski(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')),a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')))
    | a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_147,c_30272])).

tff(c_30308,plain,(
    a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_30292])).

tff(c_30310,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_460,c_30308])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:26:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.24/6.54  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.36/6.55  
% 14.36/6.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.36/6.55  %$ r2_orders_2 > r1_orders_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_struct_0 > l1_orders_2 > k1_orders_2 > a_2_0_orders_2 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_4 > #skF_3 > #skF_1
% 14.36/6.55  
% 14.36/6.55  %Foreground sorts:
% 14.36/6.55  
% 14.36/6.55  
% 14.36/6.55  %Background operators:
% 14.36/6.55  
% 14.36/6.55  
% 14.36/6.55  %Foreground operators:
% 14.36/6.55  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 14.36/6.55  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 14.36/6.55  tff(k1_orders_2, type, k1_orders_2: ($i * $i) > $i).
% 14.36/6.55  tff('#skF_2', type, '#skF_2': $i > $i).
% 14.36/6.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.36/6.55  tff(a_2_0_orders_2, type, a_2_0_orders_2: ($i * $i) > $i).
% 14.36/6.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 14.36/6.55  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 14.36/6.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 14.36/6.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.36/6.55  tff('#skF_5', type, '#skF_5': $i).
% 14.36/6.55  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 14.36/6.55  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 14.36/6.55  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 14.36/6.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 14.36/6.55  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 14.36/6.55  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 14.36/6.55  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 14.36/6.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.36/6.55  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 14.36/6.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.36/6.55  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 14.36/6.55  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 14.36/6.55  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 14.36/6.55  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 14.36/6.55  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 14.36/6.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 14.36/6.55  
% 14.43/6.57  tff(f_36, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 14.43/6.57  tff(f_38, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 14.43/6.57  tff(f_167, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (k1_orders_2(A, k2_struct_0(A)) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_orders_2)).
% 14.43/6.57  tff(f_126, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 14.43/6.57  tff(f_76, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 14.43/6.57  tff(f_107, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_orders_2(A, B) = a_2_0_orders_2(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_orders_2)).
% 14.43/6.57  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 14.43/6.57  tff(f_72, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: (((r2_hidden(C, D) & r2_hidden(D, E)) & r2_hidden(E, B)) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_mcart_1)).
% 14.43/6.57  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 14.43/6.57  tff(f_122, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_orders_2(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_orders_2)).
% 14.43/6.57  tff(f_50, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 14.43/6.57  tff(f_153, axiom, (![A, B, C]: ((((((~v2_struct_0(B) & v3_orders_2(B)) & v4_orders_2(B)) & v5_orders_2(B)) & l1_orders_2(B)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B)))) => (r2_hidden(A, a_2_0_orders_2(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r2_hidden(E, C) => r2_orders_2(B, E, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fraenkel_a_2_0_orders_2)).
% 14.43/6.57  tff(f_40, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 14.43/6.57  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 14.43/6.57  tff(f_55, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 14.43/6.57  tff(f_91, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_orders_2(A, B, C) <=> (r1_orders_2(A, B, C) & ~(B = C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_orders_2)).
% 14.43/6.57  tff(c_10, plain, (![A_7]: (k2_subset_1(A_7)=A_7)), inference(cnfTransformation, [status(thm)], [f_36])).
% 14.43/6.57  tff(c_12, plain, (![A_8]: (m1_subset_1(k2_subset_1(A_8), k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 14.43/6.57  tff(c_65, plain, (![A_8]: (m1_subset_1(A_8, k1_zfmisc_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_12])).
% 14.43/6.57  tff(c_64, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_167])).
% 14.43/6.57  tff(c_62, plain, (v3_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_167])).
% 14.43/6.57  tff(c_60, plain, (v4_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_167])).
% 14.43/6.57  tff(c_58, plain, (v5_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_167])).
% 14.43/6.57  tff(c_56, plain, (l1_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_167])).
% 14.43/6.57  tff(c_40, plain, (![A_44]: (l1_struct_0(A_44) | ~l1_orders_2(A_44))), inference(cnfTransformation, [status(thm)], [f_126])).
% 14.43/6.57  tff(c_85, plain, (![A_66]: (u1_struct_0(A_66)=k2_struct_0(A_66) | ~l1_struct_0(A_66))), inference(cnfTransformation, [status(thm)], [f_76])).
% 14.43/6.57  tff(c_98, plain, (![A_70]: (u1_struct_0(A_70)=k2_struct_0(A_70) | ~l1_orders_2(A_70))), inference(resolution, [status(thm)], [c_40, c_85])).
% 14.43/6.57  tff(c_102, plain, (u1_struct_0('#skF_5')=k2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_56, c_98])).
% 14.43/6.57  tff(c_356, plain, (![A_117, B_118]: (k1_orders_2(A_117, B_118)=a_2_0_orders_2(A_117, B_118) | ~m1_subset_1(B_118, k1_zfmisc_1(u1_struct_0(A_117))) | ~l1_orders_2(A_117) | ~v5_orders_2(A_117) | ~v4_orders_2(A_117) | ~v3_orders_2(A_117) | v2_struct_0(A_117))), inference(cnfTransformation, [status(thm)], [f_107])).
% 14.43/6.57  tff(c_367, plain, (![B_118]: (k1_orders_2('#skF_5', B_118)=a_2_0_orders_2('#skF_5', B_118) | ~m1_subset_1(B_118, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_102, c_356])).
% 14.43/6.57  tff(c_383, plain, (![B_118]: (k1_orders_2('#skF_5', B_118)=a_2_0_orders_2('#skF_5', B_118) | ~m1_subset_1(B_118, k1_zfmisc_1(k2_struct_0('#skF_5'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_56, c_367])).
% 14.43/6.57  tff(c_425, plain, (![B_123]: (k1_orders_2('#skF_5', B_123)=a_2_0_orders_2('#skF_5', B_123) | ~m1_subset_1(B_123, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_383])).
% 14.43/6.57  tff(c_455, plain, (k1_orders_2('#skF_5', k2_struct_0('#skF_5'))=a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_65, c_425])).
% 14.43/6.57  tff(c_54, plain, (k1_orders_2('#skF_5', k2_struct_0('#skF_5'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_167])).
% 14.43/6.57  tff(c_460, plain, (a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_455, c_54])).
% 14.43/6.57  tff(c_107, plain, (![A_71, B_72]: (r1_tarski(A_71, B_72) | ~m1_subset_1(A_71, k1_zfmisc_1(B_72)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 14.43/6.57  tff(c_120, plain, (![A_8]: (r1_tarski(A_8, A_8))), inference(resolution, [status(thm)], [c_65, c_107])).
% 14.43/6.57  tff(c_26, plain, (![A_17]: (r2_hidden('#skF_2'(A_17), A_17) | k1_xboole_0=A_17)), inference(cnfTransformation, [status(thm)], [f_72])).
% 14.43/6.57  tff(c_141, plain, (![C_80, B_81, A_82]: (r2_hidden(C_80, B_81) | ~r2_hidden(C_80, A_82) | ~r1_tarski(A_82, B_81))), inference(cnfTransformation, [status(thm)], [f_32])).
% 14.43/6.57  tff(c_147, plain, (![A_17, B_81]: (r2_hidden('#skF_2'(A_17), B_81) | ~r1_tarski(A_17, B_81) | k1_xboole_0=A_17)), inference(resolution, [status(thm)], [c_26, c_141])).
% 14.43/6.57  tff(c_515, plain, (![A_128, B_129]: (m1_subset_1(k1_orders_2(A_128, B_129), k1_zfmisc_1(u1_struct_0(A_128))) | ~m1_subset_1(B_129, k1_zfmisc_1(u1_struct_0(A_128))) | ~l1_orders_2(A_128) | ~v5_orders_2(A_128) | ~v4_orders_2(A_128) | ~v3_orders_2(A_128) | v2_struct_0(A_128))), inference(cnfTransformation, [status(thm)], [f_122])).
% 14.43/6.57  tff(c_526, plain, (m1_subset_1(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5')), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_455, c_515])).
% 14.43/6.57  tff(c_537, plain, (m1_subset_1(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5')), k1_zfmisc_1(k2_struct_0('#skF_5'))) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_56, c_65, c_102, c_102, c_526])).
% 14.43/6.57  tff(c_538, plain, (m1_subset_1(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5')), k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_64, c_537])).
% 14.43/6.57  tff(c_20, plain, (![A_12, C_14, B_13]: (m1_subset_1(A_12, C_14) | ~m1_subset_1(B_13, k1_zfmisc_1(C_14)) | ~r2_hidden(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_50])).
% 14.43/6.57  tff(c_641, plain, (![A_133]: (m1_subset_1(A_133, k2_struct_0('#skF_5')) | ~r2_hidden(A_133, a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_538, c_20])).
% 14.43/6.57  tff(c_653, plain, (m1_subset_1('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), k2_struct_0('#skF_5')) | a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_641])).
% 14.43/6.57  tff(c_658, plain, (m1_subset_1('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), k2_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_460, c_653])).
% 14.43/6.57  tff(c_659, plain, (![A_134, B_135, C_136]: ('#skF_3'(A_134, B_135, C_136)=A_134 | ~r2_hidden(A_134, a_2_0_orders_2(B_135, C_136)) | ~m1_subset_1(C_136, k1_zfmisc_1(u1_struct_0(B_135))) | ~l1_orders_2(B_135) | ~v5_orders_2(B_135) | ~v4_orders_2(B_135) | ~v3_orders_2(B_135) | v2_struct_0(B_135))), inference(cnfTransformation, [status(thm)], [f_153])).
% 14.43/6.57  tff(c_10345, plain, (![B_520, C_521]: ('#skF_3'('#skF_2'(a_2_0_orders_2(B_520, C_521)), B_520, C_521)='#skF_2'(a_2_0_orders_2(B_520, C_521)) | ~m1_subset_1(C_521, k1_zfmisc_1(u1_struct_0(B_520))) | ~l1_orders_2(B_520) | ~v5_orders_2(B_520) | ~v4_orders_2(B_520) | ~v3_orders_2(B_520) | v2_struct_0(B_520) | a_2_0_orders_2(B_520, C_521)=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_659])).
% 14.43/6.57  tff(c_10367, plain, (![C_521]: ('#skF_3'('#skF_2'(a_2_0_orders_2('#skF_5', C_521)), '#skF_5', C_521)='#skF_2'(a_2_0_orders_2('#skF_5', C_521)) | ~m1_subset_1(C_521, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5') | a_2_0_orders_2('#skF_5', C_521)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_102, c_10345])).
% 14.43/6.57  tff(c_10385, plain, (![C_521]: ('#skF_3'('#skF_2'(a_2_0_orders_2('#skF_5', C_521)), '#skF_5', C_521)='#skF_2'(a_2_0_orders_2('#skF_5', C_521)) | ~m1_subset_1(C_521, k1_zfmisc_1(k2_struct_0('#skF_5'))) | v2_struct_0('#skF_5') | a_2_0_orders_2('#skF_5', C_521)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_56, c_10367])).
% 14.43/6.57  tff(c_12690, plain, (![C_586]: ('#skF_3'('#skF_2'(a_2_0_orders_2('#skF_5', C_586)), '#skF_5', C_586)='#skF_2'(a_2_0_orders_2('#skF_5', C_586)) | ~m1_subset_1(C_586, k1_zfmisc_1(k2_struct_0('#skF_5'))) | a_2_0_orders_2('#skF_5', C_586)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_64, c_10385])).
% 14.43/6.57  tff(c_12736, plain, ('#skF_3'('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), '#skF_5', k2_struct_0('#skF_5'))='#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))) | a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))=k1_xboole_0), inference(resolution, [status(thm)], [c_65, c_12690])).
% 14.43/6.57  tff(c_12760, plain, ('#skF_3'('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), '#skF_5', k2_struct_0('#skF_5'))='#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_460, c_12736])).
% 14.43/6.57  tff(c_14, plain, (![A_9]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 14.43/6.57  tff(c_454, plain, (k1_orders_2('#skF_5', k1_xboole_0)=a_2_0_orders_2('#skF_5', k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_425])).
% 14.43/6.57  tff(c_529, plain, (m1_subset_1(a_2_0_orders_2('#skF_5', k1_xboole_0), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_454, c_515])).
% 14.43/6.57  tff(c_540, plain, (m1_subset_1(a_2_0_orders_2('#skF_5', k1_xboole_0), k1_zfmisc_1(k2_struct_0('#skF_5'))) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_56, c_14, c_102, c_529])).
% 14.43/6.57  tff(c_541, plain, (m1_subset_1(a_2_0_orders_2('#skF_5', k1_xboole_0), k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_64, c_540])).
% 14.43/6.57  tff(c_16, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | ~m1_subset_1(A_10, k1_zfmisc_1(B_11)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 14.43/6.57  tff(c_555, plain, (r1_tarski(a_2_0_orders_2('#skF_5', k1_xboole_0), k2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_541, c_16])).
% 14.43/6.57  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 14.43/6.57  tff(c_1055, plain, (![D_165, B_166, C_167]: (r2_hidden('#skF_4'(D_165, B_166, C_167, D_165), C_167) | r2_hidden(D_165, a_2_0_orders_2(B_166, C_167)) | ~m1_subset_1(D_165, u1_struct_0(B_166)) | ~m1_subset_1(C_167, k1_zfmisc_1(u1_struct_0(B_166))) | ~l1_orders_2(B_166) | ~v5_orders_2(B_166) | ~v4_orders_2(B_166) | ~v3_orders_2(B_166) | v2_struct_0(B_166))), inference(cnfTransformation, [status(thm)], [f_153])).
% 14.43/6.57  tff(c_9053, plain, (![D_480, B_481]: (r2_hidden('#skF_4'(D_480, B_481, k1_xboole_0, D_480), k1_xboole_0) | r2_hidden(D_480, a_2_0_orders_2(B_481, k1_xboole_0)) | ~m1_subset_1(D_480, u1_struct_0(B_481)) | ~l1_orders_2(B_481) | ~v5_orders_2(B_481) | ~v4_orders_2(B_481) | ~v3_orders_2(B_481) | v2_struct_0(B_481))), inference(resolution, [status(thm)], [c_14, c_1055])).
% 14.43/6.57  tff(c_22, plain, (![B_16, A_15]: (~r1_tarski(B_16, A_15) | ~r2_hidden(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_55])).
% 14.43/6.57  tff(c_9068, plain, (![D_480, B_481]: (~r1_tarski(k1_xboole_0, '#skF_4'(D_480, B_481, k1_xboole_0, D_480)) | r2_hidden(D_480, a_2_0_orders_2(B_481, k1_xboole_0)) | ~m1_subset_1(D_480, u1_struct_0(B_481)) | ~l1_orders_2(B_481) | ~v5_orders_2(B_481) | ~v4_orders_2(B_481) | ~v3_orders_2(B_481) | v2_struct_0(B_481))), inference(resolution, [status(thm)], [c_9053, c_22])).
% 14.43/6.57  tff(c_9082, plain, (![D_480, B_481]: (r2_hidden(D_480, a_2_0_orders_2(B_481, k1_xboole_0)) | ~m1_subset_1(D_480, u1_struct_0(B_481)) | ~l1_orders_2(B_481) | ~v5_orders_2(B_481) | ~v4_orders_2(B_481) | ~v3_orders_2(B_481) | v2_struct_0(B_481))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_9068])).
% 14.43/6.57  tff(c_1071, plain, (![D_165, C_167]: (r2_hidden('#skF_4'(D_165, '#skF_5', C_167, D_165), C_167) | r2_hidden(D_165, a_2_0_orders_2('#skF_5', C_167)) | ~m1_subset_1(D_165, u1_struct_0('#skF_5')) | ~m1_subset_1(C_167, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_102, c_1055])).
% 14.43/6.57  tff(c_1087, plain, (![D_165, C_167]: (r2_hidden('#skF_4'(D_165, '#skF_5', C_167, D_165), C_167) | r2_hidden(D_165, a_2_0_orders_2('#skF_5', C_167)) | ~m1_subset_1(D_165, k2_struct_0('#skF_5')) | ~m1_subset_1(C_167, k1_zfmisc_1(k2_struct_0('#skF_5'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_56, c_102, c_1071])).
% 14.43/6.57  tff(c_1135, plain, (![D_169, C_170]: (r2_hidden('#skF_4'(D_169, '#skF_5', C_170, D_169), C_170) | r2_hidden(D_169, a_2_0_orders_2('#skF_5', C_170)) | ~m1_subset_1(D_169, k2_struct_0('#skF_5')) | ~m1_subset_1(C_170, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_1087])).
% 14.43/6.57  tff(c_8336, plain, (![D_451]: (r2_hidden('#skF_4'(D_451, '#skF_5', k1_xboole_0, D_451), k1_xboole_0) | r2_hidden(D_451, a_2_0_orders_2('#skF_5', k1_xboole_0)) | ~m1_subset_1(D_451, k2_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_14, c_1135])).
% 14.43/6.57  tff(c_8351, plain, (![D_451]: (~r1_tarski(k1_xboole_0, '#skF_4'(D_451, '#skF_5', k1_xboole_0, D_451)) | r2_hidden(D_451, a_2_0_orders_2('#skF_5', k1_xboole_0)) | ~m1_subset_1(D_451, k2_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_8336, c_22])).
% 14.43/6.57  tff(c_8366, plain, (![D_452]: (r2_hidden(D_452, a_2_0_orders_2('#skF_5', k1_xboole_0)) | ~m1_subset_1(D_452, k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_8351])).
% 14.43/6.57  tff(c_50, plain, (![A_45, B_46, C_47]: ('#skF_3'(A_45, B_46, C_47)=A_45 | ~r2_hidden(A_45, a_2_0_orders_2(B_46, C_47)) | ~m1_subset_1(C_47, k1_zfmisc_1(u1_struct_0(B_46))) | ~l1_orders_2(B_46) | ~v5_orders_2(B_46) | ~v4_orders_2(B_46) | ~v3_orders_2(B_46) | v2_struct_0(B_46))), inference(cnfTransformation, [status(thm)], [f_153])).
% 14.43/6.57  tff(c_8368, plain, (![D_452]: ('#skF_3'(D_452, '#skF_5', k1_xboole_0)=D_452 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5') | ~m1_subset_1(D_452, k2_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_8366, c_50])).
% 14.43/6.57  tff(c_8391, plain, (![D_452]: ('#skF_3'(D_452, '#skF_5', k1_xboole_0)=D_452 | v2_struct_0('#skF_5') | ~m1_subset_1(D_452, k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_56, c_14, c_102, c_8368])).
% 14.43/6.57  tff(c_8400, plain, (![D_453]: ('#skF_3'(D_453, '#skF_5', k1_xboole_0)=D_453 | ~m1_subset_1(D_453, k2_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_64, c_8391])).
% 14.43/6.57  tff(c_8446, plain, ('#skF_3'('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), '#skF_5', k1_xboole_0)='#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_658, c_8400])).
% 14.43/6.57  tff(c_6867, plain, (![B_384, E_385, A_386, C_387]: (r2_orders_2(B_384, E_385, '#skF_3'(A_386, B_384, C_387)) | ~r2_hidden(E_385, C_387) | ~m1_subset_1(E_385, u1_struct_0(B_384)) | ~r2_hidden(A_386, a_2_0_orders_2(B_384, C_387)) | ~m1_subset_1(C_387, k1_zfmisc_1(u1_struct_0(B_384))) | ~l1_orders_2(B_384) | ~v5_orders_2(B_384) | ~v4_orders_2(B_384) | ~v3_orders_2(B_384) | v2_struct_0(B_384))), inference(cnfTransformation, [status(thm)], [f_153])).
% 14.43/6.57  tff(c_10053, plain, (![B_512, E_513, A_514]: (r2_orders_2(B_512, E_513, '#skF_3'(A_514, B_512, k1_xboole_0)) | ~r2_hidden(E_513, k1_xboole_0) | ~m1_subset_1(E_513, u1_struct_0(B_512)) | ~r2_hidden(A_514, a_2_0_orders_2(B_512, k1_xboole_0)) | ~l1_orders_2(B_512) | ~v5_orders_2(B_512) | ~v4_orders_2(B_512) | ~v3_orders_2(B_512) | v2_struct_0(B_512))), inference(resolution, [status(thm)], [c_14, c_6867])).
% 14.43/6.57  tff(c_10064, plain, (![E_513]: (r2_orders_2('#skF_5', E_513, '#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5')))) | ~r2_hidden(E_513, k1_xboole_0) | ~m1_subset_1(E_513, u1_struct_0('#skF_5')) | ~r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), a_2_0_orders_2('#skF_5', k1_xboole_0)) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_8446, c_10053])).
% 14.43/6.57  tff(c_10075, plain, (![E_513]: (r2_orders_2('#skF_5', E_513, '#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5')))) | ~r2_hidden(E_513, k1_xboole_0) | ~m1_subset_1(E_513, k2_struct_0('#skF_5')) | ~r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), a_2_0_orders_2('#skF_5', k1_xboole_0)) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_56, c_102, c_10064])).
% 14.43/6.57  tff(c_10076, plain, (![E_513]: (r2_orders_2('#skF_5', E_513, '#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5')))) | ~r2_hidden(E_513, k1_xboole_0) | ~m1_subset_1(E_513, k2_struct_0('#skF_5')) | ~r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), a_2_0_orders_2('#skF_5', k1_xboole_0)))), inference(negUnitSimplification, [status(thm)], [c_64, c_10075])).
% 14.43/6.57  tff(c_17700, plain, (~r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), a_2_0_orders_2('#skF_5', k1_xboole_0))), inference(splitLeft, [status(thm)], [c_10076])).
% 14.43/6.57  tff(c_17703, plain, (~m1_subset_1('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_9082, c_17700])).
% 14.43/6.57  tff(c_17715, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_56, c_658, c_102, c_17703])).
% 14.43/6.57  tff(c_17717, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_17715])).
% 14.43/6.57  tff(c_17719, plain, (r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), a_2_0_orders_2('#skF_5', k1_xboole_0))), inference(splitRight, [status(thm)], [c_10076])).
% 14.43/6.57  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 14.43/6.57  tff(c_17889, plain, (![B_701]: (r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), B_701) | ~r1_tarski(a_2_0_orders_2('#skF_5', k1_xboole_0), B_701))), inference(resolution, [status(thm)], [c_17719, c_2])).
% 14.43/6.57  tff(c_23557, plain, (![B_809, B_810]: (r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), B_809) | ~r1_tarski(B_810, B_809) | ~r1_tarski(a_2_0_orders_2('#skF_5', k1_xboole_0), B_810))), inference(resolution, [status(thm)], [c_17889, c_2])).
% 14.43/6.57  tff(c_23615, plain, (r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), k2_struct_0('#skF_5')) | ~r1_tarski(a_2_0_orders_2('#skF_5', k1_xboole_0), a_2_0_orders_2('#skF_5', k1_xboole_0))), inference(resolution, [status(thm)], [c_555, c_23557])).
% 14.43/6.57  tff(c_23660, plain, (r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), k2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_23615])).
% 14.43/6.57  tff(c_18, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 14.43/6.57  tff(c_10387, plain, (![B_520, A_10]: ('#skF_3'('#skF_2'(a_2_0_orders_2(B_520, A_10)), B_520, A_10)='#skF_2'(a_2_0_orders_2(B_520, A_10)) | ~l1_orders_2(B_520) | ~v5_orders_2(B_520) | ~v4_orders_2(B_520) | ~v3_orders_2(B_520) | v2_struct_0(B_520) | a_2_0_orders_2(B_520, A_10)=k1_xboole_0 | ~r1_tarski(A_10, u1_struct_0(B_520)))), inference(resolution, [status(thm)], [c_18, c_10345])).
% 14.43/6.57  tff(c_11012, plain, (![B_546, E_547, A_548]: (r2_orders_2(B_546, E_547, '#skF_3'(A_548, B_546, u1_struct_0(B_546))) | ~r2_hidden(E_547, u1_struct_0(B_546)) | ~m1_subset_1(E_547, u1_struct_0(B_546)) | ~r2_hidden(A_548, a_2_0_orders_2(B_546, u1_struct_0(B_546))) | ~l1_orders_2(B_546) | ~v5_orders_2(B_546) | ~v4_orders_2(B_546) | ~v3_orders_2(B_546) | v2_struct_0(B_546))), inference(resolution, [status(thm)], [c_65, c_6867])).
% 14.43/6.57  tff(c_32, plain, (![A_32, C_38]: (~r2_orders_2(A_32, C_38, C_38) | ~m1_subset_1(C_38, u1_struct_0(A_32)) | ~l1_orders_2(A_32))), inference(cnfTransformation, [status(thm)], [f_91])).
% 14.43/6.57  tff(c_30185, plain, (![A_954, B_955]: (~r2_hidden('#skF_3'(A_954, B_955, u1_struct_0(B_955)), u1_struct_0(B_955)) | ~m1_subset_1('#skF_3'(A_954, B_955, u1_struct_0(B_955)), u1_struct_0(B_955)) | ~r2_hidden(A_954, a_2_0_orders_2(B_955, u1_struct_0(B_955))) | ~l1_orders_2(B_955) | ~v5_orders_2(B_955) | ~v4_orders_2(B_955) | ~v3_orders_2(B_955) | v2_struct_0(B_955))), inference(resolution, [status(thm)], [c_11012, c_32])).
% 14.43/6.57  tff(c_30199, plain, (![A_954]: (~r2_hidden('#skF_3'(A_954, '#skF_5', k2_struct_0('#skF_5')), u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_3'(A_954, '#skF_5', u1_struct_0('#skF_5')), u1_struct_0('#skF_5')) | ~r2_hidden(A_954, a_2_0_orders_2('#skF_5', u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_102, c_30185])).
% 14.43/6.57  tff(c_30208, plain, (![A_954]: (~r2_hidden('#skF_3'(A_954, '#skF_5', k2_struct_0('#skF_5')), k2_struct_0('#skF_5')) | ~m1_subset_1('#skF_3'(A_954, '#skF_5', k2_struct_0('#skF_5')), k2_struct_0('#skF_5')) | ~r2_hidden(A_954, a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_56, c_102, c_102, c_102, c_102, c_30199])).
% 14.43/6.57  tff(c_30252, plain, (![A_958]: (~r2_hidden('#skF_3'(A_958, '#skF_5', k2_struct_0('#skF_5')), k2_struct_0('#skF_5')) | ~m1_subset_1('#skF_3'(A_958, '#skF_5', k2_struct_0('#skF_5')), k2_struct_0('#skF_5')) | ~r2_hidden(A_958, a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_30208])).
% 14.43/6.57  tff(c_30260, plain, (~r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), k2_struct_0('#skF_5')) | ~m1_subset_1('#skF_3'('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), '#skF_5', k2_struct_0('#skF_5')), k2_struct_0('#skF_5')) | ~r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5') | a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))=k1_xboole_0 | ~r1_tarski(k2_struct_0('#skF_5'), u1_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_10387, c_30252])).
% 14.43/6.57  tff(c_30271, plain, (~r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))) | v2_struct_0('#skF_5') | a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_120, c_102, c_62, c_60, c_58, c_56, c_658, c_12760, c_23660, c_30260])).
% 14.43/6.57  tff(c_30272, plain, (~r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_460, c_64, c_30271])).
% 14.43/6.57  tff(c_30292, plain, (~r1_tarski(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5')), a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))) | a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))=k1_xboole_0), inference(resolution, [status(thm)], [c_147, c_30272])).
% 14.43/6.57  tff(c_30308, plain, (a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_120, c_30292])).
% 14.43/6.57  tff(c_30310, plain, $false, inference(negUnitSimplification, [status(thm)], [c_460, c_30308])).
% 14.43/6.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.43/6.57  
% 14.43/6.57  Inference rules
% 14.43/6.57  ----------------------
% 14.43/6.57  #Ref     : 0
% 14.43/6.57  #Sup     : 6876
% 14.43/6.57  #Fact    : 0
% 14.43/6.57  #Define  : 0
% 14.43/6.57  #Split   : 44
% 14.43/6.57  #Chain   : 0
% 14.43/6.57  #Close   : 0
% 14.43/6.57  
% 14.43/6.57  Ordering : KBO
% 14.43/6.57  
% 14.43/6.57  Simplification rules
% 14.43/6.57  ----------------------
% 14.43/6.57  #Subsume      : 2290
% 14.43/6.57  #Demod        : 4355
% 14.43/6.57  #Tautology    : 1196
% 14.43/6.57  #SimpNegUnit  : 621
% 14.43/6.57  #BackRed      : 183
% 14.43/6.57  
% 14.43/6.57  #Partial instantiations: 0
% 14.43/6.57  #Strategies tried      : 1
% 14.43/6.57  
% 14.43/6.57  Timing (in seconds)
% 14.43/6.57  ----------------------
% 14.43/6.57  Preprocessing        : 0.35
% 14.43/6.57  Parsing              : 0.18
% 14.43/6.57  CNF conversion       : 0.03
% 14.43/6.57  Main loop            : 5.45
% 14.43/6.57  Inferencing          : 1.11
% 14.43/6.57  Reduction            : 1.69
% 14.43/6.57  Demodulation         : 1.19
% 14.43/6.57  BG Simplification    : 0.12
% 14.43/6.58  Subsumption          : 2.12
% 14.43/6.58  Abstraction          : 0.18
% 14.43/6.58  MUC search           : 0.00
% 14.43/6.58  Cooper               : 0.00
% 14.43/6.58  Total                : 5.85
% 14.43/6.58  Index Insertion      : 0.00
% 14.43/6.58  Index Deletion       : 0.00
% 14.43/6.58  Index Matching       : 0.00
% 14.43/6.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
