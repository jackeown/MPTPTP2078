%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:30 EST 2020

% Result     : Theorem 5.93s
% Output     : CNFRefutation 6.31s
% Verified   : 
% Statistics : Number of formulae       :  134 (1384 expanded)
%              Number of leaves         :   39 ( 516 expanded)
%              Depth                    :   21
%              Number of atoms          :  375 (4059 expanded)
%              Number of equality atoms :   37 ( 714 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r1_orders_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_struct_0 > l1_orders_2 > k2_orders_2 > a_2_1_orders_2 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_4 > #skF_3

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(a_2_1_orders_2,type,(
    a_2_1_orders_2: ( $i * $i ) > $i )).

tff(k2_orders_2,type,(
    k2_orders_2: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_156,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => k2_orders_2(A,k2_struct_0(A)) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_orders_2)).

tff(f_115,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_96,axiom,(
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

tff(f_57,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_mcart_1)).

tff(f_111,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_orders_2(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_orders_2)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_36,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_142,axiom,(
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

tff(f_47,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_80,axiom,(
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

tff(f_34,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(c_46,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_30,plain,(
    ! [A_28] :
      ( l1_struct_0(A_28)
      | ~ l1_orders_2(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_60,plain,(
    ! [A_48] :
      ( u1_struct_0(A_48) = k2_struct_0(A_48)
      | ~ l1_struct_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_70,plain,(
    ! [A_50] :
      ( u1_struct_0(A_50) = k2_struct_0(A_50)
      | ~ l1_orders_2(A_50) ) ),
    inference(resolution,[status(thm)],[c_30,c_60])).

tff(c_74,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_70])).

tff(c_79,plain,(
    ! [A_51] :
      ( m1_subset_1(k2_struct_0(A_51),k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ l1_struct_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_82,plain,
    ( m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | ~ l1_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_79])).

tff(c_90,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_93,plain,(
    ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_90])).

tff(c_97,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_93])).

tff(c_98,plain,(
    m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_52,plain,(
    v3_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_50,plain,(
    v4_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_48,plain,(
    v5_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_474,plain,(
    ! [A_136,B_137] :
      ( k2_orders_2(A_136,B_137) = a_2_1_orders_2(A_136,B_137)
      | ~ m1_subset_1(B_137,k1_zfmisc_1(u1_struct_0(A_136)))
      | ~ l1_orders_2(A_136)
      | ~ v5_orders_2(A_136)
      | ~ v4_orders_2(A_136)
      | ~ v3_orders_2(A_136)
      | v2_struct_0(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_480,plain,(
    ! [B_137] :
      ( k2_orders_2('#skF_4',B_137) = a_2_1_orders_2('#skF_4',B_137)
      | ~ m1_subset_1(B_137,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_474])).

tff(c_487,plain,(
    ! [B_137] :
      ( k2_orders_2('#skF_4',B_137) = a_2_1_orders_2('#skF_4',B_137)
      | ~ m1_subset_1(B_137,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_480])).

tff(c_490,plain,(
    ! [B_138] :
      ( k2_orders_2('#skF_4',B_138) = a_2_1_orders_2('#skF_4',B_138)
      | ~ m1_subset_1(B_138,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_487])).

tff(c_498,plain,(
    k2_orders_2('#skF_4',k2_struct_0('#skF_4')) = a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_98,c_490])).

tff(c_44,plain,(
    k2_orders_2('#skF_4',k2_struct_0('#skF_4')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_537,plain,(
    a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_498,c_44])).

tff(c_14,plain,(
    ! [A_12] :
      ( r2_hidden('#skF_1'(A_12),A_12)
      | k1_xboole_0 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_28,plain,(
    ! [A_26,B_27] :
      ( m1_subset_1(k2_orders_2(A_26,B_27),k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ m1_subset_1(B_27,k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ l1_orders_2(A_26)
      | ~ v5_orders_2(A_26)
      | ~ v4_orders_2(A_26)
      | ~ v3_orders_2(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_541,plain,
    ( m1_subset_1(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_498,c_28])).

tff(c_545,plain,
    ( m1_subset_1(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_98,c_74,c_74,c_541])).

tff(c_546,plain,(
    m1_subset_1(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_545])).

tff(c_8,plain,(
    ! [A_7,C_9,B_8] :
      ( m1_subset_1(A_7,C_9)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(C_9))
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_589,plain,(
    ! [A_142] :
      ( m1_subset_1(A_142,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_142,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_546,c_8])).

tff(c_597,plain,
    ( m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4'))
    | a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_589])).

tff(c_601,plain,(
    m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_537,c_597])).

tff(c_6,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_499,plain,(
    k2_orders_2('#skF_4',k1_xboole_0) = a_2_1_orders_2('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_490])).

tff(c_504,plain,(
    ! [A_139,B_140] :
      ( m1_subset_1(k2_orders_2(A_139,B_140),k1_zfmisc_1(u1_struct_0(A_139)))
      | ~ m1_subset_1(B_140,k1_zfmisc_1(u1_struct_0(A_139)))
      | ~ l1_orders_2(A_139)
      | ~ v5_orders_2(A_139)
      | ~ v4_orders_2(A_139)
      | ~ v3_orders_2(A_139)
      | v2_struct_0(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_514,plain,
    ( m1_subset_1(a_2_1_orders_2('#skF_4',k1_xboole_0),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_499,c_504])).

tff(c_522,plain,
    ( m1_subset_1(a_2_1_orders_2('#skF_4',k1_xboole_0),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_6,c_74,c_74,c_514])).

tff(c_523,plain,(
    m1_subset_1(a_2_1_orders_2('#skF_4',k1_xboole_0),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_522])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_999,plain,(
    ! [D_175,B_176,C_177] :
      ( r2_hidden('#skF_3'(D_175,B_176,C_177,D_175),C_177)
      | r2_hidden(D_175,a_2_1_orders_2(B_176,C_177))
      | ~ m1_subset_1(D_175,u1_struct_0(B_176))
      | ~ m1_subset_1(C_177,k1_zfmisc_1(u1_struct_0(B_176)))
      | ~ l1_orders_2(B_176)
      | ~ v5_orders_2(B_176)
      | ~ v4_orders_2(B_176)
      | ~ v3_orders_2(B_176)
      | v2_struct_0(B_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_1005,plain,(
    ! [D_175,C_177] :
      ( r2_hidden('#skF_3'(D_175,'#skF_4',C_177,D_175),C_177)
      | r2_hidden(D_175,a_2_1_orders_2('#skF_4',C_177))
      | ~ m1_subset_1(D_175,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_177,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_999])).

tff(c_1012,plain,(
    ! [D_175,C_177] :
      ( r2_hidden('#skF_3'(D_175,'#skF_4',C_177,D_175),C_177)
      | r2_hidden(D_175,a_2_1_orders_2('#skF_4',C_177))
      | ~ m1_subset_1(D_175,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(C_177,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_74,c_1005])).

tff(c_1140,plain,(
    ! [D_190,C_191] :
      ( r2_hidden('#skF_3'(D_190,'#skF_4',C_191,D_190),C_191)
      | r2_hidden(D_190,a_2_1_orders_2('#skF_4',C_191))
      | ~ m1_subset_1(D_190,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(C_191,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1012])).

tff(c_1251,plain,(
    ! [D_198] :
      ( r2_hidden('#skF_3'(D_198,'#skF_4',k1_xboole_0,D_198),k1_xboole_0)
      | r2_hidden(D_198,a_2_1_orders_2('#skF_4',k1_xboole_0))
      | ~ m1_subset_1(D_198,k2_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_6,c_1140])).

tff(c_10,plain,(
    ! [B_11,A_10] :
      ( ~ r1_tarski(B_11,A_10)
      | ~ r2_hidden(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1258,plain,(
    ! [D_198] :
      ( ~ r1_tarski(k1_xboole_0,'#skF_3'(D_198,'#skF_4',k1_xboole_0,D_198))
      | r2_hidden(D_198,a_2_1_orders_2('#skF_4',k1_xboole_0))
      | ~ m1_subset_1(D_198,k2_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_1251,c_10])).

tff(c_1265,plain,(
    ! [D_198] :
      ( r2_hidden(D_198,a_2_1_orders_2('#skF_4',k1_xboole_0))
      | ~ m1_subset_1(D_198,k2_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1258])).

tff(c_1270,plain,(
    ! [D_201] :
      ( r2_hidden(D_201,a_2_1_orders_2('#skF_4',k1_xboole_0))
      | ~ m1_subset_1(D_201,k2_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1258])).

tff(c_40,plain,(
    ! [A_29,B_30,C_31] :
      ( '#skF_2'(A_29,B_30,C_31) = A_29
      | ~ r2_hidden(A_29,a_2_1_orders_2(B_30,C_31))
      | ~ m1_subset_1(C_31,k1_zfmisc_1(u1_struct_0(B_30)))
      | ~ l1_orders_2(B_30)
      | ~ v5_orders_2(B_30)
      | ~ v4_orders_2(B_30)
      | ~ v3_orders_2(B_30)
      | v2_struct_0(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_1272,plain,(
    ! [D_201] :
      ( '#skF_2'(D_201,'#skF_4',k1_xboole_0) = D_201
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1(D_201,k2_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_1270,c_40])).

tff(c_1283,plain,(
    ! [D_201] :
      ( '#skF_2'(D_201,'#skF_4',k1_xboole_0) = D_201
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1(D_201,k2_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_6,c_74,c_1272])).

tff(c_1288,plain,(
    ! [D_202] :
      ( '#skF_2'(D_202,'#skF_4',k1_xboole_0) = D_202
      | ~ m1_subset_1(D_202,k2_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1283])).

tff(c_1314,plain,(
    '#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),'#skF_4',k1_xboole_0) = '#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_601,c_1288])).

tff(c_893,plain,(
    ! [A_167,B_168,C_169] :
      ( m1_subset_1('#skF_2'(A_167,B_168,C_169),u1_struct_0(B_168))
      | ~ r2_hidden(A_167,a_2_1_orders_2(B_168,C_169))
      | ~ m1_subset_1(C_169,k1_zfmisc_1(u1_struct_0(B_168)))
      | ~ l1_orders_2(B_168)
      | ~ v5_orders_2(B_168)
      | ~ v4_orders_2(B_168)
      | ~ v3_orders_2(B_168)
      | v2_struct_0(B_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_898,plain,(
    ! [A_167,C_169] :
      ( m1_subset_1('#skF_2'(A_167,'#skF_4',C_169),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_167,a_2_1_orders_2('#skF_4',C_169))
      | ~ m1_subset_1(C_169,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_893])).

tff(c_901,plain,(
    ! [A_167,C_169] :
      ( m1_subset_1('#skF_2'(A_167,'#skF_4',C_169),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_167,a_2_1_orders_2('#skF_4',C_169))
      | ~ m1_subset_1(C_169,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_74,c_898])).

tff(c_902,plain,(
    ! [A_167,C_169] :
      ( m1_subset_1('#skF_2'(A_167,'#skF_4',C_169),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_167,a_2_1_orders_2('#skF_4',C_169))
      | ~ m1_subset_1(C_169,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_901])).

tff(c_1348,plain,(
    ! [B_204,A_205,C_206,E_207] :
      ( r2_orders_2(B_204,'#skF_2'(A_205,B_204,C_206),E_207)
      | ~ r2_hidden(E_207,C_206)
      | ~ m1_subset_1(E_207,u1_struct_0(B_204))
      | ~ r2_hidden(A_205,a_2_1_orders_2(B_204,C_206))
      | ~ m1_subset_1(C_206,k1_zfmisc_1(u1_struct_0(B_204)))
      | ~ l1_orders_2(B_204)
      | ~ v5_orders_2(B_204)
      | ~ v4_orders_2(B_204)
      | ~ v3_orders_2(B_204)
      | v2_struct_0(B_204) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_1354,plain,(
    ! [A_205,C_206,E_207] :
      ( r2_orders_2('#skF_4','#skF_2'(A_205,'#skF_4',C_206),E_207)
      | ~ r2_hidden(E_207,C_206)
      | ~ m1_subset_1(E_207,u1_struct_0('#skF_4'))
      | ~ r2_hidden(A_205,a_2_1_orders_2('#skF_4',C_206))
      | ~ m1_subset_1(C_206,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_1348])).

tff(c_1361,plain,(
    ! [A_205,C_206,E_207] :
      ( r2_orders_2('#skF_4','#skF_2'(A_205,'#skF_4',C_206),E_207)
      | ~ r2_hidden(E_207,C_206)
      | ~ m1_subset_1(E_207,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_205,a_2_1_orders_2('#skF_4',C_206))
      | ~ m1_subset_1(C_206,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_74,c_1354])).

tff(c_1387,plain,(
    ! [A_212,C_213,E_214] :
      ( r2_orders_2('#skF_4','#skF_2'(A_212,'#skF_4',C_213),E_214)
      | ~ r2_hidden(E_214,C_213)
      | ~ m1_subset_1(E_214,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_212,a_2_1_orders_2('#skF_4',C_213))
      | ~ m1_subset_1(C_213,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1361])).

tff(c_1830,plain,(
    ! [A_237,E_238] :
      ( r2_orders_2('#skF_4','#skF_2'(A_237,'#skF_4',k1_xboole_0),E_238)
      | ~ r2_hidden(E_238,k1_xboole_0)
      | ~ m1_subset_1(E_238,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_237,a_2_1_orders_2('#skF_4',k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_6,c_1387])).

tff(c_22,plain,(
    ! [A_16,C_22] :
      ( ~ r2_orders_2(A_16,C_22,C_22)
      | ~ m1_subset_1(C_22,u1_struct_0(A_16))
      | ~ l1_orders_2(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1838,plain,(
    ! [A_237] :
      ( ~ m1_subset_1('#skF_2'(A_237,'#skF_4',k1_xboole_0),u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ r2_hidden('#skF_2'(A_237,'#skF_4',k1_xboole_0),k1_xboole_0)
      | ~ m1_subset_1('#skF_2'(A_237,'#skF_4',k1_xboole_0),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_237,a_2_1_orders_2('#skF_4',k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_1830,c_22])).

tff(c_1858,plain,(
    ! [A_239] :
      ( ~ r2_hidden('#skF_2'(A_239,'#skF_4',k1_xboole_0),k1_xboole_0)
      | ~ m1_subset_1('#skF_2'(A_239,'#skF_4',k1_xboole_0),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_239,a_2_1_orders_2('#skF_4',k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_74,c_1838])).

tff(c_1871,plain,(
    ! [A_167] :
      ( ~ r2_hidden('#skF_2'(A_167,'#skF_4',k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_167,a_2_1_orders_2('#skF_4',k1_xboole_0))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_902,c_1858])).

tff(c_1896,plain,(
    ! [A_242] :
      ( ~ r2_hidden('#skF_2'(A_242,'#skF_4',k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_242,a_2_1_orders_2('#skF_4',k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1871])).

tff(c_1899,plain,
    ( ~ r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),k1_xboole_0)
    | ~ r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),a_2_1_orders_2('#skF_4',k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1314,c_1896])).

tff(c_2505,plain,(
    ~ r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),a_2_1_orders_2('#skF_4',k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_1899])).

tff(c_2508,plain,(
    ~ m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_1265,c_2505])).

tff(c_2515,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_601,c_2508])).

tff(c_2517,plain,(
    r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),a_2_1_orders_2('#skF_4',k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_1899])).

tff(c_4,plain,(
    ! [C_5,A_2,B_3] :
      ( r2_hidden(C_5,A_2)
      | ~ r2_hidden(C_5,B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2632,plain,(
    ! [A_281] :
      ( r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),A_281)
      | ~ m1_subset_1(a_2_1_orders_2('#skF_4',k1_xboole_0),k1_zfmisc_1(A_281)) ) ),
    inference(resolution,[status(thm)],[c_2517,c_4])).

tff(c_2967,plain,(
    ! [A_305,A_306] :
      ( r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),A_305)
      | ~ m1_subset_1(A_306,k1_zfmisc_1(A_305))
      | ~ m1_subset_1(a_2_1_orders_2('#skF_4',k1_xboole_0),k1_zfmisc_1(A_306)) ) ),
    inference(resolution,[status(thm)],[c_2632,c_4])).

tff(c_2977,plain,
    ( r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4'))
    | ~ m1_subset_1(a_2_1_orders_2('#skF_4',k1_xboole_0),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_98,c_2967])).

tff(c_2988,plain,(
    r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_523,c_2977])).

tff(c_99,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_605,plain,(
    ! [A_143,B_144,C_145] :
      ( '#skF_2'(A_143,B_144,C_145) = A_143
      | ~ r2_hidden(A_143,a_2_1_orders_2(B_144,C_145))
      | ~ m1_subset_1(C_145,k1_zfmisc_1(u1_struct_0(B_144)))
      | ~ l1_orders_2(B_144)
      | ~ v5_orders_2(B_144)
      | ~ v4_orders_2(B_144)
      | ~ v3_orders_2(B_144)
      | v2_struct_0(B_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_2111,plain,(
    ! [B_252,C_253] :
      ( '#skF_2'('#skF_1'(a_2_1_orders_2(B_252,C_253)),B_252,C_253) = '#skF_1'(a_2_1_orders_2(B_252,C_253))
      | ~ m1_subset_1(C_253,k1_zfmisc_1(u1_struct_0(B_252)))
      | ~ l1_orders_2(B_252)
      | ~ v5_orders_2(B_252)
      | ~ v4_orders_2(B_252)
      | ~ v3_orders_2(B_252)
      | v2_struct_0(B_252)
      | a_2_1_orders_2(B_252,C_253) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_14,c_605])).

tff(c_2117,plain,(
    ! [C_253] :
      ( '#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4',C_253)),'#skF_4',C_253) = '#skF_1'(a_2_1_orders_2('#skF_4',C_253))
      | ~ m1_subset_1(C_253,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4')
      | a_2_1_orders_2('#skF_4',C_253) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_2111])).

tff(c_2124,plain,(
    ! [C_253] :
      ( '#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4',C_253)),'#skF_4',C_253) = '#skF_1'(a_2_1_orders_2('#skF_4',C_253))
      | ~ m1_subset_1(C_253,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4')
      | a_2_1_orders_2('#skF_4',C_253) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_2117])).

tff(c_2198,plain,(
    ! [C_255] :
      ( '#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4',C_255)),'#skF_4',C_255) = '#skF_1'(a_2_1_orders_2('#skF_4',C_255))
      | ~ m1_subset_1(C_255,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | a_2_1_orders_2('#skF_4',C_255) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_2124])).

tff(c_2206,plain,
    ( '#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),'#skF_4',k2_struct_0('#skF_4')) = '#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')))
    | a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_98,c_2198])).

tff(c_2217,plain,(
    '#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),'#skF_4',k2_struct_0('#skF_4')) = '#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_537,c_2206])).

tff(c_18,plain,(
    ! [A_15] :
      ( m1_subset_1(k2_struct_0(A_15),k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ l1_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2436,plain,(
    ! [A_269,A_270,E_271] :
      ( r2_orders_2(A_269,'#skF_2'(A_270,A_269,k2_struct_0(A_269)),E_271)
      | ~ r2_hidden(E_271,k2_struct_0(A_269))
      | ~ m1_subset_1(E_271,u1_struct_0(A_269))
      | ~ r2_hidden(A_270,a_2_1_orders_2(A_269,k2_struct_0(A_269)))
      | ~ l1_orders_2(A_269)
      | ~ v5_orders_2(A_269)
      | ~ v4_orders_2(A_269)
      | ~ v3_orders_2(A_269)
      | v2_struct_0(A_269)
      | ~ l1_struct_0(A_269) ) ),
    inference(resolution,[status(thm)],[c_18,c_1348])).

tff(c_2447,plain,(
    ! [E_271] :
      ( r2_orders_2('#skF_4','#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),E_271)
      | ~ r2_hidden(E_271,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(E_271,u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2217,c_2436])).

tff(c_2452,plain,(
    ! [E_271] :
      ( r2_orders_2('#skF_4','#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),E_271)
      | ~ r2_hidden(E_271,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(E_271,k2_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_52,c_50,c_48,c_46,c_74,c_2447])).

tff(c_2453,plain,(
    ! [E_271] :
      ( r2_orders_2('#skF_4','#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),E_271)
      | ~ r2_hidden(E_271,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(E_271,k2_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_2452])).

tff(c_3954,plain,(
    ~ r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_2453])).

tff(c_3966,plain,(
    a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_3954])).

tff(c_3975,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_537,c_3966])).

tff(c_4055,plain,(
    ! [E_370] :
      ( r2_orders_2('#skF_4','#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),E_370)
      | ~ r2_hidden(E_370,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(E_370,k2_struct_0('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_2453])).

tff(c_4063,plain,
    ( ~ m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4')
    | ~ r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_4055,c_22])).

tff(c_4074,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_601,c_2988,c_46,c_601,c_74,c_4063])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:09:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.93/2.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.31/2.22  
% 6.31/2.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.31/2.22  %$ r2_orders_2 > r1_orders_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_struct_0 > l1_orders_2 > k2_orders_2 > a_2_1_orders_2 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_4 > #skF_3
% 6.31/2.22  
% 6.31/2.22  %Foreground sorts:
% 6.31/2.22  
% 6.31/2.22  
% 6.31/2.22  %Background operators:
% 6.31/2.22  
% 6.31/2.22  
% 6.31/2.22  %Foreground operators:
% 6.31/2.22  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.31/2.22  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 6.31/2.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.31/2.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.31/2.22  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.31/2.22  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 6.31/2.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.31/2.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.31/2.22  tff(a_2_1_orders_2, type, a_2_1_orders_2: ($i * $i) > $i).
% 6.31/2.22  tff(k2_orders_2, type, k2_orders_2: ($i * $i) > $i).
% 6.31/2.22  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.31/2.22  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.31/2.22  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 6.31/2.22  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 6.31/2.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.31/2.22  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 6.31/2.22  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 6.31/2.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.31/2.22  tff('#skF_4', type, '#skF_4': $i).
% 6.31/2.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.31/2.22  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 6.31/2.22  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 6.31/2.22  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.31/2.22  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 6.31/2.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.31/2.22  
% 6.31/2.24  tff(f_156, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (k2_orders_2(A, k2_struct_0(A)) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_orders_2)).
% 6.31/2.24  tff(f_115, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 6.31/2.24  tff(f_61, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 6.31/2.24  tff(f_65, axiom, (![A]: (l1_struct_0(A) => m1_subset_1(k2_struct_0(A), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 6.31/2.24  tff(f_96, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_orders_2(A, B) = a_2_1_orders_2(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_orders_2)).
% 6.31/2.24  tff(f_57, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & r1_xboole_0(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_mcart_1)).
% 6.31/2.24  tff(f_111, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_orders_2(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_orders_2)).
% 6.31/2.24  tff(f_42, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 6.31/2.24  tff(f_36, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 6.31/2.24  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.31/2.24  tff(f_142, axiom, (![A, B, C]: ((((((~v2_struct_0(B) & v3_orders_2(B)) & v4_orders_2(B)) & v5_orders_2(B)) & l1_orders_2(B)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B)))) => (r2_hidden(A, a_2_1_orders_2(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r2_hidden(E, C) => r2_orders_2(B, D, E))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fraenkel_a_2_1_orders_2)).
% 6.31/2.24  tff(f_47, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 6.31/2.24  tff(f_80, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_orders_2(A, B, C) <=> (r1_orders_2(A, B, C) & ~(B = C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_orders_2)).
% 6.31/2.24  tff(f_34, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 6.31/2.24  tff(c_46, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_156])).
% 6.31/2.24  tff(c_30, plain, (![A_28]: (l1_struct_0(A_28) | ~l1_orders_2(A_28))), inference(cnfTransformation, [status(thm)], [f_115])).
% 6.31/2.24  tff(c_60, plain, (![A_48]: (u1_struct_0(A_48)=k2_struct_0(A_48) | ~l1_struct_0(A_48))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.31/2.24  tff(c_70, plain, (![A_50]: (u1_struct_0(A_50)=k2_struct_0(A_50) | ~l1_orders_2(A_50))), inference(resolution, [status(thm)], [c_30, c_60])).
% 6.31/2.24  tff(c_74, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_46, c_70])).
% 6.31/2.24  tff(c_79, plain, (![A_51]: (m1_subset_1(k2_struct_0(A_51), k1_zfmisc_1(u1_struct_0(A_51))) | ~l1_struct_0(A_51))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.31/2.24  tff(c_82, plain, (m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_74, c_79])).
% 6.31/2.24  tff(c_90, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_82])).
% 6.31/2.24  tff(c_93, plain, (~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_30, c_90])).
% 6.31/2.24  tff(c_97, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_93])).
% 6.31/2.24  tff(c_98, plain, (m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_82])).
% 6.31/2.24  tff(c_54, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_156])).
% 6.31/2.24  tff(c_52, plain, (v3_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_156])).
% 6.31/2.24  tff(c_50, plain, (v4_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_156])).
% 6.31/2.24  tff(c_48, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_156])).
% 6.31/2.24  tff(c_474, plain, (![A_136, B_137]: (k2_orders_2(A_136, B_137)=a_2_1_orders_2(A_136, B_137) | ~m1_subset_1(B_137, k1_zfmisc_1(u1_struct_0(A_136))) | ~l1_orders_2(A_136) | ~v5_orders_2(A_136) | ~v4_orders_2(A_136) | ~v3_orders_2(A_136) | v2_struct_0(A_136))), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.31/2.24  tff(c_480, plain, (![B_137]: (k2_orders_2('#skF_4', B_137)=a_2_1_orders_2('#skF_4', B_137) | ~m1_subset_1(B_137, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_74, c_474])).
% 6.31/2.24  tff(c_487, plain, (![B_137]: (k2_orders_2('#skF_4', B_137)=a_2_1_orders_2('#skF_4', B_137) | ~m1_subset_1(B_137, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_480])).
% 6.31/2.24  tff(c_490, plain, (![B_138]: (k2_orders_2('#skF_4', B_138)=a_2_1_orders_2('#skF_4', B_138) | ~m1_subset_1(B_138, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_54, c_487])).
% 6.31/2.24  tff(c_498, plain, (k2_orders_2('#skF_4', k2_struct_0('#skF_4'))=a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_98, c_490])).
% 6.31/2.24  tff(c_44, plain, (k2_orders_2('#skF_4', k2_struct_0('#skF_4'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_156])).
% 6.31/2.24  tff(c_537, plain, (a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_498, c_44])).
% 6.31/2.24  tff(c_14, plain, (![A_12]: (r2_hidden('#skF_1'(A_12), A_12) | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.31/2.24  tff(c_28, plain, (![A_26, B_27]: (m1_subset_1(k2_orders_2(A_26, B_27), k1_zfmisc_1(u1_struct_0(A_26))) | ~m1_subset_1(B_27, k1_zfmisc_1(u1_struct_0(A_26))) | ~l1_orders_2(A_26) | ~v5_orders_2(A_26) | ~v4_orders_2(A_26) | ~v3_orders_2(A_26) | v2_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_111])).
% 6.31/2.24  tff(c_541, plain, (m1_subset_1(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_498, c_28])).
% 6.31/2.24  tff(c_545, plain, (m1_subset_1(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4')), k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_98, c_74, c_74, c_541])).
% 6.31/2.24  tff(c_546, plain, (m1_subset_1(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4')), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_54, c_545])).
% 6.31/2.24  tff(c_8, plain, (![A_7, C_9, B_8]: (m1_subset_1(A_7, C_9) | ~m1_subset_1(B_8, k1_zfmisc_1(C_9)) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.31/2.24  tff(c_589, plain, (![A_142]: (m1_subset_1(A_142, k2_struct_0('#skF_4')) | ~r2_hidden(A_142, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_546, c_8])).
% 6.31/2.24  tff(c_597, plain, (m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4')) | a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_14, c_589])).
% 6.31/2.24  tff(c_601, plain, (m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_537, c_597])).
% 6.31/2.24  tff(c_6, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 6.31/2.24  tff(c_499, plain, (k2_orders_2('#skF_4', k1_xboole_0)=a_2_1_orders_2('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_490])).
% 6.31/2.24  tff(c_504, plain, (![A_139, B_140]: (m1_subset_1(k2_orders_2(A_139, B_140), k1_zfmisc_1(u1_struct_0(A_139))) | ~m1_subset_1(B_140, k1_zfmisc_1(u1_struct_0(A_139))) | ~l1_orders_2(A_139) | ~v5_orders_2(A_139) | ~v4_orders_2(A_139) | ~v3_orders_2(A_139) | v2_struct_0(A_139))), inference(cnfTransformation, [status(thm)], [f_111])).
% 6.31/2.24  tff(c_514, plain, (m1_subset_1(a_2_1_orders_2('#skF_4', k1_xboole_0), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_499, c_504])).
% 6.31/2.24  tff(c_522, plain, (m1_subset_1(a_2_1_orders_2('#skF_4', k1_xboole_0), k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_6, c_74, c_74, c_514])).
% 6.31/2.24  tff(c_523, plain, (m1_subset_1(a_2_1_orders_2('#skF_4', k1_xboole_0), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_54, c_522])).
% 6.31/2.24  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.31/2.24  tff(c_999, plain, (![D_175, B_176, C_177]: (r2_hidden('#skF_3'(D_175, B_176, C_177, D_175), C_177) | r2_hidden(D_175, a_2_1_orders_2(B_176, C_177)) | ~m1_subset_1(D_175, u1_struct_0(B_176)) | ~m1_subset_1(C_177, k1_zfmisc_1(u1_struct_0(B_176))) | ~l1_orders_2(B_176) | ~v5_orders_2(B_176) | ~v4_orders_2(B_176) | ~v3_orders_2(B_176) | v2_struct_0(B_176))), inference(cnfTransformation, [status(thm)], [f_142])).
% 6.31/2.24  tff(c_1005, plain, (![D_175, C_177]: (r2_hidden('#skF_3'(D_175, '#skF_4', C_177, D_175), C_177) | r2_hidden(D_175, a_2_1_orders_2('#skF_4', C_177)) | ~m1_subset_1(D_175, u1_struct_0('#skF_4')) | ~m1_subset_1(C_177, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_74, c_999])).
% 6.31/2.24  tff(c_1012, plain, (![D_175, C_177]: (r2_hidden('#skF_3'(D_175, '#skF_4', C_177, D_175), C_177) | r2_hidden(D_175, a_2_1_orders_2('#skF_4', C_177)) | ~m1_subset_1(D_175, k2_struct_0('#skF_4')) | ~m1_subset_1(C_177, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_74, c_1005])).
% 6.31/2.24  tff(c_1140, plain, (![D_190, C_191]: (r2_hidden('#skF_3'(D_190, '#skF_4', C_191, D_190), C_191) | r2_hidden(D_190, a_2_1_orders_2('#skF_4', C_191)) | ~m1_subset_1(D_190, k2_struct_0('#skF_4')) | ~m1_subset_1(C_191, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_54, c_1012])).
% 6.31/2.24  tff(c_1251, plain, (![D_198]: (r2_hidden('#skF_3'(D_198, '#skF_4', k1_xboole_0, D_198), k1_xboole_0) | r2_hidden(D_198, a_2_1_orders_2('#skF_4', k1_xboole_0)) | ~m1_subset_1(D_198, k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_6, c_1140])).
% 6.31/2.24  tff(c_10, plain, (![B_11, A_10]: (~r1_tarski(B_11, A_10) | ~r2_hidden(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.31/2.24  tff(c_1258, plain, (![D_198]: (~r1_tarski(k1_xboole_0, '#skF_3'(D_198, '#skF_4', k1_xboole_0, D_198)) | r2_hidden(D_198, a_2_1_orders_2('#skF_4', k1_xboole_0)) | ~m1_subset_1(D_198, k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_1251, c_10])).
% 6.31/2.24  tff(c_1265, plain, (![D_198]: (r2_hidden(D_198, a_2_1_orders_2('#skF_4', k1_xboole_0)) | ~m1_subset_1(D_198, k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1258])).
% 6.31/2.24  tff(c_1270, plain, (![D_201]: (r2_hidden(D_201, a_2_1_orders_2('#skF_4', k1_xboole_0)) | ~m1_subset_1(D_201, k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1258])).
% 6.31/2.24  tff(c_40, plain, (![A_29, B_30, C_31]: ('#skF_2'(A_29, B_30, C_31)=A_29 | ~r2_hidden(A_29, a_2_1_orders_2(B_30, C_31)) | ~m1_subset_1(C_31, k1_zfmisc_1(u1_struct_0(B_30))) | ~l1_orders_2(B_30) | ~v5_orders_2(B_30) | ~v4_orders_2(B_30) | ~v3_orders_2(B_30) | v2_struct_0(B_30))), inference(cnfTransformation, [status(thm)], [f_142])).
% 6.31/2.24  tff(c_1272, plain, (![D_201]: ('#skF_2'(D_201, '#skF_4', k1_xboole_0)=D_201 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4') | ~m1_subset_1(D_201, k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_1270, c_40])).
% 6.31/2.24  tff(c_1283, plain, (![D_201]: ('#skF_2'(D_201, '#skF_4', k1_xboole_0)=D_201 | v2_struct_0('#skF_4') | ~m1_subset_1(D_201, k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_6, c_74, c_1272])).
% 6.31/2.24  tff(c_1288, plain, (![D_202]: ('#skF_2'(D_202, '#skF_4', k1_xboole_0)=D_202 | ~m1_subset_1(D_202, k2_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_54, c_1283])).
% 6.31/2.24  tff(c_1314, plain, ('#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), '#skF_4', k1_xboole_0)='#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_601, c_1288])).
% 6.31/2.24  tff(c_893, plain, (![A_167, B_168, C_169]: (m1_subset_1('#skF_2'(A_167, B_168, C_169), u1_struct_0(B_168)) | ~r2_hidden(A_167, a_2_1_orders_2(B_168, C_169)) | ~m1_subset_1(C_169, k1_zfmisc_1(u1_struct_0(B_168))) | ~l1_orders_2(B_168) | ~v5_orders_2(B_168) | ~v4_orders_2(B_168) | ~v3_orders_2(B_168) | v2_struct_0(B_168))), inference(cnfTransformation, [status(thm)], [f_142])).
% 6.31/2.24  tff(c_898, plain, (![A_167, C_169]: (m1_subset_1('#skF_2'(A_167, '#skF_4', C_169), k2_struct_0('#skF_4')) | ~r2_hidden(A_167, a_2_1_orders_2('#skF_4', C_169)) | ~m1_subset_1(C_169, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_74, c_893])).
% 6.31/2.24  tff(c_901, plain, (![A_167, C_169]: (m1_subset_1('#skF_2'(A_167, '#skF_4', C_169), k2_struct_0('#skF_4')) | ~r2_hidden(A_167, a_2_1_orders_2('#skF_4', C_169)) | ~m1_subset_1(C_169, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_74, c_898])).
% 6.31/2.24  tff(c_902, plain, (![A_167, C_169]: (m1_subset_1('#skF_2'(A_167, '#skF_4', C_169), k2_struct_0('#skF_4')) | ~r2_hidden(A_167, a_2_1_orders_2('#skF_4', C_169)) | ~m1_subset_1(C_169, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_54, c_901])).
% 6.31/2.24  tff(c_1348, plain, (![B_204, A_205, C_206, E_207]: (r2_orders_2(B_204, '#skF_2'(A_205, B_204, C_206), E_207) | ~r2_hidden(E_207, C_206) | ~m1_subset_1(E_207, u1_struct_0(B_204)) | ~r2_hidden(A_205, a_2_1_orders_2(B_204, C_206)) | ~m1_subset_1(C_206, k1_zfmisc_1(u1_struct_0(B_204))) | ~l1_orders_2(B_204) | ~v5_orders_2(B_204) | ~v4_orders_2(B_204) | ~v3_orders_2(B_204) | v2_struct_0(B_204))), inference(cnfTransformation, [status(thm)], [f_142])).
% 6.31/2.24  tff(c_1354, plain, (![A_205, C_206, E_207]: (r2_orders_2('#skF_4', '#skF_2'(A_205, '#skF_4', C_206), E_207) | ~r2_hidden(E_207, C_206) | ~m1_subset_1(E_207, u1_struct_0('#skF_4')) | ~r2_hidden(A_205, a_2_1_orders_2('#skF_4', C_206)) | ~m1_subset_1(C_206, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_74, c_1348])).
% 6.31/2.24  tff(c_1361, plain, (![A_205, C_206, E_207]: (r2_orders_2('#skF_4', '#skF_2'(A_205, '#skF_4', C_206), E_207) | ~r2_hidden(E_207, C_206) | ~m1_subset_1(E_207, k2_struct_0('#skF_4')) | ~r2_hidden(A_205, a_2_1_orders_2('#skF_4', C_206)) | ~m1_subset_1(C_206, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_74, c_1354])).
% 6.31/2.24  tff(c_1387, plain, (![A_212, C_213, E_214]: (r2_orders_2('#skF_4', '#skF_2'(A_212, '#skF_4', C_213), E_214) | ~r2_hidden(E_214, C_213) | ~m1_subset_1(E_214, k2_struct_0('#skF_4')) | ~r2_hidden(A_212, a_2_1_orders_2('#skF_4', C_213)) | ~m1_subset_1(C_213, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_54, c_1361])).
% 6.31/2.24  tff(c_1830, plain, (![A_237, E_238]: (r2_orders_2('#skF_4', '#skF_2'(A_237, '#skF_4', k1_xboole_0), E_238) | ~r2_hidden(E_238, k1_xboole_0) | ~m1_subset_1(E_238, k2_struct_0('#skF_4')) | ~r2_hidden(A_237, a_2_1_orders_2('#skF_4', k1_xboole_0)))), inference(resolution, [status(thm)], [c_6, c_1387])).
% 6.31/2.24  tff(c_22, plain, (![A_16, C_22]: (~r2_orders_2(A_16, C_22, C_22) | ~m1_subset_1(C_22, u1_struct_0(A_16)) | ~l1_orders_2(A_16))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.31/2.24  tff(c_1838, plain, (![A_237]: (~m1_subset_1('#skF_2'(A_237, '#skF_4', k1_xboole_0), u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~r2_hidden('#skF_2'(A_237, '#skF_4', k1_xboole_0), k1_xboole_0) | ~m1_subset_1('#skF_2'(A_237, '#skF_4', k1_xboole_0), k2_struct_0('#skF_4')) | ~r2_hidden(A_237, a_2_1_orders_2('#skF_4', k1_xboole_0)))), inference(resolution, [status(thm)], [c_1830, c_22])).
% 6.31/2.24  tff(c_1858, plain, (![A_239]: (~r2_hidden('#skF_2'(A_239, '#skF_4', k1_xboole_0), k1_xboole_0) | ~m1_subset_1('#skF_2'(A_239, '#skF_4', k1_xboole_0), k2_struct_0('#skF_4')) | ~r2_hidden(A_239, a_2_1_orders_2('#skF_4', k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_74, c_1838])).
% 6.31/2.24  tff(c_1871, plain, (![A_167]: (~r2_hidden('#skF_2'(A_167, '#skF_4', k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_167, a_2_1_orders_2('#skF_4', k1_xboole_0)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_902, c_1858])).
% 6.31/2.24  tff(c_1896, plain, (![A_242]: (~r2_hidden('#skF_2'(A_242, '#skF_4', k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_242, a_2_1_orders_2('#skF_4', k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1871])).
% 6.31/2.24  tff(c_1899, plain, (~r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), k1_xboole_0) | ~r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_1_orders_2('#skF_4', k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1314, c_1896])).
% 6.31/2.24  tff(c_2505, plain, (~r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_1_orders_2('#skF_4', k1_xboole_0))), inference(splitLeft, [status(thm)], [c_1899])).
% 6.31/2.24  tff(c_2508, plain, (~m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_1265, c_2505])).
% 6.31/2.24  tff(c_2515, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_601, c_2508])).
% 6.31/2.24  tff(c_2517, plain, (r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_1_orders_2('#skF_4', k1_xboole_0))), inference(splitRight, [status(thm)], [c_1899])).
% 6.31/2.24  tff(c_4, plain, (![C_5, A_2, B_3]: (r2_hidden(C_5, A_2) | ~r2_hidden(C_5, B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.31/2.24  tff(c_2632, plain, (![A_281]: (r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), A_281) | ~m1_subset_1(a_2_1_orders_2('#skF_4', k1_xboole_0), k1_zfmisc_1(A_281)))), inference(resolution, [status(thm)], [c_2517, c_4])).
% 6.31/2.24  tff(c_2967, plain, (![A_305, A_306]: (r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), A_305) | ~m1_subset_1(A_306, k1_zfmisc_1(A_305)) | ~m1_subset_1(a_2_1_orders_2('#skF_4', k1_xboole_0), k1_zfmisc_1(A_306)))), inference(resolution, [status(thm)], [c_2632, c_4])).
% 6.31/2.24  tff(c_2977, plain, (r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4')) | ~m1_subset_1(a_2_1_orders_2('#skF_4', k1_xboole_0), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_98, c_2967])).
% 6.31/2.24  tff(c_2988, plain, (r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_523, c_2977])).
% 6.31/2.24  tff(c_99, plain, (l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_82])).
% 6.31/2.24  tff(c_605, plain, (![A_143, B_144, C_145]: ('#skF_2'(A_143, B_144, C_145)=A_143 | ~r2_hidden(A_143, a_2_1_orders_2(B_144, C_145)) | ~m1_subset_1(C_145, k1_zfmisc_1(u1_struct_0(B_144))) | ~l1_orders_2(B_144) | ~v5_orders_2(B_144) | ~v4_orders_2(B_144) | ~v3_orders_2(B_144) | v2_struct_0(B_144))), inference(cnfTransformation, [status(thm)], [f_142])).
% 6.31/2.24  tff(c_2111, plain, (![B_252, C_253]: ('#skF_2'('#skF_1'(a_2_1_orders_2(B_252, C_253)), B_252, C_253)='#skF_1'(a_2_1_orders_2(B_252, C_253)) | ~m1_subset_1(C_253, k1_zfmisc_1(u1_struct_0(B_252))) | ~l1_orders_2(B_252) | ~v5_orders_2(B_252) | ~v4_orders_2(B_252) | ~v3_orders_2(B_252) | v2_struct_0(B_252) | a_2_1_orders_2(B_252, C_253)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_605])).
% 6.31/2.24  tff(c_2117, plain, (![C_253]: ('#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4', C_253)), '#skF_4', C_253)='#skF_1'(a_2_1_orders_2('#skF_4', C_253)) | ~m1_subset_1(C_253, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4') | a_2_1_orders_2('#skF_4', C_253)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_74, c_2111])).
% 6.31/2.24  tff(c_2124, plain, (![C_253]: ('#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4', C_253)), '#skF_4', C_253)='#skF_1'(a_2_1_orders_2('#skF_4', C_253)) | ~m1_subset_1(C_253, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4') | a_2_1_orders_2('#skF_4', C_253)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_2117])).
% 6.31/2.24  tff(c_2198, plain, (![C_255]: ('#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4', C_255)), '#skF_4', C_255)='#skF_1'(a_2_1_orders_2('#skF_4', C_255)) | ~m1_subset_1(C_255, k1_zfmisc_1(k2_struct_0('#skF_4'))) | a_2_1_orders_2('#skF_4', C_255)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_54, c_2124])).
% 6.31/2.24  tff(c_2206, plain, ('#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), '#skF_4', k2_struct_0('#skF_4'))='#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))) | a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_98, c_2198])).
% 6.31/2.24  tff(c_2217, plain, ('#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), '#skF_4', k2_struct_0('#skF_4'))='#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_537, c_2206])).
% 6.31/2.24  tff(c_18, plain, (![A_15]: (m1_subset_1(k2_struct_0(A_15), k1_zfmisc_1(u1_struct_0(A_15))) | ~l1_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.31/2.24  tff(c_2436, plain, (![A_269, A_270, E_271]: (r2_orders_2(A_269, '#skF_2'(A_270, A_269, k2_struct_0(A_269)), E_271) | ~r2_hidden(E_271, k2_struct_0(A_269)) | ~m1_subset_1(E_271, u1_struct_0(A_269)) | ~r2_hidden(A_270, a_2_1_orders_2(A_269, k2_struct_0(A_269))) | ~l1_orders_2(A_269) | ~v5_orders_2(A_269) | ~v4_orders_2(A_269) | ~v3_orders_2(A_269) | v2_struct_0(A_269) | ~l1_struct_0(A_269))), inference(resolution, [status(thm)], [c_18, c_1348])).
% 6.31/2.24  tff(c_2447, plain, (![E_271]: (r2_orders_2('#skF_4', '#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), E_271) | ~r2_hidden(E_271, k2_struct_0('#skF_4')) | ~m1_subset_1(E_271, u1_struct_0('#skF_4')) | ~r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4') | ~l1_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2217, c_2436])).
% 6.31/2.24  tff(c_2452, plain, (![E_271]: (r2_orders_2('#skF_4', '#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), E_271) | ~r2_hidden(E_271, k2_struct_0('#skF_4')) | ~m1_subset_1(E_271, k2_struct_0('#skF_4')) | ~r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_99, c_52, c_50, c_48, c_46, c_74, c_2447])).
% 6.31/2.24  tff(c_2453, plain, (![E_271]: (r2_orders_2('#skF_4', '#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), E_271) | ~r2_hidden(E_271, k2_struct_0('#skF_4')) | ~m1_subset_1(E_271, k2_struct_0('#skF_4')) | ~r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_54, c_2452])).
% 6.31/2.24  tff(c_3954, plain, (~r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_2453])).
% 6.31/2.24  tff(c_3966, plain, (a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_14, c_3954])).
% 6.31/2.24  tff(c_3975, plain, $false, inference(negUnitSimplification, [status(thm)], [c_537, c_3966])).
% 6.31/2.24  tff(c_4055, plain, (![E_370]: (r2_orders_2('#skF_4', '#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), E_370) | ~r2_hidden(E_370, k2_struct_0('#skF_4')) | ~m1_subset_1(E_370, k2_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_2453])).
% 6.31/2.24  tff(c_4063, plain, (~m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_4055, c_22])).
% 6.31/2.24  tff(c_4074, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_601, c_2988, c_46, c_601, c_74, c_4063])).
% 6.31/2.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.31/2.24  
% 6.31/2.24  Inference rules
% 6.31/2.24  ----------------------
% 6.31/2.24  #Ref     : 0
% 6.31/2.24  #Sup     : 845
% 6.31/2.24  #Fact    : 0
% 6.31/2.24  #Define  : 0
% 6.31/2.24  #Split   : 9
% 6.31/2.24  #Chain   : 0
% 6.31/2.24  #Close   : 0
% 6.31/2.24  
% 6.31/2.24  Ordering : KBO
% 6.31/2.24  
% 6.31/2.24  Simplification rules
% 6.31/2.24  ----------------------
% 6.31/2.24  #Subsume      : 176
% 6.31/2.24  #Demod        : 1388
% 6.31/2.24  #Tautology    : 247
% 6.31/2.24  #SimpNegUnit  : 139
% 6.31/2.24  #BackRed      : 26
% 6.31/2.24  
% 6.31/2.24  #Partial instantiations: 0
% 6.31/2.24  #Strategies tried      : 1
% 6.31/2.24  
% 6.31/2.24  Timing (in seconds)
% 6.31/2.24  ----------------------
% 6.31/2.24  Preprocessing        : 0.34
% 6.31/2.24  Parsing              : 0.18
% 6.31/2.24  CNF conversion       : 0.02
% 6.31/2.24  Main loop            : 1.10
% 6.31/2.24  Inferencing          : 0.37
% 6.31/2.24  Reduction            : 0.36
% 6.31/2.24  Demodulation         : 0.25
% 6.31/2.24  BG Simplification    : 0.04
% 6.31/2.24  Subsumption          : 0.24
% 6.31/2.24  Abstraction          : 0.05
% 6.31/2.24  MUC search           : 0.00
% 6.31/2.24  Cooper               : 0.00
% 6.31/2.24  Total                : 1.49
% 6.31/2.24  Index Insertion      : 0.00
% 6.31/2.24  Index Deletion       : 0.00
% 6.31/2.24  Index Matching       : 0.00
% 6.31/2.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
