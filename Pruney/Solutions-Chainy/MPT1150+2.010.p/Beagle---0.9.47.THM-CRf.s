%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:25 EST 2020

% Result     : Theorem 14.26s
% Output     : CNFRefutation 14.45s
% Verified   : 
% Statistics : Number of formulae       :  148 (2154 expanded)
%              Number of leaves         :   40 ( 812 expanded)
%              Depth                    :   22
%              Number of atoms          :  397 (6634 expanded)
%              Number of equality atoms :   51 (1113 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_struct_0 > l1_orders_2 > k3_mcart_1 > k1_orders_2 > a_2_0_orders_2 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_4 > #skF_3 > #skF_1

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

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_162,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => k1_orders_2(A,k2_struct_0(A)) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_orders_2)).

tff(f_36,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_121,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_102,axiom,(
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

tff(f_117,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_orders_2(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_orders_2)).

tff(f_40,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_148,axiom,(
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

tff(f_51,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_67,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).

tff(f_86,axiom,(
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

tff(c_62,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_60,plain,(
    v3_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_58,plain,(
    v4_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_56,plain,(
    v5_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_54,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_10,plain,(
    ! [A_7] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_38,plain,(
    ! [A_42] :
      ( l1_struct_0(A_42)
      | ~ l1_orders_2(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_67,plain,(
    ! [A_61] :
      ( u1_struct_0(A_61) = k2_struct_0(A_61)
      | ~ l1_struct_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_77,plain,(
    ! [A_63] :
      ( u1_struct_0(A_63) = k2_struct_0(A_63)
      | ~ l1_orders_2(A_63) ) ),
    inference(resolution,[status(thm)],[c_38,c_67])).

tff(c_81,plain,(
    u1_struct_0('#skF_5') = k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_77])).

tff(c_561,plain,(
    ! [A_148,B_149] :
      ( k1_orders_2(A_148,B_149) = a_2_0_orders_2(A_148,B_149)
      | ~ m1_subset_1(B_149,k1_zfmisc_1(u1_struct_0(A_148)))
      | ~ l1_orders_2(A_148)
      | ~ v5_orders_2(A_148)
      | ~ v4_orders_2(A_148)
      | ~ v3_orders_2(A_148)
      | v2_struct_0(A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_576,plain,(
    ! [B_149] :
      ( k1_orders_2('#skF_5',B_149) = a_2_0_orders_2('#skF_5',B_149)
      | ~ m1_subset_1(B_149,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_561])).

tff(c_585,plain,(
    ! [B_149] :
      ( k1_orders_2('#skF_5',B_149) = a_2_0_orders_2('#skF_5',B_149)
      | ~ m1_subset_1(B_149,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_54,c_576])).

tff(c_588,plain,(
    ! [B_150] :
      ( k1_orders_2('#skF_5',B_150) = a_2_0_orders_2('#skF_5',B_150)
      | ~ m1_subset_1(B_150,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_585])).

tff(c_608,plain,(
    k1_orders_2('#skF_5',k1_xboole_0) = a_2_0_orders_2('#skF_5',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10,c_588])).

tff(c_673,plain,(
    ! [A_154,B_155] :
      ( m1_subset_1(k1_orders_2(A_154,B_155),k1_zfmisc_1(u1_struct_0(A_154)))
      | ~ m1_subset_1(B_155,k1_zfmisc_1(u1_struct_0(A_154)))
      | ~ l1_orders_2(A_154)
      | ~ v5_orders_2(A_154)
      | ~ v4_orders_2(A_154)
      | ~ v3_orders_2(A_154)
      | v2_struct_0(A_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_687,plain,
    ( m1_subset_1(a_2_0_orders_2('#skF_5',k1_xboole_0),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_608,c_673])).

tff(c_698,plain,
    ( m1_subset_1(a_2_0_orders_2('#skF_5',k1_xboole_0),k1_zfmisc_1(k2_struct_0('#skF_5')))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_54,c_10,c_81,c_687])).

tff(c_699,plain,(
    m1_subset_1(a_2_0_orders_2('#skF_5',k1_xboole_0),k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_698])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(A_8,B_9)
      | ~ m1_subset_1(A_8,k1_zfmisc_1(B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_713,plain,(
    r1_tarski(a_2_0_orders_2('#skF_5',k1_xboole_0),k2_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_699,c_12])).

tff(c_105,plain,(
    ! [A_71,B_72] :
      ( r2_hidden('#skF_1'(A_71,B_72),A_71)
      | r1_tarski(A_71,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_113,plain,(
    ! [A_71] : r1_tarski(A_71,A_71) ),
    inference(resolution,[status(thm)],[c_105,c_4])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_613,plain,(
    ! [A_151] :
      ( k1_orders_2('#skF_5',A_151) = a_2_0_orders_2('#skF_5',A_151)
      | ~ r1_tarski(A_151,k2_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_14,c_588])).

tff(c_632,plain,(
    k1_orders_2('#skF_5',k2_struct_0('#skF_5')) = a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_113,c_613])).

tff(c_52,plain,(
    k1_orders_2('#skF_5',k2_struct_0('#skF_5')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_635,plain,(
    a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_632,c_52])).

tff(c_684,plain,
    ( m1_subset_1(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_632,c_673])).

tff(c_695,plain,
    ( m1_subset_1(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')),k1_zfmisc_1(k2_struct_0('#skF_5')))
    | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5')))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_54,c_81,c_81,c_684])).

tff(c_696,plain,
    ( m1_subset_1(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')),k1_zfmisc_1(k2_struct_0('#skF_5')))
    | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_695])).

tff(c_823,plain,(
    ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_696])).

tff(c_826,plain,(
    ~ r1_tarski(k2_struct_0('#skF_5'),k2_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_14,c_823])).

tff(c_830,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_826])).

tff(c_831,plain,(
    m1_subset_1(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')),k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_696])).

tff(c_856,plain,(
    r1_tarski(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')),k2_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_831,c_12])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_832,plain,(
    m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_696])).

tff(c_16,plain,(
    ! [A_10,C_12,B_11] :
      ( m1_subset_1(A_10,C_12)
      | ~ m1_subset_1(B_11,k1_zfmisc_1(C_12))
      | ~ r2_hidden(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_869,plain,(
    ! [A_161] :
      ( m1_subset_1(A_161,k2_struct_0('#skF_5'))
      | ~ r2_hidden(A_161,k2_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_832,c_16])).

tff(c_888,plain,(
    ! [B_2] :
      ( m1_subset_1('#skF_1'(k2_struct_0('#skF_5'),B_2),k2_struct_0('#skF_5'))
      | r1_tarski(k2_struct_0('#skF_5'),B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_869])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2280,plain,(
    ! [D_272,B_273,C_274] :
      ( r2_hidden('#skF_4'(D_272,B_273,C_274,D_272),C_274)
      | r2_hidden(D_272,a_2_0_orders_2(B_273,C_274))
      | ~ m1_subset_1(D_272,u1_struct_0(B_273))
      | ~ m1_subset_1(C_274,k1_zfmisc_1(u1_struct_0(B_273)))
      | ~ l1_orders_2(B_273)
      | ~ v5_orders_2(B_273)
      | ~ v4_orders_2(B_273)
      | ~ v3_orders_2(B_273)
      | v2_struct_0(B_273) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_2293,plain,(
    ! [D_272,C_274] :
      ( r2_hidden('#skF_4'(D_272,'#skF_5',C_274,D_272),C_274)
      | r2_hidden(D_272,a_2_0_orders_2('#skF_5',C_274))
      | ~ m1_subset_1(D_272,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(C_274,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_2280])).

tff(c_2302,plain,(
    ! [D_272,C_274] :
      ( r2_hidden('#skF_4'(D_272,'#skF_5',C_274,D_272),C_274)
      | r2_hidden(D_272,a_2_0_orders_2('#skF_5',C_274))
      | ~ m1_subset_1(D_272,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(C_274,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_54,c_81,c_2293])).

tff(c_2308,plain,(
    ! [D_275,C_276] :
      ( r2_hidden('#skF_4'(D_275,'#skF_5',C_276,D_275),C_276)
      | r2_hidden(D_275,a_2_0_orders_2('#skF_5',C_276))
      | ~ m1_subset_1(D_275,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(C_276,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_2302])).

tff(c_20030,plain,(
    ! [D_865] :
      ( r2_hidden('#skF_4'(D_865,'#skF_5',k1_xboole_0,D_865),k1_xboole_0)
      | r2_hidden(D_865,a_2_0_orders_2('#skF_5',k1_xboole_0))
      | ~ m1_subset_1(D_865,k2_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_10,c_2308])).

tff(c_18,plain,(
    ! [B_14,A_13] :
      ( ~ r1_tarski(B_14,A_13)
      | ~ r2_hidden(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_20046,plain,(
    ! [D_865] :
      ( ~ r1_tarski(k1_xboole_0,'#skF_4'(D_865,'#skF_5',k1_xboole_0,D_865))
      | r2_hidden(D_865,a_2_0_orders_2('#skF_5',k1_xboole_0))
      | ~ m1_subset_1(D_865,k2_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_20030,c_18])).

tff(c_20064,plain,(
    ! [D_866] :
      ( r2_hidden(D_866,a_2_0_orders_2('#skF_5',k1_xboole_0))
      | ~ m1_subset_1(D_866,k2_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_20046])).

tff(c_21035,plain,(
    ! [A_903] :
      ( r1_tarski(A_903,a_2_0_orders_2('#skF_5',k1_xboole_0))
      | ~ m1_subset_1('#skF_1'(A_903,a_2_0_orders_2('#skF_5',k1_xboole_0)),k2_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_20064,c_4])).

tff(c_21080,plain,(
    r1_tarski(k2_struct_0('#skF_5'),a_2_0_orders_2('#skF_5',k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_888,c_21035])).

tff(c_20,plain,(
    ! [A_15] :
      ( r2_hidden('#skF_2'(A_15),A_15)
      | k1_xboole_0 = A_15 ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_115,plain,(
    ! [C_73,B_74,A_75] :
      ( r2_hidden(C_73,B_74)
      | ~ r2_hidden(C_73,A_75)
      | ~ r1_tarski(A_75,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_130,plain,(
    ! [A_79,B_80] :
      ( r2_hidden('#skF_2'(A_79),B_80)
      | ~ r1_tarski(A_79,B_80)
      | k1_xboole_0 = A_79 ) ),
    inference(resolution,[status(thm)],[c_20,c_115])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_136,plain,(
    ! [A_79,B_2,B_80] :
      ( r2_hidden('#skF_2'(A_79),B_2)
      | ~ r1_tarski(B_80,B_2)
      | ~ r1_tarski(A_79,B_80)
      | k1_xboole_0 = A_79 ) ),
    inference(resolution,[status(thm)],[c_130,c_2])).

tff(c_21140,plain,(
    ! [A_79] :
      ( r2_hidden('#skF_2'(A_79),a_2_0_orders_2('#skF_5',k1_xboole_0))
      | ~ r1_tarski(A_79,k2_struct_0('#skF_5'))
      | k1_xboole_0 = A_79 ) ),
    inference(resolution,[status(thm)],[c_21080,c_136])).

tff(c_933,plain,(
    ! [A_167] :
      ( m1_subset_1(A_167,k2_struct_0('#skF_5'))
      | ~ r2_hidden(A_167,a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_831,c_16])).

tff(c_949,plain,
    ( m1_subset_1('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),k2_struct_0('#skF_5'))
    | a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_933])).

tff(c_955,plain,(
    m1_subset_1('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),k2_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_635,c_949])).

tff(c_163,plain,(
    ! [A_86,C_87,B_88] :
      ( m1_subset_1(A_86,C_87)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(C_87))
      | ~ r2_hidden(A_86,B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_185,plain,(
    ! [A_91,B_92,A_93] :
      ( m1_subset_1(A_91,B_92)
      | ~ r2_hidden(A_91,A_93)
      | ~ r1_tarski(A_93,B_92) ) ),
    inference(resolution,[status(thm)],[c_14,c_163])).

tff(c_194,plain,(
    ! [A_15,B_92] :
      ( m1_subset_1('#skF_2'(A_15),B_92)
      | ~ r1_tarski(A_15,B_92)
      | k1_xboole_0 = A_15 ) ),
    inference(resolution,[status(thm)],[c_20,c_185])).

tff(c_48,plain,(
    ! [A_43,B_44,C_45] :
      ( '#skF_3'(A_43,B_44,C_45) = A_43
      | ~ r2_hidden(A_43,a_2_0_orders_2(B_44,C_45))
      | ~ m1_subset_1(C_45,k1_zfmisc_1(u1_struct_0(B_44)))
      | ~ l1_orders_2(B_44)
      | ~ v5_orders_2(B_44)
      | ~ v4_orders_2(B_44)
      | ~ v3_orders_2(B_44)
      | v2_struct_0(B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_20066,plain,(
    ! [D_866] :
      ( '#skF_3'(D_866,'#skF_5',k1_xboole_0) = D_866
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ m1_subset_1(D_866,k2_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_20064,c_48])).

tff(c_20090,plain,(
    ! [D_866] :
      ( '#skF_3'(D_866,'#skF_5',k1_xboole_0) = D_866
      | v2_struct_0('#skF_5')
      | ~ m1_subset_1(D_866,k2_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_54,c_10,c_81,c_20066])).

tff(c_20104,plain,(
    ! [D_867] :
      ( '#skF_3'(D_867,'#skF_5',k1_xboole_0) = D_867
      | ~ m1_subset_1(D_867,k2_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_20090])).

tff(c_21424,plain,(
    ! [A_912] :
      ( '#skF_3'('#skF_2'(A_912),'#skF_5',k1_xboole_0) = '#skF_2'(A_912)
      | ~ r1_tarski(A_912,k2_struct_0('#skF_5'))
      | k1_xboole_0 = A_912 ) ),
    inference(resolution,[status(thm)],[c_194,c_20104])).

tff(c_21495,plain,
    ( '#skF_3'('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),'#skF_5',k1_xboole_0) = '#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')))
    | a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_856,c_21424])).

tff(c_21539,plain,(
    '#skF_3'('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),'#skF_5',k1_xboole_0) = '#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_635,c_21495])).

tff(c_2708,plain,(
    ! [B_314,E_315,A_316,C_317] :
      ( r2_orders_2(B_314,E_315,'#skF_3'(A_316,B_314,C_317))
      | ~ r2_hidden(E_315,C_317)
      | ~ m1_subset_1(E_315,u1_struct_0(B_314))
      | ~ r2_hidden(A_316,a_2_0_orders_2(B_314,C_317))
      | ~ m1_subset_1(C_317,k1_zfmisc_1(u1_struct_0(B_314)))
      | ~ l1_orders_2(B_314)
      | ~ v5_orders_2(B_314)
      | ~ v4_orders_2(B_314)
      | ~ v3_orders_2(B_314)
      | v2_struct_0(B_314) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_4600,plain,(
    ! [B_410,E_411,A_412] :
      ( r2_orders_2(B_410,E_411,'#skF_3'(A_412,B_410,k1_xboole_0))
      | ~ r2_hidden(E_411,k1_xboole_0)
      | ~ m1_subset_1(E_411,u1_struct_0(B_410))
      | ~ r2_hidden(A_412,a_2_0_orders_2(B_410,k1_xboole_0))
      | ~ l1_orders_2(B_410)
      | ~ v5_orders_2(B_410)
      | ~ v4_orders_2(B_410)
      | ~ v3_orders_2(B_410)
      | v2_struct_0(B_410) ) ),
    inference(resolution,[status(thm)],[c_10,c_2708])).

tff(c_30,plain,(
    ! [A_30,C_36] :
      ( ~ r2_orders_2(A_30,C_36,C_36)
      | ~ m1_subset_1(C_36,u1_struct_0(A_30))
      | ~ l1_orders_2(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_22863,plain,(
    ! [A_941,B_942] :
      ( ~ r2_hidden('#skF_3'(A_941,B_942,k1_xboole_0),k1_xboole_0)
      | ~ m1_subset_1('#skF_3'(A_941,B_942,k1_xboole_0),u1_struct_0(B_942))
      | ~ r2_hidden(A_941,a_2_0_orders_2(B_942,k1_xboole_0))
      | ~ l1_orders_2(B_942)
      | ~ v5_orders_2(B_942)
      | ~ v4_orders_2(B_942)
      | ~ v3_orders_2(B_942)
      | v2_struct_0(B_942) ) ),
    inference(resolution,[status(thm)],[c_4600,c_30])).

tff(c_22866,plain,
    ( ~ r2_hidden('#skF_3'('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),'#skF_5',k1_xboole_0),k1_xboole_0)
    | ~ m1_subset_1('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),u1_struct_0('#skF_5'))
    | ~ r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),a_2_0_orders_2('#skF_5',k1_xboole_0))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_21539,c_22863])).

tff(c_22890,plain,
    ( ~ r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),k1_xboole_0)
    | ~ r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),a_2_0_orders_2('#skF_5',k1_xboole_0))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_54,c_955,c_81,c_21539,c_22866])).

tff(c_22891,plain,
    ( ~ r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),k1_xboole_0)
    | ~ r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),a_2_0_orders_2('#skF_5',k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_22890])).

tff(c_23002,plain,(
    ~ r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),a_2_0_orders_2('#skF_5',k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_22891])).

tff(c_23012,plain,
    ( ~ r1_tarski(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')),k2_struct_0('#skF_5'))
    | a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_21140,c_23002])).

tff(c_23030,plain,(
    a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_856,c_23012])).

tff(c_23032,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_635,c_23030])).

tff(c_23034,plain,(
    r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),a_2_0_orders_2('#skF_5',k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_22891])).

tff(c_23091,plain,(
    ! [B_2] :
      ( r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),B_2)
      | ~ r1_tarski(a_2_0_orders_2('#skF_5',k1_xboole_0),B_2) ) ),
    inference(resolution,[status(thm)],[c_23034,c_2])).

tff(c_121,plain,(
    ! [A_15,B_74] :
      ( r2_hidden('#skF_2'(A_15),B_74)
      | ~ r1_tarski(A_15,B_74)
      | k1_xboole_0 = A_15 ) ),
    inference(resolution,[status(thm)],[c_20,c_115])).

tff(c_793,plain,(
    ! [A_158,B_159,C_160] :
      ( '#skF_3'(A_158,B_159,C_160) = A_158
      | ~ r2_hidden(A_158,a_2_0_orders_2(B_159,C_160))
      | ~ m1_subset_1(C_160,k1_zfmisc_1(u1_struct_0(B_159)))
      | ~ l1_orders_2(B_159)
      | ~ v5_orders_2(B_159)
      | ~ v4_orders_2(B_159)
      | ~ v3_orders_2(B_159)
      | v2_struct_0(B_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_5487,plain,(
    ! [B_447,C_448] :
      ( '#skF_3'('#skF_2'(a_2_0_orders_2(B_447,C_448)),B_447,C_448) = '#skF_2'(a_2_0_orders_2(B_447,C_448))
      | ~ m1_subset_1(C_448,k1_zfmisc_1(u1_struct_0(B_447)))
      | ~ l1_orders_2(B_447)
      | ~ v5_orders_2(B_447)
      | ~ v4_orders_2(B_447)
      | ~ v3_orders_2(B_447)
      | v2_struct_0(B_447)
      | a_2_0_orders_2(B_447,C_448) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_20,c_793])).

tff(c_5503,plain,(
    ! [C_448] :
      ( '#skF_3'('#skF_2'(a_2_0_orders_2('#skF_5',C_448)),'#skF_5',C_448) = '#skF_2'(a_2_0_orders_2('#skF_5',C_448))
      | ~ m1_subset_1(C_448,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5')
      | a_2_0_orders_2('#skF_5',C_448) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_5487])).

tff(c_5513,plain,(
    ! [C_448] :
      ( '#skF_3'('#skF_2'(a_2_0_orders_2('#skF_5',C_448)),'#skF_5',C_448) = '#skF_2'(a_2_0_orders_2('#skF_5',C_448))
      | ~ m1_subset_1(C_448,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | v2_struct_0('#skF_5')
      | a_2_0_orders_2('#skF_5',C_448) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_54,c_5503])).

tff(c_5638,plain,(
    ! [C_453] :
      ( '#skF_3'('#skF_2'(a_2_0_orders_2('#skF_5',C_453)),'#skF_5',C_453) = '#skF_2'(a_2_0_orders_2('#skF_5',C_453))
      | ~ m1_subset_1(C_453,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | a_2_0_orders_2('#skF_5',C_453) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_5513])).

tff(c_5651,plain,
    ( '#skF_3'('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),'#skF_5',k2_struct_0('#skF_5')) = '#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')))
    | a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_832,c_5638])).

tff(c_5677,plain,(
    '#skF_3'('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),'#skF_5',k2_struct_0('#skF_5')) = '#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_635,c_5651])).

tff(c_5824,plain,(
    ! [B_458,E_459,A_460,A_461] :
      ( r2_orders_2(B_458,E_459,'#skF_3'(A_460,B_458,A_461))
      | ~ r2_hidden(E_459,A_461)
      | ~ m1_subset_1(E_459,u1_struct_0(B_458))
      | ~ r2_hidden(A_460,a_2_0_orders_2(B_458,A_461))
      | ~ l1_orders_2(B_458)
      | ~ v5_orders_2(B_458)
      | ~ v4_orders_2(B_458)
      | ~ v3_orders_2(B_458)
      | v2_struct_0(B_458)
      | ~ r1_tarski(A_461,u1_struct_0(B_458)) ) ),
    inference(resolution,[status(thm)],[c_14,c_2708])).

tff(c_5835,plain,(
    ! [E_459] :
      ( r2_orders_2('#skF_5',E_459,'#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))))
      | ~ r2_hidden(E_459,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(E_459,u1_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r1_tarski(k2_struct_0('#skF_5'),u1_struct_0('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5677,c_5824])).

tff(c_5843,plain,(
    ! [E_459] :
      ( r2_orders_2('#skF_5',E_459,'#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))))
      | ~ r2_hidden(E_459,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(E_459,k2_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_81,c_60,c_58,c_56,c_54,c_81,c_5835])).

tff(c_5844,plain,(
    ! [E_459] :
      ( r2_orders_2('#skF_5',E_459,'#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))))
      | ~ r2_hidden(E_459,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(E_459,k2_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_5843])).

tff(c_17551,plain,(
    ~ r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_5844])).

tff(c_17557,plain,
    ( ~ r1_tarski(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')),a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')))
    | a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_121,c_17551])).

tff(c_17566,plain,(
    a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_17557])).

tff(c_17568,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_635,c_17566])).

tff(c_17570,plain,(
    r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_5844])).

tff(c_26120,plain,(
    ! [A_1010,B_1011,A_1012] :
      ( ~ r2_hidden('#skF_3'(A_1010,B_1011,A_1012),A_1012)
      | ~ m1_subset_1('#skF_3'(A_1010,B_1011,A_1012),u1_struct_0(B_1011))
      | ~ r2_hidden(A_1010,a_2_0_orders_2(B_1011,A_1012))
      | ~ l1_orders_2(B_1011)
      | ~ v5_orders_2(B_1011)
      | ~ v4_orders_2(B_1011)
      | ~ v3_orders_2(B_1011)
      | v2_struct_0(B_1011)
      | ~ r1_tarski(A_1012,u1_struct_0(B_1011)) ) ),
    inference(resolution,[status(thm)],[c_5824,c_30])).

tff(c_26152,plain,
    ( ~ r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),k2_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_3'('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),'#skF_5',k2_struct_0('#skF_5')),u1_struct_0('#skF_5'))
    | ~ r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ r1_tarski(k2_struct_0('#skF_5'),u1_struct_0('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5677,c_26120])).

tff(c_26184,plain,
    ( ~ r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),k2_struct_0('#skF_5'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_81,c_60,c_58,c_56,c_54,c_17570,c_955,c_81,c_5677,c_26152])).

tff(c_26185,plain,(
    ~ r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),k2_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_26184])).

tff(c_26191,plain,(
    ~ r1_tarski(a_2_0_orders_2('#skF_5',k1_xboole_0),k2_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_23091,c_26185])).

tff(c_26216,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_713,c_26191])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:16:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.26/6.05  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.26/6.06  
% 14.26/6.06  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.26/6.06  %$ r2_orders_2 > r1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_struct_0 > l1_orders_2 > k3_mcart_1 > k1_orders_2 > a_2_0_orders_2 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_4 > #skF_3 > #skF_1
% 14.26/6.06  
% 14.26/6.06  %Foreground sorts:
% 14.26/6.06  
% 14.26/6.06  
% 14.26/6.06  %Background operators:
% 14.26/6.06  
% 14.26/6.06  
% 14.26/6.06  %Foreground operators:
% 14.26/6.06  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 14.26/6.06  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 14.26/6.06  tff(k1_orders_2, type, k1_orders_2: ($i * $i) > $i).
% 14.26/6.06  tff('#skF_2', type, '#skF_2': $i > $i).
% 14.26/6.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.26/6.06  tff(a_2_0_orders_2, type, a_2_0_orders_2: ($i * $i) > $i).
% 14.26/6.06  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 14.26/6.06  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 14.26/6.06  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 14.26/6.06  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 14.26/6.06  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.26/6.06  tff('#skF_5', type, '#skF_5': $i).
% 14.26/6.06  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 14.26/6.06  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 14.26/6.06  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 14.26/6.06  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 14.26/6.06  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 14.26/6.06  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 14.26/6.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.26/6.06  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 14.26/6.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.26/6.06  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 14.26/6.06  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 14.26/6.06  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 14.26/6.06  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 14.26/6.06  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 14.26/6.06  
% 14.45/6.08  tff(f_162, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (k1_orders_2(A, k2_struct_0(A)) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_orders_2)).
% 14.45/6.08  tff(f_36, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 14.45/6.08  tff(f_121, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 14.45/6.08  tff(f_71, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 14.45/6.08  tff(f_102, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_orders_2(A, B) = a_2_0_orders_2(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_orders_2)).
% 14.45/6.08  tff(f_117, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_orders_2(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_orders_2)).
% 14.45/6.08  tff(f_40, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 14.45/6.08  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 14.45/6.08  tff(f_46, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 14.45/6.08  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 14.45/6.08  tff(f_148, axiom, (![A, B, C]: ((((((~v2_struct_0(B) & v3_orders_2(B)) & v4_orders_2(B)) & v5_orders_2(B)) & l1_orders_2(B)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B)))) => (r2_hidden(A, a_2_0_orders_2(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r2_hidden(E, C) => r2_orders_2(B, E, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fraenkel_a_2_0_orders_2)).
% 14.45/6.08  tff(f_51, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 14.45/6.08  tff(f_67, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_mcart_1)).
% 14.45/6.08  tff(f_86, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_orders_2(A, B, C) <=> (r1_orders_2(A, B, C) & ~(B = C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_orders_2)).
% 14.45/6.08  tff(c_62, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_162])).
% 14.45/6.08  tff(c_60, plain, (v3_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_162])).
% 14.45/6.08  tff(c_58, plain, (v4_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_162])).
% 14.45/6.08  tff(c_56, plain, (v5_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_162])).
% 14.45/6.08  tff(c_54, plain, (l1_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_162])).
% 14.45/6.08  tff(c_10, plain, (![A_7]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 14.45/6.08  tff(c_38, plain, (![A_42]: (l1_struct_0(A_42) | ~l1_orders_2(A_42))), inference(cnfTransformation, [status(thm)], [f_121])).
% 14.45/6.08  tff(c_67, plain, (![A_61]: (u1_struct_0(A_61)=k2_struct_0(A_61) | ~l1_struct_0(A_61))), inference(cnfTransformation, [status(thm)], [f_71])).
% 14.45/6.08  tff(c_77, plain, (![A_63]: (u1_struct_0(A_63)=k2_struct_0(A_63) | ~l1_orders_2(A_63))), inference(resolution, [status(thm)], [c_38, c_67])).
% 14.45/6.08  tff(c_81, plain, (u1_struct_0('#skF_5')=k2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_54, c_77])).
% 14.45/6.08  tff(c_561, plain, (![A_148, B_149]: (k1_orders_2(A_148, B_149)=a_2_0_orders_2(A_148, B_149) | ~m1_subset_1(B_149, k1_zfmisc_1(u1_struct_0(A_148))) | ~l1_orders_2(A_148) | ~v5_orders_2(A_148) | ~v4_orders_2(A_148) | ~v3_orders_2(A_148) | v2_struct_0(A_148))), inference(cnfTransformation, [status(thm)], [f_102])).
% 14.45/6.08  tff(c_576, plain, (![B_149]: (k1_orders_2('#skF_5', B_149)=a_2_0_orders_2('#skF_5', B_149) | ~m1_subset_1(B_149, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_81, c_561])).
% 14.45/6.08  tff(c_585, plain, (![B_149]: (k1_orders_2('#skF_5', B_149)=a_2_0_orders_2('#skF_5', B_149) | ~m1_subset_1(B_149, k1_zfmisc_1(k2_struct_0('#skF_5'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_54, c_576])).
% 14.45/6.08  tff(c_588, plain, (![B_150]: (k1_orders_2('#skF_5', B_150)=a_2_0_orders_2('#skF_5', B_150) | ~m1_subset_1(B_150, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_62, c_585])).
% 14.45/6.08  tff(c_608, plain, (k1_orders_2('#skF_5', k1_xboole_0)=a_2_0_orders_2('#skF_5', k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_588])).
% 14.45/6.08  tff(c_673, plain, (![A_154, B_155]: (m1_subset_1(k1_orders_2(A_154, B_155), k1_zfmisc_1(u1_struct_0(A_154))) | ~m1_subset_1(B_155, k1_zfmisc_1(u1_struct_0(A_154))) | ~l1_orders_2(A_154) | ~v5_orders_2(A_154) | ~v4_orders_2(A_154) | ~v3_orders_2(A_154) | v2_struct_0(A_154))), inference(cnfTransformation, [status(thm)], [f_117])).
% 14.45/6.08  tff(c_687, plain, (m1_subset_1(a_2_0_orders_2('#skF_5', k1_xboole_0), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_608, c_673])).
% 14.45/6.08  tff(c_698, plain, (m1_subset_1(a_2_0_orders_2('#skF_5', k1_xboole_0), k1_zfmisc_1(k2_struct_0('#skF_5'))) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_54, c_10, c_81, c_687])).
% 14.45/6.08  tff(c_699, plain, (m1_subset_1(a_2_0_orders_2('#skF_5', k1_xboole_0), k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_62, c_698])).
% 14.45/6.08  tff(c_12, plain, (![A_8, B_9]: (r1_tarski(A_8, B_9) | ~m1_subset_1(A_8, k1_zfmisc_1(B_9)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 14.45/6.08  tff(c_713, plain, (r1_tarski(a_2_0_orders_2('#skF_5', k1_xboole_0), k2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_699, c_12])).
% 14.45/6.08  tff(c_105, plain, (![A_71, B_72]: (r2_hidden('#skF_1'(A_71, B_72), A_71) | r1_tarski(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_32])).
% 14.45/6.08  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 14.45/6.08  tff(c_113, plain, (![A_71]: (r1_tarski(A_71, A_71))), inference(resolution, [status(thm)], [c_105, c_4])).
% 14.45/6.08  tff(c_14, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_40])).
% 14.45/6.08  tff(c_613, plain, (![A_151]: (k1_orders_2('#skF_5', A_151)=a_2_0_orders_2('#skF_5', A_151) | ~r1_tarski(A_151, k2_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_14, c_588])).
% 14.45/6.08  tff(c_632, plain, (k1_orders_2('#skF_5', k2_struct_0('#skF_5'))=a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_113, c_613])).
% 14.45/6.08  tff(c_52, plain, (k1_orders_2('#skF_5', k2_struct_0('#skF_5'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_162])).
% 14.45/6.08  tff(c_635, plain, (a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_632, c_52])).
% 14.45/6.08  tff(c_684, plain, (m1_subset_1(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5')), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_632, c_673])).
% 14.45/6.08  tff(c_695, plain, (m1_subset_1(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5')), k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_5'))) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_54, c_81, c_81, c_684])).
% 14.45/6.08  tff(c_696, plain, (m1_subset_1(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5')), k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_62, c_695])).
% 14.45/6.08  tff(c_823, plain, (~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(splitLeft, [status(thm)], [c_696])).
% 14.45/6.08  tff(c_826, plain, (~r1_tarski(k2_struct_0('#skF_5'), k2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_14, c_823])).
% 14.45/6.08  tff(c_830, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_113, c_826])).
% 14.45/6.08  tff(c_831, plain, (m1_subset_1(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5')), k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_696])).
% 14.45/6.08  tff(c_856, plain, (r1_tarski(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5')), k2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_831, c_12])).
% 14.45/6.08  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 14.45/6.08  tff(c_832, plain, (m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_696])).
% 14.45/6.08  tff(c_16, plain, (![A_10, C_12, B_11]: (m1_subset_1(A_10, C_12) | ~m1_subset_1(B_11, k1_zfmisc_1(C_12)) | ~r2_hidden(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_46])).
% 14.45/6.08  tff(c_869, plain, (![A_161]: (m1_subset_1(A_161, k2_struct_0('#skF_5')) | ~r2_hidden(A_161, k2_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_832, c_16])).
% 14.45/6.08  tff(c_888, plain, (![B_2]: (m1_subset_1('#skF_1'(k2_struct_0('#skF_5'), B_2), k2_struct_0('#skF_5')) | r1_tarski(k2_struct_0('#skF_5'), B_2))), inference(resolution, [status(thm)], [c_6, c_869])).
% 14.45/6.08  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 14.45/6.08  tff(c_2280, plain, (![D_272, B_273, C_274]: (r2_hidden('#skF_4'(D_272, B_273, C_274, D_272), C_274) | r2_hidden(D_272, a_2_0_orders_2(B_273, C_274)) | ~m1_subset_1(D_272, u1_struct_0(B_273)) | ~m1_subset_1(C_274, k1_zfmisc_1(u1_struct_0(B_273))) | ~l1_orders_2(B_273) | ~v5_orders_2(B_273) | ~v4_orders_2(B_273) | ~v3_orders_2(B_273) | v2_struct_0(B_273))), inference(cnfTransformation, [status(thm)], [f_148])).
% 14.45/6.08  tff(c_2293, plain, (![D_272, C_274]: (r2_hidden('#skF_4'(D_272, '#skF_5', C_274, D_272), C_274) | r2_hidden(D_272, a_2_0_orders_2('#skF_5', C_274)) | ~m1_subset_1(D_272, u1_struct_0('#skF_5')) | ~m1_subset_1(C_274, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_81, c_2280])).
% 14.45/6.08  tff(c_2302, plain, (![D_272, C_274]: (r2_hidden('#skF_4'(D_272, '#skF_5', C_274, D_272), C_274) | r2_hidden(D_272, a_2_0_orders_2('#skF_5', C_274)) | ~m1_subset_1(D_272, k2_struct_0('#skF_5')) | ~m1_subset_1(C_274, k1_zfmisc_1(k2_struct_0('#skF_5'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_54, c_81, c_2293])).
% 14.45/6.08  tff(c_2308, plain, (![D_275, C_276]: (r2_hidden('#skF_4'(D_275, '#skF_5', C_276, D_275), C_276) | r2_hidden(D_275, a_2_0_orders_2('#skF_5', C_276)) | ~m1_subset_1(D_275, k2_struct_0('#skF_5')) | ~m1_subset_1(C_276, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_62, c_2302])).
% 14.45/6.08  tff(c_20030, plain, (![D_865]: (r2_hidden('#skF_4'(D_865, '#skF_5', k1_xboole_0, D_865), k1_xboole_0) | r2_hidden(D_865, a_2_0_orders_2('#skF_5', k1_xboole_0)) | ~m1_subset_1(D_865, k2_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_10, c_2308])).
% 14.45/6.08  tff(c_18, plain, (![B_14, A_13]: (~r1_tarski(B_14, A_13) | ~r2_hidden(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_51])).
% 14.45/6.08  tff(c_20046, plain, (![D_865]: (~r1_tarski(k1_xboole_0, '#skF_4'(D_865, '#skF_5', k1_xboole_0, D_865)) | r2_hidden(D_865, a_2_0_orders_2('#skF_5', k1_xboole_0)) | ~m1_subset_1(D_865, k2_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_20030, c_18])).
% 14.45/6.08  tff(c_20064, plain, (![D_866]: (r2_hidden(D_866, a_2_0_orders_2('#skF_5', k1_xboole_0)) | ~m1_subset_1(D_866, k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_20046])).
% 14.45/6.08  tff(c_21035, plain, (![A_903]: (r1_tarski(A_903, a_2_0_orders_2('#skF_5', k1_xboole_0)) | ~m1_subset_1('#skF_1'(A_903, a_2_0_orders_2('#skF_5', k1_xboole_0)), k2_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_20064, c_4])).
% 14.45/6.08  tff(c_21080, plain, (r1_tarski(k2_struct_0('#skF_5'), a_2_0_orders_2('#skF_5', k1_xboole_0))), inference(resolution, [status(thm)], [c_888, c_21035])).
% 14.45/6.08  tff(c_20, plain, (![A_15]: (r2_hidden('#skF_2'(A_15), A_15) | k1_xboole_0=A_15)), inference(cnfTransformation, [status(thm)], [f_67])).
% 14.45/6.08  tff(c_115, plain, (![C_73, B_74, A_75]: (r2_hidden(C_73, B_74) | ~r2_hidden(C_73, A_75) | ~r1_tarski(A_75, B_74))), inference(cnfTransformation, [status(thm)], [f_32])).
% 14.45/6.08  tff(c_130, plain, (![A_79, B_80]: (r2_hidden('#skF_2'(A_79), B_80) | ~r1_tarski(A_79, B_80) | k1_xboole_0=A_79)), inference(resolution, [status(thm)], [c_20, c_115])).
% 14.45/6.08  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 14.45/6.08  tff(c_136, plain, (![A_79, B_2, B_80]: (r2_hidden('#skF_2'(A_79), B_2) | ~r1_tarski(B_80, B_2) | ~r1_tarski(A_79, B_80) | k1_xboole_0=A_79)), inference(resolution, [status(thm)], [c_130, c_2])).
% 14.45/6.08  tff(c_21140, plain, (![A_79]: (r2_hidden('#skF_2'(A_79), a_2_0_orders_2('#skF_5', k1_xboole_0)) | ~r1_tarski(A_79, k2_struct_0('#skF_5')) | k1_xboole_0=A_79)), inference(resolution, [status(thm)], [c_21080, c_136])).
% 14.45/6.08  tff(c_933, plain, (![A_167]: (m1_subset_1(A_167, k2_struct_0('#skF_5')) | ~r2_hidden(A_167, a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_831, c_16])).
% 14.45/6.08  tff(c_949, plain, (m1_subset_1('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), k2_struct_0('#skF_5')) | a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))=k1_xboole_0), inference(resolution, [status(thm)], [c_20, c_933])).
% 14.45/6.08  tff(c_955, plain, (m1_subset_1('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), k2_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_635, c_949])).
% 14.45/6.08  tff(c_163, plain, (![A_86, C_87, B_88]: (m1_subset_1(A_86, C_87) | ~m1_subset_1(B_88, k1_zfmisc_1(C_87)) | ~r2_hidden(A_86, B_88))), inference(cnfTransformation, [status(thm)], [f_46])).
% 14.45/6.08  tff(c_185, plain, (![A_91, B_92, A_93]: (m1_subset_1(A_91, B_92) | ~r2_hidden(A_91, A_93) | ~r1_tarski(A_93, B_92))), inference(resolution, [status(thm)], [c_14, c_163])).
% 14.45/6.08  tff(c_194, plain, (![A_15, B_92]: (m1_subset_1('#skF_2'(A_15), B_92) | ~r1_tarski(A_15, B_92) | k1_xboole_0=A_15)), inference(resolution, [status(thm)], [c_20, c_185])).
% 14.45/6.08  tff(c_48, plain, (![A_43, B_44, C_45]: ('#skF_3'(A_43, B_44, C_45)=A_43 | ~r2_hidden(A_43, a_2_0_orders_2(B_44, C_45)) | ~m1_subset_1(C_45, k1_zfmisc_1(u1_struct_0(B_44))) | ~l1_orders_2(B_44) | ~v5_orders_2(B_44) | ~v4_orders_2(B_44) | ~v3_orders_2(B_44) | v2_struct_0(B_44))), inference(cnfTransformation, [status(thm)], [f_148])).
% 14.45/6.08  tff(c_20066, plain, (![D_866]: ('#skF_3'(D_866, '#skF_5', k1_xboole_0)=D_866 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5') | ~m1_subset_1(D_866, k2_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_20064, c_48])).
% 14.45/6.08  tff(c_20090, plain, (![D_866]: ('#skF_3'(D_866, '#skF_5', k1_xboole_0)=D_866 | v2_struct_0('#skF_5') | ~m1_subset_1(D_866, k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_54, c_10, c_81, c_20066])).
% 14.45/6.08  tff(c_20104, plain, (![D_867]: ('#skF_3'(D_867, '#skF_5', k1_xboole_0)=D_867 | ~m1_subset_1(D_867, k2_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_62, c_20090])).
% 14.45/6.08  tff(c_21424, plain, (![A_912]: ('#skF_3'('#skF_2'(A_912), '#skF_5', k1_xboole_0)='#skF_2'(A_912) | ~r1_tarski(A_912, k2_struct_0('#skF_5')) | k1_xboole_0=A_912)), inference(resolution, [status(thm)], [c_194, c_20104])).
% 14.45/6.08  tff(c_21495, plain, ('#skF_3'('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), '#skF_5', k1_xboole_0)='#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))) | a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))=k1_xboole_0), inference(resolution, [status(thm)], [c_856, c_21424])).
% 14.45/6.08  tff(c_21539, plain, ('#skF_3'('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), '#skF_5', k1_xboole_0)='#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_635, c_21495])).
% 14.45/6.08  tff(c_2708, plain, (![B_314, E_315, A_316, C_317]: (r2_orders_2(B_314, E_315, '#skF_3'(A_316, B_314, C_317)) | ~r2_hidden(E_315, C_317) | ~m1_subset_1(E_315, u1_struct_0(B_314)) | ~r2_hidden(A_316, a_2_0_orders_2(B_314, C_317)) | ~m1_subset_1(C_317, k1_zfmisc_1(u1_struct_0(B_314))) | ~l1_orders_2(B_314) | ~v5_orders_2(B_314) | ~v4_orders_2(B_314) | ~v3_orders_2(B_314) | v2_struct_0(B_314))), inference(cnfTransformation, [status(thm)], [f_148])).
% 14.45/6.08  tff(c_4600, plain, (![B_410, E_411, A_412]: (r2_orders_2(B_410, E_411, '#skF_3'(A_412, B_410, k1_xboole_0)) | ~r2_hidden(E_411, k1_xboole_0) | ~m1_subset_1(E_411, u1_struct_0(B_410)) | ~r2_hidden(A_412, a_2_0_orders_2(B_410, k1_xboole_0)) | ~l1_orders_2(B_410) | ~v5_orders_2(B_410) | ~v4_orders_2(B_410) | ~v3_orders_2(B_410) | v2_struct_0(B_410))), inference(resolution, [status(thm)], [c_10, c_2708])).
% 14.45/6.08  tff(c_30, plain, (![A_30, C_36]: (~r2_orders_2(A_30, C_36, C_36) | ~m1_subset_1(C_36, u1_struct_0(A_30)) | ~l1_orders_2(A_30))), inference(cnfTransformation, [status(thm)], [f_86])).
% 14.45/6.08  tff(c_22863, plain, (![A_941, B_942]: (~r2_hidden('#skF_3'(A_941, B_942, k1_xboole_0), k1_xboole_0) | ~m1_subset_1('#skF_3'(A_941, B_942, k1_xboole_0), u1_struct_0(B_942)) | ~r2_hidden(A_941, a_2_0_orders_2(B_942, k1_xboole_0)) | ~l1_orders_2(B_942) | ~v5_orders_2(B_942) | ~v4_orders_2(B_942) | ~v3_orders_2(B_942) | v2_struct_0(B_942))), inference(resolution, [status(thm)], [c_4600, c_30])).
% 14.45/6.08  tff(c_22866, plain, (~r2_hidden('#skF_3'('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), '#skF_5', k1_xboole_0), k1_xboole_0) | ~m1_subset_1('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), u1_struct_0('#skF_5')) | ~r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), a_2_0_orders_2('#skF_5', k1_xboole_0)) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_21539, c_22863])).
% 14.45/6.08  tff(c_22890, plain, (~r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), k1_xboole_0) | ~r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), a_2_0_orders_2('#skF_5', k1_xboole_0)) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_54, c_955, c_81, c_21539, c_22866])).
% 14.45/6.08  tff(c_22891, plain, (~r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), k1_xboole_0) | ~r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), a_2_0_orders_2('#skF_5', k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_62, c_22890])).
% 14.45/6.08  tff(c_23002, plain, (~r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), a_2_0_orders_2('#skF_5', k1_xboole_0))), inference(splitLeft, [status(thm)], [c_22891])).
% 14.45/6.08  tff(c_23012, plain, (~r1_tarski(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5')), k2_struct_0('#skF_5')) | a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))=k1_xboole_0), inference(resolution, [status(thm)], [c_21140, c_23002])).
% 14.45/6.09  tff(c_23030, plain, (a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_856, c_23012])).
% 14.45/6.09  tff(c_23032, plain, $false, inference(negUnitSimplification, [status(thm)], [c_635, c_23030])).
% 14.45/6.09  tff(c_23034, plain, (r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), a_2_0_orders_2('#skF_5', k1_xboole_0))), inference(splitRight, [status(thm)], [c_22891])).
% 14.45/6.09  tff(c_23091, plain, (![B_2]: (r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), B_2) | ~r1_tarski(a_2_0_orders_2('#skF_5', k1_xboole_0), B_2))), inference(resolution, [status(thm)], [c_23034, c_2])).
% 14.45/6.09  tff(c_121, plain, (![A_15, B_74]: (r2_hidden('#skF_2'(A_15), B_74) | ~r1_tarski(A_15, B_74) | k1_xboole_0=A_15)), inference(resolution, [status(thm)], [c_20, c_115])).
% 14.45/6.09  tff(c_793, plain, (![A_158, B_159, C_160]: ('#skF_3'(A_158, B_159, C_160)=A_158 | ~r2_hidden(A_158, a_2_0_orders_2(B_159, C_160)) | ~m1_subset_1(C_160, k1_zfmisc_1(u1_struct_0(B_159))) | ~l1_orders_2(B_159) | ~v5_orders_2(B_159) | ~v4_orders_2(B_159) | ~v3_orders_2(B_159) | v2_struct_0(B_159))), inference(cnfTransformation, [status(thm)], [f_148])).
% 14.45/6.09  tff(c_5487, plain, (![B_447, C_448]: ('#skF_3'('#skF_2'(a_2_0_orders_2(B_447, C_448)), B_447, C_448)='#skF_2'(a_2_0_orders_2(B_447, C_448)) | ~m1_subset_1(C_448, k1_zfmisc_1(u1_struct_0(B_447))) | ~l1_orders_2(B_447) | ~v5_orders_2(B_447) | ~v4_orders_2(B_447) | ~v3_orders_2(B_447) | v2_struct_0(B_447) | a_2_0_orders_2(B_447, C_448)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_793])).
% 14.45/6.09  tff(c_5503, plain, (![C_448]: ('#skF_3'('#skF_2'(a_2_0_orders_2('#skF_5', C_448)), '#skF_5', C_448)='#skF_2'(a_2_0_orders_2('#skF_5', C_448)) | ~m1_subset_1(C_448, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5') | a_2_0_orders_2('#skF_5', C_448)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_81, c_5487])).
% 14.45/6.09  tff(c_5513, plain, (![C_448]: ('#skF_3'('#skF_2'(a_2_0_orders_2('#skF_5', C_448)), '#skF_5', C_448)='#skF_2'(a_2_0_orders_2('#skF_5', C_448)) | ~m1_subset_1(C_448, k1_zfmisc_1(k2_struct_0('#skF_5'))) | v2_struct_0('#skF_5') | a_2_0_orders_2('#skF_5', C_448)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_54, c_5503])).
% 14.45/6.09  tff(c_5638, plain, (![C_453]: ('#skF_3'('#skF_2'(a_2_0_orders_2('#skF_5', C_453)), '#skF_5', C_453)='#skF_2'(a_2_0_orders_2('#skF_5', C_453)) | ~m1_subset_1(C_453, k1_zfmisc_1(k2_struct_0('#skF_5'))) | a_2_0_orders_2('#skF_5', C_453)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_62, c_5513])).
% 14.45/6.09  tff(c_5651, plain, ('#skF_3'('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), '#skF_5', k2_struct_0('#skF_5'))='#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))) | a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))=k1_xboole_0), inference(resolution, [status(thm)], [c_832, c_5638])).
% 14.45/6.09  tff(c_5677, plain, ('#skF_3'('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), '#skF_5', k2_struct_0('#skF_5'))='#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_635, c_5651])).
% 14.45/6.09  tff(c_5824, plain, (![B_458, E_459, A_460, A_461]: (r2_orders_2(B_458, E_459, '#skF_3'(A_460, B_458, A_461)) | ~r2_hidden(E_459, A_461) | ~m1_subset_1(E_459, u1_struct_0(B_458)) | ~r2_hidden(A_460, a_2_0_orders_2(B_458, A_461)) | ~l1_orders_2(B_458) | ~v5_orders_2(B_458) | ~v4_orders_2(B_458) | ~v3_orders_2(B_458) | v2_struct_0(B_458) | ~r1_tarski(A_461, u1_struct_0(B_458)))), inference(resolution, [status(thm)], [c_14, c_2708])).
% 14.45/6.09  tff(c_5835, plain, (![E_459]: (r2_orders_2('#skF_5', E_459, '#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5')))) | ~r2_hidden(E_459, k2_struct_0('#skF_5')) | ~m1_subset_1(E_459, u1_struct_0('#skF_5')) | ~r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5') | ~r1_tarski(k2_struct_0('#skF_5'), u1_struct_0('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_5677, c_5824])).
% 14.45/6.09  tff(c_5843, plain, (![E_459]: (r2_orders_2('#skF_5', E_459, '#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5')))) | ~r2_hidden(E_459, k2_struct_0('#skF_5')) | ~m1_subset_1(E_459, k2_struct_0('#skF_5')) | ~r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_81, c_60, c_58, c_56, c_54, c_81, c_5835])).
% 14.45/6.09  tff(c_5844, plain, (![E_459]: (r2_orders_2('#skF_5', E_459, '#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5')))) | ~r2_hidden(E_459, k2_struct_0('#skF_5')) | ~m1_subset_1(E_459, k2_struct_0('#skF_5')) | ~r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_62, c_5843])).
% 14.45/6.09  tff(c_17551, plain, (~r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5')))), inference(splitLeft, [status(thm)], [c_5844])).
% 14.45/6.09  tff(c_17557, plain, (~r1_tarski(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5')), a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))) | a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))=k1_xboole_0), inference(resolution, [status(thm)], [c_121, c_17551])).
% 14.45/6.09  tff(c_17566, plain, (a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_113, c_17557])).
% 14.45/6.09  tff(c_17568, plain, $false, inference(negUnitSimplification, [status(thm)], [c_635, c_17566])).
% 14.45/6.09  tff(c_17570, plain, (r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_5844])).
% 14.45/6.09  tff(c_26120, plain, (![A_1010, B_1011, A_1012]: (~r2_hidden('#skF_3'(A_1010, B_1011, A_1012), A_1012) | ~m1_subset_1('#skF_3'(A_1010, B_1011, A_1012), u1_struct_0(B_1011)) | ~r2_hidden(A_1010, a_2_0_orders_2(B_1011, A_1012)) | ~l1_orders_2(B_1011) | ~v5_orders_2(B_1011) | ~v4_orders_2(B_1011) | ~v3_orders_2(B_1011) | v2_struct_0(B_1011) | ~r1_tarski(A_1012, u1_struct_0(B_1011)))), inference(resolution, [status(thm)], [c_5824, c_30])).
% 14.45/6.09  tff(c_26152, plain, (~r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), k2_struct_0('#skF_5')) | ~m1_subset_1('#skF_3'('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), '#skF_5', k2_struct_0('#skF_5')), u1_struct_0('#skF_5')) | ~r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5') | ~r1_tarski(k2_struct_0('#skF_5'), u1_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_5677, c_26120])).
% 14.45/6.09  tff(c_26184, plain, (~r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), k2_struct_0('#skF_5')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_113, c_81, c_60, c_58, c_56, c_54, c_17570, c_955, c_81, c_5677, c_26152])).
% 14.45/6.09  tff(c_26185, plain, (~r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), k2_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_62, c_26184])).
% 14.45/6.09  tff(c_26191, plain, (~r1_tarski(a_2_0_orders_2('#skF_5', k1_xboole_0), k2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_23091, c_26185])).
% 14.45/6.09  tff(c_26216, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_713, c_26191])).
% 14.45/6.09  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.45/6.09  
% 14.45/6.09  Inference rules
% 14.45/6.09  ----------------------
% 14.45/6.09  #Ref     : 0
% 14.45/6.09  #Sup     : 5967
% 14.45/6.09  #Fact    : 0
% 14.45/6.09  #Define  : 0
% 14.45/6.09  #Split   : 37
% 14.45/6.09  #Chain   : 0
% 14.45/6.09  #Close   : 0
% 14.45/6.09  
% 14.45/6.09  Ordering : KBO
% 14.45/6.09  
% 14.45/6.09  Simplification rules
% 14.45/6.09  ----------------------
% 14.45/6.09  #Subsume      : 1913
% 14.45/6.09  #Demod        : 3848
% 14.45/6.09  #Tautology    : 981
% 14.45/6.09  #SimpNegUnit  : 488
% 14.45/6.09  #BackRed      : 56
% 14.45/6.09  
% 14.45/6.09  #Partial instantiations: 0
% 14.45/6.09  #Strategies tried      : 1
% 14.45/6.09  
% 14.45/6.09  Timing (in seconds)
% 14.45/6.09  ----------------------
% 14.45/6.09  Preprocessing        : 0.36
% 14.45/6.09  Parsing              : 0.19
% 14.45/6.09  CNF conversion       : 0.03
% 14.45/6.09  Main loop            : 4.94
% 14.45/6.09  Inferencing          : 1.09
% 14.45/6.09  Reduction            : 1.52
% 14.45/6.09  Demodulation         : 1.03
% 14.45/6.09  BG Simplification    : 0.11
% 14.45/6.09  Subsumption          : 1.86
% 14.45/6.09  Abstraction          : 0.16
% 14.45/6.09  MUC search           : 0.00
% 14.45/6.09  Cooper               : 0.00
% 14.45/6.09  Total                : 5.35
% 14.45/6.09  Index Insertion      : 0.00
% 14.45/6.09  Index Deletion       : 0.00
% 14.45/6.09  Index Matching       : 0.00
% 14.45/6.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
