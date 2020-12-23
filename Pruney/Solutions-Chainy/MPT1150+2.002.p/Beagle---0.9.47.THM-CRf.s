%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:24 EST 2020

% Result     : Theorem 16.56s
% Output     : CNFRefutation 16.72s
% Verified   : 
% Statistics : Number of formulae       :  152 (1956 expanded)
%              Number of leaves         :   41 ( 750 expanded)
%              Depth                    :   28
%              Number of atoms          :  384 (5993 expanded)
%              Number of equality atoms :   56 (1050 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_struct_0 > l1_orders_2 > k4_mcart_1 > k1_orders_2 > a_2_0_orders_2 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_4 > #skF_3 > #skF_1

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

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_168,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => k1_orders_2(A,k2_struct_0(A)) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_orders_2)).

tff(f_127,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_77,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_108,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_orders_2(A,B) = a_2_0_orders_2(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_orders_2)).

tff(f_73,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_mcart_1(C,D,E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_mcart_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_123,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_orders_2(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_orders_2)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_154,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_0_orders_2)).

tff(f_42,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_92,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r2_orders_2(A,B,C)
              <=> ( r1_orders_2(A,B,C)
                  & B != C ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_orders_2)).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_20,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_66,plain,(
    v3_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_64,plain,(
    v4_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_62,plain,(
    v5_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_60,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_44,plain,(
    ! [A_48] :
      ( l1_struct_0(A_48)
      | ~ l1_orders_2(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_75,plain,(
    ! [A_68] :
      ( u1_struct_0(A_68) = k2_struct_0(A_68)
      | ~ l1_struct_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_85,plain,(
    ! [A_70] :
      ( u1_struct_0(A_70) = k2_struct_0(A_70)
      | ~ l1_orders_2(A_70) ) ),
    inference(resolution,[status(thm)],[c_44,c_75])).

tff(c_89,plain,(
    u1_struct_0('#skF_5') = k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_85])).

tff(c_561,plain,(
    ! [A_155,B_156] :
      ( k1_orders_2(A_155,B_156) = a_2_0_orders_2(A_155,B_156)
      | ~ m1_subset_1(B_156,k1_zfmisc_1(u1_struct_0(A_155)))
      | ~ l1_orders_2(A_155)
      | ~ v5_orders_2(A_155)
      | ~ v4_orders_2(A_155)
      | ~ v3_orders_2(A_155)
      | v2_struct_0(A_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_576,plain,(
    ! [B_156] :
      ( k1_orders_2('#skF_5',B_156) = a_2_0_orders_2('#skF_5',B_156)
      | ~ m1_subset_1(B_156,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_561])).

tff(c_585,plain,(
    ! [B_156] :
      ( k1_orders_2('#skF_5',B_156) = a_2_0_orders_2('#skF_5',B_156)
      | ~ m1_subset_1(B_156,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_60,c_576])).

tff(c_636,plain,(
    ! [B_163] :
      ( k1_orders_2('#skF_5',B_163) = a_2_0_orders_2('#skF_5',B_163)
      | ~ m1_subset_1(B_163,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_585])).

tff(c_675,plain,(
    ! [A_167] :
      ( k1_orders_2('#skF_5',A_167) = a_2_0_orders_2('#skF_5',A_167)
      | ~ r1_tarski(A_167,k2_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_20,c_636])).

tff(c_694,plain,(
    k1_orders_2('#skF_5',k2_struct_0('#skF_5')) = a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_12,c_675])).

tff(c_58,plain,(
    k1_orders_2('#skF_5',k2_struct_0('#skF_5')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_697,plain,(
    a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_694,c_58])).

tff(c_26,plain,(
    ! [A_17] :
      ( r2_hidden('#skF_2'(A_17),A_17)
      | k1_xboole_0 = A_17 ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_154,plain,(
    ! [C_85,B_86,A_87] :
      ( r2_hidden(C_85,B_86)
      | ~ r2_hidden(C_85,A_87)
      | ~ r1_tarski(A_87,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_160,plain,(
    ! [A_17,B_86] :
      ( r2_hidden('#skF_2'(A_17),B_86)
      | ~ r1_tarski(A_17,B_86)
      | k1_xboole_0 = A_17 ) ),
    inference(resolution,[status(thm)],[c_26,c_154])).

tff(c_702,plain,(
    ! [A_168,B_169] :
      ( m1_subset_1(k1_orders_2(A_168,B_169),k1_zfmisc_1(u1_struct_0(A_168)))
      | ~ m1_subset_1(B_169,k1_zfmisc_1(u1_struct_0(A_168)))
      | ~ l1_orders_2(A_168)
      | ~ v5_orders_2(A_168)
      | ~ v4_orders_2(A_168)
      | ~ v3_orders_2(A_168)
      | v2_struct_0(A_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_713,plain,
    ( m1_subset_1(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_694,c_702])).

tff(c_724,plain,
    ( m1_subset_1(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')),k1_zfmisc_1(k2_struct_0('#skF_5')))
    | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5')))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_60,c_89,c_89,c_713])).

tff(c_725,plain,
    ( m1_subset_1(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')),k1_zfmisc_1(k2_struct_0('#skF_5')))
    | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_724])).

tff(c_27477,plain,(
    ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_725])).

tff(c_27518,plain,(
    ~ r1_tarski(k2_struct_0('#skF_5'),k2_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_20,c_27477])).

tff(c_27522,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_27518])).

tff(c_27523,plain,(
    m1_subset_1(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')),k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_725])).

tff(c_22,plain,(
    ! [A_12,C_14,B_13] :
      ( m1_subset_1(A_12,C_14)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(C_14))
      | ~ r2_hidden(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_27716,plain,(
    ! [A_973] :
      ( m1_subset_1(A_973,k2_struct_0('#skF_5'))
      | ~ r2_hidden(A_973,a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_27523,c_22])).

tff(c_27732,plain,
    ( m1_subset_1('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),k2_struct_0('#skF_5'))
    | a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_27716])).

tff(c_27738,plain,(
    m1_subset_1('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),k2_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_697,c_27732])).

tff(c_27524,plain,(
    m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_725])).

tff(c_819,plain,(
    ! [A_173,B_174,C_175] :
      ( '#skF_3'(A_173,B_174,C_175) = A_173
      | ~ r2_hidden(A_173,a_2_0_orders_2(B_174,C_175))
      | ~ m1_subset_1(C_175,k1_zfmisc_1(u1_struct_0(B_174)))
      | ~ l1_orders_2(B_174)
      | ~ v5_orders_2(B_174)
      | ~ v4_orders_2(B_174)
      | ~ v3_orders_2(B_174)
      | v2_struct_0(B_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_30683,plain,(
    ! [B_1112,C_1113] :
      ( '#skF_3'('#skF_2'(a_2_0_orders_2(B_1112,C_1113)),B_1112,C_1113) = '#skF_2'(a_2_0_orders_2(B_1112,C_1113))
      | ~ m1_subset_1(C_1113,k1_zfmisc_1(u1_struct_0(B_1112)))
      | ~ l1_orders_2(B_1112)
      | ~ v5_orders_2(B_1112)
      | ~ v4_orders_2(B_1112)
      | ~ v3_orders_2(B_1112)
      | v2_struct_0(B_1112)
      | a_2_0_orders_2(B_1112,C_1113) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_26,c_819])).

tff(c_30702,plain,(
    ! [C_1113] :
      ( '#skF_3'('#skF_2'(a_2_0_orders_2('#skF_5',C_1113)),'#skF_5',C_1113) = '#skF_2'(a_2_0_orders_2('#skF_5',C_1113))
      | ~ m1_subset_1(C_1113,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5')
      | a_2_0_orders_2('#skF_5',C_1113) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_30683])).

tff(c_30713,plain,(
    ! [C_1113] :
      ( '#skF_3'('#skF_2'(a_2_0_orders_2('#skF_5',C_1113)),'#skF_5',C_1113) = '#skF_2'(a_2_0_orders_2('#skF_5',C_1113))
      | ~ m1_subset_1(C_1113,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | v2_struct_0('#skF_5')
      | a_2_0_orders_2('#skF_5',C_1113) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_60,c_30702])).

tff(c_31280,plain,(
    ! [C_1127] :
      ( '#skF_3'('#skF_2'(a_2_0_orders_2('#skF_5',C_1127)),'#skF_5',C_1127) = '#skF_2'(a_2_0_orders_2('#skF_5',C_1127))
      | ~ m1_subset_1(C_1127,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | a_2_0_orders_2('#skF_5',C_1127) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_30713])).

tff(c_31297,plain,
    ( '#skF_3'('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),'#skF_5',k2_struct_0('#skF_5')) = '#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')))
    | a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_27524,c_31280])).

tff(c_31321,plain,(
    '#skF_3'('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),'#skF_5',k2_struct_0('#skF_5')) = '#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_697,c_31297])).

tff(c_16,plain,(
    ! [A_9] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_656,plain,(
    k1_orders_2('#skF_5',k1_xboole_0) = a_2_0_orders_2('#skF_5',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_636])).

tff(c_716,plain,
    ( m1_subset_1(a_2_0_orders_2('#skF_5',k1_xboole_0),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_656,c_702])).

tff(c_727,plain,
    ( m1_subset_1(a_2_0_orders_2('#skF_5',k1_xboole_0),k1_zfmisc_1(k2_struct_0('#skF_5')))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_60,c_16,c_89,c_716])).

tff(c_728,plain,(
    m1_subset_1(a_2_0_orders_2('#skF_5',k1_xboole_0),k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_727])).

tff(c_18,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | ~ m1_subset_1(A_10,k1_zfmisc_1(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_742,plain,(
    r1_tarski(a_2_0_orders_2('#skF_5',k1_xboole_0),k2_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_728,c_18])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_760,plain,
    ( a_2_0_orders_2('#skF_5',k1_xboole_0) = k2_struct_0('#skF_5')
    | ~ r1_tarski(k2_struct_0('#skF_5'),a_2_0_orders_2('#skF_5',k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_742,c_8])).

tff(c_941,plain,(
    ~ r1_tarski(k2_struct_0('#skF_5'),a_2_0_orders_2('#skF_5',k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_760])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3105,plain,(
    ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_725])).

tff(c_3108,plain,(
    ~ r1_tarski(k2_struct_0('#skF_5'),k2_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_20,c_3105])).

tff(c_3112,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_3108])).

tff(c_3114,plain,(
    m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_725])).

tff(c_3164,plain,(
    ! [A_309] :
      ( m1_subset_1(A_309,k2_struct_0('#skF_5'))
      | ~ r2_hidden(A_309,k2_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_3114,c_22])).

tff(c_3183,plain,(
    ! [B_2] :
      ( m1_subset_1('#skF_1'(k2_struct_0('#skF_5'),B_2),k2_struct_0('#skF_5'))
      | r1_tarski(k2_struct_0('#skF_5'),B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_3164])).

tff(c_14,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_3015,plain,(
    ! [D_299,B_300,C_301] :
      ( r2_hidden('#skF_4'(D_299,B_300,C_301,D_299),C_301)
      | r2_hidden(D_299,a_2_0_orders_2(B_300,C_301))
      | ~ m1_subset_1(D_299,u1_struct_0(B_300))
      | ~ m1_subset_1(C_301,k1_zfmisc_1(u1_struct_0(B_300)))
      | ~ l1_orders_2(B_300)
      | ~ v5_orders_2(B_300)
      | ~ v4_orders_2(B_300)
      | ~ v3_orders_2(B_300)
      | v2_struct_0(B_300) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_3028,plain,(
    ! [D_299,C_301] :
      ( r2_hidden('#skF_4'(D_299,'#skF_5',C_301,D_299),C_301)
      | r2_hidden(D_299,a_2_0_orders_2('#skF_5',C_301))
      | ~ m1_subset_1(D_299,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(C_301,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_3015])).

tff(c_3037,plain,(
    ! [D_299,C_301] :
      ( r2_hidden('#skF_4'(D_299,'#skF_5',C_301,D_299),C_301)
      | r2_hidden(D_299,a_2_0_orders_2('#skF_5',C_301))
      | ~ m1_subset_1(D_299,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(C_301,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_60,c_89,c_3028])).

tff(c_3504,plain,(
    ! [D_333,C_334] :
      ( r2_hidden('#skF_4'(D_333,'#skF_5',C_334,D_333),C_334)
      | r2_hidden(D_333,a_2_0_orders_2('#skF_5',C_334))
      | ~ m1_subset_1(D_333,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(C_334,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_3037])).

tff(c_25981,plain,(
    ! [D_919] :
      ( r2_hidden('#skF_4'(D_919,'#skF_5',k1_xboole_0,D_919),k1_xboole_0)
      | r2_hidden(D_919,a_2_0_orders_2('#skF_5',k1_xboole_0))
      | ~ m1_subset_1(D_919,k2_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_16,c_3504])).

tff(c_24,plain,(
    ! [B_16,A_15] :
      ( ~ r1_tarski(B_16,A_15)
      | ~ r2_hidden(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_26003,plain,(
    ! [D_919] :
      ( ~ r1_tarski(k1_xboole_0,'#skF_4'(D_919,'#skF_5',k1_xboole_0,D_919))
      | r2_hidden(D_919,a_2_0_orders_2('#skF_5',k1_xboole_0))
      | ~ m1_subset_1(D_919,k2_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_25981,c_24])).

tff(c_26025,plain,(
    ! [D_920] :
      ( r2_hidden(D_920,a_2_0_orders_2('#skF_5',k1_xboole_0))
      | ~ m1_subset_1(D_920,k2_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_26003])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_27377,plain,(
    ! [A_964] :
      ( r1_tarski(A_964,a_2_0_orders_2('#skF_5',k1_xboole_0))
      | ~ m1_subset_1('#skF_1'(A_964,a_2_0_orders_2('#skF_5',k1_xboole_0)),k2_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_26025,c_4])).

tff(c_27461,plain,(
    r1_tarski(k2_struct_0('#skF_5'),a_2_0_orders_2('#skF_5',k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_3183,c_27377])).

tff(c_27474,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_941,c_941,c_27461])).

tff(c_27475,plain,(
    a_2_0_orders_2('#skF_5',k1_xboole_0) = k2_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_760])).

tff(c_586,plain,(
    ! [B_156] :
      ( k1_orders_2('#skF_5',B_156) = a_2_0_orders_2('#skF_5',B_156)
      | ~ m1_subset_1(B_156,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_585])).

tff(c_740,plain,(
    k1_orders_2('#skF_5',a_2_0_orders_2('#skF_5',k1_xboole_0)) = a_2_0_orders_2('#skF_5',a_2_0_orders_2('#skF_5',k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_728,c_586])).

tff(c_719,plain,(
    ! [B_169] :
      ( m1_subset_1(k1_orders_2('#skF_5',B_169),k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(B_169,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_702])).

tff(c_730,plain,(
    ! [B_169] :
      ( m1_subset_1(k1_orders_2('#skF_5',B_169),k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(B_169,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_60,c_89,c_719])).

tff(c_731,plain,(
    ! [B_169] :
      ( m1_subset_1(k1_orders_2('#skF_5',B_169),k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(B_169,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_730])).

tff(c_839,plain,
    ( m1_subset_1(a_2_0_orders_2('#skF_5',a_2_0_orders_2('#skF_5',k1_xboole_0)),k1_zfmisc_1(k2_struct_0('#skF_5')))
    | ~ m1_subset_1(a_2_0_orders_2('#skF_5',k1_xboole_0),k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_740,c_731])).

tff(c_846,plain,(
    m1_subset_1(a_2_0_orders_2('#skF_5',a_2_0_orders_2('#skF_5',k1_xboole_0)),k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_728,c_839])).

tff(c_861,plain,(
    r1_tarski(a_2_0_orders_2('#skF_5',a_2_0_orders_2('#skF_5',k1_xboole_0)),k2_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_846,c_18])).

tff(c_27525,plain,(
    r1_tarski(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')),k2_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27475,c_861])).

tff(c_161,plain,(
    ! [A_88,B_89] :
      ( r2_hidden('#skF_2'(A_88),B_89)
      | ~ r1_tarski(A_88,B_89)
      | k1_xboole_0 = A_88 ) ),
    inference(resolution,[status(thm)],[c_26,c_154])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_27754,plain,(
    ! [A_980,B_981,B_982] :
      ( r2_hidden('#skF_2'(A_980),B_981)
      | ~ r1_tarski(B_982,B_981)
      | ~ r1_tarski(A_980,B_982)
      | k1_xboole_0 = A_980 ) ),
    inference(resolution,[status(thm)],[c_161,c_2])).

tff(c_27767,plain,(
    ! [A_980] :
      ( r2_hidden('#skF_2'(A_980),k2_struct_0('#skF_5'))
      | ~ r1_tarski(A_980,a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')))
      | k1_xboole_0 = A_980 ) ),
    inference(resolution,[status(thm)],[c_27525,c_27754])).

tff(c_54,plain,(
    ! [A_49,B_50,C_51] :
      ( '#skF_3'(A_49,B_50,C_51) = A_49
      | ~ r2_hidden(A_49,a_2_0_orders_2(B_50,C_51))
      | ~ m1_subset_1(C_51,k1_zfmisc_1(u1_struct_0(B_50)))
      | ~ l1_orders_2(B_50)
      | ~ v5_orders_2(B_50)
      | ~ v4_orders_2(B_50)
      | ~ v3_orders_2(B_50)
      | v2_struct_0(B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_27536,plain,(
    ! [A_49] :
      ( '#skF_3'(A_49,'#skF_5',k1_xboole_0) = A_49
      | ~ r2_hidden(A_49,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_27475,c_54])).

tff(c_27540,plain,(
    ! [A_49] :
      ( '#skF_3'(A_49,'#skF_5',k1_xboole_0) = A_49
      | ~ r2_hidden(A_49,k2_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_60,c_16,c_89,c_27536])).

tff(c_27692,plain,(
    ! [A_972] :
      ( '#skF_3'(A_972,'#skF_5',k1_xboole_0) = A_972
      | ~ r2_hidden(A_972,k2_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_27540])).

tff(c_28376,plain,(
    ! [A_1028] :
      ( '#skF_3'('#skF_2'(A_1028),'#skF_5',k1_xboole_0) = '#skF_2'(A_1028)
      | ~ r1_tarski(A_1028,k2_struct_0('#skF_5'))
      | k1_xboole_0 = A_1028 ) ),
    inference(resolution,[status(thm)],[c_160,c_27692])).

tff(c_28386,plain,
    ( '#skF_3'('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),'#skF_5',k1_xboole_0) = '#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')))
    | a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_27525,c_28376])).

tff(c_28410,plain,(
    '#skF_3'('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),'#skF_5',k1_xboole_0) = '#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_697,c_28386])).

tff(c_27881,plain,(
    ! [B_989,E_990,A_991,C_992] :
      ( r2_orders_2(B_989,E_990,'#skF_3'(A_991,B_989,C_992))
      | ~ r2_hidden(E_990,C_992)
      | ~ m1_subset_1(E_990,u1_struct_0(B_989))
      | ~ r2_hidden(A_991,a_2_0_orders_2(B_989,C_992))
      | ~ m1_subset_1(C_992,k1_zfmisc_1(u1_struct_0(B_989)))
      | ~ l1_orders_2(B_989)
      | ~ v5_orders_2(B_989)
      | ~ v4_orders_2(B_989)
      | ~ v3_orders_2(B_989)
      | v2_struct_0(B_989) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_31711,plain,(
    ! [B_1147,E_1148,A_1149,A_1150] :
      ( r2_orders_2(B_1147,E_1148,'#skF_3'(A_1149,B_1147,A_1150))
      | ~ r2_hidden(E_1148,A_1150)
      | ~ m1_subset_1(E_1148,u1_struct_0(B_1147))
      | ~ r2_hidden(A_1149,a_2_0_orders_2(B_1147,A_1150))
      | ~ l1_orders_2(B_1147)
      | ~ v5_orders_2(B_1147)
      | ~ v4_orders_2(B_1147)
      | ~ v3_orders_2(B_1147)
      | v2_struct_0(B_1147)
      | ~ r1_tarski(A_1150,u1_struct_0(B_1147)) ) ),
    inference(resolution,[status(thm)],[c_20,c_27881])).

tff(c_31722,plain,(
    ! [E_1148] :
      ( r2_orders_2('#skF_5',E_1148,'#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))))
      | ~ r2_hidden(E_1148,k1_xboole_0)
      | ~ m1_subset_1(E_1148,u1_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),a_2_0_orders_2('#skF_5',k1_xboole_0))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r1_tarski(k1_xboole_0,u1_struct_0('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28410,c_31711])).

tff(c_31730,plain,(
    ! [E_1148] :
      ( r2_orders_2('#skF_5',E_1148,'#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))))
      | ~ r2_hidden(E_1148,k1_xboole_0)
      | ~ m1_subset_1(E_1148,k2_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),k2_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_89,c_66,c_64,c_62,c_60,c_27475,c_89,c_31722])).

tff(c_31731,plain,(
    ! [E_1148] :
      ( r2_orders_2('#skF_5',E_1148,'#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))))
      | ~ r2_hidden(E_1148,k1_xboole_0)
      | ~ m1_subset_1(E_1148,k2_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),k2_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_31730])).

tff(c_33756,plain,(
    ~ r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),k2_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_31731])).

tff(c_33759,plain,
    ( ~ r1_tarski(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')),a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')))
    | a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_27767,c_33756])).

tff(c_33765,plain,(
    a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_33759])).

tff(c_33767,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_697,c_33765])).

tff(c_33769,plain,(
    r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),k2_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_31731])).

tff(c_36,plain,(
    ! [A_36,C_42] :
      ( ~ r2_orders_2(A_36,C_42,C_42)
      | ~ m1_subset_1(C_42,u1_struct_0(A_36))
      | ~ l1_orders_2(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_45645,plain,(
    ! [A_1558,B_1559,A_1560] :
      ( ~ r2_hidden('#skF_3'(A_1558,B_1559,A_1560),A_1560)
      | ~ m1_subset_1('#skF_3'(A_1558,B_1559,A_1560),u1_struct_0(B_1559))
      | ~ r2_hidden(A_1558,a_2_0_orders_2(B_1559,A_1560))
      | ~ l1_orders_2(B_1559)
      | ~ v5_orders_2(B_1559)
      | ~ v4_orders_2(B_1559)
      | ~ v3_orders_2(B_1559)
      | v2_struct_0(B_1559)
      | ~ r1_tarski(A_1560,u1_struct_0(B_1559)) ) ),
    inference(resolution,[status(thm)],[c_31711,c_36])).

tff(c_45667,plain,
    ( ~ r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),k2_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_3'('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),'#skF_5',k2_struct_0('#skF_5')),u1_struct_0('#skF_5'))
    | ~ r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ r1_tarski(k2_struct_0('#skF_5'),u1_struct_0('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_31321,c_45645])).

tff(c_45686,plain,
    ( ~ r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_89,c_66,c_64,c_62,c_60,c_27738,c_89,c_31321,c_33769,c_45667])).

tff(c_45687,plain,(
    ~ r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_45686])).

tff(c_45696,plain,
    ( ~ r1_tarski(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')),a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')))
    | a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_160,c_45687])).

tff(c_45703,plain,(
    a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_45696])).

tff(c_45705,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_697,c_45703])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:40:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 16.56/8.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.56/8.45  
% 16.56/8.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.56/8.45  %$ r2_orders_2 > r1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_struct_0 > l1_orders_2 > k4_mcart_1 > k1_orders_2 > a_2_0_orders_2 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_4 > #skF_3 > #skF_1
% 16.56/8.45  
% 16.56/8.45  %Foreground sorts:
% 16.56/8.45  
% 16.56/8.45  
% 16.56/8.45  %Background operators:
% 16.56/8.45  
% 16.56/8.45  
% 16.56/8.45  %Foreground operators:
% 16.56/8.45  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 16.56/8.45  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 16.56/8.45  tff(k1_orders_2, type, k1_orders_2: ($i * $i) > $i).
% 16.56/8.45  tff('#skF_2', type, '#skF_2': $i > $i).
% 16.56/8.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.56/8.45  tff(a_2_0_orders_2, type, a_2_0_orders_2: ($i * $i) > $i).
% 16.56/8.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 16.56/8.45  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 16.56/8.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 16.56/8.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 16.56/8.45  tff('#skF_5', type, '#skF_5': $i).
% 16.56/8.45  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 16.56/8.45  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 16.56/8.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 16.56/8.45  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 16.56/8.45  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 16.56/8.45  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 16.56/8.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.56/8.45  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 16.56/8.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.56/8.45  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 16.56/8.45  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 16.56/8.45  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 16.56/8.45  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 16.56/8.45  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 16.56/8.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 16.56/8.45  
% 16.72/8.47  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 16.72/8.47  tff(f_46, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 16.72/8.47  tff(f_168, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (k1_orders_2(A, k2_struct_0(A)) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_orders_2)).
% 16.72/8.47  tff(f_127, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 16.72/8.47  tff(f_77, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 16.72/8.47  tff(f_108, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_orders_2(A, B) = a_2_0_orders_2(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_orders_2)).
% 16.72/8.47  tff(f_73, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_mcart_1(C, D, E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_mcart_1)).
% 16.72/8.47  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 16.72/8.47  tff(f_123, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_orders_2(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_orders_2)).
% 16.72/8.47  tff(f_52, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 16.72/8.47  tff(f_154, axiom, (![A, B, C]: ((((((~v2_struct_0(B) & v3_orders_2(B)) & v4_orders_2(B)) & v5_orders_2(B)) & l1_orders_2(B)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B)))) => (r2_hidden(A, a_2_0_orders_2(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r2_hidden(E, C) => r2_orders_2(B, E, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_0_orders_2)).
% 16.72/8.47  tff(f_42, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 16.72/8.47  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 16.72/8.47  tff(f_57, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 16.72/8.47  tff(f_92, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_orders_2(A, B, C) <=> (r1_orders_2(A, B, C) & ~(B = C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_orders_2)).
% 16.72/8.47  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 16.72/8.47  tff(c_20, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_46])).
% 16.72/8.47  tff(c_68, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_168])).
% 16.72/8.47  tff(c_66, plain, (v3_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_168])).
% 16.72/8.47  tff(c_64, plain, (v4_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_168])).
% 16.72/8.47  tff(c_62, plain, (v5_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_168])).
% 16.72/8.47  tff(c_60, plain, (l1_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_168])).
% 16.72/8.47  tff(c_44, plain, (![A_48]: (l1_struct_0(A_48) | ~l1_orders_2(A_48))), inference(cnfTransformation, [status(thm)], [f_127])).
% 16.72/8.47  tff(c_75, plain, (![A_68]: (u1_struct_0(A_68)=k2_struct_0(A_68) | ~l1_struct_0(A_68))), inference(cnfTransformation, [status(thm)], [f_77])).
% 16.72/8.47  tff(c_85, plain, (![A_70]: (u1_struct_0(A_70)=k2_struct_0(A_70) | ~l1_orders_2(A_70))), inference(resolution, [status(thm)], [c_44, c_75])).
% 16.72/8.47  tff(c_89, plain, (u1_struct_0('#skF_5')=k2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_60, c_85])).
% 16.72/8.47  tff(c_561, plain, (![A_155, B_156]: (k1_orders_2(A_155, B_156)=a_2_0_orders_2(A_155, B_156) | ~m1_subset_1(B_156, k1_zfmisc_1(u1_struct_0(A_155))) | ~l1_orders_2(A_155) | ~v5_orders_2(A_155) | ~v4_orders_2(A_155) | ~v3_orders_2(A_155) | v2_struct_0(A_155))), inference(cnfTransformation, [status(thm)], [f_108])).
% 16.72/8.47  tff(c_576, plain, (![B_156]: (k1_orders_2('#skF_5', B_156)=a_2_0_orders_2('#skF_5', B_156) | ~m1_subset_1(B_156, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_89, c_561])).
% 16.72/8.47  tff(c_585, plain, (![B_156]: (k1_orders_2('#skF_5', B_156)=a_2_0_orders_2('#skF_5', B_156) | ~m1_subset_1(B_156, k1_zfmisc_1(k2_struct_0('#skF_5'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_60, c_576])).
% 16.72/8.47  tff(c_636, plain, (![B_163]: (k1_orders_2('#skF_5', B_163)=a_2_0_orders_2('#skF_5', B_163) | ~m1_subset_1(B_163, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_68, c_585])).
% 16.72/8.47  tff(c_675, plain, (![A_167]: (k1_orders_2('#skF_5', A_167)=a_2_0_orders_2('#skF_5', A_167) | ~r1_tarski(A_167, k2_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_20, c_636])).
% 16.72/8.47  tff(c_694, plain, (k1_orders_2('#skF_5', k2_struct_0('#skF_5'))=a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_12, c_675])).
% 16.72/8.47  tff(c_58, plain, (k1_orders_2('#skF_5', k2_struct_0('#skF_5'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_168])).
% 16.72/8.47  tff(c_697, plain, (a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_694, c_58])).
% 16.72/8.47  tff(c_26, plain, (![A_17]: (r2_hidden('#skF_2'(A_17), A_17) | k1_xboole_0=A_17)), inference(cnfTransformation, [status(thm)], [f_73])).
% 16.72/8.47  tff(c_154, plain, (![C_85, B_86, A_87]: (r2_hidden(C_85, B_86) | ~r2_hidden(C_85, A_87) | ~r1_tarski(A_87, B_86))), inference(cnfTransformation, [status(thm)], [f_32])).
% 16.72/8.47  tff(c_160, plain, (![A_17, B_86]: (r2_hidden('#skF_2'(A_17), B_86) | ~r1_tarski(A_17, B_86) | k1_xboole_0=A_17)), inference(resolution, [status(thm)], [c_26, c_154])).
% 16.72/8.47  tff(c_702, plain, (![A_168, B_169]: (m1_subset_1(k1_orders_2(A_168, B_169), k1_zfmisc_1(u1_struct_0(A_168))) | ~m1_subset_1(B_169, k1_zfmisc_1(u1_struct_0(A_168))) | ~l1_orders_2(A_168) | ~v5_orders_2(A_168) | ~v4_orders_2(A_168) | ~v3_orders_2(A_168) | v2_struct_0(A_168))), inference(cnfTransformation, [status(thm)], [f_123])).
% 16.72/8.47  tff(c_713, plain, (m1_subset_1(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5')), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_694, c_702])).
% 16.72/8.47  tff(c_724, plain, (m1_subset_1(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5')), k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_5'))) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_60, c_89, c_89, c_713])).
% 16.72/8.47  tff(c_725, plain, (m1_subset_1(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5')), k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_68, c_724])).
% 16.72/8.47  tff(c_27477, plain, (~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(splitLeft, [status(thm)], [c_725])).
% 16.72/8.47  tff(c_27518, plain, (~r1_tarski(k2_struct_0('#skF_5'), k2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_20, c_27477])).
% 16.72/8.47  tff(c_27522, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_27518])).
% 16.72/8.47  tff(c_27523, plain, (m1_subset_1(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5')), k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_725])).
% 16.72/8.47  tff(c_22, plain, (![A_12, C_14, B_13]: (m1_subset_1(A_12, C_14) | ~m1_subset_1(B_13, k1_zfmisc_1(C_14)) | ~r2_hidden(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_52])).
% 16.72/8.47  tff(c_27716, plain, (![A_973]: (m1_subset_1(A_973, k2_struct_0('#skF_5')) | ~r2_hidden(A_973, a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_27523, c_22])).
% 16.72/8.47  tff(c_27732, plain, (m1_subset_1('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), k2_struct_0('#skF_5')) | a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_27716])).
% 16.72/8.47  tff(c_27738, plain, (m1_subset_1('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), k2_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_697, c_27732])).
% 16.72/8.47  tff(c_27524, plain, (m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_725])).
% 16.72/8.47  tff(c_819, plain, (![A_173, B_174, C_175]: ('#skF_3'(A_173, B_174, C_175)=A_173 | ~r2_hidden(A_173, a_2_0_orders_2(B_174, C_175)) | ~m1_subset_1(C_175, k1_zfmisc_1(u1_struct_0(B_174))) | ~l1_orders_2(B_174) | ~v5_orders_2(B_174) | ~v4_orders_2(B_174) | ~v3_orders_2(B_174) | v2_struct_0(B_174))), inference(cnfTransformation, [status(thm)], [f_154])).
% 16.72/8.47  tff(c_30683, plain, (![B_1112, C_1113]: ('#skF_3'('#skF_2'(a_2_0_orders_2(B_1112, C_1113)), B_1112, C_1113)='#skF_2'(a_2_0_orders_2(B_1112, C_1113)) | ~m1_subset_1(C_1113, k1_zfmisc_1(u1_struct_0(B_1112))) | ~l1_orders_2(B_1112) | ~v5_orders_2(B_1112) | ~v4_orders_2(B_1112) | ~v3_orders_2(B_1112) | v2_struct_0(B_1112) | a_2_0_orders_2(B_1112, C_1113)=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_819])).
% 16.72/8.47  tff(c_30702, plain, (![C_1113]: ('#skF_3'('#skF_2'(a_2_0_orders_2('#skF_5', C_1113)), '#skF_5', C_1113)='#skF_2'(a_2_0_orders_2('#skF_5', C_1113)) | ~m1_subset_1(C_1113, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5') | a_2_0_orders_2('#skF_5', C_1113)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_89, c_30683])).
% 16.72/8.47  tff(c_30713, plain, (![C_1113]: ('#skF_3'('#skF_2'(a_2_0_orders_2('#skF_5', C_1113)), '#skF_5', C_1113)='#skF_2'(a_2_0_orders_2('#skF_5', C_1113)) | ~m1_subset_1(C_1113, k1_zfmisc_1(k2_struct_0('#skF_5'))) | v2_struct_0('#skF_5') | a_2_0_orders_2('#skF_5', C_1113)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_60, c_30702])).
% 16.72/8.47  tff(c_31280, plain, (![C_1127]: ('#skF_3'('#skF_2'(a_2_0_orders_2('#skF_5', C_1127)), '#skF_5', C_1127)='#skF_2'(a_2_0_orders_2('#skF_5', C_1127)) | ~m1_subset_1(C_1127, k1_zfmisc_1(k2_struct_0('#skF_5'))) | a_2_0_orders_2('#skF_5', C_1127)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_68, c_30713])).
% 16.72/8.47  tff(c_31297, plain, ('#skF_3'('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), '#skF_5', k2_struct_0('#skF_5'))='#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))) | a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))=k1_xboole_0), inference(resolution, [status(thm)], [c_27524, c_31280])).
% 16.72/8.47  tff(c_31321, plain, ('#skF_3'('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), '#skF_5', k2_struct_0('#skF_5'))='#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_697, c_31297])).
% 16.72/8.47  tff(c_16, plain, (![A_9]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 16.72/8.47  tff(c_656, plain, (k1_orders_2('#skF_5', k1_xboole_0)=a_2_0_orders_2('#skF_5', k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_636])).
% 16.72/8.47  tff(c_716, plain, (m1_subset_1(a_2_0_orders_2('#skF_5', k1_xboole_0), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_656, c_702])).
% 16.72/8.47  tff(c_727, plain, (m1_subset_1(a_2_0_orders_2('#skF_5', k1_xboole_0), k1_zfmisc_1(k2_struct_0('#skF_5'))) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_60, c_16, c_89, c_716])).
% 16.72/8.47  tff(c_728, plain, (m1_subset_1(a_2_0_orders_2('#skF_5', k1_xboole_0), k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_68, c_727])).
% 16.72/8.47  tff(c_18, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | ~m1_subset_1(A_10, k1_zfmisc_1(B_11)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 16.72/8.47  tff(c_742, plain, (r1_tarski(a_2_0_orders_2('#skF_5', k1_xboole_0), k2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_728, c_18])).
% 16.72/8.47  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 16.72/8.47  tff(c_760, plain, (a_2_0_orders_2('#skF_5', k1_xboole_0)=k2_struct_0('#skF_5') | ~r1_tarski(k2_struct_0('#skF_5'), a_2_0_orders_2('#skF_5', k1_xboole_0))), inference(resolution, [status(thm)], [c_742, c_8])).
% 16.72/8.47  tff(c_941, plain, (~r1_tarski(k2_struct_0('#skF_5'), a_2_0_orders_2('#skF_5', k1_xboole_0))), inference(splitLeft, [status(thm)], [c_760])).
% 16.72/8.47  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 16.72/8.47  tff(c_3105, plain, (~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(splitLeft, [status(thm)], [c_725])).
% 16.72/8.47  tff(c_3108, plain, (~r1_tarski(k2_struct_0('#skF_5'), k2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_20, c_3105])).
% 16.72/8.47  tff(c_3112, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_3108])).
% 16.72/8.47  tff(c_3114, plain, (m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_725])).
% 16.72/8.47  tff(c_3164, plain, (![A_309]: (m1_subset_1(A_309, k2_struct_0('#skF_5')) | ~r2_hidden(A_309, k2_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_3114, c_22])).
% 16.72/8.47  tff(c_3183, plain, (![B_2]: (m1_subset_1('#skF_1'(k2_struct_0('#skF_5'), B_2), k2_struct_0('#skF_5')) | r1_tarski(k2_struct_0('#skF_5'), B_2))), inference(resolution, [status(thm)], [c_6, c_3164])).
% 16.72/8.47  tff(c_14, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 16.72/8.47  tff(c_3015, plain, (![D_299, B_300, C_301]: (r2_hidden('#skF_4'(D_299, B_300, C_301, D_299), C_301) | r2_hidden(D_299, a_2_0_orders_2(B_300, C_301)) | ~m1_subset_1(D_299, u1_struct_0(B_300)) | ~m1_subset_1(C_301, k1_zfmisc_1(u1_struct_0(B_300))) | ~l1_orders_2(B_300) | ~v5_orders_2(B_300) | ~v4_orders_2(B_300) | ~v3_orders_2(B_300) | v2_struct_0(B_300))), inference(cnfTransformation, [status(thm)], [f_154])).
% 16.72/8.47  tff(c_3028, plain, (![D_299, C_301]: (r2_hidden('#skF_4'(D_299, '#skF_5', C_301, D_299), C_301) | r2_hidden(D_299, a_2_0_orders_2('#skF_5', C_301)) | ~m1_subset_1(D_299, u1_struct_0('#skF_5')) | ~m1_subset_1(C_301, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_89, c_3015])).
% 16.72/8.47  tff(c_3037, plain, (![D_299, C_301]: (r2_hidden('#skF_4'(D_299, '#skF_5', C_301, D_299), C_301) | r2_hidden(D_299, a_2_0_orders_2('#skF_5', C_301)) | ~m1_subset_1(D_299, k2_struct_0('#skF_5')) | ~m1_subset_1(C_301, k1_zfmisc_1(k2_struct_0('#skF_5'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_60, c_89, c_3028])).
% 16.72/8.47  tff(c_3504, plain, (![D_333, C_334]: (r2_hidden('#skF_4'(D_333, '#skF_5', C_334, D_333), C_334) | r2_hidden(D_333, a_2_0_orders_2('#skF_5', C_334)) | ~m1_subset_1(D_333, k2_struct_0('#skF_5')) | ~m1_subset_1(C_334, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_68, c_3037])).
% 16.72/8.47  tff(c_25981, plain, (![D_919]: (r2_hidden('#skF_4'(D_919, '#skF_5', k1_xboole_0, D_919), k1_xboole_0) | r2_hidden(D_919, a_2_0_orders_2('#skF_5', k1_xboole_0)) | ~m1_subset_1(D_919, k2_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_16, c_3504])).
% 16.72/8.47  tff(c_24, plain, (![B_16, A_15]: (~r1_tarski(B_16, A_15) | ~r2_hidden(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_57])).
% 16.72/8.47  tff(c_26003, plain, (![D_919]: (~r1_tarski(k1_xboole_0, '#skF_4'(D_919, '#skF_5', k1_xboole_0, D_919)) | r2_hidden(D_919, a_2_0_orders_2('#skF_5', k1_xboole_0)) | ~m1_subset_1(D_919, k2_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_25981, c_24])).
% 16.72/8.47  tff(c_26025, plain, (![D_920]: (r2_hidden(D_920, a_2_0_orders_2('#skF_5', k1_xboole_0)) | ~m1_subset_1(D_920, k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_26003])).
% 16.72/8.47  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 16.72/8.47  tff(c_27377, plain, (![A_964]: (r1_tarski(A_964, a_2_0_orders_2('#skF_5', k1_xboole_0)) | ~m1_subset_1('#skF_1'(A_964, a_2_0_orders_2('#skF_5', k1_xboole_0)), k2_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_26025, c_4])).
% 16.72/8.47  tff(c_27461, plain, (r1_tarski(k2_struct_0('#skF_5'), a_2_0_orders_2('#skF_5', k1_xboole_0))), inference(resolution, [status(thm)], [c_3183, c_27377])).
% 16.72/8.47  tff(c_27474, plain, $false, inference(negUnitSimplification, [status(thm)], [c_941, c_941, c_27461])).
% 16.72/8.47  tff(c_27475, plain, (a_2_0_orders_2('#skF_5', k1_xboole_0)=k2_struct_0('#skF_5')), inference(splitRight, [status(thm)], [c_760])).
% 16.72/8.47  tff(c_586, plain, (![B_156]: (k1_orders_2('#skF_5', B_156)=a_2_0_orders_2('#skF_5', B_156) | ~m1_subset_1(B_156, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_68, c_585])).
% 16.72/8.47  tff(c_740, plain, (k1_orders_2('#skF_5', a_2_0_orders_2('#skF_5', k1_xboole_0))=a_2_0_orders_2('#skF_5', a_2_0_orders_2('#skF_5', k1_xboole_0))), inference(resolution, [status(thm)], [c_728, c_586])).
% 16.72/8.47  tff(c_719, plain, (![B_169]: (m1_subset_1(k1_orders_2('#skF_5', B_169), k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(B_169, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_89, c_702])).
% 16.72/8.47  tff(c_730, plain, (![B_169]: (m1_subset_1(k1_orders_2('#skF_5', B_169), k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(B_169, k1_zfmisc_1(k2_struct_0('#skF_5'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_60, c_89, c_719])).
% 16.72/8.47  tff(c_731, plain, (![B_169]: (m1_subset_1(k1_orders_2('#skF_5', B_169), k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(B_169, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_68, c_730])).
% 16.72/8.47  tff(c_839, plain, (m1_subset_1(a_2_0_orders_2('#skF_5', a_2_0_orders_2('#skF_5', k1_xboole_0)), k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(a_2_0_orders_2('#skF_5', k1_xboole_0), k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_740, c_731])).
% 16.72/8.47  tff(c_846, plain, (m1_subset_1(a_2_0_orders_2('#skF_5', a_2_0_orders_2('#skF_5', k1_xboole_0)), k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_728, c_839])).
% 16.72/8.47  tff(c_861, plain, (r1_tarski(a_2_0_orders_2('#skF_5', a_2_0_orders_2('#skF_5', k1_xboole_0)), k2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_846, c_18])).
% 16.72/8.47  tff(c_27525, plain, (r1_tarski(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5')), k2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_27475, c_861])).
% 16.72/8.47  tff(c_161, plain, (![A_88, B_89]: (r2_hidden('#skF_2'(A_88), B_89) | ~r1_tarski(A_88, B_89) | k1_xboole_0=A_88)), inference(resolution, [status(thm)], [c_26, c_154])).
% 16.72/8.47  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 16.72/8.47  tff(c_27754, plain, (![A_980, B_981, B_982]: (r2_hidden('#skF_2'(A_980), B_981) | ~r1_tarski(B_982, B_981) | ~r1_tarski(A_980, B_982) | k1_xboole_0=A_980)), inference(resolution, [status(thm)], [c_161, c_2])).
% 16.72/8.47  tff(c_27767, plain, (![A_980]: (r2_hidden('#skF_2'(A_980), k2_struct_0('#skF_5')) | ~r1_tarski(A_980, a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))) | k1_xboole_0=A_980)), inference(resolution, [status(thm)], [c_27525, c_27754])).
% 16.72/8.47  tff(c_54, plain, (![A_49, B_50, C_51]: ('#skF_3'(A_49, B_50, C_51)=A_49 | ~r2_hidden(A_49, a_2_0_orders_2(B_50, C_51)) | ~m1_subset_1(C_51, k1_zfmisc_1(u1_struct_0(B_50))) | ~l1_orders_2(B_50) | ~v5_orders_2(B_50) | ~v4_orders_2(B_50) | ~v3_orders_2(B_50) | v2_struct_0(B_50))), inference(cnfTransformation, [status(thm)], [f_154])).
% 16.72/8.47  tff(c_27536, plain, (![A_49]: ('#skF_3'(A_49, '#skF_5', k1_xboole_0)=A_49 | ~r2_hidden(A_49, k2_struct_0('#skF_5')) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_27475, c_54])).
% 16.72/8.47  tff(c_27540, plain, (![A_49]: ('#skF_3'(A_49, '#skF_5', k1_xboole_0)=A_49 | ~r2_hidden(A_49, k2_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_60, c_16, c_89, c_27536])).
% 16.72/8.47  tff(c_27692, plain, (![A_972]: ('#skF_3'(A_972, '#skF_5', k1_xboole_0)=A_972 | ~r2_hidden(A_972, k2_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_68, c_27540])).
% 16.72/8.47  tff(c_28376, plain, (![A_1028]: ('#skF_3'('#skF_2'(A_1028), '#skF_5', k1_xboole_0)='#skF_2'(A_1028) | ~r1_tarski(A_1028, k2_struct_0('#skF_5')) | k1_xboole_0=A_1028)), inference(resolution, [status(thm)], [c_160, c_27692])).
% 16.72/8.47  tff(c_28386, plain, ('#skF_3'('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), '#skF_5', k1_xboole_0)='#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))) | a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))=k1_xboole_0), inference(resolution, [status(thm)], [c_27525, c_28376])).
% 16.72/8.47  tff(c_28410, plain, ('#skF_3'('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), '#skF_5', k1_xboole_0)='#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_697, c_28386])).
% 16.72/8.47  tff(c_27881, plain, (![B_989, E_990, A_991, C_992]: (r2_orders_2(B_989, E_990, '#skF_3'(A_991, B_989, C_992)) | ~r2_hidden(E_990, C_992) | ~m1_subset_1(E_990, u1_struct_0(B_989)) | ~r2_hidden(A_991, a_2_0_orders_2(B_989, C_992)) | ~m1_subset_1(C_992, k1_zfmisc_1(u1_struct_0(B_989))) | ~l1_orders_2(B_989) | ~v5_orders_2(B_989) | ~v4_orders_2(B_989) | ~v3_orders_2(B_989) | v2_struct_0(B_989))), inference(cnfTransformation, [status(thm)], [f_154])).
% 16.72/8.47  tff(c_31711, plain, (![B_1147, E_1148, A_1149, A_1150]: (r2_orders_2(B_1147, E_1148, '#skF_3'(A_1149, B_1147, A_1150)) | ~r2_hidden(E_1148, A_1150) | ~m1_subset_1(E_1148, u1_struct_0(B_1147)) | ~r2_hidden(A_1149, a_2_0_orders_2(B_1147, A_1150)) | ~l1_orders_2(B_1147) | ~v5_orders_2(B_1147) | ~v4_orders_2(B_1147) | ~v3_orders_2(B_1147) | v2_struct_0(B_1147) | ~r1_tarski(A_1150, u1_struct_0(B_1147)))), inference(resolution, [status(thm)], [c_20, c_27881])).
% 16.72/8.47  tff(c_31722, plain, (![E_1148]: (r2_orders_2('#skF_5', E_1148, '#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5')))) | ~r2_hidden(E_1148, k1_xboole_0) | ~m1_subset_1(E_1148, u1_struct_0('#skF_5')) | ~r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), a_2_0_orders_2('#skF_5', k1_xboole_0)) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5') | ~r1_tarski(k1_xboole_0, u1_struct_0('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_28410, c_31711])).
% 16.72/8.47  tff(c_31730, plain, (![E_1148]: (r2_orders_2('#skF_5', E_1148, '#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5')))) | ~r2_hidden(E_1148, k1_xboole_0) | ~m1_subset_1(E_1148, k2_struct_0('#skF_5')) | ~r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), k2_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_89, c_66, c_64, c_62, c_60, c_27475, c_89, c_31722])).
% 16.72/8.47  tff(c_31731, plain, (![E_1148]: (r2_orders_2('#skF_5', E_1148, '#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5')))) | ~r2_hidden(E_1148, k1_xboole_0) | ~m1_subset_1(E_1148, k2_struct_0('#skF_5')) | ~r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), k2_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_68, c_31730])).
% 16.72/8.47  tff(c_33756, plain, (~r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), k2_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_31731])).
% 16.72/8.47  tff(c_33759, plain, (~r1_tarski(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5')), a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))) | a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))=k1_xboole_0), inference(resolution, [status(thm)], [c_27767, c_33756])).
% 16.72/8.47  tff(c_33765, plain, (a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_12, c_33759])).
% 16.72/8.47  tff(c_33767, plain, $false, inference(negUnitSimplification, [status(thm)], [c_697, c_33765])).
% 16.72/8.47  tff(c_33769, plain, (r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), k2_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_31731])).
% 16.72/8.47  tff(c_36, plain, (![A_36, C_42]: (~r2_orders_2(A_36, C_42, C_42) | ~m1_subset_1(C_42, u1_struct_0(A_36)) | ~l1_orders_2(A_36))), inference(cnfTransformation, [status(thm)], [f_92])).
% 16.72/8.47  tff(c_45645, plain, (![A_1558, B_1559, A_1560]: (~r2_hidden('#skF_3'(A_1558, B_1559, A_1560), A_1560) | ~m1_subset_1('#skF_3'(A_1558, B_1559, A_1560), u1_struct_0(B_1559)) | ~r2_hidden(A_1558, a_2_0_orders_2(B_1559, A_1560)) | ~l1_orders_2(B_1559) | ~v5_orders_2(B_1559) | ~v4_orders_2(B_1559) | ~v3_orders_2(B_1559) | v2_struct_0(B_1559) | ~r1_tarski(A_1560, u1_struct_0(B_1559)))), inference(resolution, [status(thm)], [c_31711, c_36])).
% 16.72/8.47  tff(c_45667, plain, (~r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), k2_struct_0('#skF_5')) | ~m1_subset_1('#skF_3'('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), '#skF_5', k2_struct_0('#skF_5')), u1_struct_0('#skF_5')) | ~r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5') | ~r1_tarski(k2_struct_0('#skF_5'), u1_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_31321, c_45645])).
% 16.72/8.47  tff(c_45686, plain, (~r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_89, c_66, c_64, c_62, c_60, c_27738, c_89, c_31321, c_33769, c_45667])).
% 16.72/8.47  tff(c_45687, plain, (~r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_68, c_45686])).
% 16.72/8.47  tff(c_45696, plain, (~r1_tarski(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5')), a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))) | a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))=k1_xboole_0), inference(resolution, [status(thm)], [c_160, c_45687])).
% 16.72/8.47  tff(c_45703, plain, (a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_12, c_45696])).
% 16.72/8.47  tff(c_45705, plain, $false, inference(negUnitSimplification, [status(thm)], [c_697, c_45703])).
% 16.72/8.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.72/8.47  
% 16.72/8.47  Inference rules
% 16.72/8.47  ----------------------
% 16.72/8.47  #Ref     : 0
% 16.72/8.47  #Sup     : 10998
% 16.72/8.47  #Fact    : 0
% 16.72/8.47  #Define  : 0
% 16.72/8.47  #Split   : 57
% 16.72/8.47  #Chain   : 0
% 16.72/8.47  #Close   : 0
% 16.72/8.47  
% 16.72/8.47  Ordering : KBO
% 16.72/8.47  
% 16.72/8.47  Simplification rules
% 16.72/8.47  ----------------------
% 16.72/8.47  #Subsume      : 4895
% 16.72/8.47  #Demod        : 5993
% 16.72/8.47  #Tautology    : 1529
% 16.72/8.47  #SimpNegUnit  : 709
% 16.72/8.47  #BackRed      : 191
% 16.72/8.47  
% 16.72/8.47  #Partial instantiations: 0
% 16.72/8.47  #Strategies tried      : 1
% 16.72/8.47  
% 16.72/8.47  Timing (in seconds)
% 16.72/8.47  ----------------------
% 16.72/8.47  Preprocessing        : 0.35
% 16.72/8.47  Parsing              : 0.18
% 16.72/8.47  CNF conversion       : 0.03
% 16.72/8.47  Main loop            : 7.36
% 16.72/8.47  Inferencing          : 1.50
% 16.72/8.47  Reduction            : 2.09
% 16.72/8.48  Demodulation         : 1.41
% 16.72/8.48  BG Simplification    : 0.14
% 16.72/8.48  Subsumption          : 3.16
% 16.72/8.48  Abstraction          : 0.24
% 16.72/8.48  MUC search           : 0.00
% 16.72/8.48  Cooper               : 0.00
% 16.72/8.48  Total                : 7.76
% 16.72/8.48  Index Insertion      : 0.00
% 16.72/8.48  Index Deletion       : 0.00
% 16.72/8.48  Index Matching       : 0.00
% 16.72/8.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
