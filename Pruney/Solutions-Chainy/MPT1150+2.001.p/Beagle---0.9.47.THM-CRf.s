%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:23 EST 2020

% Result     : Theorem 5.60s
% Output     : CNFRefutation 5.71s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 436 expanded)
%              Number of leaves         :   40 ( 177 expanded)
%              Depth                    :   17
%              Number of atoms          :  247 (1295 expanded)
%              Number of equality atoms :   32 ( 212 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_struct_0 > l1_orders_2 > k4_tarski > k1_orders_2 > a_2_0_orders_2 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

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

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_163,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => k1_orders_2(A,k2_struct_0(A)) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_orders_2)).

tff(f_109,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_74,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_105,axiom,(
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

tff(f_66,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_136,axiom,(
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

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_70,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k1_struct_0(A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_struct_0)).

tff(f_149,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => k1_orders_2(A,k1_struct_0(A)) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_orders_2)).

tff(f_35,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_89,axiom,(
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

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_62,plain,(
    v3_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_60,plain,(
    v4_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_58,plain,(
    v5_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_56,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_38,plain,(
    ! [A_34] :
      ( l1_struct_0(A_34)
      | ~ l1_orders_2(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_85,plain,(
    ! [A_57] :
      ( u1_struct_0(A_57) = k2_struct_0(A_57)
      | ~ l1_struct_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_95,plain,(
    ! [A_59] :
      ( u1_struct_0(A_59) = k2_struct_0(A_59)
      | ~ l1_orders_2(A_59) ) ),
    inference(resolution,[status(thm)],[c_38,c_85])).

tff(c_99,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_95])).

tff(c_417,plain,(
    ! [A_118,B_119] :
      ( k1_orders_2(A_118,B_119) = a_2_0_orders_2(A_118,B_119)
      | ~ m1_subset_1(B_119,k1_zfmisc_1(u1_struct_0(A_118)))
      | ~ l1_orders_2(A_118)
      | ~ v5_orders_2(A_118)
      | ~ v4_orders_2(A_118)
      | ~ v3_orders_2(A_118)
      | v2_struct_0(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_432,plain,(
    ! [B_119] :
      ( k1_orders_2('#skF_4',B_119) = a_2_0_orders_2('#skF_4',B_119)
      | ~ m1_subset_1(B_119,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_417])).

tff(c_441,plain,(
    ! [B_119] :
      ( k1_orders_2('#skF_4',B_119) = a_2_0_orders_2('#skF_4',B_119)
      | ~ m1_subset_1(B_119,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_56,c_432])).

tff(c_444,plain,(
    ! [B_120] :
      ( k1_orders_2('#skF_4',B_120) = a_2_0_orders_2('#skF_4',B_120)
      | ~ m1_subset_1(B_120,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_441])).

tff(c_470,plain,(
    ! [A_121] :
      ( k1_orders_2('#skF_4',A_121) = a_2_0_orders_2('#skF_4',A_121)
      | ~ r1_tarski(A_121,k2_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_14,c_444])).

tff(c_489,plain,(
    k1_orders_2('#skF_4',k2_struct_0('#skF_4')) = a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_6,c_470])).

tff(c_54,plain,(
    k1_orders_2('#skF_4',k2_struct_0('#skF_4')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_514,plain,(
    a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_489,c_54])).

tff(c_20,plain,(
    ! [A_12] :
      ( r2_hidden('#skF_1'(A_12),A_12)
      | k1_xboole_0 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_713,plain,(
    ! [A_139,B_140,C_141] :
      ( m1_subset_1('#skF_2'(A_139,B_140,C_141),u1_struct_0(B_140))
      | ~ r2_hidden(A_139,a_2_0_orders_2(B_140,C_141))
      | ~ m1_subset_1(C_141,k1_zfmisc_1(u1_struct_0(B_140)))
      | ~ l1_orders_2(B_140)
      | ~ v5_orders_2(B_140)
      | ~ v4_orders_2(B_140)
      | ~ v3_orders_2(B_140)
      | v2_struct_0(B_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_721,plain,(
    ! [A_139,C_141] :
      ( m1_subset_1('#skF_2'(A_139,'#skF_4',C_141),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_139,a_2_0_orders_2('#skF_4',C_141))
      | ~ m1_subset_1(C_141,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_713])).

tff(c_727,plain,(
    ! [A_139,C_141] :
      ( m1_subset_1('#skF_2'(A_139,'#skF_4',C_141),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_139,a_2_0_orders_2('#skF_4',C_141))
      | ~ m1_subset_1(C_141,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_56,c_99,c_721])).

tff(c_728,plain,(
    ! [A_139,C_141] :
      ( m1_subset_1('#skF_2'(A_139,'#skF_4',C_141),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_139,a_2_0_orders_2('#skF_4',C_141))
      | ~ m1_subset_1(C_141,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_727])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_70,plain,(
    ! [A_53] :
      ( k1_struct_0(A_53) = k1_xboole_0
      | ~ l1_struct_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_75,plain,(
    ! [A_54] :
      ( k1_struct_0(A_54) = k1_xboole_0
      | ~ l1_orders_2(A_54) ) ),
    inference(resolution,[status(thm)],[c_38,c_70])).

tff(c_79,plain,(
    k1_struct_0('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_56,c_75])).

tff(c_215,plain,(
    ! [A_93] :
      ( k1_orders_2(A_93,k1_struct_0(A_93)) = u1_struct_0(A_93)
      | ~ l1_orders_2(A_93)
      | ~ v5_orders_2(A_93)
      | ~ v4_orders_2(A_93)
      | ~ v3_orders_2(A_93)
      | v2_struct_0(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_224,plain,
    ( k1_orders_2('#skF_4',k1_xboole_0) = u1_struct_0('#skF_4')
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_215])).

tff(c_228,plain,
    ( k1_orders_2('#skF_4',k1_xboole_0) = k2_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_56,c_99,c_224])).

tff(c_229,plain,(
    k1_orders_2('#skF_4',k1_xboole_0) = k2_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_228])).

tff(c_10,plain,(
    ! [A_4] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_460,plain,(
    k1_orders_2('#skF_4',k1_xboole_0) = a_2_0_orders_2('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10,c_444])).

tff(c_465,plain,(
    a_2_0_orders_2('#skF_4',k1_xboole_0) = k2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_460])).

tff(c_780,plain,(
    ! [D_146,B_147,C_148] :
      ( r2_hidden('#skF_3'(D_146,B_147,C_148,D_146),C_148)
      | r2_hidden(D_146,a_2_0_orders_2(B_147,C_148))
      | ~ m1_subset_1(D_146,u1_struct_0(B_147))
      | ~ m1_subset_1(C_148,k1_zfmisc_1(u1_struct_0(B_147)))
      | ~ l1_orders_2(B_147)
      | ~ v5_orders_2(B_147)
      | ~ v4_orders_2(B_147)
      | ~ v3_orders_2(B_147)
      | v2_struct_0(B_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_791,plain,(
    ! [D_146,C_148] :
      ( r2_hidden('#skF_3'(D_146,'#skF_4',C_148,D_146),C_148)
      | r2_hidden(D_146,a_2_0_orders_2('#skF_4',C_148))
      | ~ m1_subset_1(D_146,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_148,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_780])).

tff(c_799,plain,(
    ! [D_146,C_148] :
      ( r2_hidden('#skF_3'(D_146,'#skF_4',C_148,D_146),C_148)
      | r2_hidden(D_146,a_2_0_orders_2('#skF_4',C_148))
      | ~ m1_subset_1(D_146,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(C_148,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_56,c_99,c_791])).

tff(c_842,plain,(
    ! [D_150,C_151] :
      ( r2_hidden('#skF_3'(D_150,'#skF_4',C_151,D_150),C_151)
      | r2_hidden(D_150,a_2_0_orders_2('#skF_4',C_151))
      | ~ m1_subset_1(D_150,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(C_151,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_799])).

tff(c_857,plain,(
    ! [D_150] :
      ( r2_hidden('#skF_3'(D_150,'#skF_4',k1_xboole_0,D_150),k1_xboole_0)
      | r2_hidden(D_150,a_2_0_orders_2('#skF_4',k1_xboole_0))
      | ~ m1_subset_1(D_150,k2_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_10,c_842])).

tff(c_957,plain,(
    ! [D_159] :
      ( r2_hidden('#skF_3'(D_159,'#skF_4',k1_xboole_0,D_159),k1_xboole_0)
      | r2_hidden(D_159,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(D_159,k2_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_465,c_857])).

tff(c_18,plain,(
    ! [B_11,A_10] :
      ( ~ r1_tarski(B_11,A_10)
      | ~ r2_hidden(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_971,plain,(
    ! [D_159] :
      ( ~ r1_tarski(k1_xboole_0,'#skF_3'(D_159,'#skF_4',k1_xboole_0,D_159))
      | r2_hidden(D_159,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(D_159,k2_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_957,c_18])).

tff(c_985,plain,(
    ! [D_159] :
      ( r2_hidden(D_159,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(D_159,k2_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_971])).

tff(c_1181,plain,(
    ! [B_175,E_176,A_177,C_178] :
      ( r2_orders_2(B_175,E_176,'#skF_2'(A_177,B_175,C_178))
      | ~ r2_hidden(E_176,C_178)
      | ~ m1_subset_1(E_176,u1_struct_0(B_175))
      | ~ r2_hidden(A_177,a_2_0_orders_2(B_175,C_178))
      | ~ m1_subset_1(C_178,k1_zfmisc_1(u1_struct_0(B_175)))
      | ~ l1_orders_2(B_175)
      | ~ v5_orders_2(B_175)
      | ~ v4_orders_2(B_175)
      | ~ v3_orders_2(B_175)
      | v2_struct_0(B_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1192,plain,(
    ! [E_176,A_177,C_178] :
      ( r2_orders_2('#skF_4',E_176,'#skF_2'(A_177,'#skF_4',C_178))
      | ~ r2_hidden(E_176,C_178)
      | ~ m1_subset_1(E_176,u1_struct_0('#skF_4'))
      | ~ r2_hidden(A_177,a_2_0_orders_2('#skF_4',C_178))
      | ~ m1_subset_1(C_178,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_1181])).

tff(c_1200,plain,(
    ! [E_176,A_177,C_178] :
      ( r2_orders_2('#skF_4',E_176,'#skF_2'(A_177,'#skF_4',C_178))
      | ~ r2_hidden(E_176,C_178)
      | ~ m1_subset_1(E_176,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_177,a_2_0_orders_2('#skF_4',C_178))
      | ~ m1_subset_1(C_178,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_56,c_99,c_1192])).

tff(c_1231,plain,(
    ! [E_181,A_182,C_183] :
      ( r2_orders_2('#skF_4',E_181,'#skF_2'(A_182,'#skF_4',C_183))
      | ~ r2_hidden(E_181,C_183)
      | ~ m1_subset_1(E_181,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_182,a_2_0_orders_2('#skF_4',C_183))
      | ~ m1_subset_1(C_183,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1200])).

tff(c_2654,plain,(
    ! [E_270,A_271,A_272] :
      ( r2_orders_2('#skF_4',E_270,'#skF_2'(A_271,'#skF_4',A_272))
      | ~ r2_hidden(E_270,A_272)
      | ~ m1_subset_1(E_270,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_271,a_2_0_orders_2('#skF_4',A_272))
      | ~ r1_tarski(A_272,k2_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_14,c_1231])).

tff(c_32,plain,(
    ! [A_24,C_30] :
      ( ~ r2_orders_2(A_24,C_30,C_30)
      | ~ m1_subset_1(C_30,u1_struct_0(A_24))
      | ~ l1_orders_2(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2662,plain,(
    ! [A_271,A_272] :
      ( ~ m1_subset_1('#skF_2'(A_271,'#skF_4',A_272),u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ r2_hidden('#skF_2'(A_271,'#skF_4',A_272),A_272)
      | ~ m1_subset_1('#skF_2'(A_271,'#skF_4',A_272),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_271,a_2_0_orders_2('#skF_4',A_272))
      | ~ r1_tarski(A_272,k2_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_2654,c_32])).

tff(c_2686,plain,(
    ! [A_273,A_274] :
      ( ~ r2_hidden('#skF_2'(A_273,'#skF_4',A_274),A_274)
      | ~ m1_subset_1('#skF_2'(A_273,'#skF_4',A_274),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_273,a_2_0_orders_2('#skF_4',A_274))
      | ~ r1_tarski(A_274,k2_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_99,c_2662])).

tff(c_2698,plain,(
    ! [A_273] :
      ( ~ r2_hidden(A_273,a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')))
      | ~ r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_2'(A_273,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_985,c_2686])).

tff(c_2831,plain,(
    ! [A_276] :
      ( ~ r2_hidden(A_276,a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')))
      | ~ m1_subset_1('#skF_2'(A_276,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2698])).

tff(c_2843,plain,(
    ! [A_139] :
      ( ~ r2_hidden(A_139,a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')))
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_728,c_2831])).

tff(c_2844,plain,(
    ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_2843])).

tff(c_2847,plain,(
    ~ r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_14,c_2844])).

tff(c_2851,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2847])).

tff(c_2862,plain,(
    ! [A_278] : ~ r2_hidden(A_278,a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_2843])).

tff(c_2874,plain,(
    a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_2862])).

tff(c_2880,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_514,c_2874])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:09:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.60/2.06  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.60/2.07  
% 5.60/2.07  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.60/2.07  %$ r2_orders_2 > r1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_struct_0 > l1_orders_2 > k4_tarski > k1_orders_2 > a_2_0_orders_2 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_4 > #skF_3
% 5.60/2.07  
% 5.60/2.07  %Foreground sorts:
% 5.60/2.07  
% 5.60/2.07  
% 5.60/2.07  %Background operators:
% 5.60/2.07  
% 5.60/2.07  
% 5.60/2.07  %Foreground operators:
% 5.60/2.07  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.60/2.07  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 5.60/2.07  tff(k1_orders_2, type, k1_orders_2: ($i * $i) > $i).
% 5.60/2.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.60/2.07  tff(a_2_0_orders_2, type, a_2_0_orders_2: ($i * $i) > $i).
% 5.60/2.07  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.60/2.07  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.60/2.07  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.60/2.07  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 5.60/2.07  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.60/2.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.60/2.07  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.60/2.07  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 5.60/2.07  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 5.60/2.07  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.60/2.07  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.60/2.07  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 5.60/2.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.60/2.07  tff('#skF_4', type, '#skF_4': $i).
% 5.60/2.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.60/2.07  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 5.60/2.07  tff(k1_struct_0, type, k1_struct_0: $i > $i).
% 5.60/2.07  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 5.60/2.07  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.60/2.07  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 5.60/2.07  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.60/2.07  
% 5.71/2.09  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.71/2.09  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.71/2.09  tff(f_163, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (k1_orders_2(A, k2_struct_0(A)) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_orders_2)).
% 5.71/2.09  tff(f_109, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 5.71/2.09  tff(f_74, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 5.71/2.09  tff(f_105, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_orders_2(A, B) = a_2_0_orders_2(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_orders_2)).
% 5.71/2.09  tff(f_66, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_mcart_1)).
% 5.71/2.09  tff(f_136, axiom, (![A, B, C]: ((((((~v2_struct_0(B) & v3_orders_2(B)) & v4_orders_2(B)) & v5_orders_2(B)) & l1_orders_2(B)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B)))) => (r2_hidden(A, a_2_0_orders_2(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r2_hidden(E, C) => r2_orders_2(B, E, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_0_orders_2)).
% 5.71/2.09  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.71/2.09  tff(f_70, axiom, (![A]: (l1_struct_0(A) => (k1_struct_0(A) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_struct_0)).
% 5.71/2.09  tff(f_149, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (k1_orders_2(A, k1_struct_0(A)) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_orders_2)).
% 5.71/2.09  tff(f_35, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 5.71/2.09  tff(f_50, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 5.71/2.09  tff(f_89, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_orders_2(A, B, C) <=> (r1_orders_2(A, B, C) & ~(B = C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_orders_2)).
% 5.71/2.09  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.71/2.09  tff(c_14, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.71/2.09  tff(c_64, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_163])).
% 5.71/2.09  tff(c_62, plain, (v3_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_163])).
% 5.71/2.09  tff(c_60, plain, (v4_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_163])).
% 5.71/2.09  tff(c_58, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_163])).
% 5.71/2.09  tff(c_56, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_163])).
% 5.71/2.09  tff(c_38, plain, (![A_34]: (l1_struct_0(A_34) | ~l1_orders_2(A_34))), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.71/2.09  tff(c_85, plain, (![A_57]: (u1_struct_0(A_57)=k2_struct_0(A_57) | ~l1_struct_0(A_57))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.71/2.09  tff(c_95, plain, (![A_59]: (u1_struct_0(A_59)=k2_struct_0(A_59) | ~l1_orders_2(A_59))), inference(resolution, [status(thm)], [c_38, c_85])).
% 5.71/2.09  tff(c_99, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_56, c_95])).
% 5.71/2.09  tff(c_417, plain, (![A_118, B_119]: (k1_orders_2(A_118, B_119)=a_2_0_orders_2(A_118, B_119) | ~m1_subset_1(B_119, k1_zfmisc_1(u1_struct_0(A_118))) | ~l1_orders_2(A_118) | ~v5_orders_2(A_118) | ~v4_orders_2(A_118) | ~v3_orders_2(A_118) | v2_struct_0(A_118))), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.71/2.09  tff(c_432, plain, (![B_119]: (k1_orders_2('#skF_4', B_119)=a_2_0_orders_2('#skF_4', B_119) | ~m1_subset_1(B_119, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_99, c_417])).
% 5.71/2.09  tff(c_441, plain, (![B_119]: (k1_orders_2('#skF_4', B_119)=a_2_0_orders_2('#skF_4', B_119) | ~m1_subset_1(B_119, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_56, c_432])).
% 5.71/2.09  tff(c_444, plain, (![B_120]: (k1_orders_2('#skF_4', B_120)=a_2_0_orders_2('#skF_4', B_120) | ~m1_subset_1(B_120, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_441])).
% 5.71/2.09  tff(c_470, plain, (![A_121]: (k1_orders_2('#skF_4', A_121)=a_2_0_orders_2('#skF_4', A_121) | ~r1_tarski(A_121, k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_14, c_444])).
% 5.71/2.09  tff(c_489, plain, (k1_orders_2('#skF_4', k2_struct_0('#skF_4'))=a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_6, c_470])).
% 5.71/2.09  tff(c_54, plain, (k1_orders_2('#skF_4', k2_struct_0('#skF_4'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_163])).
% 5.71/2.09  tff(c_514, plain, (a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_489, c_54])).
% 5.71/2.09  tff(c_20, plain, (![A_12]: (r2_hidden('#skF_1'(A_12), A_12) | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.71/2.09  tff(c_713, plain, (![A_139, B_140, C_141]: (m1_subset_1('#skF_2'(A_139, B_140, C_141), u1_struct_0(B_140)) | ~r2_hidden(A_139, a_2_0_orders_2(B_140, C_141)) | ~m1_subset_1(C_141, k1_zfmisc_1(u1_struct_0(B_140))) | ~l1_orders_2(B_140) | ~v5_orders_2(B_140) | ~v4_orders_2(B_140) | ~v3_orders_2(B_140) | v2_struct_0(B_140))), inference(cnfTransformation, [status(thm)], [f_136])).
% 5.71/2.09  tff(c_721, plain, (![A_139, C_141]: (m1_subset_1('#skF_2'(A_139, '#skF_4', C_141), k2_struct_0('#skF_4')) | ~r2_hidden(A_139, a_2_0_orders_2('#skF_4', C_141)) | ~m1_subset_1(C_141, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_99, c_713])).
% 5.71/2.09  tff(c_727, plain, (![A_139, C_141]: (m1_subset_1('#skF_2'(A_139, '#skF_4', C_141), k2_struct_0('#skF_4')) | ~r2_hidden(A_139, a_2_0_orders_2('#skF_4', C_141)) | ~m1_subset_1(C_141, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_56, c_99, c_721])).
% 5.71/2.09  tff(c_728, plain, (![A_139, C_141]: (m1_subset_1('#skF_2'(A_139, '#skF_4', C_141), k2_struct_0('#skF_4')) | ~r2_hidden(A_139, a_2_0_orders_2('#skF_4', C_141)) | ~m1_subset_1(C_141, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_727])).
% 5.71/2.09  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.71/2.09  tff(c_70, plain, (![A_53]: (k1_struct_0(A_53)=k1_xboole_0 | ~l1_struct_0(A_53))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.71/2.09  tff(c_75, plain, (![A_54]: (k1_struct_0(A_54)=k1_xboole_0 | ~l1_orders_2(A_54))), inference(resolution, [status(thm)], [c_38, c_70])).
% 5.71/2.09  tff(c_79, plain, (k1_struct_0('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_56, c_75])).
% 5.71/2.09  tff(c_215, plain, (![A_93]: (k1_orders_2(A_93, k1_struct_0(A_93))=u1_struct_0(A_93) | ~l1_orders_2(A_93) | ~v5_orders_2(A_93) | ~v4_orders_2(A_93) | ~v3_orders_2(A_93) | v2_struct_0(A_93))), inference(cnfTransformation, [status(thm)], [f_149])).
% 5.71/2.09  tff(c_224, plain, (k1_orders_2('#skF_4', k1_xboole_0)=u1_struct_0('#skF_4') | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_79, c_215])).
% 5.71/2.09  tff(c_228, plain, (k1_orders_2('#skF_4', k1_xboole_0)=k2_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_56, c_99, c_224])).
% 5.71/2.09  tff(c_229, plain, (k1_orders_2('#skF_4', k1_xboole_0)=k2_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_64, c_228])).
% 5.71/2.09  tff(c_10, plain, (![A_4]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.71/2.09  tff(c_460, plain, (k1_orders_2('#skF_4', k1_xboole_0)=a_2_0_orders_2('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_444])).
% 5.71/2.09  tff(c_465, plain, (a_2_0_orders_2('#skF_4', k1_xboole_0)=k2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_229, c_460])).
% 5.71/2.09  tff(c_780, plain, (![D_146, B_147, C_148]: (r2_hidden('#skF_3'(D_146, B_147, C_148, D_146), C_148) | r2_hidden(D_146, a_2_0_orders_2(B_147, C_148)) | ~m1_subset_1(D_146, u1_struct_0(B_147)) | ~m1_subset_1(C_148, k1_zfmisc_1(u1_struct_0(B_147))) | ~l1_orders_2(B_147) | ~v5_orders_2(B_147) | ~v4_orders_2(B_147) | ~v3_orders_2(B_147) | v2_struct_0(B_147))), inference(cnfTransformation, [status(thm)], [f_136])).
% 5.71/2.09  tff(c_791, plain, (![D_146, C_148]: (r2_hidden('#skF_3'(D_146, '#skF_4', C_148, D_146), C_148) | r2_hidden(D_146, a_2_0_orders_2('#skF_4', C_148)) | ~m1_subset_1(D_146, u1_struct_0('#skF_4')) | ~m1_subset_1(C_148, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_99, c_780])).
% 5.71/2.09  tff(c_799, plain, (![D_146, C_148]: (r2_hidden('#skF_3'(D_146, '#skF_4', C_148, D_146), C_148) | r2_hidden(D_146, a_2_0_orders_2('#skF_4', C_148)) | ~m1_subset_1(D_146, k2_struct_0('#skF_4')) | ~m1_subset_1(C_148, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_56, c_99, c_791])).
% 5.71/2.09  tff(c_842, plain, (![D_150, C_151]: (r2_hidden('#skF_3'(D_150, '#skF_4', C_151, D_150), C_151) | r2_hidden(D_150, a_2_0_orders_2('#skF_4', C_151)) | ~m1_subset_1(D_150, k2_struct_0('#skF_4')) | ~m1_subset_1(C_151, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_799])).
% 5.71/2.09  tff(c_857, plain, (![D_150]: (r2_hidden('#skF_3'(D_150, '#skF_4', k1_xboole_0, D_150), k1_xboole_0) | r2_hidden(D_150, a_2_0_orders_2('#skF_4', k1_xboole_0)) | ~m1_subset_1(D_150, k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_10, c_842])).
% 5.71/2.09  tff(c_957, plain, (![D_159]: (r2_hidden('#skF_3'(D_159, '#skF_4', k1_xboole_0, D_159), k1_xboole_0) | r2_hidden(D_159, k2_struct_0('#skF_4')) | ~m1_subset_1(D_159, k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_465, c_857])).
% 5.71/2.09  tff(c_18, plain, (![B_11, A_10]: (~r1_tarski(B_11, A_10) | ~r2_hidden(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.71/2.09  tff(c_971, plain, (![D_159]: (~r1_tarski(k1_xboole_0, '#skF_3'(D_159, '#skF_4', k1_xboole_0, D_159)) | r2_hidden(D_159, k2_struct_0('#skF_4')) | ~m1_subset_1(D_159, k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_957, c_18])).
% 5.71/2.09  tff(c_985, plain, (![D_159]: (r2_hidden(D_159, k2_struct_0('#skF_4')) | ~m1_subset_1(D_159, k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_971])).
% 5.71/2.09  tff(c_1181, plain, (![B_175, E_176, A_177, C_178]: (r2_orders_2(B_175, E_176, '#skF_2'(A_177, B_175, C_178)) | ~r2_hidden(E_176, C_178) | ~m1_subset_1(E_176, u1_struct_0(B_175)) | ~r2_hidden(A_177, a_2_0_orders_2(B_175, C_178)) | ~m1_subset_1(C_178, k1_zfmisc_1(u1_struct_0(B_175))) | ~l1_orders_2(B_175) | ~v5_orders_2(B_175) | ~v4_orders_2(B_175) | ~v3_orders_2(B_175) | v2_struct_0(B_175))), inference(cnfTransformation, [status(thm)], [f_136])).
% 5.71/2.09  tff(c_1192, plain, (![E_176, A_177, C_178]: (r2_orders_2('#skF_4', E_176, '#skF_2'(A_177, '#skF_4', C_178)) | ~r2_hidden(E_176, C_178) | ~m1_subset_1(E_176, u1_struct_0('#skF_4')) | ~r2_hidden(A_177, a_2_0_orders_2('#skF_4', C_178)) | ~m1_subset_1(C_178, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_99, c_1181])).
% 5.71/2.09  tff(c_1200, plain, (![E_176, A_177, C_178]: (r2_orders_2('#skF_4', E_176, '#skF_2'(A_177, '#skF_4', C_178)) | ~r2_hidden(E_176, C_178) | ~m1_subset_1(E_176, k2_struct_0('#skF_4')) | ~r2_hidden(A_177, a_2_0_orders_2('#skF_4', C_178)) | ~m1_subset_1(C_178, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_56, c_99, c_1192])).
% 5.71/2.09  tff(c_1231, plain, (![E_181, A_182, C_183]: (r2_orders_2('#skF_4', E_181, '#skF_2'(A_182, '#skF_4', C_183)) | ~r2_hidden(E_181, C_183) | ~m1_subset_1(E_181, k2_struct_0('#skF_4')) | ~r2_hidden(A_182, a_2_0_orders_2('#skF_4', C_183)) | ~m1_subset_1(C_183, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_1200])).
% 5.71/2.09  tff(c_2654, plain, (![E_270, A_271, A_272]: (r2_orders_2('#skF_4', E_270, '#skF_2'(A_271, '#skF_4', A_272)) | ~r2_hidden(E_270, A_272) | ~m1_subset_1(E_270, k2_struct_0('#skF_4')) | ~r2_hidden(A_271, a_2_0_orders_2('#skF_4', A_272)) | ~r1_tarski(A_272, k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_14, c_1231])).
% 5.71/2.09  tff(c_32, plain, (![A_24, C_30]: (~r2_orders_2(A_24, C_30, C_30) | ~m1_subset_1(C_30, u1_struct_0(A_24)) | ~l1_orders_2(A_24))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.71/2.09  tff(c_2662, plain, (![A_271, A_272]: (~m1_subset_1('#skF_2'(A_271, '#skF_4', A_272), u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~r2_hidden('#skF_2'(A_271, '#skF_4', A_272), A_272) | ~m1_subset_1('#skF_2'(A_271, '#skF_4', A_272), k2_struct_0('#skF_4')) | ~r2_hidden(A_271, a_2_0_orders_2('#skF_4', A_272)) | ~r1_tarski(A_272, k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_2654, c_32])).
% 5.71/2.09  tff(c_2686, plain, (![A_273, A_274]: (~r2_hidden('#skF_2'(A_273, '#skF_4', A_274), A_274) | ~m1_subset_1('#skF_2'(A_273, '#skF_4', A_274), k2_struct_0('#skF_4')) | ~r2_hidden(A_273, a_2_0_orders_2('#skF_4', A_274)) | ~r1_tarski(A_274, k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_99, c_2662])).
% 5.71/2.09  tff(c_2698, plain, (![A_273]: (~r2_hidden(A_273, a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))) | ~r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_2'(A_273, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_985, c_2686])).
% 5.71/2.09  tff(c_2831, plain, (![A_276]: (~r2_hidden(A_276, a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))) | ~m1_subset_1('#skF_2'(A_276, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_2698])).
% 5.71/2.09  tff(c_2843, plain, (![A_139]: (~r2_hidden(A_139, a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_728, c_2831])).
% 5.71/2.09  tff(c_2844, plain, (~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_2843])).
% 5.71/2.09  tff(c_2847, plain, (~r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_14, c_2844])).
% 5.71/2.09  tff(c_2851, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_2847])).
% 5.71/2.09  tff(c_2862, plain, (![A_278]: (~r2_hidden(A_278, a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(splitRight, [status(thm)], [c_2843])).
% 5.71/2.09  tff(c_2874, plain, (a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_20, c_2862])).
% 5.71/2.09  tff(c_2880, plain, $false, inference(negUnitSimplification, [status(thm)], [c_514, c_2874])).
% 5.71/2.09  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.71/2.09  
% 5.71/2.09  Inference rules
% 5.71/2.09  ----------------------
% 5.71/2.09  #Ref     : 0
% 5.71/2.09  #Sup     : 558
% 5.71/2.09  #Fact    : 0
% 5.71/2.09  #Define  : 0
% 5.71/2.09  #Split   : 12
% 5.71/2.09  #Chain   : 0
% 5.71/2.09  #Close   : 0
% 5.71/2.09  
% 5.71/2.09  Ordering : KBO
% 5.71/2.09  
% 5.71/2.09  Simplification rules
% 5.71/2.09  ----------------------
% 5.71/2.09  #Subsume      : 125
% 5.71/2.09  #Demod        : 941
% 5.71/2.09  #Tautology    : 139
% 5.71/2.09  #SimpNegUnit  : 138
% 5.71/2.09  #BackRed      : 42
% 5.71/2.09  
% 5.71/2.09  #Partial instantiations: 0
% 5.71/2.09  #Strategies tried      : 1
% 5.71/2.09  
% 5.71/2.09  Timing (in seconds)
% 5.71/2.09  ----------------------
% 5.71/2.10  Preprocessing        : 0.34
% 5.71/2.10  Parsing              : 0.18
% 5.71/2.10  CNF conversion       : 0.02
% 5.71/2.10  Main loop            : 0.96
% 5.71/2.10  Inferencing          : 0.29
% 5.71/2.10  Reduction            : 0.31
% 5.71/2.10  Demodulation         : 0.21
% 5.71/2.10  BG Simplification    : 0.04
% 5.71/2.10  Subsumption          : 0.25
% 5.71/2.10  Abstraction          : 0.05
% 5.71/2.10  MUC search           : 0.00
% 5.71/2.10  Cooper               : 0.00
% 5.71/2.10  Total                : 1.34
% 5.71/2.10  Index Insertion      : 0.00
% 5.71/2.10  Index Deletion       : 0.00
% 5.71/2.10  Index Matching       : 0.00
% 5.71/2.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
