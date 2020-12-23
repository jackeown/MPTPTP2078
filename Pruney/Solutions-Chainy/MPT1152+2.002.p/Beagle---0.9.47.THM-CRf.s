%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:27 EST 2020

% Result     : Theorem 5.20s
% Output     : CNFRefutation 5.20s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 251 expanded)
%              Number of leaves         :   40 ( 109 expanded)
%              Depth                    :   15
%              Number of atoms          :  228 ( 682 expanded)
%              Number of equality atoms :   35 ( 124 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r1_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_struct_0 > l1_orders_2 > k2_zfmisc_1 > k2_orders_2 > a_2_1_orders_2 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_4 > #skF_3

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

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_44,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_46,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_151,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => k2_orders_2(A,k2_struct_0(A)) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_orders_2)).

tff(f_97,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_93,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_orders_2(A,B) = a_2_1_orders_2(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_orders_2)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_124,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k1_struct_0(A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_struct_0)).

tff(f_137,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => k2_orders_2(A,k1_struct_0(A)) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_orders_2)).

tff(f_48,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_77,axiom,(
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
    ! [A_7] : k2_subset_1(A_7) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_14,plain,(
    ! [A_8] : m1_subset_1(k2_subset_1(A_8),k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_59,plain,(
    ! [A_8] : m1_subset_1(A_8,k1_zfmisc_1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_14])).

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

tff(c_32,plain,(
    ! [A_25] :
      ( l1_struct_0(A_25)
      | ~ l1_orders_2(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_106,plain,(
    ! [A_49] :
      ( u1_struct_0(A_49) = k2_struct_0(A_49)
      | ~ l1_struct_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_128,plain,(
    ! [A_53] :
      ( u1_struct_0(A_53) = k2_struct_0(A_53)
      | ~ l1_orders_2(A_53) ) ),
    inference(resolution,[status(thm)],[c_32,c_106])).

tff(c_132,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_128])).

tff(c_225,plain,(
    ! [A_78,B_79] :
      ( k2_orders_2(A_78,B_79) = a_2_1_orders_2(A_78,B_79)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ l1_orders_2(A_78)
      | ~ v5_orders_2(A_78)
      | ~ v4_orders_2(A_78)
      | ~ v3_orders_2(A_78)
      | v2_struct_0(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_236,plain,(
    ! [B_79] :
      ( k2_orders_2('#skF_4',B_79) = a_2_1_orders_2('#skF_4',B_79)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_225])).

tff(c_248,plain,(
    ! [B_79] :
      ( k2_orders_2('#skF_4',B_79) = a_2_1_orders_2('#skF_4',B_79)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_236])).

tff(c_252,plain,(
    ! [B_80] :
      ( k2_orders_2('#skF_4',B_80) = a_2_1_orders_2('#skF_4',B_80)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_248])).

tff(c_271,plain,(
    k2_orders_2('#skF_4',k2_struct_0('#skF_4')) = a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_59,c_252])).

tff(c_48,plain,(
    k2_orders_2('#skF_4',k2_struct_0('#skF_4')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_278,plain,(
    a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_271,c_48])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2132,plain,(
    ! [A_190,B_191,C_192] :
      ( m1_subset_1('#skF_2'(A_190,B_191,C_192),u1_struct_0(B_191))
      | ~ r2_hidden(A_190,a_2_1_orders_2(B_191,C_192))
      | ~ m1_subset_1(C_192,k1_zfmisc_1(u1_struct_0(B_191)))
      | ~ l1_orders_2(B_191)
      | ~ v5_orders_2(B_191)
      | ~ v4_orders_2(B_191)
      | ~ v3_orders_2(B_191)
      | v2_struct_0(B_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_2137,plain,(
    ! [A_190,C_192] :
      ( m1_subset_1('#skF_2'(A_190,'#skF_4',C_192),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_190,a_2_1_orders_2('#skF_4',C_192))
      | ~ m1_subset_1(C_192,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_2132])).

tff(c_2140,plain,(
    ! [A_190,C_192] :
      ( m1_subset_1('#skF_2'(A_190,'#skF_4',C_192),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_190,a_2_1_orders_2('#skF_4',C_192))
      | ~ m1_subset_1(C_192,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_132,c_2137])).

tff(c_2141,plain,(
    ! [A_190,C_192] :
      ( m1_subset_1('#skF_2'(A_190,'#skF_4',C_192),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_190,a_2_1_orders_2('#skF_4',C_192))
      | ~ m1_subset_1(C_192,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_2140])).

tff(c_6,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_99,plain,(
    ! [A_47,B_48] : ~ r2_hidden(A_47,k2_zfmisc_1(A_47,B_48)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_105,plain,(
    ! [A_3] : ~ r2_hidden(A_3,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_99])).

tff(c_94,plain,(
    ! [A_46] :
      ( k1_struct_0(A_46) = k1_xboole_0
      | ~ l1_struct_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_112,plain,(
    ! [A_51] :
      ( k1_struct_0(A_51) = k1_xboole_0
      | ~ l1_orders_2(A_51) ) ),
    inference(resolution,[status(thm)],[c_32,c_94])).

tff(c_116,plain,(
    k1_struct_0('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_50,c_112])).

tff(c_177,plain,(
    ! [A_67] :
      ( k2_orders_2(A_67,k1_struct_0(A_67)) = u1_struct_0(A_67)
      | ~ l1_orders_2(A_67)
      | ~ v5_orders_2(A_67)
      | ~ v4_orders_2(A_67)
      | ~ v3_orders_2(A_67)
      | v2_struct_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_186,plain,
    ( k2_orders_2('#skF_4',k1_xboole_0) = u1_struct_0('#skF_4')
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_177])).

tff(c_190,plain,
    ( k2_orders_2('#skF_4',k1_xboole_0) = k2_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_132,c_186])).

tff(c_191,plain,(
    k2_orders_2('#skF_4',k1_xboole_0) = k2_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_190])).

tff(c_16,plain,(
    ! [A_9] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_268,plain,(
    k2_orders_2('#skF_4',k1_xboole_0) = a_2_1_orders_2('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_252])).

tff(c_273,plain,(
    a_2_1_orders_2('#skF_4',k1_xboole_0) = k2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_268])).

tff(c_2240,plain,(
    ! [D_196,B_197,C_198] :
      ( r2_hidden('#skF_3'(D_196,B_197,C_198,D_196),C_198)
      | r2_hidden(D_196,a_2_1_orders_2(B_197,C_198))
      | ~ m1_subset_1(D_196,u1_struct_0(B_197))
      | ~ m1_subset_1(C_198,k1_zfmisc_1(u1_struct_0(B_197)))
      | ~ l1_orders_2(B_197)
      | ~ v5_orders_2(B_197)
      | ~ v4_orders_2(B_197)
      | ~ v3_orders_2(B_197)
      | v2_struct_0(B_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_2248,plain,(
    ! [D_196,C_198] :
      ( r2_hidden('#skF_3'(D_196,'#skF_4',C_198,D_196),C_198)
      | r2_hidden(D_196,a_2_1_orders_2('#skF_4',C_198))
      | ~ m1_subset_1(D_196,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_198,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_2240])).

tff(c_2258,plain,(
    ! [D_196,C_198] :
      ( r2_hidden('#skF_3'(D_196,'#skF_4',C_198,D_196),C_198)
      | r2_hidden(D_196,a_2_1_orders_2('#skF_4',C_198))
      | ~ m1_subset_1(D_196,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(C_198,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_132,c_2248])).

tff(c_2282,plain,(
    ! [D_202,C_203] :
      ( r2_hidden('#skF_3'(D_202,'#skF_4',C_203,D_202),C_203)
      | r2_hidden(D_202,a_2_1_orders_2('#skF_4',C_203))
      | ~ m1_subset_1(D_202,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(C_203,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_2258])).

tff(c_2296,plain,(
    ! [D_202] :
      ( r2_hidden('#skF_3'(D_202,'#skF_4',k1_xboole_0,D_202),k1_xboole_0)
      | r2_hidden(D_202,a_2_1_orders_2('#skF_4',k1_xboole_0))
      | ~ m1_subset_1(D_202,k2_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_16,c_2282])).

tff(c_2306,plain,(
    ! [D_202] :
      ( r2_hidden('#skF_3'(D_202,'#skF_4',k1_xboole_0,D_202),k1_xboole_0)
      | r2_hidden(D_202,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(D_202,k2_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_273,c_2296])).

tff(c_2307,plain,(
    ! [D_202] :
      ( r2_hidden(D_202,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(D_202,k2_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_105,c_2306])).

tff(c_2677,plain,(
    ! [B_230,A_231,C_232,E_233] :
      ( r2_orders_2(B_230,'#skF_2'(A_231,B_230,C_232),E_233)
      | ~ r2_hidden(E_233,C_232)
      | ~ m1_subset_1(E_233,u1_struct_0(B_230))
      | ~ r2_hidden(A_231,a_2_1_orders_2(B_230,C_232))
      | ~ m1_subset_1(C_232,k1_zfmisc_1(u1_struct_0(B_230)))
      | ~ l1_orders_2(B_230)
      | ~ v5_orders_2(B_230)
      | ~ v4_orders_2(B_230)
      | ~ v3_orders_2(B_230)
      | v2_struct_0(B_230) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_2685,plain,(
    ! [A_231,C_232,E_233] :
      ( r2_orders_2('#skF_4','#skF_2'(A_231,'#skF_4',C_232),E_233)
      | ~ r2_hidden(E_233,C_232)
      | ~ m1_subset_1(E_233,u1_struct_0('#skF_4'))
      | ~ r2_hidden(A_231,a_2_1_orders_2('#skF_4',C_232))
      | ~ m1_subset_1(C_232,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_2677])).

tff(c_2695,plain,(
    ! [A_231,C_232,E_233] :
      ( r2_orders_2('#skF_4','#skF_2'(A_231,'#skF_4',C_232),E_233)
      | ~ r2_hidden(E_233,C_232)
      | ~ m1_subset_1(E_233,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_231,a_2_1_orders_2('#skF_4',C_232))
      | ~ m1_subset_1(C_232,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_132,c_2685])).

tff(c_2762,plain,(
    ! [A_238,C_239,E_240] :
      ( r2_orders_2('#skF_4','#skF_2'(A_238,'#skF_4',C_239),E_240)
      | ~ r2_hidden(E_240,C_239)
      | ~ m1_subset_1(E_240,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_238,a_2_1_orders_2('#skF_4',C_239))
      | ~ m1_subset_1(C_239,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_2695])).

tff(c_2813,plain,(
    ! [A_242,E_243] :
      ( r2_orders_2('#skF_4','#skF_2'(A_242,'#skF_4',k2_struct_0('#skF_4')),E_243)
      | ~ r2_hidden(E_243,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(E_243,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_242,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_59,c_2762])).

tff(c_26,plain,(
    ! [A_15,C_21] :
      ( ~ r2_orders_2(A_15,C_21,C_21)
      | ~ m1_subset_1(C_21,u1_struct_0(A_15))
      | ~ l1_orders_2(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2821,plain,(
    ! [A_242] :
      ( ~ m1_subset_1('#skF_2'(A_242,'#skF_4',k2_struct_0('#skF_4')),u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ r2_hidden('#skF_2'(A_242,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_2'(A_242,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_242,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_2813,c_26])).

tff(c_2832,plain,(
    ! [A_244] :
      ( ~ r2_hidden('#skF_2'(A_244,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_2'(A_244,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_244,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_132,c_2821])).

tff(c_2837,plain,(
    ! [A_245] :
      ( ~ r2_hidden(A_245,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')))
      | ~ m1_subset_1('#skF_2'(A_245,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_2307,c_2832])).

tff(c_2841,plain,(
    ! [A_190] :
      ( ~ r2_hidden(A_190,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')))
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_2141,c_2837])).

tff(c_2847,plain,(
    ! [A_246] : ~ r2_hidden(A_246,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_2841])).

tff(c_2851,plain,(
    a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_2847])).

tff(c_2855,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_278,c_2851])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n022.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 18:51:10 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.20/1.93  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.20/1.94  
% 5.20/1.94  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.20/1.94  %$ r2_orders_2 > r1_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_struct_0 > l1_orders_2 > k2_zfmisc_1 > k2_orders_2 > a_2_1_orders_2 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_4 > #skF_3
% 5.20/1.94  
% 5.20/1.94  %Foreground sorts:
% 5.20/1.94  
% 5.20/1.94  
% 5.20/1.94  %Background operators:
% 5.20/1.94  
% 5.20/1.94  
% 5.20/1.94  %Foreground operators:
% 5.20/1.94  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.20/1.94  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 5.20/1.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.20/1.94  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.20/1.94  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.20/1.94  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 5.20/1.94  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.20/1.94  tff(a_2_1_orders_2, type, a_2_1_orders_2: ($i * $i) > $i).
% 5.20/1.94  tff(k2_orders_2, type, k2_orders_2: ($i * $i) > $i).
% 5.20/1.94  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.20/1.94  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 5.20/1.94  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 5.20/1.94  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.20/1.94  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.20/1.94  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 5.20/1.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.20/1.94  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.20/1.94  tff('#skF_4', type, '#skF_4': $i).
% 5.20/1.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.20/1.94  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 5.20/1.94  tff(k1_struct_0, type, k1_struct_0: $i > $i).
% 5.20/1.94  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 5.20/1.94  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.20/1.94  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 5.20/1.94  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 5.20/1.94  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.20/1.94  
% 5.20/1.96  tff(f_44, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 5.20/1.96  tff(f_46, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 5.20/1.96  tff(f_151, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (k2_orders_2(A, k2_struct_0(A)) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_orders_2)).
% 5.20/1.96  tff(f_97, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 5.20/1.96  tff(f_62, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 5.20/1.96  tff(f_93, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_orders_2(A, B) = a_2_1_orders_2(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_orders_2)).
% 5.20/1.96  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 5.20/1.96  tff(f_124, axiom, (![A, B, C]: ((((((~v2_struct_0(B) & v3_orders_2(B)) & v4_orders_2(B)) & v5_orders_2(B)) & l1_orders_2(B)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B)))) => (r2_hidden(A, a_2_1_orders_2(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r2_hidden(E, C) => r2_orders_2(B, D, E))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_1_orders_2)).
% 5.20/1.96  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.20/1.96  tff(f_42, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 5.20/1.96  tff(f_58, axiom, (![A]: (l1_struct_0(A) => (k1_struct_0(A) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_struct_0)).
% 5.20/1.96  tff(f_137, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (k2_orders_2(A, k1_struct_0(A)) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_orders_2)).
% 5.20/1.96  tff(f_48, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 5.20/1.96  tff(f_77, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_orders_2(A, B, C) <=> (r1_orders_2(A, B, C) & ~(B = C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_orders_2)).
% 5.20/1.96  tff(c_12, plain, (![A_7]: (k2_subset_1(A_7)=A_7)), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.20/1.96  tff(c_14, plain, (![A_8]: (m1_subset_1(k2_subset_1(A_8), k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.20/1.96  tff(c_59, plain, (![A_8]: (m1_subset_1(A_8, k1_zfmisc_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_14])).
% 5.20/1.96  tff(c_58, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_151])).
% 5.20/1.96  tff(c_56, plain, (v3_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_151])).
% 5.20/1.96  tff(c_54, plain, (v4_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_151])).
% 5.20/1.96  tff(c_52, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_151])).
% 5.20/1.96  tff(c_50, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_151])).
% 5.20/1.96  tff(c_32, plain, (![A_25]: (l1_struct_0(A_25) | ~l1_orders_2(A_25))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.20/1.96  tff(c_106, plain, (![A_49]: (u1_struct_0(A_49)=k2_struct_0(A_49) | ~l1_struct_0(A_49))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.20/1.96  tff(c_128, plain, (![A_53]: (u1_struct_0(A_53)=k2_struct_0(A_53) | ~l1_orders_2(A_53))), inference(resolution, [status(thm)], [c_32, c_106])).
% 5.20/1.96  tff(c_132, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_50, c_128])).
% 5.20/1.96  tff(c_225, plain, (![A_78, B_79]: (k2_orders_2(A_78, B_79)=a_2_1_orders_2(A_78, B_79) | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0(A_78))) | ~l1_orders_2(A_78) | ~v5_orders_2(A_78) | ~v4_orders_2(A_78) | ~v3_orders_2(A_78) | v2_struct_0(A_78))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.20/1.96  tff(c_236, plain, (![B_79]: (k2_orders_2('#skF_4', B_79)=a_2_1_orders_2('#skF_4', B_79) | ~m1_subset_1(B_79, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_132, c_225])).
% 5.20/1.96  tff(c_248, plain, (![B_79]: (k2_orders_2('#skF_4', B_79)=a_2_1_orders_2('#skF_4', B_79) | ~m1_subset_1(B_79, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_236])).
% 5.20/1.96  tff(c_252, plain, (![B_80]: (k2_orders_2('#skF_4', B_80)=a_2_1_orders_2('#skF_4', B_80) | ~m1_subset_1(B_80, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_58, c_248])).
% 5.20/1.96  tff(c_271, plain, (k2_orders_2('#skF_4', k2_struct_0('#skF_4'))=a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_59, c_252])).
% 5.20/1.96  tff(c_48, plain, (k2_orders_2('#skF_4', k2_struct_0('#skF_4'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_151])).
% 5.20/1.96  tff(c_278, plain, (a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_271, c_48])).
% 5.20/1.96  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.20/1.96  tff(c_2132, plain, (![A_190, B_191, C_192]: (m1_subset_1('#skF_2'(A_190, B_191, C_192), u1_struct_0(B_191)) | ~r2_hidden(A_190, a_2_1_orders_2(B_191, C_192)) | ~m1_subset_1(C_192, k1_zfmisc_1(u1_struct_0(B_191))) | ~l1_orders_2(B_191) | ~v5_orders_2(B_191) | ~v4_orders_2(B_191) | ~v3_orders_2(B_191) | v2_struct_0(B_191))), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.20/1.96  tff(c_2137, plain, (![A_190, C_192]: (m1_subset_1('#skF_2'(A_190, '#skF_4', C_192), k2_struct_0('#skF_4')) | ~r2_hidden(A_190, a_2_1_orders_2('#skF_4', C_192)) | ~m1_subset_1(C_192, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_132, c_2132])).
% 5.20/1.96  tff(c_2140, plain, (![A_190, C_192]: (m1_subset_1('#skF_2'(A_190, '#skF_4', C_192), k2_struct_0('#skF_4')) | ~r2_hidden(A_190, a_2_1_orders_2('#skF_4', C_192)) | ~m1_subset_1(C_192, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_132, c_2137])).
% 5.20/1.96  tff(c_2141, plain, (![A_190, C_192]: (m1_subset_1('#skF_2'(A_190, '#skF_4', C_192), k2_struct_0('#skF_4')) | ~r2_hidden(A_190, a_2_1_orders_2('#skF_4', C_192)) | ~m1_subset_1(C_192, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_58, c_2140])).
% 5.20/1.96  tff(c_6, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.20/1.96  tff(c_99, plain, (![A_47, B_48]: (~r2_hidden(A_47, k2_zfmisc_1(A_47, B_48)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.20/1.96  tff(c_105, plain, (![A_3]: (~r2_hidden(A_3, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_99])).
% 5.20/1.96  tff(c_94, plain, (![A_46]: (k1_struct_0(A_46)=k1_xboole_0 | ~l1_struct_0(A_46))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.20/1.96  tff(c_112, plain, (![A_51]: (k1_struct_0(A_51)=k1_xboole_0 | ~l1_orders_2(A_51))), inference(resolution, [status(thm)], [c_32, c_94])).
% 5.20/1.96  tff(c_116, plain, (k1_struct_0('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_50, c_112])).
% 5.20/1.96  tff(c_177, plain, (![A_67]: (k2_orders_2(A_67, k1_struct_0(A_67))=u1_struct_0(A_67) | ~l1_orders_2(A_67) | ~v5_orders_2(A_67) | ~v4_orders_2(A_67) | ~v3_orders_2(A_67) | v2_struct_0(A_67))), inference(cnfTransformation, [status(thm)], [f_137])).
% 5.20/1.96  tff(c_186, plain, (k2_orders_2('#skF_4', k1_xboole_0)=u1_struct_0('#skF_4') | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_116, c_177])).
% 5.20/1.96  tff(c_190, plain, (k2_orders_2('#skF_4', k1_xboole_0)=k2_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_132, c_186])).
% 5.20/1.96  tff(c_191, plain, (k2_orders_2('#skF_4', k1_xboole_0)=k2_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_58, c_190])).
% 5.20/1.96  tff(c_16, plain, (![A_9]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.20/1.96  tff(c_268, plain, (k2_orders_2('#skF_4', k1_xboole_0)=a_2_1_orders_2('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_252])).
% 5.20/1.96  tff(c_273, plain, (a_2_1_orders_2('#skF_4', k1_xboole_0)=k2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_191, c_268])).
% 5.20/1.96  tff(c_2240, plain, (![D_196, B_197, C_198]: (r2_hidden('#skF_3'(D_196, B_197, C_198, D_196), C_198) | r2_hidden(D_196, a_2_1_orders_2(B_197, C_198)) | ~m1_subset_1(D_196, u1_struct_0(B_197)) | ~m1_subset_1(C_198, k1_zfmisc_1(u1_struct_0(B_197))) | ~l1_orders_2(B_197) | ~v5_orders_2(B_197) | ~v4_orders_2(B_197) | ~v3_orders_2(B_197) | v2_struct_0(B_197))), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.20/1.96  tff(c_2248, plain, (![D_196, C_198]: (r2_hidden('#skF_3'(D_196, '#skF_4', C_198, D_196), C_198) | r2_hidden(D_196, a_2_1_orders_2('#skF_4', C_198)) | ~m1_subset_1(D_196, u1_struct_0('#skF_4')) | ~m1_subset_1(C_198, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_132, c_2240])).
% 5.20/1.96  tff(c_2258, plain, (![D_196, C_198]: (r2_hidden('#skF_3'(D_196, '#skF_4', C_198, D_196), C_198) | r2_hidden(D_196, a_2_1_orders_2('#skF_4', C_198)) | ~m1_subset_1(D_196, k2_struct_0('#skF_4')) | ~m1_subset_1(C_198, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_132, c_2248])).
% 5.20/1.96  tff(c_2282, plain, (![D_202, C_203]: (r2_hidden('#skF_3'(D_202, '#skF_4', C_203, D_202), C_203) | r2_hidden(D_202, a_2_1_orders_2('#skF_4', C_203)) | ~m1_subset_1(D_202, k2_struct_0('#skF_4')) | ~m1_subset_1(C_203, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_58, c_2258])).
% 5.20/1.96  tff(c_2296, plain, (![D_202]: (r2_hidden('#skF_3'(D_202, '#skF_4', k1_xboole_0, D_202), k1_xboole_0) | r2_hidden(D_202, a_2_1_orders_2('#skF_4', k1_xboole_0)) | ~m1_subset_1(D_202, k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_16, c_2282])).
% 5.20/1.96  tff(c_2306, plain, (![D_202]: (r2_hidden('#skF_3'(D_202, '#skF_4', k1_xboole_0, D_202), k1_xboole_0) | r2_hidden(D_202, k2_struct_0('#skF_4')) | ~m1_subset_1(D_202, k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_273, c_2296])).
% 5.20/1.96  tff(c_2307, plain, (![D_202]: (r2_hidden(D_202, k2_struct_0('#skF_4')) | ~m1_subset_1(D_202, k2_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_105, c_2306])).
% 5.20/1.96  tff(c_2677, plain, (![B_230, A_231, C_232, E_233]: (r2_orders_2(B_230, '#skF_2'(A_231, B_230, C_232), E_233) | ~r2_hidden(E_233, C_232) | ~m1_subset_1(E_233, u1_struct_0(B_230)) | ~r2_hidden(A_231, a_2_1_orders_2(B_230, C_232)) | ~m1_subset_1(C_232, k1_zfmisc_1(u1_struct_0(B_230))) | ~l1_orders_2(B_230) | ~v5_orders_2(B_230) | ~v4_orders_2(B_230) | ~v3_orders_2(B_230) | v2_struct_0(B_230))), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.20/1.96  tff(c_2685, plain, (![A_231, C_232, E_233]: (r2_orders_2('#skF_4', '#skF_2'(A_231, '#skF_4', C_232), E_233) | ~r2_hidden(E_233, C_232) | ~m1_subset_1(E_233, u1_struct_0('#skF_4')) | ~r2_hidden(A_231, a_2_1_orders_2('#skF_4', C_232)) | ~m1_subset_1(C_232, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_132, c_2677])).
% 5.20/1.96  tff(c_2695, plain, (![A_231, C_232, E_233]: (r2_orders_2('#skF_4', '#skF_2'(A_231, '#skF_4', C_232), E_233) | ~r2_hidden(E_233, C_232) | ~m1_subset_1(E_233, k2_struct_0('#skF_4')) | ~r2_hidden(A_231, a_2_1_orders_2('#skF_4', C_232)) | ~m1_subset_1(C_232, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_132, c_2685])).
% 5.20/1.96  tff(c_2762, plain, (![A_238, C_239, E_240]: (r2_orders_2('#skF_4', '#skF_2'(A_238, '#skF_4', C_239), E_240) | ~r2_hidden(E_240, C_239) | ~m1_subset_1(E_240, k2_struct_0('#skF_4')) | ~r2_hidden(A_238, a_2_1_orders_2('#skF_4', C_239)) | ~m1_subset_1(C_239, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_58, c_2695])).
% 5.20/1.96  tff(c_2813, plain, (![A_242, E_243]: (r2_orders_2('#skF_4', '#skF_2'(A_242, '#skF_4', k2_struct_0('#skF_4')), E_243) | ~r2_hidden(E_243, k2_struct_0('#skF_4')) | ~m1_subset_1(E_243, k2_struct_0('#skF_4')) | ~r2_hidden(A_242, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_59, c_2762])).
% 5.20/1.96  tff(c_26, plain, (![A_15, C_21]: (~r2_orders_2(A_15, C_21, C_21) | ~m1_subset_1(C_21, u1_struct_0(A_15)) | ~l1_orders_2(A_15))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.20/1.96  tff(c_2821, plain, (![A_242]: (~m1_subset_1('#skF_2'(A_242, '#skF_4', k2_struct_0('#skF_4')), u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~r2_hidden('#skF_2'(A_242, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_2'(A_242, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')) | ~r2_hidden(A_242, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_2813, c_26])).
% 5.20/1.96  tff(c_2832, plain, (![A_244]: (~r2_hidden('#skF_2'(A_244, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_2'(A_244, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')) | ~r2_hidden(A_244, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_132, c_2821])).
% 5.20/1.96  tff(c_2837, plain, (![A_245]: (~r2_hidden(A_245, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))) | ~m1_subset_1('#skF_2'(A_245, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_2307, c_2832])).
% 5.20/1.96  tff(c_2841, plain, (![A_190]: (~r2_hidden(A_190, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_2141, c_2837])).
% 5.20/1.96  tff(c_2847, plain, (![A_246]: (~r2_hidden(A_246, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_2841])).
% 5.20/1.96  tff(c_2851, plain, (a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_2847])).
% 5.20/1.96  tff(c_2855, plain, $false, inference(negUnitSimplification, [status(thm)], [c_278, c_2851])).
% 5.20/1.96  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.20/1.96  
% 5.20/1.96  Inference rules
% 5.20/1.96  ----------------------
% 5.20/1.96  #Ref     : 0
% 5.20/1.96  #Sup     : 575
% 5.20/1.96  #Fact    : 0
% 5.20/1.96  #Define  : 0
% 5.20/1.96  #Split   : 11
% 5.20/1.96  #Chain   : 0
% 5.20/1.96  #Close   : 0
% 5.20/1.96  
% 5.20/1.96  Ordering : KBO
% 5.20/1.96  
% 5.20/1.96  Simplification rules
% 5.20/1.96  ----------------------
% 5.20/1.96  #Subsume      : 81
% 5.20/1.96  #Demod        : 793
% 5.20/1.96  #Tautology    : 215
% 5.20/1.96  #SimpNegUnit  : 115
% 5.20/1.96  #BackRed      : 31
% 5.20/1.96  
% 5.20/1.96  #Partial instantiations: 0
% 5.20/1.96  #Strategies tried      : 1
% 5.20/1.96  
% 5.20/1.96  Timing (in seconds)
% 5.20/1.96  ----------------------
% 5.20/1.96  Preprocessing        : 0.35
% 5.20/1.96  Parsing              : 0.18
% 5.20/1.96  CNF conversion       : 0.03
% 5.20/1.96  Main loop            : 0.86
% 5.20/1.96  Inferencing          : 0.29
% 5.20/1.96  Reduction            : 0.30
% 5.20/1.96  Demodulation         : 0.21
% 5.20/1.96  BG Simplification    : 0.04
% 5.20/1.96  Subsumption          : 0.17
% 5.20/1.96  Abstraction          : 0.05
% 5.20/1.96  MUC search           : 0.00
% 5.20/1.96  Cooper               : 0.00
% 5.20/1.96  Total                : 1.26
% 5.20/1.96  Index Insertion      : 0.00
% 5.20/1.96  Index Deletion       : 0.00
% 5.20/1.96  Index Matching       : 0.00
% 5.20/1.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
