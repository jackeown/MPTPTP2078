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
% DateTime   : Thu Dec  3 10:19:24 EST 2020

% Result     : Theorem 5.11s
% Output     : CNFRefutation 5.11s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 252 expanded)
%              Number of leaves         :   41 ( 110 expanded)
%              Depth                    :   16
%              Number of atoms          :  233 ( 687 expanded)
%              Number of equality atoms :   32 ( 121 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_struct_0 > l1_orders_2 > k3_mcart_1 > k1_orders_2 > a_2_0_orders_2 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_4 > #skF_3

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_29,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_31,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_157,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => k1_orders_2(A,k2_struct_0(A)) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_orders_2)).

tff(f_103,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_99,axiom,(
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

tff(f_60,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).

tff(f_130,axiom,(
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

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k1_struct_0(A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_struct_0)).

tff(f_143,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => k1_orders_2(A,k1_struct_0(A)) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_orders_2)).

tff(f_33,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_83,axiom,(
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

tff(c_4,plain,(
    ! [A_2] : k2_subset_1(A_2) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_3] : m1_subset_1(k2_subset_1(A_3),k1_zfmisc_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_59,plain,(
    ! [A_3] : m1_subset_1(A_3,k1_zfmisc_1(A_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_56,plain,(
    v3_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_54,plain,(
    v4_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_52,plain,(
    v5_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_50,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_32,plain,(
    ! [A_36] :
      ( l1_struct_0(A_36)
      | ~ l1_orders_2(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_87,plain,(
    ! [A_58] :
      ( u1_struct_0(A_58) = k2_struct_0(A_58)
      | ~ l1_struct_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_98,plain,(
    ! [A_62] :
      ( u1_struct_0(A_62) = k2_struct_0(A_62)
      | ~ l1_orders_2(A_62) ) ),
    inference(resolution,[status(thm)],[c_32,c_87])).

tff(c_102,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_98])).

tff(c_207,plain,(
    ! [A_102,B_103] :
      ( k1_orders_2(A_102,B_103) = a_2_0_orders_2(A_102,B_103)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ l1_orders_2(A_102)
      | ~ v5_orders_2(A_102)
      | ~ v4_orders_2(A_102)
      | ~ v3_orders_2(A_102)
      | v2_struct_0(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_218,plain,(
    ! [B_103] :
      ( k1_orders_2('#skF_4',B_103) = a_2_0_orders_2('#skF_4',B_103)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_207])).

tff(c_230,plain,(
    ! [B_103] :
      ( k1_orders_2('#skF_4',B_103) = a_2_0_orders_2('#skF_4',B_103)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_218])).

tff(c_234,plain,(
    ! [B_104] :
      ( k1_orders_2('#skF_4',B_104) = a_2_0_orders_2('#skF_4',B_104)
      | ~ m1_subset_1(B_104,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_230])).

tff(c_253,plain,(
    k1_orders_2('#skF_4',k2_struct_0('#skF_4')) = a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_59,c_234])).

tff(c_48,plain,(
    k1_orders_2('#skF_4',k2_struct_0('#skF_4')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_256,plain,(
    a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_48])).

tff(c_14,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_1'(A_10),A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1663,plain,(
    ! [A_224,B_225,C_226] :
      ( m1_subset_1('#skF_2'(A_224,B_225,C_226),u1_struct_0(B_225))
      | ~ r2_hidden(A_224,a_2_0_orders_2(B_225,C_226))
      | ~ m1_subset_1(C_226,k1_zfmisc_1(u1_struct_0(B_225)))
      | ~ l1_orders_2(B_225)
      | ~ v5_orders_2(B_225)
      | ~ v4_orders_2(B_225)
      | ~ v3_orders_2(B_225)
      | v2_struct_0(B_225) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_1668,plain,(
    ! [A_224,C_226] :
      ( m1_subset_1('#skF_2'(A_224,'#skF_4',C_226),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_224,a_2_0_orders_2('#skF_4',C_226))
      | ~ m1_subset_1(C_226,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_1663])).

tff(c_1671,plain,(
    ! [A_224,C_226] :
      ( m1_subset_1('#skF_2'(A_224,'#skF_4',C_226),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_224,a_2_0_orders_2('#skF_4',C_226))
      | ~ m1_subset_1(C_226,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_102,c_1668])).

tff(c_1672,plain,(
    ! [A_224,C_226] :
      ( m1_subset_1('#skF_2'(A_224,'#skF_4',C_226),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_224,a_2_0_orders_2('#skF_4',C_226))
      | ~ m1_subset_1(C_226,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1671])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_73,plain,(
    ! [A_56] :
      ( k1_struct_0(A_56) = k1_xboole_0
      | ~ l1_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_78,plain,(
    ! [A_57] :
      ( k1_struct_0(A_57) = k1_xboole_0
      | ~ l1_orders_2(A_57) ) ),
    inference(resolution,[status(thm)],[c_32,c_73])).

tff(c_82,plain,(
    k1_struct_0('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_50,c_78])).

tff(c_148,plain,(
    ! [A_88] :
      ( k1_orders_2(A_88,k1_struct_0(A_88)) = u1_struct_0(A_88)
      | ~ l1_orders_2(A_88)
      | ~ v5_orders_2(A_88)
      | ~ v4_orders_2(A_88)
      | ~ v3_orders_2(A_88)
      | v2_struct_0(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_157,plain,
    ( k1_orders_2('#skF_4',k1_xboole_0) = u1_struct_0('#skF_4')
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_148])).

tff(c_161,plain,
    ( k1_orders_2('#skF_4',k1_xboole_0) = k2_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_102,c_157])).

tff(c_162,plain,(
    k1_orders_2('#skF_4',k1_xboole_0) = k2_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_161])).

tff(c_8,plain,(
    ! [A_4] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_250,plain,(
    k1_orders_2('#skF_4',k1_xboole_0) = a_2_0_orders_2('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_234])).

tff(c_255,plain,(
    a_2_0_orders_2('#skF_4',k1_xboole_0) = k2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_250])).

tff(c_1743,plain,(
    ! [D_232,B_233,C_234] :
      ( r2_hidden('#skF_3'(D_232,B_233,C_234,D_232),C_234)
      | r2_hidden(D_232,a_2_0_orders_2(B_233,C_234))
      | ~ m1_subset_1(D_232,u1_struct_0(B_233))
      | ~ m1_subset_1(C_234,k1_zfmisc_1(u1_struct_0(B_233)))
      | ~ l1_orders_2(B_233)
      | ~ v5_orders_2(B_233)
      | ~ v4_orders_2(B_233)
      | ~ v3_orders_2(B_233)
      | v2_struct_0(B_233) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_1751,plain,(
    ! [D_232,C_234] :
      ( r2_hidden('#skF_3'(D_232,'#skF_4',C_234,D_232),C_234)
      | r2_hidden(D_232,a_2_0_orders_2('#skF_4',C_234))
      | ~ m1_subset_1(D_232,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_234,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_1743])).

tff(c_1761,plain,(
    ! [D_232,C_234] :
      ( r2_hidden('#skF_3'(D_232,'#skF_4',C_234,D_232),C_234)
      | r2_hidden(D_232,a_2_0_orders_2('#skF_4',C_234))
      | ~ m1_subset_1(D_232,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(C_234,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_102,c_1751])).

tff(c_1765,plain,(
    ! [D_235,C_236] :
      ( r2_hidden('#skF_3'(D_235,'#skF_4',C_236,D_235),C_236)
      | r2_hidden(D_235,a_2_0_orders_2('#skF_4',C_236))
      | ~ m1_subset_1(D_235,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(C_236,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1761])).

tff(c_1777,plain,(
    ! [D_235] :
      ( r2_hidden('#skF_3'(D_235,'#skF_4',k1_xboole_0,D_235),k1_xboole_0)
      | r2_hidden(D_235,a_2_0_orders_2('#skF_4',k1_xboole_0))
      | ~ m1_subset_1(D_235,k2_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_8,c_1765])).

tff(c_1787,plain,(
    ! [D_237] :
      ( r2_hidden('#skF_3'(D_237,'#skF_4',k1_xboole_0,D_237),k1_xboole_0)
      | r2_hidden(D_237,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(D_237,k2_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_255,c_1777])).

tff(c_12,plain,(
    ! [B_9,A_8] :
      ( ~ r1_tarski(B_9,A_8)
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1799,plain,(
    ! [D_237] :
      ( ~ r1_tarski(k1_xboole_0,'#skF_3'(D_237,'#skF_4',k1_xboole_0,D_237))
      | r2_hidden(D_237,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(D_237,k2_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_1787,c_12])).

tff(c_1808,plain,(
    ! [D_237] :
      ( r2_hidden(D_237,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(D_237,k2_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1799])).

tff(c_2159,plain,(
    ! [B_273,E_274,A_275,C_276] :
      ( r2_orders_2(B_273,E_274,'#skF_2'(A_275,B_273,C_276))
      | ~ r2_hidden(E_274,C_276)
      | ~ m1_subset_1(E_274,u1_struct_0(B_273))
      | ~ r2_hidden(A_275,a_2_0_orders_2(B_273,C_276))
      | ~ m1_subset_1(C_276,k1_zfmisc_1(u1_struct_0(B_273)))
      | ~ l1_orders_2(B_273)
      | ~ v5_orders_2(B_273)
      | ~ v4_orders_2(B_273)
      | ~ v3_orders_2(B_273)
      | v2_struct_0(B_273) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_2170,plain,(
    ! [E_274,A_275,C_276] :
      ( r2_orders_2('#skF_4',E_274,'#skF_2'(A_275,'#skF_4',C_276))
      | ~ r2_hidden(E_274,C_276)
      | ~ m1_subset_1(E_274,u1_struct_0('#skF_4'))
      | ~ r2_hidden(A_275,a_2_0_orders_2('#skF_4',C_276))
      | ~ m1_subset_1(C_276,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_2159])).

tff(c_2181,plain,(
    ! [E_274,A_275,C_276] :
      ( r2_orders_2('#skF_4',E_274,'#skF_2'(A_275,'#skF_4',C_276))
      | ~ r2_hidden(E_274,C_276)
      | ~ m1_subset_1(E_274,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_275,a_2_0_orders_2('#skF_4',C_276))
      | ~ m1_subset_1(C_276,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_102,c_2170])).

tff(c_2185,plain,(
    ! [E_277,A_278,C_279] :
      ( r2_orders_2('#skF_4',E_277,'#skF_2'(A_278,'#skF_4',C_279))
      | ~ r2_hidden(E_277,C_279)
      | ~ m1_subset_1(E_277,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_278,a_2_0_orders_2('#skF_4',C_279))
      | ~ m1_subset_1(C_279,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_2181])).

tff(c_2548,plain,(
    ! [E_308,A_309] :
      ( r2_orders_2('#skF_4',E_308,'#skF_2'(A_309,'#skF_4',k2_struct_0('#skF_4')))
      | ~ r2_hidden(E_308,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(E_308,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_309,a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_59,c_2185])).

tff(c_26,plain,(
    ! [A_26,C_32] :
      ( ~ r2_orders_2(A_26,C_32,C_32)
      | ~ m1_subset_1(C_32,u1_struct_0(A_26))
      | ~ l1_orders_2(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2556,plain,(
    ! [A_309] :
      ( ~ m1_subset_1('#skF_2'(A_309,'#skF_4',k2_struct_0('#skF_4')),u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ r2_hidden('#skF_2'(A_309,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_2'(A_309,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_309,a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_2548,c_26])).

tff(c_2625,plain,(
    ! [A_311] :
      ( ~ r2_hidden('#skF_2'(A_311,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_2'(A_311,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_311,a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_102,c_2556])).

tff(c_2657,plain,(
    ! [A_314] :
      ( ~ r2_hidden(A_314,a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')))
      | ~ m1_subset_1('#skF_2'(A_314,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_1808,c_2625])).

tff(c_2661,plain,(
    ! [A_224] :
      ( ~ r2_hidden(A_224,a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')))
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_1672,c_2657])).

tff(c_2672,plain,(
    ! [A_315] : ~ r2_hidden(A_315,a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_2661])).

tff(c_2676,plain,(
    a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_2672])).

tff(c_2680,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_256,c_2676])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:17:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.11/1.92  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.11/1.93  
% 5.11/1.93  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.11/1.93  %$ r2_orders_2 > r1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_struct_0 > l1_orders_2 > k3_mcart_1 > k1_orders_2 > a_2_0_orders_2 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_4 > #skF_3
% 5.11/1.93  
% 5.11/1.93  %Foreground sorts:
% 5.11/1.93  
% 5.11/1.93  
% 5.11/1.93  %Background operators:
% 5.11/1.93  
% 5.11/1.93  
% 5.11/1.93  %Foreground operators:
% 5.11/1.93  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.11/1.93  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 5.11/1.93  tff(k1_orders_2, type, k1_orders_2: ($i * $i) > $i).
% 5.11/1.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.11/1.93  tff(a_2_0_orders_2, type, a_2_0_orders_2: ($i * $i) > $i).
% 5.11/1.93  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.11/1.93  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.11/1.93  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 5.11/1.93  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.11/1.93  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 5.11/1.93  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.11/1.93  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.11/1.93  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 5.11/1.93  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 5.11/1.93  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.11/1.93  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.11/1.93  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 5.11/1.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.11/1.93  tff('#skF_4', type, '#skF_4': $i).
% 5.11/1.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.11/1.93  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 5.11/1.93  tff(k1_struct_0, type, k1_struct_0: $i > $i).
% 5.11/1.93  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 5.11/1.93  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.11/1.93  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 5.11/1.93  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 5.11/1.93  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.11/1.93  
% 5.11/1.95  tff(f_29, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 5.11/1.95  tff(f_31, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 5.11/1.95  tff(f_157, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (k1_orders_2(A, k2_struct_0(A)) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_orders_2)).
% 5.11/1.95  tff(f_103, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 5.11/1.95  tff(f_68, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 5.11/1.95  tff(f_99, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_orders_2(A, B) = a_2_0_orders_2(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_orders_2)).
% 5.11/1.95  tff(f_60, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_mcart_1)).
% 5.11/1.95  tff(f_130, axiom, (![A, B, C]: ((((((~v2_struct_0(B) & v3_orders_2(B)) & v4_orders_2(B)) & v5_orders_2(B)) & l1_orders_2(B)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B)))) => (r2_hidden(A, a_2_0_orders_2(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r2_hidden(E, C) => r2_orders_2(B, E, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fraenkel_a_2_0_orders_2)).
% 5.11/1.95  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.11/1.95  tff(f_64, axiom, (![A]: (l1_struct_0(A) => (k1_struct_0(A) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_struct_0)).
% 5.11/1.95  tff(f_143, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (k1_orders_2(A, k1_struct_0(A)) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_orders_2)).
% 5.11/1.95  tff(f_33, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 5.11/1.95  tff(f_44, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 5.11/1.95  tff(f_83, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_orders_2(A, B, C) <=> (r1_orders_2(A, B, C) & ~(B = C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_orders_2)).
% 5.11/1.95  tff(c_4, plain, (![A_2]: (k2_subset_1(A_2)=A_2)), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.11/1.95  tff(c_6, plain, (![A_3]: (m1_subset_1(k2_subset_1(A_3), k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.11/1.95  tff(c_59, plain, (![A_3]: (m1_subset_1(A_3, k1_zfmisc_1(A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6])).
% 5.11/1.95  tff(c_58, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_157])).
% 5.11/1.95  tff(c_56, plain, (v3_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_157])).
% 5.11/1.95  tff(c_54, plain, (v4_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_157])).
% 5.11/1.95  tff(c_52, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_157])).
% 5.11/1.95  tff(c_50, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_157])).
% 5.11/1.95  tff(c_32, plain, (![A_36]: (l1_struct_0(A_36) | ~l1_orders_2(A_36))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.11/1.95  tff(c_87, plain, (![A_58]: (u1_struct_0(A_58)=k2_struct_0(A_58) | ~l1_struct_0(A_58))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.11/1.95  tff(c_98, plain, (![A_62]: (u1_struct_0(A_62)=k2_struct_0(A_62) | ~l1_orders_2(A_62))), inference(resolution, [status(thm)], [c_32, c_87])).
% 5.11/1.95  tff(c_102, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_50, c_98])).
% 5.11/1.95  tff(c_207, plain, (![A_102, B_103]: (k1_orders_2(A_102, B_103)=a_2_0_orders_2(A_102, B_103) | ~m1_subset_1(B_103, k1_zfmisc_1(u1_struct_0(A_102))) | ~l1_orders_2(A_102) | ~v5_orders_2(A_102) | ~v4_orders_2(A_102) | ~v3_orders_2(A_102) | v2_struct_0(A_102))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.11/1.95  tff(c_218, plain, (![B_103]: (k1_orders_2('#skF_4', B_103)=a_2_0_orders_2('#skF_4', B_103) | ~m1_subset_1(B_103, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_102, c_207])).
% 5.11/1.95  tff(c_230, plain, (![B_103]: (k1_orders_2('#skF_4', B_103)=a_2_0_orders_2('#skF_4', B_103) | ~m1_subset_1(B_103, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_218])).
% 5.11/1.95  tff(c_234, plain, (![B_104]: (k1_orders_2('#skF_4', B_104)=a_2_0_orders_2('#skF_4', B_104) | ~m1_subset_1(B_104, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_58, c_230])).
% 5.11/1.95  tff(c_253, plain, (k1_orders_2('#skF_4', k2_struct_0('#skF_4'))=a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_59, c_234])).
% 5.11/1.95  tff(c_48, plain, (k1_orders_2('#skF_4', k2_struct_0('#skF_4'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_157])).
% 5.11/1.95  tff(c_256, plain, (a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_253, c_48])).
% 5.11/1.95  tff(c_14, plain, (![A_10]: (r2_hidden('#skF_1'(A_10), A_10) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.11/1.95  tff(c_1663, plain, (![A_224, B_225, C_226]: (m1_subset_1('#skF_2'(A_224, B_225, C_226), u1_struct_0(B_225)) | ~r2_hidden(A_224, a_2_0_orders_2(B_225, C_226)) | ~m1_subset_1(C_226, k1_zfmisc_1(u1_struct_0(B_225))) | ~l1_orders_2(B_225) | ~v5_orders_2(B_225) | ~v4_orders_2(B_225) | ~v3_orders_2(B_225) | v2_struct_0(B_225))), inference(cnfTransformation, [status(thm)], [f_130])).
% 5.11/1.95  tff(c_1668, plain, (![A_224, C_226]: (m1_subset_1('#skF_2'(A_224, '#skF_4', C_226), k2_struct_0('#skF_4')) | ~r2_hidden(A_224, a_2_0_orders_2('#skF_4', C_226)) | ~m1_subset_1(C_226, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_102, c_1663])).
% 5.11/1.95  tff(c_1671, plain, (![A_224, C_226]: (m1_subset_1('#skF_2'(A_224, '#skF_4', C_226), k2_struct_0('#skF_4')) | ~r2_hidden(A_224, a_2_0_orders_2('#skF_4', C_226)) | ~m1_subset_1(C_226, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_102, c_1668])).
% 5.11/1.95  tff(c_1672, plain, (![A_224, C_226]: (m1_subset_1('#skF_2'(A_224, '#skF_4', C_226), k2_struct_0('#skF_4')) | ~r2_hidden(A_224, a_2_0_orders_2('#skF_4', C_226)) | ~m1_subset_1(C_226, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_58, c_1671])).
% 5.11/1.95  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.11/1.95  tff(c_73, plain, (![A_56]: (k1_struct_0(A_56)=k1_xboole_0 | ~l1_struct_0(A_56))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.11/1.95  tff(c_78, plain, (![A_57]: (k1_struct_0(A_57)=k1_xboole_0 | ~l1_orders_2(A_57))), inference(resolution, [status(thm)], [c_32, c_73])).
% 5.11/1.95  tff(c_82, plain, (k1_struct_0('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_50, c_78])).
% 5.11/1.95  tff(c_148, plain, (![A_88]: (k1_orders_2(A_88, k1_struct_0(A_88))=u1_struct_0(A_88) | ~l1_orders_2(A_88) | ~v5_orders_2(A_88) | ~v4_orders_2(A_88) | ~v3_orders_2(A_88) | v2_struct_0(A_88))), inference(cnfTransformation, [status(thm)], [f_143])).
% 5.11/1.95  tff(c_157, plain, (k1_orders_2('#skF_4', k1_xboole_0)=u1_struct_0('#skF_4') | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_82, c_148])).
% 5.11/1.95  tff(c_161, plain, (k1_orders_2('#skF_4', k1_xboole_0)=k2_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_102, c_157])).
% 5.11/1.95  tff(c_162, plain, (k1_orders_2('#skF_4', k1_xboole_0)=k2_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_58, c_161])).
% 5.11/1.95  tff(c_8, plain, (![A_4]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.11/1.95  tff(c_250, plain, (k1_orders_2('#skF_4', k1_xboole_0)=a_2_0_orders_2('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_234])).
% 5.11/1.95  tff(c_255, plain, (a_2_0_orders_2('#skF_4', k1_xboole_0)=k2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_162, c_250])).
% 5.11/1.95  tff(c_1743, plain, (![D_232, B_233, C_234]: (r2_hidden('#skF_3'(D_232, B_233, C_234, D_232), C_234) | r2_hidden(D_232, a_2_0_orders_2(B_233, C_234)) | ~m1_subset_1(D_232, u1_struct_0(B_233)) | ~m1_subset_1(C_234, k1_zfmisc_1(u1_struct_0(B_233))) | ~l1_orders_2(B_233) | ~v5_orders_2(B_233) | ~v4_orders_2(B_233) | ~v3_orders_2(B_233) | v2_struct_0(B_233))), inference(cnfTransformation, [status(thm)], [f_130])).
% 5.11/1.95  tff(c_1751, plain, (![D_232, C_234]: (r2_hidden('#skF_3'(D_232, '#skF_4', C_234, D_232), C_234) | r2_hidden(D_232, a_2_0_orders_2('#skF_4', C_234)) | ~m1_subset_1(D_232, u1_struct_0('#skF_4')) | ~m1_subset_1(C_234, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_102, c_1743])).
% 5.11/1.95  tff(c_1761, plain, (![D_232, C_234]: (r2_hidden('#skF_3'(D_232, '#skF_4', C_234, D_232), C_234) | r2_hidden(D_232, a_2_0_orders_2('#skF_4', C_234)) | ~m1_subset_1(D_232, k2_struct_0('#skF_4')) | ~m1_subset_1(C_234, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_102, c_1751])).
% 5.11/1.95  tff(c_1765, plain, (![D_235, C_236]: (r2_hidden('#skF_3'(D_235, '#skF_4', C_236, D_235), C_236) | r2_hidden(D_235, a_2_0_orders_2('#skF_4', C_236)) | ~m1_subset_1(D_235, k2_struct_0('#skF_4')) | ~m1_subset_1(C_236, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_58, c_1761])).
% 5.11/1.95  tff(c_1777, plain, (![D_235]: (r2_hidden('#skF_3'(D_235, '#skF_4', k1_xboole_0, D_235), k1_xboole_0) | r2_hidden(D_235, a_2_0_orders_2('#skF_4', k1_xboole_0)) | ~m1_subset_1(D_235, k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_8, c_1765])).
% 5.11/1.95  tff(c_1787, plain, (![D_237]: (r2_hidden('#skF_3'(D_237, '#skF_4', k1_xboole_0, D_237), k1_xboole_0) | r2_hidden(D_237, k2_struct_0('#skF_4')) | ~m1_subset_1(D_237, k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_255, c_1777])).
% 5.11/1.95  tff(c_12, plain, (![B_9, A_8]: (~r1_tarski(B_9, A_8) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.11/1.95  tff(c_1799, plain, (![D_237]: (~r1_tarski(k1_xboole_0, '#skF_3'(D_237, '#skF_4', k1_xboole_0, D_237)) | r2_hidden(D_237, k2_struct_0('#skF_4')) | ~m1_subset_1(D_237, k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_1787, c_12])).
% 5.11/1.95  tff(c_1808, plain, (![D_237]: (r2_hidden(D_237, k2_struct_0('#skF_4')) | ~m1_subset_1(D_237, k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1799])).
% 5.11/1.95  tff(c_2159, plain, (![B_273, E_274, A_275, C_276]: (r2_orders_2(B_273, E_274, '#skF_2'(A_275, B_273, C_276)) | ~r2_hidden(E_274, C_276) | ~m1_subset_1(E_274, u1_struct_0(B_273)) | ~r2_hidden(A_275, a_2_0_orders_2(B_273, C_276)) | ~m1_subset_1(C_276, k1_zfmisc_1(u1_struct_0(B_273))) | ~l1_orders_2(B_273) | ~v5_orders_2(B_273) | ~v4_orders_2(B_273) | ~v3_orders_2(B_273) | v2_struct_0(B_273))), inference(cnfTransformation, [status(thm)], [f_130])).
% 5.11/1.95  tff(c_2170, plain, (![E_274, A_275, C_276]: (r2_orders_2('#skF_4', E_274, '#skF_2'(A_275, '#skF_4', C_276)) | ~r2_hidden(E_274, C_276) | ~m1_subset_1(E_274, u1_struct_0('#skF_4')) | ~r2_hidden(A_275, a_2_0_orders_2('#skF_4', C_276)) | ~m1_subset_1(C_276, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_102, c_2159])).
% 5.11/1.95  tff(c_2181, plain, (![E_274, A_275, C_276]: (r2_orders_2('#skF_4', E_274, '#skF_2'(A_275, '#skF_4', C_276)) | ~r2_hidden(E_274, C_276) | ~m1_subset_1(E_274, k2_struct_0('#skF_4')) | ~r2_hidden(A_275, a_2_0_orders_2('#skF_4', C_276)) | ~m1_subset_1(C_276, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_102, c_2170])).
% 5.11/1.95  tff(c_2185, plain, (![E_277, A_278, C_279]: (r2_orders_2('#skF_4', E_277, '#skF_2'(A_278, '#skF_4', C_279)) | ~r2_hidden(E_277, C_279) | ~m1_subset_1(E_277, k2_struct_0('#skF_4')) | ~r2_hidden(A_278, a_2_0_orders_2('#skF_4', C_279)) | ~m1_subset_1(C_279, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_58, c_2181])).
% 5.11/1.95  tff(c_2548, plain, (![E_308, A_309]: (r2_orders_2('#skF_4', E_308, '#skF_2'(A_309, '#skF_4', k2_struct_0('#skF_4'))) | ~r2_hidden(E_308, k2_struct_0('#skF_4')) | ~m1_subset_1(E_308, k2_struct_0('#skF_4')) | ~r2_hidden(A_309, a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_59, c_2185])).
% 5.11/1.95  tff(c_26, plain, (![A_26, C_32]: (~r2_orders_2(A_26, C_32, C_32) | ~m1_subset_1(C_32, u1_struct_0(A_26)) | ~l1_orders_2(A_26))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.11/1.95  tff(c_2556, plain, (![A_309]: (~m1_subset_1('#skF_2'(A_309, '#skF_4', k2_struct_0('#skF_4')), u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~r2_hidden('#skF_2'(A_309, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_2'(A_309, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')) | ~r2_hidden(A_309, a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_2548, c_26])).
% 5.11/1.95  tff(c_2625, plain, (![A_311]: (~r2_hidden('#skF_2'(A_311, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_2'(A_311, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')) | ~r2_hidden(A_311, a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_102, c_2556])).
% 5.11/1.95  tff(c_2657, plain, (![A_314]: (~r2_hidden(A_314, a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))) | ~m1_subset_1('#skF_2'(A_314, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_1808, c_2625])).
% 5.11/1.95  tff(c_2661, plain, (![A_224]: (~r2_hidden(A_224, a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_1672, c_2657])).
% 5.11/1.95  tff(c_2672, plain, (![A_315]: (~r2_hidden(A_315, a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_2661])).
% 5.11/1.95  tff(c_2676, plain, (a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_14, c_2672])).
% 5.11/1.95  tff(c_2680, plain, $false, inference(negUnitSimplification, [status(thm)], [c_256, c_2676])).
% 5.11/1.95  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.11/1.95  
% 5.11/1.95  Inference rules
% 5.11/1.95  ----------------------
% 5.11/1.95  #Ref     : 0
% 5.11/1.95  #Sup     : 532
% 5.11/1.95  #Fact    : 0
% 5.11/1.95  #Define  : 0
% 5.11/1.95  #Split   : 15
% 5.11/1.95  #Chain   : 0
% 5.11/1.95  #Close   : 0
% 5.11/1.95  
% 5.11/1.95  Ordering : KBO
% 5.11/1.95  
% 5.11/1.95  Simplification rules
% 5.11/1.95  ----------------------
% 5.11/1.95  #Subsume      : 80
% 5.11/1.95  #Demod        : 751
% 5.11/1.95  #Tautology    : 138
% 5.11/1.95  #SimpNegUnit  : 131
% 5.11/1.95  #BackRed      : 37
% 5.11/1.95  
% 5.11/1.95  #Partial instantiations: 0
% 5.11/1.95  #Strategies tried      : 1
% 5.11/1.95  
% 5.11/1.95  Timing (in seconds)
% 5.11/1.95  ----------------------
% 5.11/1.95  Preprocessing        : 0.33
% 5.11/1.95  Parsing              : 0.17
% 5.11/1.95  CNF conversion       : 0.02
% 5.11/1.95  Main loop            : 0.84
% 5.11/1.95  Inferencing          : 0.27
% 5.11/1.95  Reduction            : 0.29
% 5.11/1.95  Demodulation         : 0.21
% 5.11/1.95  BG Simplification    : 0.04
% 5.11/1.95  Subsumption          : 0.18
% 5.11/1.95  Abstraction          : 0.05
% 5.11/1.95  MUC search           : 0.00
% 5.11/1.95  Cooper               : 0.00
% 5.11/1.95  Total                : 1.21
% 5.11/1.95  Index Insertion      : 0.00
% 5.11/1.95  Index Deletion       : 0.00
% 5.11/1.95  Index Matching       : 0.00
% 5.11/1.95  BG Taut test         : 0.00
%------------------------------------------------------------------------------
