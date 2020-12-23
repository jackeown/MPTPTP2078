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
% DateTime   : Thu Dec  3 10:19:31 EST 2020

% Result     : Theorem 4.83s
% Output     : CNFRefutation 4.83s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 588 expanded)
%              Number of leaves         :   36 ( 211 expanded)
%              Depth                    :   20
%              Number of atoms          :  237 (1427 expanded)
%              Number of equality atoms :   29 ( 275 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r1_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k4_tarski > k2_orders_2 > a_2_1_orders_2 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_4 > #skF_3

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_54,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_153,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => k2_orders_2(A,k2_struct_0(A)) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_orders_2)).

tff(f_112,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).

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

tff(f_139,axiom,(
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

tff(f_38,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

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

tff(f_108,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_orders_2(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_orders_2)).

tff(c_6,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_1'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_42,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_26,plain,(
    ! [A_30] :
      ( l1_struct_0(A_30)
      | ~ l1_orders_2(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_53,plain,(
    ! [A_46] :
      ( u1_struct_0(A_46) = k2_struct_0(A_46)
      | ~ l1_struct_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_59,plain,(
    ! [A_48] :
      ( u1_struct_0(A_48) = k2_struct_0(A_48)
      | ~ l1_orders_2(A_48) ) ),
    inference(resolution,[status(thm)],[c_26,c_53])).

tff(c_63,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_59])).

tff(c_14,plain,(
    ! [A_17] :
      ( m1_subset_1(k2_struct_0(A_17),k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ l1_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_67,plain,
    ( m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | ~ l1_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_14])).

tff(c_72,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_67])).

tff(c_75,plain,(
    ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_72])).

tff(c_79,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_75])).

tff(c_80,plain,(
    m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_67])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_48,plain,(
    v3_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_46,plain,(
    v4_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_44,plain,(
    v5_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_139,plain,(
    ! [A_85,B_86] :
      ( k2_orders_2(A_85,B_86) = a_2_1_orders_2(A_85,B_86)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_orders_2(A_85)
      | ~ v5_orders_2(A_85)
      | ~ v4_orders_2(A_85)
      | ~ v3_orders_2(A_85)
      | v2_struct_0(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_142,plain,(
    ! [B_86] :
      ( k2_orders_2('#skF_4',B_86) = a_2_1_orders_2('#skF_4',B_86)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_139])).

tff(c_147,plain,(
    ! [B_86] :
      ( k2_orders_2('#skF_4',B_86) = a_2_1_orders_2('#skF_4',B_86)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_142])).

tff(c_150,plain,(
    ! [B_87] :
      ( k2_orders_2('#skF_4',B_87) = a_2_1_orders_2('#skF_4',B_87)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_147])).

tff(c_154,plain,(
    k2_orders_2('#skF_4',k2_struct_0('#skF_4')) = a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_80,c_150])).

tff(c_40,plain,(
    k2_orders_2('#skF_4',k2_struct_0('#skF_4')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_169,plain,(
    a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_40])).

tff(c_368,plain,(
    ! [A_97,B_98,C_99] :
      ( m1_subset_1('#skF_2'(A_97,B_98,C_99),u1_struct_0(B_98))
      | ~ r2_hidden(A_97,a_2_1_orders_2(B_98,C_99))
      | ~ m1_subset_1(C_99,k1_zfmisc_1(u1_struct_0(B_98)))
      | ~ l1_orders_2(B_98)
      | ~ v5_orders_2(B_98)
      | ~ v4_orders_2(B_98)
      | ~ v3_orders_2(B_98)
      | v2_struct_0(B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_373,plain,(
    ! [A_97,C_99] :
      ( m1_subset_1('#skF_2'(A_97,'#skF_4',C_99),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_97,a_2_1_orders_2('#skF_4',C_99))
      | ~ m1_subset_1(C_99,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_368])).

tff(c_376,plain,(
    ! [A_97,C_99] :
      ( m1_subset_1('#skF_2'(A_97,'#skF_4',C_99),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_97,a_2_1_orders_2('#skF_4',C_99))
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_63,c_373])).

tff(c_377,plain,(
    ! [A_97,C_99] :
      ( m1_subset_1('#skF_2'(A_97,'#skF_4',C_99),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_97,a_2_1_orders_2('#skF_4',C_99))
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_376])).

tff(c_4,plain,(
    ! [C_5,B_4,A_3] :
      ( ~ v1_xboole_0(C_5)
      | ~ m1_subset_1(B_4,k1_zfmisc_1(C_5))
      | ~ r2_hidden(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_93,plain,(
    ! [A_3] :
      ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_3,k2_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_80,c_4])).

tff(c_94,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_93])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_hidden(A_1,B_2)
      | v1_xboole_0(B_2)
      | ~ m1_subset_1(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2181,plain,(
    ! [B_214,A_215,C_216,E_217] :
      ( r2_orders_2(B_214,'#skF_2'(A_215,B_214,C_216),E_217)
      | ~ r2_hidden(E_217,C_216)
      | ~ m1_subset_1(E_217,u1_struct_0(B_214))
      | ~ r2_hidden(A_215,a_2_1_orders_2(B_214,C_216))
      | ~ m1_subset_1(C_216,k1_zfmisc_1(u1_struct_0(B_214)))
      | ~ l1_orders_2(B_214)
      | ~ v5_orders_2(B_214)
      | ~ v4_orders_2(B_214)
      | ~ v3_orders_2(B_214)
      | v2_struct_0(B_214) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_2185,plain,(
    ! [A_215,C_216,E_217] :
      ( r2_orders_2('#skF_4','#skF_2'(A_215,'#skF_4',C_216),E_217)
      | ~ r2_hidden(E_217,C_216)
      | ~ m1_subset_1(E_217,u1_struct_0('#skF_4'))
      | ~ r2_hidden(A_215,a_2_1_orders_2('#skF_4',C_216))
      | ~ m1_subset_1(C_216,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_2181])).

tff(c_2190,plain,(
    ! [A_215,C_216,E_217] :
      ( r2_orders_2('#skF_4','#skF_2'(A_215,'#skF_4',C_216),E_217)
      | ~ r2_hidden(E_217,C_216)
      | ~ m1_subset_1(E_217,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_215,a_2_1_orders_2('#skF_4',C_216))
      | ~ m1_subset_1(C_216,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_63,c_2185])).

tff(c_2193,plain,(
    ! [A_218,C_219,E_220] :
      ( r2_orders_2('#skF_4','#skF_2'(A_218,'#skF_4',C_219),E_220)
      | ~ r2_hidden(E_220,C_219)
      | ~ m1_subset_1(E_220,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_218,a_2_1_orders_2('#skF_4',C_219))
      | ~ m1_subset_1(C_219,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_2190])).

tff(c_2221,plain,(
    ! [A_221,E_222] :
      ( r2_orders_2('#skF_4','#skF_2'(A_221,'#skF_4',k2_struct_0('#skF_4')),E_222)
      | ~ r2_hidden(E_222,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(E_222,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_221,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_80,c_2193])).

tff(c_18,plain,(
    ! [A_18,C_24] :
      ( ~ r2_orders_2(A_18,C_24,C_24)
      | ~ m1_subset_1(C_24,u1_struct_0(A_18))
      | ~ l1_orders_2(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2229,plain,(
    ! [A_221] :
      ( ~ m1_subset_1('#skF_2'(A_221,'#skF_4',k2_struct_0('#skF_4')),u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ r2_hidden('#skF_2'(A_221,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_2'(A_221,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_221,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_2221,c_18])).

tff(c_2243,plain,(
    ! [A_223] :
      ( ~ r2_hidden('#skF_2'(A_223,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_2'(A_223,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_223,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_63,c_2229])).

tff(c_2249,plain,(
    ! [A_223] :
      ( ~ r2_hidden(A_223,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')))
      | v1_xboole_0(k2_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_2'(A_223,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_2,c_2243])).

tff(c_2266,plain,(
    ! [A_225] :
      ( ~ r2_hidden(A_225,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')))
      | ~ m1_subset_1('#skF_2'(A_225,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_2249])).

tff(c_2273,plain,(
    ! [A_97] :
      ( ~ r2_hidden(A_97,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')))
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_377,c_2266])).

tff(c_2281,plain,(
    ! [A_226] : ~ r2_hidden(A_226,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_2273])).

tff(c_2289,plain,(
    a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_2281])).

tff(c_2294,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_169,c_2289])).

tff(c_2297,plain,(
    ! [A_227] : ~ r2_hidden(A_227,k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_93])).

tff(c_2308,plain,(
    k2_struct_0('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_2297])).

tff(c_2311,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2308,c_2308,c_80])).

tff(c_2312,plain,(
    u1_struct_0('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2308,c_63])).

tff(c_2418,plain,(
    ! [A_260,B_261] :
      ( k2_orders_2(A_260,B_261) = a_2_1_orders_2(A_260,B_261)
      | ~ m1_subset_1(B_261,k1_zfmisc_1(u1_struct_0(A_260)))
      | ~ l1_orders_2(A_260)
      | ~ v5_orders_2(A_260)
      | ~ v4_orders_2(A_260)
      | ~ v3_orders_2(A_260)
      | v2_struct_0(A_260) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2421,plain,(
    ! [B_261] :
      ( k2_orders_2('#skF_4',B_261) = a_2_1_orders_2('#skF_4',B_261)
      | ~ m1_subset_1(B_261,k1_zfmisc_1(k1_xboole_0))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2312,c_2418])).

tff(c_2426,plain,(
    ! [B_261] :
      ( k2_orders_2('#skF_4',B_261) = a_2_1_orders_2('#skF_4',B_261)
      | ~ m1_subset_1(B_261,k1_zfmisc_1(k1_xboole_0))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_2421])).

tff(c_2429,plain,(
    ! [B_262] :
      ( k2_orders_2('#skF_4',B_262) = a_2_1_orders_2('#skF_4',B_262)
      | ~ m1_subset_1(B_262,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_2426])).

tff(c_2433,plain,(
    k2_orders_2('#skF_4',k1_xboole_0) = a_2_1_orders_2('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2311,c_2429])).

tff(c_2313,plain,(
    k2_orders_2('#skF_4',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2308,c_40])).

tff(c_2434,plain,(
    a_2_1_orders_2('#skF_4',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2433,c_2313])).

tff(c_2296,plain,(
    v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_93])).

tff(c_2310,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2308,c_2296])).

tff(c_2439,plain,(
    ! [A_263,B_264] :
      ( m1_subset_1(k2_orders_2(A_263,B_264),k1_zfmisc_1(u1_struct_0(A_263)))
      | ~ m1_subset_1(B_264,k1_zfmisc_1(u1_struct_0(A_263)))
      | ~ l1_orders_2(A_263)
      | ~ v5_orders_2(A_263)
      | ~ v4_orders_2(A_263)
      | ~ v3_orders_2(A_263)
      | v2_struct_0(A_263) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_2447,plain,
    ( m1_subset_1(a_2_1_orders_2('#skF_4',k1_xboole_0),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2433,c_2439])).

tff(c_2454,plain,
    ( m1_subset_1(a_2_1_orders_2('#skF_4',k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_2311,c_2312,c_2312,c_2447])).

tff(c_2455,plain,(
    m1_subset_1(a_2_1_orders_2('#skF_4',k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_2454])).

tff(c_2463,plain,(
    ! [A_3] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_3,a_2_1_orders_2('#skF_4',k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_2455,c_4])).

tff(c_2468,plain,(
    ! [A_265] : ~ r2_hidden(A_265,a_2_1_orders_2('#skF_4',k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2310,c_2463])).

tff(c_2476,plain,(
    a_2_1_orders_2('#skF_4',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_2468])).

tff(c_2481,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2434,c_2476])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:12:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.83/1.88  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.83/1.89  
% 4.83/1.89  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.83/1.89  %$ r2_orders_2 > r1_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k4_tarski > k2_orders_2 > a_2_1_orders_2 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_4 > #skF_3
% 4.83/1.89  
% 4.83/1.89  %Foreground sorts:
% 4.83/1.89  
% 4.83/1.89  
% 4.83/1.89  %Background operators:
% 4.83/1.89  
% 4.83/1.89  
% 4.83/1.89  %Foreground operators:
% 4.83/1.89  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.83/1.89  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 4.83/1.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.83/1.89  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.83/1.89  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.83/1.89  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.83/1.89  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 4.83/1.89  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.83/1.89  tff(a_2_1_orders_2, type, a_2_1_orders_2: ($i * $i) > $i).
% 4.83/1.89  tff(k2_orders_2, type, k2_orders_2: ($i * $i) > $i).
% 4.83/1.89  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.83/1.89  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 4.83/1.89  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 4.83/1.89  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.83/1.89  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.83/1.89  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 4.83/1.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.83/1.89  tff('#skF_4', type, '#skF_4': $i).
% 4.83/1.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.83/1.89  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 4.83/1.89  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 4.83/1.89  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.83/1.89  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.83/1.89  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.83/1.89  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.83/1.89  
% 4.83/1.91  tff(f_54, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_mcart_1)).
% 4.83/1.91  tff(f_153, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (k2_orders_2(A, k2_struct_0(A)) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_orders_2)).
% 4.83/1.91  tff(f_112, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 4.83/1.91  tff(f_58, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 4.83/1.91  tff(f_62, axiom, (![A]: (l1_struct_0(A) => m1_subset_1(k2_struct_0(A), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 4.83/1.91  tff(f_93, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_orders_2(A, B) = a_2_1_orders_2(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_orders_2)).
% 4.83/1.91  tff(f_139, axiom, (![A, B, C]: ((((((~v2_struct_0(B) & v3_orders_2(B)) & v4_orders_2(B)) & v5_orders_2(B)) & l1_orders_2(B)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B)))) => (r2_hidden(A, a_2_1_orders_2(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r2_hidden(E, C) => r2_orders_2(B, D, E))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_1_orders_2)).
% 4.83/1.91  tff(f_38, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 4.83/1.91  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 4.83/1.91  tff(f_77, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_orders_2(A, B, C) <=> (r1_orders_2(A, B, C) & ~(B = C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_orders_2)).
% 4.83/1.91  tff(f_108, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_orders_2(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_orders_2)).
% 4.83/1.91  tff(c_6, plain, (![A_6]: (r2_hidden('#skF_1'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.83/1.91  tff(c_42, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_153])).
% 4.83/1.91  tff(c_26, plain, (![A_30]: (l1_struct_0(A_30) | ~l1_orders_2(A_30))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.83/1.91  tff(c_53, plain, (![A_46]: (u1_struct_0(A_46)=k2_struct_0(A_46) | ~l1_struct_0(A_46))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.83/1.91  tff(c_59, plain, (![A_48]: (u1_struct_0(A_48)=k2_struct_0(A_48) | ~l1_orders_2(A_48))), inference(resolution, [status(thm)], [c_26, c_53])).
% 4.83/1.91  tff(c_63, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_42, c_59])).
% 4.83/1.91  tff(c_14, plain, (![A_17]: (m1_subset_1(k2_struct_0(A_17), k1_zfmisc_1(u1_struct_0(A_17))) | ~l1_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.83/1.91  tff(c_67, plain, (m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_63, c_14])).
% 4.83/1.91  tff(c_72, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_67])).
% 4.83/1.91  tff(c_75, plain, (~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_26, c_72])).
% 4.83/1.91  tff(c_79, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_75])).
% 4.83/1.91  tff(c_80, plain, (m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_67])).
% 4.83/1.91  tff(c_50, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_153])).
% 4.83/1.91  tff(c_48, plain, (v3_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_153])).
% 4.83/1.91  tff(c_46, plain, (v4_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_153])).
% 4.83/1.91  tff(c_44, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_153])).
% 4.83/1.91  tff(c_139, plain, (![A_85, B_86]: (k2_orders_2(A_85, B_86)=a_2_1_orders_2(A_85, B_86) | ~m1_subset_1(B_86, k1_zfmisc_1(u1_struct_0(A_85))) | ~l1_orders_2(A_85) | ~v5_orders_2(A_85) | ~v4_orders_2(A_85) | ~v3_orders_2(A_85) | v2_struct_0(A_85))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.83/1.91  tff(c_142, plain, (![B_86]: (k2_orders_2('#skF_4', B_86)=a_2_1_orders_2('#skF_4', B_86) | ~m1_subset_1(B_86, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_63, c_139])).
% 4.83/1.91  tff(c_147, plain, (![B_86]: (k2_orders_2('#skF_4', B_86)=a_2_1_orders_2('#skF_4', B_86) | ~m1_subset_1(B_86, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_142])).
% 4.83/1.91  tff(c_150, plain, (![B_87]: (k2_orders_2('#skF_4', B_87)=a_2_1_orders_2('#skF_4', B_87) | ~m1_subset_1(B_87, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_147])).
% 4.83/1.91  tff(c_154, plain, (k2_orders_2('#skF_4', k2_struct_0('#skF_4'))=a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_80, c_150])).
% 4.83/1.91  tff(c_40, plain, (k2_orders_2('#skF_4', k2_struct_0('#skF_4'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_153])).
% 4.83/1.91  tff(c_169, plain, (a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_154, c_40])).
% 4.83/1.91  tff(c_368, plain, (![A_97, B_98, C_99]: (m1_subset_1('#skF_2'(A_97, B_98, C_99), u1_struct_0(B_98)) | ~r2_hidden(A_97, a_2_1_orders_2(B_98, C_99)) | ~m1_subset_1(C_99, k1_zfmisc_1(u1_struct_0(B_98))) | ~l1_orders_2(B_98) | ~v5_orders_2(B_98) | ~v4_orders_2(B_98) | ~v3_orders_2(B_98) | v2_struct_0(B_98))), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.83/1.91  tff(c_373, plain, (![A_97, C_99]: (m1_subset_1('#skF_2'(A_97, '#skF_4', C_99), k2_struct_0('#skF_4')) | ~r2_hidden(A_97, a_2_1_orders_2('#skF_4', C_99)) | ~m1_subset_1(C_99, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_63, c_368])).
% 4.83/1.91  tff(c_376, plain, (![A_97, C_99]: (m1_subset_1('#skF_2'(A_97, '#skF_4', C_99), k2_struct_0('#skF_4')) | ~r2_hidden(A_97, a_2_1_orders_2('#skF_4', C_99)) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_63, c_373])).
% 4.83/1.91  tff(c_377, plain, (![A_97, C_99]: (m1_subset_1('#skF_2'(A_97, '#skF_4', C_99), k2_struct_0('#skF_4')) | ~r2_hidden(A_97, a_2_1_orders_2('#skF_4', C_99)) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_376])).
% 4.83/1.91  tff(c_4, plain, (![C_5, B_4, A_3]: (~v1_xboole_0(C_5) | ~m1_subset_1(B_4, k1_zfmisc_1(C_5)) | ~r2_hidden(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.83/1.91  tff(c_93, plain, (![A_3]: (~v1_xboole_0(k2_struct_0('#skF_4')) | ~r2_hidden(A_3, k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_80, c_4])).
% 4.83/1.91  tff(c_94, plain, (~v1_xboole_0(k2_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_93])).
% 4.83/1.91  tff(c_2, plain, (![A_1, B_2]: (r2_hidden(A_1, B_2) | v1_xboole_0(B_2) | ~m1_subset_1(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.83/1.91  tff(c_2181, plain, (![B_214, A_215, C_216, E_217]: (r2_orders_2(B_214, '#skF_2'(A_215, B_214, C_216), E_217) | ~r2_hidden(E_217, C_216) | ~m1_subset_1(E_217, u1_struct_0(B_214)) | ~r2_hidden(A_215, a_2_1_orders_2(B_214, C_216)) | ~m1_subset_1(C_216, k1_zfmisc_1(u1_struct_0(B_214))) | ~l1_orders_2(B_214) | ~v5_orders_2(B_214) | ~v4_orders_2(B_214) | ~v3_orders_2(B_214) | v2_struct_0(B_214))), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.83/1.91  tff(c_2185, plain, (![A_215, C_216, E_217]: (r2_orders_2('#skF_4', '#skF_2'(A_215, '#skF_4', C_216), E_217) | ~r2_hidden(E_217, C_216) | ~m1_subset_1(E_217, u1_struct_0('#skF_4')) | ~r2_hidden(A_215, a_2_1_orders_2('#skF_4', C_216)) | ~m1_subset_1(C_216, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_63, c_2181])).
% 4.83/1.91  tff(c_2190, plain, (![A_215, C_216, E_217]: (r2_orders_2('#skF_4', '#skF_2'(A_215, '#skF_4', C_216), E_217) | ~r2_hidden(E_217, C_216) | ~m1_subset_1(E_217, k2_struct_0('#skF_4')) | ~r2_hidden(A_215, a_2_1_orders_2('#skF_4', C_216)) | ~m1_subset_1(C_216, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_63, c_2185])).
% 4.83/1.91  tff(c_2193, plain, (![A_218, C_219, E_220]: (r2_orders_2('#skF_4', '#skF_2'(A_218, '#skF_4', C_219), E_220) | ~r2_hidden(E_220, C_219) | ~m1_subset_1(E_220, k2_struct_0('#skF_4')) | ~r2_hidden(A_218, a_2_1_orders_2('#skF_4', C_219)) | ~m1_subset_1(C_219, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_2190])).
% 4.83/1.91  tff(c_2221, plain, (![A_221, E_222]: (r2_orders_2('#skF_4', '#skF_2'(A_221, '#skF_4', k2_struct_0('#skF_4')), E_222) | ~r2_hidden(E_222, k2_struct_0('#skF_4')) | ~m1_subset_1(E_222, k2_struct_0('#skF_4')) | ~r2_hidden(A_221, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_80, c_2193])).
% 4.83/1.91  tff(c_18, plain, (![A_18, C_24]: (~r2_orders_2(A_18, C_24, C_24) | ~m1_subset_1(C_24, u1_struct_0(A_18)) | ~l1_orders_2(A_18))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.83/1.91  tff(c_2229, plain, (![A_221]: (~m1_subset_1('#skF_2'(A_221, '#skF_4', k2_struct_0('#skF_4')), u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~r2_hidden('#skF_2'(A_221, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_2'(A_221, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')) | ~r2_hidden(A_221, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_2221, c_18])).
% 4.83/1.91  tff(c_2243, plain, (![A_223]: (~r2_hidden('#skF_2'(A_223, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_2'(A_223, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')) | ~r2_hidden(A_223, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_63, c_2229])).
% 4.83/1.91  tff(c_2249, plain, (![A_223]: (~r2_hidden(A_223, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))) | v1_xboole_0(k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_2'(A_223, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_2, c_2243])).
% 4.83/1.91  tff(c_2266, plain, (![A_225]: (~r2_hidden(A_225, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))) | ~m1_subset_1('#skF_2'(A_225, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_94, c_2249])).
% 4.83/1.91  tff(c_2273, plain, (![A_97]: (~r2_hidden(A_97, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_377, c_2266])).
% 4.83/1.91  tff(c_2281, plain, (![A_226]: (~r2_hidden(A_226, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_2273])).
% 4.83/1.91  tff(c_2289, plain, (a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_2281])).
% 4.83/1.91  tff(c_2294, plain, $false, inference(negUnitSimplification, [status(thm)], [c_169, c_2289])).
% 4.83/1.91  tff(c_2297, plain, (![A_227]: (~r2_hidden(A_227, k2_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_93])).
% 4.83/1.91  tff(c_2308, plain, (k2_struct_0('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_2297])).
% 4.83/1.91  tff(c_2311, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_2308, c_2308, c_80])).
% 4.83/1.91  tff(c_2312, plain, (u1_struct_0('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2308, c_63])).
% 4.83/1.91  tff(c_2418, plain, (![A_260, B_261]: (k2_orders_2(A_260, B_261)=a_2_1_orders_2(A_260, B_261) | ~m1_subset_1(B_261, k1_zfmisc_1(u1_struct_0(A_260))) | ~l1_orders_2(A_260) | ~v5_orders_2(A_260) | ~v4_orders_2(A_260) | ~v3_orders_2(A_260) | v2_struct_0(A_260))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.83/1.91  tff(c_2421, plain, (![B_261]: (k2_orders_2('#skF_4', B_261)=a_2_1_orders_2('#skF_4', B_261) | ~m1_subset_1(B_261, k1_zfmisc_1(k1_xboole_0)) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2312, c_2418])).
% 4.83/1.91  tff(c_2426, plain, (![B_261]: (k2_orders_2('#skF_4', B_261)=a_2_1_orders_2('#skF_4', B_261) | ~m1_subset_1(B_261, k1_zfmisc_1(k1_xboole_0)) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_2421])).
% 4.83/1.91  tff(c_2429, plain, (![B_262]: (k2_orders_2('#skF_4', B_262)=a_2_1_orders_2('#skF_4', B_262) | ~m1_subset_1(B_262, k1_zfmisc_1(k1_xboole_0)))), inference(negUnitSimplification, [status(thm)], [c_50, c_2426])).
% 4.83/1.91  tff(c_2433, plain, (k2_orders_2('#skF_4', k1_xboole_0)=a_2_1_orders_2('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_2311, c_2429])).
% 4.83/1.91  tff(c_2313, plain, (k2_orders_2('#skF_4', k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2308, c_40])).
% 4.83/1.91  tff(c_2434, plain, (a_2_1_orders_2('#skF_4', k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2433, c_2313])).
% 4.83/1.91  tff(c_2296, plain, (v1_xboole_0(k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_93])).
% 4.83/1.91  tff(c_2310, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2308, c_2296])).
% 4.83/1.91  tff(c_2439, plain, (![A_263, B_264]: (m1_subset_1(k2_orders_2(A_263, B_264), k1_zfmisc_1(u1_struct_0(A_263))) | ~m1_subset_1(B_264, k1_zfmisc_1(u1_struct_0(A_263))) | ~l1_orders_2(A_263) | ~v5_orders_2(A_263) | ~v4_orders_2(A_263) | ~v3_orders_2(A_263) | v2_struct_0(A_263))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.83/1.91  tff(c_2447, plain, (m1_subset_1(a_2_1_orders_2('#skF_4', k1_xboole_0), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2433, c_2439])).
% 4.83/1.91  tff(c_2454, plain, (m1_subset_1(a_2_1_orders_2('#skF_4', k1_xboole_0), k1_zfmisc_1(k1_xboole_0)) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_2311, c_2312, c_2312, c_2447])).
% 4.83/1.91  tff(c_2455, plain, (m1_subset_1(a_2_1_orders_2('#skF_4', k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_50, c_2454])).
% 4.83/1.91  tff(c_2463, plain, (![A_3]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_3, a_2_1_orders_2('#skF_4', k1_xboole_0)))), inference(resolution, [status(thm)], [c_2455, c_4])).
% 4.83/1.91  tff(c_2468, plain, (![A_265]: (~r2_hidden(A_265, a_2_1_orders_2('#skF_4', k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_2310, c_2463])).
% 4.83/1.91  tff(c_2476, plain, (a_2_1_orders_2('#skF_4', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_2468])).
% 4.83/1.91  tff(c_2481, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2434, c_2476])).
% 4.83/1.91  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.83/1.91  
% 4.83/1.91  Inference rules
% 4.83/1.91  ----------------------
% 4.83/1.91  #Ref     : 0
% 4.83/1.91  #Sup     : 509
% 4.83/1.91  #Fact    : 0
% 4.83/1.91  #Define  : 0
% 4.83/1.91  #Split   : 6
% 4.83/1.91  #Chain   : 0
% 4.83/1.91  #Close   : 0
% 4.83/1.91  
% 4.83/1.91  Ordering : KBO
% 4.83/1.91  
% 4.83/1.91  Simplification rules
% 4.83/1.91  ----------------------
% 4.83/1.91  #Subsume      : 99
% 4.83/1.91  #Demod        : 1306
% 4.83/1.91  #Tautology    : 127
% 4.83/1.91  #SimpNegUnit  : 137
% 4.83/1.91  #BackRed      : 36
% 4.83/1.91  
% 4.83/1.91  #Partial instantiations: 0
% 4.83/1.91  #Strategies tried      : 1
% 4.83/1.91  
% 4.83/1.91  Timing (in seconds)
% 4.83/1.91  ----------------------
% 4.83/1.91  Preprocessing        : 0.34
% 4.83/1.91  Parsing              : 0.18
% 4.83/1.91  CNF conversion       : 0.02
% 4.83/1.91  Main loop            : 0.80
% 4.83/1.91  Inferencing          : 0.27
% 4.83/1.91  Reduction            : 0.28
% 4.83/1.91  Demodulation         : 0.20
% 4.83/1.91  BG Simplification    : 0.03
% 4.83/1.91  Subsumption          : 0.15
% 4.83/1.91  Abstraction          : 0.04
% 4.83/1.91  MUC search           : 0.00
% 4.83/1.91  Cooper               : 0.00
% 4.83/1.91  Total                : 1.18
% 4.83/1.91  Index Insertion      : 0.00
% 4.83/1.91  Index Deletion       : 0.00
% 4.83/1.91  Index Matching       : 0.00
% 4.83/1.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
