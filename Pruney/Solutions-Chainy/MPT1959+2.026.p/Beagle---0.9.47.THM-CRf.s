%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:01 EST 2020

% Result     : Theorem 6.79s
% Output     : CNFRefutation 7.08s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 818 expanded)
%              Number of leaves         :   49 ( 309 expanded)
%              Depth                    :   27
%              Number of atoms          :  299 (3559 expanded)
%              Number of equality atoms :   34 ( 151 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_yellow_0 > r2_hidden > r1_yellow_0 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > l1_orders_2 > k6_domain_1 > k2_yellow_0 > k1_yellow_0 > #nlpp > u1_struct_0 > k3_yellow_0 > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_yellow_0,type,(
    k1_yellow_0: ( $i * $i ) > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_waybel_0,type,(
    v2_waybel_0: ( $i * $i ) > $o )).

tff(k3_yellow_0,type,(
    k3_yellow_0: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r2_yellow_0,type,(
    r2_yellow_0: ( $i * $i ) > $o )).

tff(k2_yellow_0,type,(
    k2_yellow_0: ( $i * $i ) > $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(r1_yellow_0,type,(
    r1_yellow_0: ( $i * $i ) > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v13_waybel_0,type,(
    v13_waybel_0: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(v1_yellow_0,type,(
    v1_yellow_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_36,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_46,axiom,(
    ! [A] : ~ v1_subset_1(k2_subset_1(A),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_subset_1)).

tff(f_179,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & v1_yellow_0(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & v2_waybel_0(B,A)
              & v13_waybel_0(B,A)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ( v1_subset_1(B,u1_struct_0(A))
            <=> ~ r2_hidden(k3_yellow_0(A),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_7)).

tff(f_32,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_111,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( k1_yellow_0(A,k6_domain_1(u1_struct_0(A),B)) = B
            & k2_yellow_0(A,k6_domain_1(u1_struct_0(A),B)) = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_yellow_0)).

tff(f_64,axiom,(
    ! [A,B] :
      ( l1_orders_2(A)
     => m1_subset_1(k1_yellow_0(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_150,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => k3_yellow_0(A) = k1_yellow_0(A,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_yellow_0)).

tff(f_95,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( r1_yellow_0(A,k6_domain_1(u1_struct_0(A),B))
            & r2_yellow_0(A,k6_domain_1(u1_struct_0(A),B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_yellow_0)).

tff(f_124,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v5_orders_2(A)
        & v1_yellow_0(A)
        & l1_orders_2(A) )
     => ( r1_yellow_0(A,k1_xboole_0)
        & r2_yellow_0(A,u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_yellow_0)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_79,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( ( r1_tarski(B,C)
            & r1_yellow_0(A,B)
            & r1_yellow_0(A,C) )
         => r1_orders_2(A,k1_yellow_0(A,B),k1_yellow_0(A,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_yellow_0)).

tff(f_143,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v13_waybel_0(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( ( r2_hidden(C,B)
                        & r1_orders_2(A,C,D) )
                     => r2_hidden(D,B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_waybel_0)).

tff(c_12,plain,(
    ! [A_5] : k2_subset_1(A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_16,plain,(
    ! [A_10] : ~ v1_subset_1(k2_subset_1(A_10),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_85,plain,(
    ! [A_10] : ~ v1_subset_1(A_10,A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_16])).

tff(c_58,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_179,plain,(
    ! [A_83,B_84] :
      ( r2_hidden('#skF_1'(A_83,B_84),B_84)
      | r2_hidden('#skF_2'(A_83,B_84),A_83)
      | B_84 = A_83 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_14,plain,(
    ! [C_9,A_6,B_7] :
      ( r2_hidden(C_9,A_6)
      | ~ r2_hidden(C_9,B_7)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_511,plain,(
    ! [A_127,B_128,A_129] :
      ( r2_hidden('#skF_1'(A_127,B_128),A_129)
      | ~ m1_subset_1(B_128,k1_zfmisc_1(A_129))
      | r2_hidden('#skF_2'(A_127,B_128),A_127)
      | B_128 = A_127 ) ),
    inference(resolution,[status(thm)],[c_179,c_14])).

tff(c_18,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,B_12)
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_912,plain,(
    ! [A_163,B_164,A_165] :
      ( m1_subset_1('#skF_2'(A_163,B_164),A_163)
      | r2_hidden('#skF_1'(A_163,B_164),A_165)
      | ~ m1_subset_1(B_164,k1_zfmisc_1(A_165))
      | B_164 = A_163 ) ),
    inference(resolution,[status(thm)],[c_511,c_18])).

tff(c_204,plain,(
    ! [A_88,B_89] :
      ( ~ r2_hidden('#skF_1'(A_88,B_89),A_88)
      | r2_hidden('#skF_2'(A_88,B_89),A_88)
      | B_89 = A_88 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_211,plain,(
    ! [A_88,B_89] :
      ( m1_subset_1('#skF_2'(A_88,B_89),A_88)
      | ~ r2_hidden('#skF_1'(A_88,B_89),A_88)
      | B_89 = A_88 ) ),
    inference(resolution,[status(thm)],[c_204,c_18])).

tff(c_952,plain,(
    ! [A_165,B_164] :
      ( m1_subset_1('#skF_2'(A_165,B_164),A_165)
      | ~ m1_subset_1(B_164,k1_zfmisc_1(A_165))
      | B_164 = A_165 ) ),
    inference(resolution,[status(thm)],[c_912,c_211])).

tff(c_76,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_74,plain,(
    v3_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_70,plain,(
    v5_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_66,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_36,plain,(
    ! [A_27,B_29] :
      ( k1_yellow_0(A_27,k6_domain_1(u1_struct_0(A_27),B_29)) = B_29
      | ~ m1_subset_1(B_29,u1_struct_0(A_27))
      | ~ l1_orders_2(A_27)
      | ~ v5_orders_2(A_27)
      | ~ v3_orders_2(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_24,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(k1_yellow_0(A_16,B_17),u1_struct_0(A_16))
      | ~ l1_orders_2(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_60,plain,(
    v13_waybel_0('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_64,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_20,plain,(
    ! [A_13,B_14] :
      ( r2_hidden(A_13,B_14)
      | v1_xboole_0(B_14)
      | ~ m1_subset_1(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_84,plain,
    ( v1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ r2_hidden(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_119,plain,(
    ~ r2_hidden(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_122,plain,
    ( v1_xboole_0('#skF_6')
    | ~ m1_subset_1(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_20,c_119])).

tff(c_125,plain,(
    ~ m1_subset_1(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_122])).

tff(c_78,plain,
    ( r2_hidden(k3_yellow_0('#skF_5'),'#skF_6')
    | ~ v1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_126,plain,(
    ~ v1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_119,c_78])).

tff(c_127,plain,(
    ! [B_70,A_71] :
      ( v1_subset_1(B_70,A_71)
      | B_70 = A_71
      | ~ m1_subset_1(B_70,k1_zfmisc_1(A_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_130,plain,
    ( v1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | u1_struct_0('#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_58,c_127])).

tff(c_133,plain,(
    u1_struct_0('#skF_5') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_126,c_130])).

tff(c_99,plain,(
    ! [A_65] :
      ( k1_yellow_0(A_65,k1_xboole_0) = k3_yellow_0(A_65)
      | ~ l1_orders_2(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_103,plain,(
    k1_yellow_0('#skF_5',k1_xboole_0) = k3_yellow_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_99])).

tff(c_113,plain,(
    ! [A_68,B_69] :
      ( m1_subset_1(k1_yellow_0(A_68,B_69),u1_struct_0(A_68))
      | ~ l1_orders_2(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_116,plain,
    ( m1_subset_1(k3_yellow_0('#skF_5'),u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_113])).

tff(c_118,plain,(
    m1_subset_1(k3_yellow_0('#skF_5'),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_116])).

tff(c_139,plain,(
    m1_subset_1(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_118])).

tff(c_142,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_125,c_139])).

tff(c_144,plain,(
    r2_hidden(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_32,plain,(
    ! [A_24,B_26] :
      ( r1_yellow_0(A_24,k6_domain_1(u1_struct_0(A_24),B_26))
      | ~ m1_subset_1(B_26,u1_struct_0(A_24))
      | ~ l1_orders_2(A_24)
      | ~ v5_orders_2(A_24)
      | ~ v3_orders_2(A_24)
      | v2_struct_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_68,plain,(
    v1_yellow_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_40,plain,(
    ! [A_30] :
      ( r1_yellow_0(A_30,k1_xboole_0)
      | ~ l1_orders_2(A_30)
      | ~ v1_yellow_0(A_30)
      | ~ v5_orders_2(A_30)
      | v2_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_10,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1394,plain,(
    ! [A_198,B_199,C_200] :
      ( r1_orders_2(A_198,k1_yellow_0(A_198,B_199),k1_yellow_0(A_198,C_200))
      | ~ r1_yellow_0(A_198,C_200)
      | ~ r1_yellow_0(A_198,B_199)
      | ~ r1_tarski(B_199,C_200)
      | ~ l1_orders_2(A_198) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1403,plain,(
    ! [C_200] :
      ( r1_orders_2('#skF_5',k3_yellow_0('#skF_5'),k1_yellow_0('#skF_5',C_200))
      | ~ r1_yellow_0('#skF_5',C_200)
      | ~ r1_yellow_0('#skF_5',k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,C_200)
      | ~ l1_orders_2('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_1394])).

tff(c_1408,plain,(
    ! [C_200] :
      ( r1_orders_2('#skF_5',k3_yellow_0('#skF_5'),k1_yellow_0('#skF_5',C_200))
      | ~ r1_yellow_0('#skF_5',C_200)
      | ~ r1_yellow_0('#skF_5',k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_10,c_1403])).

tff(c_1411,plain,(
    ~ r1_yellow_0('#skF_5',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1408])).

tff(c_1414,plain,
    ( ~ l1_orders_2('#skF_5')
    | ~ v1_yellow_0('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_1411])).

tff(c_1417,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_1414])).

tff(c_1419,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_1417])).

tff(c_1456,plain,(
    ! [C_202] :
      ( r1_orders_2('#skF_5',k3_yellow_0('#skF_5'),k1_yellow_0('#skF_5',C_202))
      | ~ r1_yellow_0('#skF_5',C_202) ) ),
    inference(splitRight,[status(thm)],[c_1408])).

tff(c_1460,plain,(
    ! [B_29] :
      ( r1_orders_2('#skF_5',k3_yellow_0('#skF_5'),B_29)
      | ~ r1_yellow_0('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),B_29))
      | ~ m1_subset_1(B_29,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_1456])).

tff(c_1465,plain,(
    ! [B_29] :
      ( r1_orders_2('#skF_5',k3_yellow_0('#skF_5'),B_29)
      | ~ r1_yellow_0('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),B_29))
      | ~ m1_subset_1(B_29,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_66,c_1460])).

tff(c_1486,plain,(
    ! [B_207] :
      ( r1_orders_2('#skF_5',k3_yellow_0('#skF_5'),B_207)
      | ~ r1_yellow_0('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),B_207))
      | ~ m1_subset_1(B_207,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_1465])).

tff(c_1490,plain,(
    ! [B_26] :
      ( r1_orders_2('#skF_5',k3_yellow_0('#skF_5'),B_26)
      | ~ m1_subset_1(B_26,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_32,c_1486])).

tff(c_1493,plain,(
    ! [B_26] :
      ( r1_orders_2('#skF_5',k3_yellow_0('#skF_5'),B_26)
      | ~ m1_subset_1(B_26,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_66,c_1490])).

tff(c_1495,plain,(
    ! [B_208] :
      ( r1_orders_2('#skF_5',k3_yellow_0('#skF_5'),B_208)
      | ~ m1_subset_1(B_208,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_1493])).

tff(c_42,plain,(
    ! [D_54,B_45,A_31,C_52] :
      ( r2_hidden(D_54,B_45)
      | ~ r1_orders_2(A_31,C_52,D_54)
      | ~ r2_hidden(C_52,B_45)
      | ~ m1_subset_1(D_54,u1_struct_0(A_31))
      | ~ m1_subset_1(C_52,u1_struct_0(A_31))
      | ~ v13_waybel_0(B_45,A_31)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ l1_orders_2(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_1497,plain,(
    ! [B_208,B_45] :
      ( r2_hidden(B_208,B_45)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_45)
      | ~ m1_subset_1(k3_yellow_0('#skF_5'),u1_struct_0('#skF_5'))
      | ~ v13_waybel_0(B_45,'#skF_5')
      | ~ m1_subset_1(B_45,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5')
      | ~ m1_subset_1(B_208,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_1495,c_42])).

tff(c_1961,plain,(
    ! [B_251,B_252] :
      ( r2_hidden(B_251,B_252)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_252)
      | ~ v13_waybel_0(B_252,'#skF_5')
      | ~ m1_subset_1(B_252,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_251,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_118,c_1497])).

tff(c_2014,plain,(
    ! [B_251] :
      ( r2_hidden(B_251,'#skF_6')
      | ~ r2_hidden(k3_yellow_0('#skF_5'),'#skF_6')
      | ~ v13_waybel_0('#skF_6','#skF_5')
      | ~ m1_subset_1(B_251,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_58,c_1961])).

tff(c_2035,plain,(
    ! [B_253] :
      ( r2_hidden(B_253,'#skF_6')
      | ~ m1_subset_1(B_253,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_144,c_2014])).

tff(c_2130,plain,(
    ! [B_17] :
      ( r2_hidden(k1_yellow_0('#skF_5',B_17),'#skF_6')
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_24,c_2035])).

tff(c_2173,plain,(
    ! [B_257] : r2_hidden(k1_yellow_0('#skF_5',B_257),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2130])).

tff(c_2191,plain,(
    ! [B_258] : m1_subset_1(k1_yellow_0('#skF_5',B_258),'#skF_6') ),
    inference(resolution,[status(thm)],[c_2173,c_18])).

tff(c_2195,plain,(
    ! [B_29] :
      ( m1_subset_1(B_29,'#skF_6')
      | ~ m1_subset_1(B_29,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_2191])).

tff(c_2199,plain,(
    ! [B_29] :
      ( m1_subset_1(B_29,'#skF_6')
      | ~ m1_subset_1(B_29,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_66,c_2195])).

tff(c_2245,plain,(
    ! [B_260] :
      ( m1_subset_1(B_260,'#skF_6')
      | ~ m1_subset_1(B_260,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_2199])).

tff(c_3407,plain,(
    ! [B_303] :
      ( m1_subset_1('#skF_2'(u1_struct_0('#skF_5'),B_303),'#skF_6')
      | ~ m1_subset_1(B_303,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | u1_struct_0('#skF_5') = B_303 ) ),
    inference(resolution,[status(thm)],[c_952,c_2245])).

tff(c_157,plain,(
    ! [C_77,A_78,B_79] :
      ( r2_hidden(C_77,A_78)
      | ~ r2_hidden(C_77,B_79)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(A_78)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_241,plain,(
    ! [A_96,A_97,B_98] :
      ( r2_hidden(A_96,A_97)
      | ~ m1_subset_1(B_98,k1_zfmisc_1(A_97))
      | v1_xboole_0(B_98)
      | ~ m1_subset_1(A_96,B_98) ) ),
    inference(resolution,[status(thm)],[c_20,c_157])).

tff(c_246,plain,(
    ! [A_96] :
      ( r2_hidden(A_96,u1_struct_0('#skF_5'))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(A_96,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_58,c_241])).

tff(c_251,plain,(
    ! [A_99] :
      ( r2_hidden(A_99,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(A_99,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_246])).

tff(c_271,plain,(
    ! [A_99] :
      ( m1_subset_1(A_99,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(A_99,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_251,c_18])).

tff(c_2202,plain,(
    ! [A_259] :
      ( r2_hidden(A_259,'#skF_6')
      | ~ m1_subset_1(A_259,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_271,c_2035])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2),B_2)
      | B_2 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2623,plain,(
    ! [A_278] :
      ( r2_hidden('#skF_1'(A_278,'#skF_6'),'#skF_6')
      | A_278 = '#skF_6'
      | ~ m1_subset_1('#skF_2'(A_278,'#skF_6'),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_2202,c_4])).

tff(c_2645,plain,(
    ! [A_278] :
      ( m1_subset_1('#skF_1'(A_278,'#skF_6'),'#skF_6')
      | A_278 = '#skF_6'
      | ~ m1_subset_1('#skF_2'(A_278,'#skF_6'),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_2623,c_18])).

tff(c_3411,plain,
    ( m1_subset_1('#skF_1'(u1_struct_0('#skF_5'),'#skF_6'),'#skF_6')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | u1_struct_0('#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_3407,c_2645])).

tff(c_3425,plain,
    ( m1_subset_1('#skF_1'(u1_struct_0('#skF_5'),'#skF_6'),'#skF_6')
    | u1_struct_0('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_3411])).

tff(c_3438,plain,(
    u1_struct_0('#skF_5') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_3425])).

tff(c_143,plain,(
    v1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_3476,plain,(
    v1_subset_1('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3438,c_143])).

tff(c_3480,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_3476])).

tff(c_3482,plain,(
    u1_struct_0('#skF_5') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_3425])).

tff(c_3481,plain,(
    m1_subset_1('#skF_1'(u1_struct_0('#skF_5'),'#skF_6'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_3425])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),A_1)
      | ~ r2_hidden('#skF_2'(A_1,B_2),B_2)
      | B_2 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_441,plain,(
    ! [B_118] :
      ( ~ r2_hidden('#skF_2'(u1_struct_0('#skF_5'),B_118),B_118)
      | u1_struct_0('#skF_5') = B_118
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_5'),B_118),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_251,c_2])).

tff(c_468,plain,(
    ! [B_14] :
      ( u1_struct_0('#skF_5') = B_14
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_5'),B_14),'#skF_6')
      | v1_xboole_0(B_14)
      | ~ m1_subset_1('#skF_2'(u1_struct_0('#skF_5'),B_14),B_14) ) ),
    inference(resolution,[status(thm)],[c_20,c_441])).

tff(c_3418,plain,
    ( ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_5'),'#skF_6'),'#skF_6')
    | v1_xboole_0('#skF_6')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | u1_struct_0('#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_3407,c_468])).

tff(c_3432,plain,
    ( ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_5'),'#skF_6'),'#skF_6')
    | v1_xboole_0('#skF_6')
    | u1_struct_0('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_3418])).

tff(c_3433,plain,
    ( ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_5'),'#skF_6'),'#skF_6')
    | u1_struct_0('#skF_5') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_3432])).

tff(c_3489,plain,(
    u1_struct_0('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3481,c_3433])).

tff(c_3490,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3482,c_3489])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n011.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:47:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.79/2.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.79/2.63  
% 6.79/2.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.79/2.63  %$ r1_orders_2 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_yellow_0 > r2_hidden > r1_yellow_0 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > l1_orders_2 > k6_domain_1 > k2_yellow_0 > k1_yellow_0 > #nlpp > u1_struct_0 > k3_yellow_0 > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4
% 6.79/2.63  
% 6.79/2.63  %Foreground sorts:
% 6.79/2.63  
% 6.79/2.63  
% 6.79/2.63  %Background operators:
% 6.79/2.63  
% 6.79/2.63  
% 6.79/2.63  %Foreground operators:
% 6.79/2.63  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.79/2.63  tff(k1_yellow_0, type, k1_yellow_0: ($i * $i) > $i).
% 6.79/2.63  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 6.79/2.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.79/2.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.79/2.63  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 6.79/2.63  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 6.79/2.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.79/2.63  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 6.79/2.63  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 6.79/2.63  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 6.79/2.63  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 6.79/2.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.79/2.63  tff('#skF_5', type, '#skF_5': $i).
% 6.79/2.63  tff('#skF_6', type, '#skF_6': $i).
% 6.79/2.63  tff(r2_yellow_0, type, r2_yellow_0: ($i * $i) > $o).
% 6.79/2.63  tff(k2_yellow_0, type, k2_yellow_0: ($i * $i) > $i).
% 6.79/2.63  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 6.79/2.63  tff(r1_yellow_0, type, r1_yellow_0: ($i * $i) > $o).
% 6.79/2.63  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 6.79/2.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.79/2.63  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 6.79/2.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.79/2.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.79/2.63  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.79/2.63  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 6.79/2.63  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.79/2.63  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.79/2.63  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 6.79/2.63  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.79/2.63  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 6.79/2.63  tff(v1_yellow_0, type, v1_yellow_0: $i > $o).
% 6.79/2.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.79/2.63  
% 7.08/2.66  tff(f_36, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 7.08/2.66  tff(f_46, axiom, (![A]: ~v1_subset_1(k2_subset_1(A), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc14_subset_1)).
% 7.08/2.66  tff(f_179, negated_conjecture, ~(![A]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, A)) & v13_waybel_0(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_subset_1(B, u1_struct_0(A)) <=> ~r2_hidden(k3_yellow_0(A), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_waybel_7)).
% 7.08/2.66  tff(f_32, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 7.08/2.66  tff(f_43, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 7.08/2.66  tff(f_50, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 7.08/2.66  tff(f_111, axiom, (![A]: ((((~v2_struct_0(A) & v3_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ((k1_yellow_0(A, k6_domain_1(u1_struct_0(A), B)) = B) & (k2_yellow_0(A, k6_domain_1(u1_struct_0(A), B)) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_yellow_0)).
% 7.08/2.66  tff(f_64, axiom, (![A, B]: (l1_orders_2(A) => m1_subset_1(k1_yellow_0(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_yellow_0)).
% 7.08/2.66  tff(f_56, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 7.08/2.66  tff(f_150, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 7.08/2.66  tff(f_60, axiom, (![A]: (l1_orders_2(A) => (k3_yellow_0(A) = k1_yellow_0(A, k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_yellow_0)).
% 7.08/2.66  tff(f_95, axiom, (![A]: ((((~v2_struct_0(A) & v3_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (r1_yellow_0(A, k6_domain_1(u1_struct_0(A), B)) & r2_yellow_0(A, k6_domain_1(u1_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_yellow_0)).
% 7.08/2.66  tff(f_124, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (r1_yellow_0(A, k1_xboole_0) & r2_yellow_0(A, u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_yellow_0)).
% 7.08/2.66  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 7.08/2.66  tff(f_79, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (((r1_tarski(B, C) & r1_yellow_0(A, B)) & r1_yellow_0(A, C)) => r1_orders_2(A, k1_yellow_0(A, B), k1_yellow_0(A, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_yellow_0)).
% 7.08/2.66  tff(f_143, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v13_waybel_0(B, A) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r2_hidden(C, B) & r1_orders_2(A, C, D)) => r2_hidden(D, B))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d20_waybel_0)).
% 7.08/2.66  tff(c_12, plain, (![A_5]: (k2_subset_1(A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.08/2.66  tff(c_16, plain, (![A_10]: (~v1_subset_1(k2_subset_1(A_10), A_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.08/2.66  tff(c_85, plain, (![A_10]: (~v1_subset_1(A_10, A_10))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_16])).
% 7.08/2.66  tff(c_58, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_179])).
% 7.08/2.66  tff(c_179, plain, (![A_83, B_84]: (r2_hidden('#skF_1'(A_83, B_84), B_84) | r2_hidden('#skF_2'(A_83, B_84), A_83) | B_84=A_83)), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.08/2.66  tff(c_14, plain, (![C_9, A_6, B_7]: (r2_hidden(C_9, A_6) | ~r2_hidden(C_9, B_7) | ~m1_subset_1(B_7, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.08/2.66  tff(c_511, plain, (![A_127, B_128, A_129]: (r2_hidden('#skF_1'(A_127, B_128), A_129) | ~m1_subset_1(B_128, k1_zfmisc_1(A_129)) | r2_hidden('#skF_2'(A_127, B_128), A_127) | B_128=A_127)), inference(resolution, [status(thm)], [c_179, c_14])).
% 7.08/2.66  tff(c_18, plain, (![A_11, B_12]: (m1_subset_1(A_11, B_12) | ~r2_hidden(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.08/2.66  tff(c_912, plain, (![A_163, B_164, A_165]: (m1_subset_1('#skF_2'(A_163, B_164), A_163) | r2_hidden('#skF_1'(A_163, B_164), A_165) | ~m1_subset_1(B_164, k1_zfmisc_1(A_165)) | B_164=A_163)), inference(resolution, [status(thm)], [c_511, c_18])).
% 7.08/2.66  tff(c_204, plain, (![A_88, B_89]: (~r2_hidden('#skF_1'(A_88, B_89), A_88) | r2_hidden('#skF_2'(A_88, B_89), A_88) | B_89=A_88)), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.08/2.66  tff(c_211, plain, (![A_88, B_89]: (m1_subset_1('#skF_2'(A_88, B_89), A_88) | ~r2_hidden('#skF_1'(A_88, B_89), A_88) | B_89=A_88)), inference(resolution, [status(thm)], [c_204, c_18])).
% 7.08/2.66  tff(c_952, plain, (![A_165, B_164]: (m1_subset_1('#skF_2'(A_165, B_164), A_165) | ~m1_subset_1(B_164, k1_zfmisc_1(A_165)) | B_164=A_165)), inference(resolution, [status(thm)], [c_912, c_211])).
% 7.08/2.66  tff(c_76, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_179])).
% 7.08/2.66  tff(c_74, plain, (v3_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_179])).
% 7.08/2.66  tff(c_70, plain, (v5_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_179])).
% 7.08/2.66  tff(c_66, plain, (l1_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_179])).
% 7.08/2.66  tff(c_36, plain, (![A_27, B_29]: (k1_yellow_0(A_27, k6_domain_1(u1_struct_0(A_27), B_29))=B_29 | ~m1_subset_1(B_29, u1_struct_0(A_27)) | ~l1_orders_2(A_27) | ~v5_orders_2(A_27) | ~v3_orders_2(A_27) | v2_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_111])).
% 7.08/2.66  tff(c_24, plain, (![A_16, B_17]: (m1_subset_1(k1_yellow_0(A_16, B_17), u1_struct_0(A_16)) | ~l1_orders_2(A_16))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.08/2.66  tff(c_60, plain, (v13_waybel_0('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_179])).
% 7.08/2.66  tff(c_64, plain, (~v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_179])).
% 7.08/2.66  tff(c_20, plain, (![A_13, B_14]: (r2_hidden(A_13, B_14) | v1_xboole_0(B_14) | ~m1_subset_1(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.08/2.66  tff(c_84, plain, (v1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~r2_hidden(k3_yellow_0('#skF_5'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_179])).
% 7.08/2.66  tff(c_119, plain, (~r2_hidden(k3_yellow_0('#skF_5'), '#skF_6')), inference(splitLeft, [status(thm)], [c_84])).
% 7.08/2.66  tff(c_122, plain, (v1_xboole_0('#skF_6') | ~m1_subset_1(k3_yellow_0('#skF_5'), '#skF_6')), inference(resolution, [status(thm)], [c_20, c_119])).
% 7.08/2.66  tff(c_125, plain, (~m1_subset_1(k3_yellow_0('#skF_5'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_64, c_122])).
% 7.08/2.66  tff(c_78, plain, (r2_hidden(k3_yellow_0('#skF_5'), '#skF_6') | ~v1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_179])).
% 7.08/2.66  tff(c_126, plain, (~v1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_119, c_78])).
% 7.08/2.66  tff(c_127, plain, (![B_70, A_71]: (v1_subset_1(B_70, A_71) | B_70=A_71 | ~m1_subset_1(B_70, k1_zfmisc_1(A_71)))), inference(cnfTransformation, [status(thm)], [f_150])).
% 7.08/2.66  tff(c_130, plain, (v1_subset_1('#skF_6', u1_struct_0('#skF_5')) | u1_struct_0('#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_58, c_127])).
% 7.08/2.66  tff(c_133, plain, (u1_struct_0('#skF_5')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_126, c_130])).
% 7.08/2.66  tff(c_99, plain, (![A_65]: (k1_yellow_0(A_65, k1_xboole_0)=k3_yellow_0(A_65) | ~l1_orders_2(A_65))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.08/2.66  tff(c_103, plain, (k1_yellow_0('#skF_5', k1_xboole_0)=k3_yellow_0('#skF_5')), inference(resolution, [status(thm)], [c_66, c_99])).
% 7.08/2.66  tff(c_113, plain, (![A_68, B_69]: (m1_subset_1(k1_yellow_0(A_68, B_69), u1_struct_0(A_68)) | ~l1_orders_2(A_68))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.08/2.66  tff(c_116, plain, (m1_subset_1(k3_yellow_0('#skF_5'), u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_103, c_113])).
% 7.08/2.66  tff(c_118, plain, (m1_subset_1(k3_yellow_0('#skF_5'), u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_116])).
% 7.08/2.66  tff(c_139, plain, (m1_subset_1(k3_yellow_0('#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_133, c_118])).
% 7.08/2.66  tff(c_142, plain, $false, inference(negUnitSimplification, [status(thm)], [c_125, c_139])).
% 7.08/2.66  tff(c_144, plain, (r2_hidden(k3_yellow_0('#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_84])).
% 7.08/2.66  tff(c_32, plain, (![A_24, B_26]: (r1_yellow_0(A_24, k6_domain_1(u1_struct_0(A_24), B_26)) | ~m1_subset_1(B_26, u1_struct_0(A_24)) | ~l1_orders_2(A_24) | ~v5_orders_2(A_24) | ~v3_orders_2(A_24) | v2_struct_0(A_24))), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.08/2.66  tff(c_68, plain, (v1_yellow_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_179])).
% 7.08/2.66  tff(c_40, plain, (![A_30]: (r1_yellow_0(A_30, k1_xboole_0) | ~l1_orders_2(A_30) | ~v1_yellow_0(A_30) | ~v5_orders_2(A_30) | v2_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_124])).
% 7.08/2.66  tff(c_10, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.08/2.66  tff(c_1394, plain, (![A_198, B_199, C_200]: (r1_orders_2(A_198, k1_yellow_0(A_198, B_199), k1_yellow_0(A_198, C_200)) | ~r1_yellow_0(A_198, C_200) | ~r1_yellow_0(A_198, B_199) | ~r1_tarski(B_199, C_200) | ~l1_orders_2(A_198))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.08/2.66  tff(c_1403, plain, (![C_200]: (r1_orders_2('#skF_5', k3_yellow_0('#skF_5'), k1_yellow_0('#skF_5', C_200)) | ~r1_yellow_0('#skF_5', C_200) | ~r1_yellow_0('#skF_5', k1_xboole_0) | ~r1_tarski(k1_xboole_0, C_200) | ~l1_orders_2('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_103, c_1394])).
% 7.08/2.66  tff(c_1408, plain, (![C_200]: (r1_orders_2('#skF_5', k3_yellow_0('#skF_5'), k1_yellow_0('#skF_5', C_200)) | ~r1_yellow_0('#skF_5', C_200) | ~r1_yellow_0('#skF_5', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_10, c_1403])).
% 7.08/2.66  tff(c_1411, plain, (~r1_yellow_0('#skF_5', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_1408])).
% 7.08/2.66  tff(c_1414, plain, (~l1_orders_2('#skF_5') | ~v1_yellow_0('#skF_5') | ~v5_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_40, c_1411])).
% 7.08/2.66  tff(c_1417, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_1414])).
% 7.08/2.66  tff(c_1419, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_1417])).
% 7.08/2.66  tff(c_1456, plain, (![C_202]: (r1_orders_2('#skF_5', k3_yellow_0('#skF_5'), k1_yellow_0('#skF_5', C_202)) | ~r1_yellow_0('#skF_5', C_202))), inference(splitRight, [status(thm)], [c_1408])).
% 7.08/2.66  tff(c_1460, plain, (![B_29]: (r1_orders_2('#skF_5', k3_yellow_0('#skF_5'), B_29) | ~r1_yellow_0('#skF_5', k6_domain_1(u1_struct_0('#skF_5'), B_29)) | ~m1_subset_1(B_29, u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_36, c_1456])).
% 7.08/2.66  tff(c_1465, plain, (![B_29]: (r1_orders_2('#skF_5', k3_yellow_0('#skF_5'), B_29) | ~r1_yellow_0('#skF_5', k6_domain_1(u1_struct_0('#skF_5'), B_29)) | ~m1_subset_1(B_29, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_66, c_1460])).
% 7.08/2.66  tff(c_1486, plain, (![B_207]: (r1_orders_2('#skF_5', k3_yellow_0('#skF_5'), B_207) | ~r1_yellow_0('#skF_5', k6_domain_1(u1_struct_0('#skF_5'), B_207)) | ~m1_subset_1(B_207, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_76, c_1465])).
% 7.08/2.66  tff(c_1490, plain, (![B_26]: (r1_orders_2('#skF_5', k3_yellow_0('#skF_5'), B_26) | ~m1_subset_1(B_26, u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_32, c_1486])).
% 7.08/2.66  tff(c_1493, plain, (![B_26]: (r1_orders_2('#skF_5', k3_yellow_0('#skF_5'), B_26) | ~m1_subset_1(B_26, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_66, c_1490])).
% 7.08/2.66  tff(c_1495, plain, (![B_208]: (r1_orders_2('#skF_5', k3_yellow_0('#skF_5'), B_208) | ~m1_subset_1(B_208, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_76, c_1493])).
% 7.08/2.66  tff(c_42, plain, (![D_54, B_45, A_31, C_52]: (r2_hidden(D_54, B_45) | ~r1_orders_2(A_31, C_52, D_54) | ~r2_hidden(C_52, B_45) | ~m1_subset_1(D_54, u1_struct_0(A_31)) | ~m1_subset_1(C_52, u1_struct_0(A_31)) | ~v13_waybel_0(B_45, A_31) | ~m1_subset_1(B_45, k1_zfmisc_1(u1_struct_0(A_31))) | ~l1_orders_2(A_31))), inference(cnfTransformation, [status(thm)], [f_143])).
% 7.08/2.66  tff(c_1497, plain, (![B_208, B_45]: (r2_hidden(B_208, B_45) | ~r2_hidden(k3_yellow_0('#skF_5'), B_45) | ~m1_subset_1(k3_yellow_0('#skF_5'), u1_struct_0('#skF_5')) | ~v13_waybel_0(B_45, '#skF_5') | ~m1_subset_1(B_45, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~m1_subset_1(B_208, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_1495, c_42])).
% 7.08/2.66  tff(c_1961, plain, (![B_251, B_252]: (r2_hidden(B_251, B_252) | ~r2_hidden(k3_yellow_0('#skF_5'), B_252) | ~v13_waybel_0(B_252, '#skF_5') | ~m1_subset_1(B_252, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_251, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_118, c_1497])).
% 7.08/2.66  tff(c_2014, plain, (![B_251]: (r2_hidden(B_251, '#skF_6') | ~r2_hidden(k3_yellow_0('#skF_5'), '#skF_6') | ~v13_waybel_0('#skF_6', '#skF_5') | ~m1_subset_1(B_251, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_58, c_1961])).
% 7.08/2.66  tff(c_2035, plain, (![B_253]: (r2_hidden(B_253, '#skF_6') | ~m1_subset_1(B_253, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_144, c_2014])).
% 7.08/2.66  tff(c_2130, plain, (![B_17]: (r2_hidden(k1_yellow_0('#skF_5', B_17), '#skF_6') | ~l1_orders_2('#skF_5'))), inference(resolution, [status(thm)], [c_24, c_2035])).
% 7.08/2.66  tff(c_2173, plain, (![B_257]: (r2_hidden(k1_yellow_0('#skF_5', B_257), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2130])).
% 7.08/2.66  tff(c_2191, plain, (![B_258]: (m1_subset_1(k1_yellow_0('#skF_5', B_258), '#skF_6'))), inference(resolution, [status(thm)], [c_2173, c_18])).
% 7.08/2.66  tff(c_2195, plain, (![B_29]: (m1_subset_1(B_29, '#skF_6') | ~m1_subset_1(B_29, u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_36, c_2191])).
% 7.08/2.66  tff(c_2199, plain, (![B_29]: (m1_subset_1(B_29, '#skF_6') | ~m1_subset_1(B_29, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_66, c_2195])).
% 7.08/2.66  tff(c_2245, plain, (![B_260]: (m1_subset_1(B_260, '#skF_6') | ~m1_subset_1(B_260, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_76, c_2199])).
% 7.08/2.66  tff(c_3407, plain, (![B_303]: (m1_subset_1('#skF_2'(u1_struct_0('#skF_5'), B_303), '#skF_6') | ~m1_subset_1(B_303, k1_zfmisc_1(u1_struct_0('#skF_5'))) | u1_struct_0('#skF_5')=B_303)), inference(resolution, [status(thm)], [c_952, c_2245])).
% 7.08/2.66  tff(c_157, plain, (![C_77, A_78, B_79]: (r2_hidden(C_77, A_78) | ~r2_hidden(C_77, B_79) | ~m1_subset_1(B_79, k1_zfmisc_1(A_78)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.08/2.66  tff(c_241, plain, (![A_96, A_97, B_98]: (r2_hidden(A_96, A_97) | ~m1_subset_1(B_98, k1_zfmisc_1(A_97)) | v1_xboole_0(B_98) | ~m1_subset_1(A_96, B_98))), inference(resolution, [status(thm)], [c_20, c_157])).
% 7.08/2.66  tff(c_246, plain, (![A_96]: (r2_hidden(A_96, u1_struct_0('#skF_5')) | v1_xboole_0('#skF_6') | ~m1_subset_1(A_96, '#skF_6'))), inference(resolution, [status(thm)], [c_58, c_241])).
% 7.08/2.66  tff(c_251, plain, (![A_99]: (r2_hidden(A_99, u1_struct_0('#skF_5')) | ~m1_subset_1(A_99, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_64, c_246])).
% 7.08/2.66  tff(c_271, plain, (![A_99]: (m1_subset_1(A_99, u1_struct_0('#skF_5')) | ~m1_subset_1(A_99, '#skF_6'))), inference(resolution, [status(thm)], [c_251, c_18])).
% 7.08/2.66  tff(c_2202, plain, (![A_259]: (r2_hidden(A_259, '#skF_6') | ~m1_subset_1(A_259, '#skF_6'))), inference(resolution, [status(thm)], [c_271, c_2035])).
% 7.08/2.66  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | ~r2_hidden('#skF_2'(A_1, B_2), B_2) | B_2=A_1)), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.08/2.66  tff(c_2623, plain, (![A_278]: (r2_hidden('#skF_1'(A_278, '#skF_6'), '#skF_6') | A_278='#skF_6' | ~m1_subset_1('#skF_2'(A_278, '#skF_6'), '#skF_6'))), inference(resolution, [status(thm)], [c_2202, c_4])).
% 7.08/2.66  tff(c_2645, plain, (![A_278]: (m1_subset_1('#skF_1'(A_278, '#skF_6'), '#skF_6') | A_278='#skF_6' | ~m1_subset_1('#skF_2'(A_278, '#skF_6'), '#skF_6'))), inference(resolution, [status(thm)], [c_2623, c_18])).
% 7.08/2.66  tff(c_3411, plain, (m1_subset_1('#skF_1'(u1_struct_0('#skF_5'), '#skF_6'), '#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | u1_struct_0('#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_3407, c_2645])).
% 7.08/2.66  tff(c_3425, plain, (m1_subset_1('#skF_1'(u1_struct_0('#skF_5'), '#skF_6'), '#skF_6') | u1_struct_0('#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_3411])).
% 7.08/2.66  tff(c_3438, plain, (u1_struct_0('#skF_5')='#skF_6'), inference(splitLeft, [status(thm)], [c_3425])).
% 7.08/2.66  tff(c_143, plain, (v1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_84])).
% 7.08/2.66  tff(c_3476, plain, (v1_subset_1('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3438, c_143])).
% 7.08/2.66  tff(c_3480, plain, $false, inference(negUnitSimplification, [status(thm)], [c_85, c_3476])).
% 7.08/2.66  tff(c_3482, plain, (u1_struct_0('#skF_5')!='#skF_6'), inference(splitRight, [status(thm)], [c_3425])).
% 7.08/2.66  tff(c_3481, plain, (m1_subset_1('#skF_1'(u1_struct_0('#skF_5'), '#skF_6'), '#skF_6')), inference(splitRight, [status(thm)], [c_3425])).
% 7.08/2.66  tff(c_2, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), A_1) | ~r2_hidden('#skF_2'(A_1, B_2), B_2) | B_2=A_1)), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.08/2.66  tff(c_441, plain, (![B_118]: (~r2_hidden('#skF_2'(u1_struct_0('#skF_5'), B_118), B_118) | u1_struct_0('#skF_5')=B_118 | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_5'), B_118), '#skF_6'))), inference(resolution, [status(thm)], [c_251, c_2])).
% 7.08/2.66  tff(c_468, plain, (![B_14]: (u1_struct_0('#skF_5')=B_14 | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_5'), B_14), '#skF_6') | v1_xboole_0(B_14) | ~m1_subset_1('#skF_2'(u1_struct_0('#skF_5'), B_14), B_14))), inference(resolution, [status(thm)], [c_20, c_441])).
% 7.08/2.66  tff(c_3418, plain, (~m1_subset_1('#skF_1'(u1_struct_0('#skF_5'), '#skF_6'), '#skF_6') | v1_xboole_0('#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | u1_struct_0('#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_3407, c_468])).
% 7.08/2.66  tff(c_3432, plain, (~m1_subset_1('#skF_1'(u1_struct_0('#skF_5'), '#skF_6'), '#skF_6') | v1_xboole_0('#skF_6') | u1_struct_0('#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_3418])).
% 7.08/2.66  tff(c_3433, plain, (~m1_subset_1('#skF_1'(u1_struct_0('#skF_5'), '#skF_6'), '#skF_6') | u1_struct_0('#skF_5')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_64, c_3432])).
% 7.08/2.66  tff(c_3489, plain, (u1_struct_0('#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_3481, c_3433])).
% 7.08/2.66  tff(c_3490, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3482, c_3489])).
% 7.08/2.66  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.08/2.66  
% 7.08/2.66  Inference rules
% 7.08/2.66  ----------------------
% 7.08/2.66  #Ref     : 0
% 7.08/2.66  #Sup     : 693
% 7.08/2.66  #Fact    : 0
% 7.08/2.66  #Define  : 0
% 7.08/2.66  #Split   : 7
% 7.08/2.66  #Chain   : 0
% 7.08/2.66  #Close   : 0
% 7.08/2.66  
% 7.08/2.66  Ordering : KBO
% 7.08/2.66  
% 7.08/2.66  Simplification rules
% 7.08/2.66  ----------------------
% 7.08/2.66  #Subsume      : 141
% 7.08/2.66  #Demod        : 178
% 7.08/2.66  #Tautology    : 109
% 7.08/2.66  #SimpNegUnit  : 28
% 7.08/2.66  #BackRed      : 40
% 7.08/2.66  
% 7.08/2.66  #Partial instantiations: 0
% 7.08/2.66  #Strategies tried      : 1
% 7.08/2.66  
% 7.08/2.66  Timing (in seconds)
% 7.08/2.66  ----------------------
% 7.08/2.66  Preprocessing        : 0.57
% 7.08/2.66  Parsing              : 0.29
% 7.08/2.66  CNF conversion       : 0.05
% 7.08/2.66  Main loop            : 1.19
% 7.08/2.66  Inferencing          : 0.42
% 7.08/2.66  Reduction            : 0.31
% 7.08/2.66  Demodulation         : 0.20
% 7.08/2.66  BG Simplification    : 0.06
% 7.08/2.66  Subsumption          : 0.32
% 7.08/2.66  Abstraction          : 0.06
% 7.08/2.66  MUC search           : 0.00
% 7.08/2.66  Cooper               : 0.00
% 7.08/2.66  Total                : 1.82
% 7.08/2.66  Index Insertion      : 0.00
% 7.08/2.66  Index Deletion       : 0.00
% 7.08/2.66  Index Matching       : 0.00
% 7.08/2.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
