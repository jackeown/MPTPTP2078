%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:05 EST 2020

% Result     : Theorem 4.87s
% Output     : CNFRefutation 4.87s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 248 expanded)
%              Number of leaves         :   35 (  99 expanded)
%              Depth                    :   14
%              Number of atoms          :  247 ( 806 expanded)
%              Number of equality atoms :   28 (  73 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > l1_orders_2 > #nlpp > u1_struct_0 > k3_yellow_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_5 > #skF_6 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(v2_waybel_0,type,(
    v2_waybel_0: ( $i * $i ) > $o )).

tff(k3_yellow_0,type,(
    k3_yellow_0: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

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

tff(v13_waybel_0,type,(
    v13_waybel_0: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(v1_yellow_0,type,(
    v1_yellow_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_52,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & ~ v1_subset_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_subset_1)).

tff(f_108,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_137,negated_conjecture,(
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

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( ! [D] :
                ( m1_subset_1(D,A)
               => ( r2_hidden(D,B)
                <=> r2_hidden(D,C) ) )
           => B = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_subset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(k3_yellow_0(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow_0)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_82,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v5_orders_2(A)
        & v1_yellow_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => r1_orders_2(A,k3_yellow_0(A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_yellow_0)).

tff(f_101,axiom,(
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

tff(f_32,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(c_14,plain,(
    ! [A_12] : ~ v1_subset_1('#skF_2'(A_12),A_12) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_16,plain,(
    ! [A_12] : m1_subset_1('#skF_2'(A_12),k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_123,plain,(
    ! [B_61,A_62] :
      ( v1_subset_1(B_61,A_62)
      | B_61 = A_62
      | ~ m1_subset_1(B_61,k1_zfmisc_1(A_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_126,plain,(
    ! [A_12] :
      ( v1_subset_1('#skF_2'(A_12),A_12)
      | '#skF_2'(A_12) = A_12 ) ),
    inference(resolution,[status(thm)],[c_16,c_123])).

tff(c_132,plain,(
    ! [A_12] : '#skF_2'(A_12) = A_12 ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_126])).

tff(c_136,plain,(
    ! [A_12] : ~ v1_subset_1(A_12,A_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_14])).

tff(c_135,plain,(
    ! [A_12] : m1_subset_1(A_12,k1_zfmisc_1(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_16])).

tff(c_42,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_4,plain,(
    ! [A_5,B_6,C_10] :
      ( m1_subset_1('#skF_1'(A_5,B_6,C_10),A_5)
      | C_10 = B_6
      | ~ m1_subset_1(C_10,k1_zfmisc_1(A_5))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_44,plain,(
    v13_waybel_0('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_48,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_18,plain,(
    ! [A_14,B_15] :
      ( r2_hidden(A_14,B_15)
      | v1_xboole_0(B_15)
      | ~ m1_subset_1(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_68,plain,
    ( v1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ r2_hidden(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_74,plain,(
    ~ r2_hidden(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_77,plain,
    ( v1_xboole_0('#skF_6')
    | ~ m1_subset_1(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_18,c_74])).

tff(c_80,plain,(
    ~ m1_subset_1(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_77])).

tff(c_50,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_62,plain,
    ( r2_hidden(k3_yellow_0('#skF_5'),'#skF_6')
    | ~ v1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_81,plain,(
    ~ v1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_62])).

tff(c_82,plain,(
    ! [B_57,A_58] :
      ( v1_subset_1(B_57,A_58)
      | B_57 = A_58
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_88,plain,
    ( v1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | u1_struct_0('#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_42,c_82])).

tff(c_94,plain,(
    u1_struct_0('#skF_5') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_88])).

tff(c_22,plain,(
    ! [A_19] :
      ( m1_subset_1(k3_yellow_0(A_19),u1_struct_0(A_19))
      | ~ l1_orders_2(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_112,plain,
    ( m1_subset_1(k3_yellow_0('#skF_5'),'#skF_6')
    | ~ l1_orders_2('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_22])).

tff(c_116,plain,(
    m1_subset_1(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_112])).

tff(c_118,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_116])).

tff(c_120,plain,(
    r2_hidden(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_54,plain,(
    v5_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_52,plain,(
    v1_yellow_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_147,plain,(
    ! [A_65,C_66,B_67] :
      ( m1_subset_1(A_65,C_66)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(C_66))
      | ~ r2_hidden(A_65,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_150,plain,(
    ! [A_65] :
      ( m1_subset_1(A_65,u1_struct_0('#skF_5'))
      | ~ r2_hidden(A_65,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_42,c_147])).

tff(c_24,plain,(
    ! [A_20,B_22] :
      ( r1_orders_2(A_20,k3_yellow_0(A_20),B_22)
      | ~ m1_subset_1(B_22,u1_struct_0(A_20))
      | ~ l1_orders_2(A_20)
      | ~ v1_yellow_0(A_20)
      | ~ v5_orders_2(A_20)
      | v2_struct_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_760,plain,(
    ! [D_147,B_148,A_149,C_150] :
      ( r2_hidden(D_147,B_148)
      | ~ r1_orders_2(A_149,C_150,D_147)
      | ~ r2_hidden(C_150,B_148)
      | ~ m1_subset_1(D_147,u1_struct_0(A_149))
      | ~ m1_subset_1(C_150,u1_struct_0(A_149))
      | ~ v13_waybel_0(B_148,A_149)
      | ~ m1_subset_1(B_148,k1_zfmisc_1(u1_struct_0(A_149)))
      | ~ l1_orders_2(A_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1336,plain,(
    ! [B_212,B_213,A_214] :
      ( r2_hidden(B_212,B_213)
      | ~ r2_hidden(k3_yellow_0(A_214),B_213)
      | ~ m1_subset_1(k3_yellow_0(A_214),u1_struct_0(A_214))
      | ~ v13_waybel_0(B_213,A_214)
      | ~ m1_subset_1(B_213,k1_zfmisc_1(u1_struct_0(A_214)))
      | ~ m1_subset_1(B_212,u1_struct_0(A_214))
      | ~ l1_orders_2(A_214)
      | ~ v1_yellow_0(A_214)
      | ~ v5_orders_2(A_214)
      | v2_struct_0(A_214) ) ),
    inference(resolution,[status(thm)],[c_24,c_760])).

tff(c_1347,plain,(
    ! [B_212,B_213] :
      ( r2_hidden(B_212,B_213)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_213)
      | ~ v13_waybel_0(B_213,'#skF_5')
      | ~ m1_subset_1(B_213,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_212,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v1_yellow_0('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r2_hidden(k3_yellow_0('#skF_5'),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_150,c_1336])).

tff(c_1364,plain,(
    ! [B_212,B_213] :
      ( r2_hidden(B_212,B_213)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_213)
      | ~ v13_waybel_0(B_213,'#skF_5')
      | ~ m1_subset_1(B_213,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_212,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_54,c_52,c_50,c_1347])).

tff(c_1367,plain,(
    ! [B_215,B_216] :
      ( r2_hidden(B_215,B_216)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_216)
      | ~ v13_waybel_0(B_216,'#skF_5')
      | ~ m1_subset_1(B_216,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_215,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1364])).

tff(c_1402,plain,(
    ! [B_215] :
      ( r2_hidden(B_215,'#skF_6')
      | ~ r2_hidden(k3_yellow_0('#skF_5'),'#skF_6')
      | ~ v13_waybel_0('#skF_6','#skF_5')
      | ~ m1_subset_1(B_215,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_42,c_1367])).

tff(c_1419,plain,(
    ! [B_217] :
      ( r2_hidden(B_217,'#skF_6')
      | ~ m1_subset_1(B_217,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_120,c_1402])).

tff(c_1752,plain,(
    ! [B_231,C_232] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_5'),B_231,C_232),'#skF_6')
      | C_232 = B_231
      | ~ m1_subset_1(C_232,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_231,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_4,c_1419])).

tff(c_465,plain,(
    ! [A_121,B_122,C_123] :
      ( r2_hidden('#skF_1'(A_121,B_122,C_123),B_122)
      | r2_hidden('#skF_1'(A_121,B_122,C_123),C_123)
      | C_123 = B_122
      | ~ m1_subset_1(C_123,k1_zfmisc_1(A_121))
      | ~ m1_subset_1(B_122,k1_zfmisc_1(A_121)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2,plain,(
    ! [C_4,A_1,B_2] :
      ( r2_hidden(C_4,A_1)
      | ~ r2_hidden(C_4,B_2)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_483,plain,(
    ! [A_121,B_122,C_123,A_1] :
      ( r2_hidden('#skF_1'(A_121,B_122,C_123),A_1)
      | ~ m1_subset_1(B_122,k1_zfmisc_1(A_1))
      | r2_hidden('#skF_1'(A_121,B_122,C_123),C_123)
      | C_123 = B_122
      | ~ m1_subset_1(C_123,k1_zfmisc_1(A_121))
      | ~ m1_subset_1(B_122,k1_zfmisc_1(A_121)) ) ),
    inference(resolution,[status(thm)],[c_465,c_2])).

tff(c_1091,plain,(
    ! [B_195,A_196,A_197] :
      ( ~ m1_subset_1(B_195,k1_zfmisc_1(A_196))
      | B_195 = A_196
      | ~ m1_subset_1(A_196,k1_zfmisc_1(A_197))
      | ~ m1_subset_1(B_195,k1_zfmisc_1(A_197))
      | r2_hidden('#skF_1'(A_197,B_195,A_196),A_196) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_483])).

tff(c_6,plain,(
    ! [A_5,B_6,C_10] :
      ( ~ r2_hidden('#skF_1'(A_5,B_6,C_10),C_10)
      | ~ r2_hidden('#skF_1'(A_5,B_6,C_10),B_6)
      | C_10 = B_6
      | ~ m1_subset_1(C_10,k1_zfmisc_1(A_5))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1125,plain,(
    ! [A_197,B_195,A_196] :
      ( ~ r2_hidden('#skF_1'(A_197,B_195,A_196),B_195)
      | ~ m1_subset_1(B_195,k1_zfmisc_1(A_196))
      | B_195 = A_196
      | ~ m1_subset_1(A_196,k1_zfmisc_1(A_197))
      | ~ m1_subset_1(B_195,k1_zfmisc_1(A_197)) ) ),
    inference(resolution,[status(thm)],[c_1091,c_6])).

tff(c_1756,plain,(
    ! [C_232] :
      ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(C_232))
      | C_232 = '#skF_6'
      | ~ m1_subset_1(C_232,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_1752,c_1125])).

tff(c_1829,plain,(
    ! [C_236] :
      ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(C_236))
      | C_236 = '#skF_6'
      | ~ m1_subset_1(C_236,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1756])).

tff(c_1873,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | u1_struct_0('#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_135,c_1829])).

tff(c_1889,plain,(
    u1_struct_0('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1873])).

tff(c_172,plain,(
    ! [C_72,A_73,B_74] :
      ( r2_hidden(C_72,A_73)
      | ~ r2_hidden(C_72,B_74)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(A_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_202,plain,(
    ! [A_79,A_80,B_81] :
      ( r2_hidden(A_79,A_80)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(A_80))
      | v1_xboole_0(B_81)
      | ~ m1_subset_1(A_79,B_81) ) ),
    inference(resolution,[status(thm)],[c_18,c_172])).

tff(c_209,plain,(
    ! [A_79] :
      ( r2_hidden(A_79,u1_struct_0('#skF_5'))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(A_79,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_42,c_202])).

tff(c_214,plain,(
    ! [A_79] :
      ( r2_hidden(A_79,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(A_79,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_209])).

tff(c_534,plain,(
    ! [A_131,B_132,C_133] :
      ( ~ r2_hidden('#skF_1'(A_131,B_132,C_133),C_133)
      | ~ r2_hidden('#skF_1'(A_131,B_132,C_133),B_132)
      | C_133 = B_132
      | ~ m1_subset_1(C_133,k1_zfmisc_1(A_131))
      | ~ m1_subset_1(B_132,k1_zfmisc_1(A_131)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_832,plain,(
    ! [A_167,B_168,B_169] :
      ( ~ r2_hidden('#skF_1'(A_167,B_168,B_169),B_168)
      | B_169 = B_168
      | ~ m1_subset_1(B_169,k1_zfmisc_1(A_167))
      | ~ m1_subset_1(B_168,k1_zfmisc_1(A_167))
      | v1_xboole_0(B_169)
      | ~ m1_subset_1('#skF_1'(A_167,B_168,B_169),B_169) ) ),
    inference(resolution,[status(thm)],[c_18,c_534])).

tff(c_856,plain,(
    ! [B_178,A_179] :
      ( u1_struct_0('#skF_5') = B_178
      | ~ m1_subset_1(B_178,k1_zfmisc_1(A_179))
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_179))
      | v1_xboole_0(B_178)
      | ~ m1_subset_1('#skF_1'(A_179,u1_struct_0('#skF_5'),B_178),B_178)
      | ~ m1_subset_1('#skF_1'(A_179,u1_struct_0('#skF_5'),B_178),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_214,c_832])).

tff(c_867,plain,(
    ! [A_5] :
      ( v1_xboole_0(A_5)
      | ~ m1_subset_1('#skF_1'(A_5,u1_struct_0('#skF_5'),A_5),'#skF_6')
      | u1_struct_0('#skF_5') = A_5
      | ~ m1_subset_1(A_5,k1_zfmisc_1(A_5))
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_5)) ) ),
    inference(resolution,[status(thm)],[c_4,c_856])).

tff(c_883,plain,(
    ! [A_180] :
      ( v1_xboole_0(A_180)
      | ~ m1_subset_1('#skF_1'(A_180,u1_struct_0('#skF_5'),A_180),'#skF_6')
      | u1_struct_0('#skF_5') = A_180
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_180)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_867])).

tff(c_891,plain,
    ( v1_xboole_0('#skF_6')
    | u1_struct_0('#skF_5') = '#skF_6'
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6'))
    | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_4,c_883])).

tff(c_894,plain,
    ( v1_xboole_0('#skF_6')
    | u1_struct_0('#skF_5') = '#skF_6'
    | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_891])).

tff(c_895,plain,
    ( u1_struct_0('#skF_5') = '#skF_6'
    | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_894])).

tff(c_896,plain,(
    ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_895])).

tff(c_1906,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1889,c_896])).

tff(c_1929,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_1906])).

tff(c_1930,plain,(
    u1_struct_0('#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_895])).

tff(c_119,plain,(
    v1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_1949,plain,(
    v1_subset_1('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1930,c_119])).

tff(c_1954,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_136,c_1949])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:13:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.87/1.94  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.87/1.95  
% 4.87/1.95  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.87/1.95  %$ r1_orders_2 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > l1_orders_2 > #nlpp > u1_struct_0 > k3_yellow_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_5 > #skF_6 > #skF_4
% 4.87/1.95  
% 4.87/1.95  %Foreground sorts:
% 4.87/1.95  
% 4.87/1.95  
% 4.87/1.95  %Background operators:
% 4.87/1.95  
% 4.87/1.95  
% 4.87/1.95  %Foreground operators:
% 4.87/1.95  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.87/1.95  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.87/1.95  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 4.87/1.95  tff('#skF_2', type, '#skF_2': $i > $i).
% 4.87/1.95  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.87/1.95  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.87/1.95  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 4.87/1.95  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 4.87/1.95  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 4.87/1.95  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 4.87/1.95  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.87/1.95  tff('#skF_5', type, '#skF_5': $i).
% 4.87/1.95  tff('#skF_6', type, '#skF_6': $i).
% 4.87/1.95  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 4.87/1.95  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 4.87/1.95  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.87/1.95  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 4.87/1.95  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.87/1.95  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.87/1.95  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 4.87/1.95  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.87/1.95  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.87/1.95  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.87/1.95  tff(v1_yellow_0, type, v1_yellow_0: $i > $o).
% 4.87/1.95  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.87/1.95  
% 4.87/1.97  tff(f_52, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & ~v1_subset_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc3_subset_1)).
% 4.87/1.97  tff(f_108, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 4.87/1.97  tff(f_137, negated_conjecture, ~(![A]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, A)) & v13_waybel_0(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_subset_1(B, u1_struct_0(A)) <=> ~r2_hidden(k3_yellow_0(A), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_waybel_7)).
% 4.87/1.97  tff(f_46, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) <=> r2_hidden(D, C)))) => (B = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_subset_1)).
% 4.87/1.97  tff(f_58, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 4.87/1.97  tff(f_68, axiom, (![A]: (l1_orders_2(A) => m1_subset_1(k3_yellow_0(A), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_yellow_0)).
% 4.87/1.97  tff(f_64, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 4.87/1.97  tff(f_82, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r1_orders_2(A, k3_yellow_0(A), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_yellow_0)).
% 4.87/1.97  tff(f_101, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v13_waybel_0(B, A) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r2_hidden(C, B) & r1_orders_2(A, C, D)) => r2_hidden(D, B))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d20_waybel_0)).
% 4.87/1.97  tff(f_32, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 4.87/1.97  tff(c_14, plain, (![A_12]: (~v1_subset_1('#skF_2'(A_12), A_12))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.87/1.97  tff(c_16, plain, (![A_12]: (m1_subset_1('#skF_2'(A_12), k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.87/1.97  tff(c_123, plain, (![B_61, A_62]: (v1_subset_1(B_61, A_62) | B_61=A_62 | ~m1_subset_1(B_61, k1_zfmisc_1(A_62)))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.87/1.97  tff(c_126, plain, (![A_12]: (v1_subset_1('#skF_2'(A_12), A_12) | '#skF_2'(A_12)=A_12)), inference(resolution, [status(thm)], [c_16, c_123])).
% 4.87/1.97  tff(c_132, plain, (![A_12]: ('#skF_2'(A_12)=A_12)), inference(negUnitSimplification, [status(thm)], [c_14, c_126])).
% 4.87/1.97  tff(c_136, plain, (![A_12]: (~v1_subset_1(A_12, A_12))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_14])).
% 4.87/1.97  tff(c_135, plain, (![A_12]: (m1_subset_1(A_12, k1_zfmisc_1(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_16])).
% 4.87/1.97  tff(c_42, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_137])).
% 4.87/1.97  tff(c_4, plain, (![A_5, B_6, C_10]: (m1_subset_1('#skF_1'(A_5, B_6, C_10), A_5) | C_10=B_6 | ~m1_subset_1(C_10, k1_zfmisc_1(A_5)) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.87/1.97  tff(c_44, plain, (v13_waybel_0('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_137])).
% 4.87/1.97  tff(c_48, plain, (~v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_137])).
% 4.87/1.97  tff(c_18, plain, (![A_14, B_15]: (r2_hidden(A_14, B_15) | v1_xboole_0(B_15) | ~m1_subset_1(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.87/1.97  tff(c_68, plain, (v1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~r2_hidden(k3_yellow_0('#skF_5'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_137])).
% 4.87/1.97  tff(c_74, plain, (~r2_hidden(k3_yellow_0('#skF_5'), '#skF_6')), inference(splitLeft, [status(thm)], [c_68])).
% 4.87/1.97  tff(c_77, plain, (v1_xboole_0('#skF_6') | ~m1_subset_1(k3_yellow_0('#skF_5'), '#skF_6')), inference(resolution, [status(thm)], [c_18, c_74])).
% 4.87/1.97  tff(c_80, plain, (~m1_subset_1(k3_yellow_0('#skF_5'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_48, c_77])).
% 4.87/1.97  tff(c_50, plain, (l1_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_137])).
% 4.87/1.97  tff(c_62, plain, (r2_hidden(k3_yellow_0('#skF_5'), '#skF_6') | ~v1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_137])).
% 4.87/1.97  tff(c_81, plain, (~v1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_74, c_62])).
% 4.87/1.97  tff(c_82, plain, (![B_57, A_58]: (v1_subset_1(B_57, A_58) | B_57=A_58 | ~m1_subset_1(B_57, k1_zfmisc_1(A_58)))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.87/1.97  tff(c_88, plain, (v1_subset_1('#skF_6', u1_struct_0('#skF_5')) | u1_struct_0('#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_42, c_82])).
% 4.87/1.97  tff(c_94, plain, (u1_struct_0('#skF_5')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_81, c_88])).
% 4.87/1.97  tff(c_22, plain, (![A_19]: (m1_subset_1(k3_yellow_0(A_19), u1_struct_0(A_19)) | ~l1_orders_2(A_19))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.87/1.97  tff(c_112, plain, (m1_subset_1(k3_yellow_0('#skF_5'), '#skF_6') | ~l1_orders_2('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_94, c_22])).
% 4.87/1.97  tff(c_116, plain, (m1_subset_1(k3_yellow_0('#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_112])).
% 4.87/1.97  tff(c_118, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_116])).
% 4.87/1.97  tff(c_120, plain, (r2_hidden(k3_yellow_0('#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_68])).
% 4.87/1.97  tff(c_60, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_137])).
% 4.87/1.97  tff(c_54, plain, (v5_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_137])).
% 4.87/1.97  tff(c_52, plain, (v1_yellow_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_137])).
% 4.87/1.97  tff(c_147, plain, (![A_65, C_66, B_67]: (m1_subset_1(A_65, C_66) | ~m1_subset_1(B_67, k1_zfmisc_1(C_66)) | ~r2_hidden(A_65, B_67))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.87/1.97  tff(c_150, plain, (![A_65]: (m1_subset_1(A_65, u1_struct_0('#skF_5')) | ~r2_hidden(A_65, '#skF_6'))), inference(resolution, [status(thm)], [c_42, c_147])).
% 4.87/1.97  tff(c_24, plain, (![A_20, B_22]: (r1_orders_2(A_20, k3_yellow_0(A_20), B_22) | ~m1_subset_1(B_22, u1_struct_0(A_20)) | ~l1_orders_2(A_20) | ~v1_yellow_0(A_20) | ~v5_orders_2(A_20) | v2_struct_0(A_20))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.87/1.97  tff(c_760, plain, (![D_147, B_148, A_149, C_150]: (r2_hidden(D_147, B_148) | ~r1_orders_2(A_149, C_150, D_147) | ~r2_hidden(C_150, B_148) | ~m1_subset_1(D_147, u1_struct_0(A_149)) | ~m1_subset_1(C_150, u1_struct_0(A_149)) | ~v13_waybel_0(B_148, A_149) | ~m1_subset_1(B_148, k1_zfmisc_1(u1_struct_0(A_149))) | ~l1_orders_2(A_149))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.87/1.97  tff(c_1336, plain, (![B_212, B_213, A_214]: (r2_hidden(B_212, B_213) | ~r2_hidden(k3_yellow_0(A_214), B_213) | ~m1_subset_1(k3_yellow_0(A_214), u1_struct_0(A_214)) | ~v13_waybel_0(B_213, A_214) | ~m1_subset_1(B_213, k1_zfmisc_1(u1_struct_0(A_214))) | ~m1_subset_1(B_212, u1_struct_0(A_214)) | ~l1_orders_2(A_214) | ~v1_yellow_0(A_214) | ~v5_orders_2(A_214) | v2_struct_0(A_214))), inference(resolution, [status(thm)], [c_24, c_760])).
% 4.87/1.97  tff(c_1347, plain, (![B_212, B_213]: (r2_hidden(B_212, B_213) | ~r2_hidden(k3_yellow_0('#skF_5'), B_213) | ~v13_waybel_0(B_213, '#skF_5') | ~m1_subset_1(B_213, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_212, u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5') | ~v1_yellow_0('#skF_5') | ~v5_orders_2('#skF_5') | v2_struct_0('#skF_5') | ~r2_hidden(k3_yellow_0('#skF_5'), '#skF_6'))), inference(resolution, [status(thm)], [c_150, c_1336])).
% 4.87/1.97  tff(c_1364, plain, (![B_212, B_213]: (r2_hidden(B_212, B_213) | ~r2_hidden(k3_yellow_0('#skF_5'), B_213) | ~v13_waybel_0(B_213, '#skF_5') | ~m1_subset_1(B_213, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_212, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_54, c_52, c_50, c_1347])).
% 4.87/1.97  tff(c_1367, plain, (![B_215, B_216]: (r2_hidden(B_215, B_216) | ~r2_hidden(k3_yellow_0('#skF_5'), B_216) | ~v13_waybel_0(B_216, '#skF_5') | ~m1_subset_1(B_216, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_215, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_60, c_1364])).
% 4.87/1.97  tff(c_1402, plain, (![B_215]: (r2_hidden(B_215, '#skF_6') | ~r2_hidden(k3_yellow_0('#skF_5'), '#skF_6') | ~v13_waybel_0('#skF_6', '#skF_5') | ~m1_subset_1(B_215, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_42, c_1367])).
% 4.87/1.97  tff(c_1419, plain, (![B_217]: (r2_hidden(B_217, '#skF_6') | ~m1_subset_1(B_217, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_120, c_1402])).
% 4.87/1.97  tff(c_1752, plain, (![B_231, C_232]: (r2_hidden('#skF_1'(u1_struct_0('#skF_5'), B_231, C_232), '#skF_6') | C_232=B_231 | ~m1_subset_1(C_232, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_231, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_4, c_1419])).
% 4.87/1.97  tff(c_465, plain, (![A_121, B_122, C_123]: (r2_hidden('#skF_1'(A_121, B_122, C_123), B_122) | r2_hidden('#skF_1'(A_121, B_122, C_123), C_123) | C_123=B_122 | ~m1_subset_1(C_123, k1_zfmisc_1(A_121)) | ~m1_subset_1(B_122, k1_zfmisc_1(A_121)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.87/1.97  tff(c_2, plain, (![C_4, A_1, B_2]: (r2_hidden(C_4, A_1) | ~r2_hidden(C_4, B_2) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.87/1.97  tff(c_483, plain, (![A_121, B_122, C_123, A_1]: (r2_hidden('#skF_1'(A_121, B_122, C_123), A_1) | ~m1_subset_1(B_122, k1_zfmisc_1(A_1)) | r2_hidden('#skF_1'(A_121, B_122, C_123), C_123) | C_123=B_122 | ~m1_subset_1(C_123, k1_zfmisc_1(A_121)) | ~m1_subset_1(B_122, k1_zfmisc_1(A_121)))), inference(resolution, [status(thm)], [c_465, c_2])).
% 4.87/1.97  tff(c_1091, plain, (![B_195, A_196, A_197]: (~m1_subset_1(B_195, k1_zfmisc_1(A_196)) | B_195=A_196 | ~m1_subset_1(A_196, k1_zfmisc_1(A_197)) | ~m1_subset_1(B_195, k1_zfmisc_1(A_197)) | r2_hidden('#skF_1'(A_197, B_195, A_196), A_196))), inference(factorization, [status(thm), theory('equality')], [c_483])).
% 4.87/1.97  tff(c_6, plain, (![A_5, B_6, C_10]: (~r2_hidden('#skF_1'(A_5, B_6, C_10), C_10) | ~r2_hidden('#skF_1'(A_5, B_6, C_10), B_6) | C_10=B_6 | ~m1_subset_1(C_10, k1_zfmisc_1(A_5)) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.87/1.97  tff(c_1125, plain, (![A_197, B_195, A_196]: (~r2_hidden('#skF_1'(A_197, B_195, A_196), B_195) | ~m1_subset_1(B_195, k1_zfmisc_1(A_196)) | B_195=A_196 | ~m1_subset_1(A_196, k1_zfmisc_1(A_197)) | ~m1_subset_1(B_195, k1_zfmisc_1(A_197)))), inference(resolution, [status(thm)], [c_1091, c_6])).
% 4.87/1.97  tff(c_1756, plain, (![C_232]: (~m1_subset_1('#skF_6', k1_zfmisc_1(C_232)) | C_232='#skF_6' | ~m1_subset_1(C_232, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_1752, c_1125])).
% 4.87/1.97  tff(c_1829, plain, (![C_236]: (~m1_subset_1('#skF_6', k1_zfmisc_1(C_236)) | C_236='#skF_6' | ~m1_subset_1(C_236, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1756])).
% 4.87/1.97  tff(c_1873, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | u1_struct_0('#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_135, c_1829])).
% 4.87/1.97  tff(c_1889, plain, (u1_struct_0('#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1873])).
% 4.87/1.97  tff(c_172, plain, (![C_72, A_73, B_74]: (r2_hidden(C_72, A_73) | ~r2_hidden(C_72, B_74) | ~m1_subset_1(B_74, k1_zfmisc_1(A_73)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.87/1.97  tff(c_202, plain, (![A_79, A_80, B_81]: (r2_hidden(A_79, A_80) | ~m1_subset_1(B_81, k1_zfmisc_1(A_80)) | v1_xboole_0(B_81) | ~m1_subset_1(A_79, B_81))), inference(resolution, [status(thm)], [c_18, c_172])).
% 4.87/1.97  tff(c_209, plain, (![A_79]: (r2_hidden(A_79, u1_struct_0('#skF_5')) | v1_xboole_0('#skF_6') | ~m1_subset_1(A_79, '#skF_6'))), inference(resolution, [status(thm)], [c_42, c_202])).
% 4.87/1.97  tff(c_214, plain, (![A_79]: (r2_hidden(A_79, u1_struct_0('#skF_5')) | ~m1_subset_1(A_79, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_48, c_209])).
% 4.87/1.97  tff(c_534, plain, (![A_131, B_132, C_133]: (~r2_hidden('#skF_1'(A_131, B_132, C_133), C_133) | ~r2_hidden('#skF_1'(A_131, B_132, C_133), B_132) | C_133=B_132 | ~m1_subset_1(C_133, k1_zfmisc_1(A_131)) | ~m1_subset_1(B_132, k1_zfmisc_1(A_131)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.87/1.97  tff(c_832, plain, (![A_167, B_168, B_169]: (~r2_hidden('#skF_1'(A_167, B_168, B_169), B_168) | B_169=B_168 | ~m1_subset_1(B_169, k1_zfmisc_1(A_167)) | ~m1_subset_1(B_168, k1_zfmisc_1(A_167)) | v1_xboole_0(B_169) | ~m1_subset_1('#skF_1'(A_167, B_168, B_169), B_169))), inference(resolution, [status(thm)], [c_18, c_534])).
% 4.87/1.97  tff(c_856, plain, (![B_178, A_179]: (u1_struct_0('#skF_5')=B_178 | ~m1_subset_1(B_178, k1_zfmisc_1(A_179)) | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(A_179)) | v1_xboole_0(B_178) | ~m1_subset_1('#skF_1'(A_179, u1_struct_0('#skF_5'), B_178), B_178) | ~m1_subset_1('#skF_1'(A_179, u1_struct_0('#skF_5'), B_178), '#skF_6'))), inference(resolution, [status(thm)], [c_214, c_832])).
% 4.87/1.97  tff(c_867, plain, (![A_5]: (v1_xboole_0(A_5) | ~m1_subset_1('#skF_1'(A_5, u1_struct_0('#skF_5'), A_5), '#skF_6') | u1_struct_0('#skF_5')=A_5 | ~m1_subset_1(A_5, k1_zfmisc_1(A_5)) | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(A_5)))), inference(resolution, [status(thm)], [c_4, c_856])).
% 4.87/1.97  tff(c_883, plain, (![A_180]: (v1_xboole_0(A_180) | ~m1_subset_1('#skF_1'(A_180, u1_struct_0('#skF_5'), A_180), '#skF_6') | u1_struct_0('#skF_5')=A_180 | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(A_180)))), inference(demodulation, [status(thm), theory('equality')], [c_135, c_867])).
% 4.87/1.97  tff(c_891, plain, (v1_xboole_0('#skF_6') | u1_struct_0('#skF_5')='#skF_6' | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6')) | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1('#skF_6'))), inference(resolution, [status(thm)], [c_4, c_883])).
% 4.87/1.97  tff(c_894, plain, (v1_xboole_0('#skF_6') | u1_struct_0('#skF_5')='#skF_6' | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_135, c_891])).
% 4.87/1.97  tff(c_895, plain, (u1_struct_0('#skF_5')='#skF_6' | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_48, c_894])).
% 4.87/1.97  tff(c_896, plain, (~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_895])).
% 4.87/1.97  tff(c_1906, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1889, c_896])).
% 4.87/1.97  tff(c_1929, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_135, c_1906])).
% 4.87/1.97  tff(c_1930, plain, (u1_struct_0('#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_895])).
% 4.87/1.97  tff(c_119, plain, (v1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_68])).
% 4.87/1.97  tff(c_1949, plain, (v1_subset_1('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1930, c_119])).
% 4.87/1.97  tff(c_1954, plain, $false, inference(negUnitSimplification, [status(thm)], [c_136, c_1949])).
% 4.87/1.97  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.87/1.97  
% 4.87/1.97  Inference rules
% 4.87/1.97  ----------------------
% 4.87/1.97  #Ref     : 0
% 4.87/1.97  #Sup     : 362
% 4.87/1.97  #Fact    : 8
% 4.87/1.97  #Define  : 0
% 4.87/1.97  #Split   : 8
% 4.87/1.97  #Chain   : 0
% 4.87/1.97  #Close   : 0
% 4.87/1.97  
% 4.87/1.97  Ordering : KBO
% 4.87/1.97  
% 4.87/1.97  Simplification rules
% 4.87/1.97  ----------------------
% 4.87/1.97  #Subsume      : 55
% 4.87/1.97  #Demod        : 167
% 4.87/1.97  #Tautology    : 59
% 4.87/1.97  #SimpNegUnit  : 18
% 4.87/1.97  #BackRed      : 55
% 4.87/1.97  
% 4.87/1.97  #Partial instantiations: 0
% 4.87/1.97  #Strategies tried      : 1
% 4.87/1.97  
% 4.87/1.97  Timing (in seconds)
% 4.87/1.97  ----------------------
% 4.87/1.97  Preprocessing        : 0.34
% 4.87/1.97  Parsing              : 0.19
% 4.87/1.97  CNF conversion       : 0.03
% 4.87/1.97  Main loop            : 0.78
% 4.87/1.97  Inferencing          : 0.27
% 4.87/1.97  Reduction            : 0.21
% 4.87/1.97  Demodulation         : 0.14
% 4.87/1.97  BG Simplification    : 0.03
% 4.87/1.97  Subsumption          : 0.20
% 4.87/1.97  Abstraction          : 0.03
% 4.87/1.97  MUC search           : 0.00
% 4.87/1.97  Cooper               : 0.00
% 4.87/1.97  Total                : 1.17
% 4.87/1.97  Index Insertion      : 0.00
% 4.87/1.97  Index Deletion       : 0.00
% 4.87/1.97  Index Matching       : 0.00
% 4.87/1.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
