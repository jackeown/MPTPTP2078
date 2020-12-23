%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1970+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:44 EST 2020

% Result     : Theorem 4.51s
% Output     : CNFRefutation 4.58s
% Verified   : 
% Statistics : Number of formulae       :  216 (3255 expanded)
%              Number of leaves         :   48 (1077 expanded)
%              Depth                    :   30
%              Number of atoms          :  708 (23220 expanded)
%              Number of equality atoms :  124 (2420 expanded)
%              Maximal formula depth    :   20 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_waybel_7 > v2_waybel_0 > v13_waybel_0 > v12_waybel_0 > r2_hidden > r1_yellow_0 > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > v1_xboole_0 > v1_lattice3 > l1_struct_0 > l1_orders_2 > k7_domain_1 > k13_lattice3 > k2_zfmisc_1 > k2_tarski > k1_yellow_0 > g1_orders_2 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_yellow_0,type,(
    k1_yellow_0: ( $i * $i ) > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k13_lattice3,type,(
    k13_lattice3: ( $i * $i * $i ) > $i )).

tff(v2_waybel_0,type,(
    v2_waybel_0: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(v12_waybel_0,type,(
    v12_waybel_0: ( $i * $i ) > $o )).

tff(g1_orders_2,type,(
    g1_orders_2: ( $i * $i ) > $i )).

tff(v1_lattice3,type,(
    v1_lattice3: $i > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k7_domain_1,type,(
    k7_domain_1: ( $i * $i * $i ) > $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(r1_yellow_0,type,(
    r1_yellow_0: ( $i * $i ) > $o )).

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

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v13_waybel_0,type,(
    v13_waybel_0: ( $i * $i ) > $o )).

tff(v2_lattice3,type,(
    v2_lattice3: $i > $o )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v2_waybel_7,type,(
    v2_waybel_7: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_239,negated_conjecture,(
    ~ ! [A] :
        ( ( v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & v1_lattice3(A)
          & v2_lattice3(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( ( v3_orders_2(B)
              & v4_orders_2(B)
              & v5_orders_2(B)
              & v1_lattice3(B)
              & v2_lattice3(B)
              & l1_orders_2(B) )
           => ( g1_orders_2(u1_struct_0(A),u1_orders_2(A)) = g1_orders_2(u1_struct_0(B),u1_orders_2(B))
             => ! [C] :
                  ( ( ~ v1_xboole_0(C)
                    & v2_waybel_0(C,A)
                    & v13_waybel_0(C,A)
                    & v2_waybel_7(C,A)
                    & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) )
                 => ( ~ v1_xboole_0(C)
                    & v2_waybel_0(C,B)
                    & v13_waybel_0(C,B)
                    & v2_waybel_7(C,B)
                    & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_waybel_7)).

tff(f_76,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(u1_orders_2(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

tff(f_93,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
     => ! [C,D] :
          ( g1_orders_2(A,B) = g1_orders_2(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_orders_2)).

tff(f_188,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( l1_orders_2(B)
         => ( g1_orders_2(u1_struct_0(A),u1_orders_2(A)) = g1_orders_2(u1_struct_0(B),u1_orders_2(B))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                   => ( ( C = D
                        & v2_waybel_0(C,A) )
                     => v2_waybel_0(D,B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_waybel_0)).

tff(f_139,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( l1_orders_2(B)
         => ( g1_orders_2(u1_struct_0(A),u1_orders_2(A)) = g1_orders_2(u1_struct_0(B),u1_orders_2(B))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                   => ( C = D
                     => ( ( v12_waybel_0(C,A)
                         => v12_waybel_0(D,B) )
                        & ( v13_waybel_0(C,A)
                         => v13_waybel_0(D,B) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_waybel_0)).

tff(f_68,axiom,(
    ! [A] :
      ( ( v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v2_waybel_0(B,A)
            & v13_waybel_0(B,A)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ( v2_waybel_7(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ~ ( r2_hidden(k13_lattice3(A,C,D),B)
                        & ~ r2_hidden(C,B)
                        & ~ r2_hidden(D,B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_waybel_7)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_84,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A)
        & m1_subset_1(C,A) )
     => k7_domain_1(A,B,C) = k2_tarski(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_domain_1)).

tff(f_169,axiom,(
    ! [A] :
      ( ( v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => k1_yellow_0(A,k7_domain_1(u1_struct_0(A),B,C)) = k13_lattice3(A,B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_yellow_0)).

tff(f_116,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & l1_orders_2(A) )
     => ( v1_lattice3(A)
      <=> ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => r1_yellow_0(A,k2_tarski(B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_yellow_0)).

tff(f_151,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( l1_orders_2(B)
         => ( g1_orders_2(u1_struct_0(A),u1_orders_2(A)) = g1_orders_2(u1_struct_0(B),u1_orders_2(B))
           => ! [C] :
                ( r1_yellow_0(A,C)
               => k1_yellow_0(A,C) = k1_yellow_0(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_yellow_0)).

tff(f_31,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v2_lattice3(A)
       => ~ v2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_lattice3)).

tff(c_72,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_74,plain,(
    v2_lattice3('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_56,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_60,plain,(
    l1_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_18,plain,(
    ! [A_28] :
      ( m1_subset_1(u1_orders_2(A_28),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_28),u1_struct_0(A_28))))
      | ~ l1_orders_2(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_58,plain,(
    g1_orders_2(u1_struct_0('#skF_5'),u1_orders_2('#skF_5')) = g1_orders_2(u1_struct_0('#skF_6'),u1_orders_2('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_544,plain,(
    ! [C_175,A_176,D_177,B_178] :
      ( C_175 = A_176
      | g1_orders_2(C_175,D_177) != g1_orders_2(A_176,B_178)
      | ~ m1_subset_1(B_178,k1_zfmisc_1(k2_zfmisc_1(A_176,A_176))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_565,plain,(
    ! [A_182,B_183] :
      ( u1_struct_0('#skF_5') = A_182
      | g1_orders_2(u1_struct_0('#skF_6'),u1_orders_2('#skF_6')) != g1_orders_2(A_182,B_183)
      | ~ m1_subset_1(B_183,k1_zfmisc_1(k2_zfmisc_1(A_182,A_182))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_544])).

tff(c_569,plain,(
    ! [A_28] :
      ( u1_struct_0(A_28) = u1_struct_0('#skF_5')
      | g1_orders_2(u1_struct_0(A_28),u1_orders_2(A_28)) != g1_orders_2(u1_struct_0('#skF_6'),u1_orders_2('#skF_6'))
      | ~ l1_orders_2(A_28) ) ),
    inference(resolution,[status(thm)],[c_18,c_565])).

tff(c_572,plain,
    ( u1_struct_0('#skF_5') = u1_struct_0('#skF_6')
    | ~ l1_orders_2('#skF_6') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_569])).

tff(c_574,plain,(
    u1_struct_0('#skF_5') = u1_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_572])).

tff(c_600,plain,
    ( m1_subset_1(u1_orders_2('#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_6'))))
    | ~ l1_orders_2('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_574,c_18])).

tff(c_613,plain,(
    m1_subset_1(u1_orders_2('#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0('#skF_6')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_574,c_600])).

tff(c_585,plain,(
    g1_orders_2(u1_struct_0('#skF_6'),u1_orders_2('#skF_5')) = g1_orders_2(u1_struct_0('#skF_6'),u1_orders_2('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_574,c_58])).

tff(c_22,plain,(
    ! [D_35,B_31,C_34,A_30] :
      ( D_35 = B_31
      | g1_orders_2(C_34,D_35) != g1_orders_2(A_30,B_31)
      | ~ m1_subset_1(B_31,k1_zfmisc_1(k2_zfmisc_1(A_30,A_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_643,plain,(
    ! [D_35,C_34] :
      ( u1_orders_2('#skF_5') = D_35
      | g1_orders_2(u1_struct_0('#skF_6'),u1_orders_2('#skF_6')) != g1_orders_2(C_34,D_35)
      | ~ m1_subset_1(u1_orders_2('#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0('#skF_6')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_585,c_22])).

tff(c_649,plain,(
    ! [D_35,C_34] :
      ( u1_orders_2('#skF_5') = D_35
      | g1_orders_2(u1_struct_0('#skF_6'),u1_orders_2('#skF_6')) != g1_orders_2(C_34,D_35) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_613,c_643])).

tff(c_663,plain,(
    u1_orders_2('#skF_5') = u1_orders_2('#skF_6') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_649])).

tff(c_100,plain,(
    ! [D_105,B_106,C_107,A_108] :
      ( D_105 = B_106
      | g1_orders_2(C_107,D_105) != g1_orders_2(A_108,B_106)
      | ~ m1_subset_1(B_106,k1_zfmisc_1(k2_zfmisc_1(A_108,A_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_224,plain,(
    ! [B_123,A_124] :
      ( u1_orders_2('#skF_5') = B_123
      | g1_orders_2(u1_struct_0('#skF_6'),u1_orders_2('#skF_6')) != g1_orders_2(A_124,B_123)
      | ~ m1_subset_1(B_123,k1_zfmisc_1(k2_zfmisc_1(A_124,A_124))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_100])).

tff(c_235,plain,(
    ! [A_28] :
      ( u1_orders_2(A_28) = u1_orders_2('#skF_5')
      | g1_orders_2(u1_struct_0(A_28),u1_orders_2(A_28)) != g1_orders_2(u1_struct_0('#skF_6'),u1_orders_2('#skF_6'))
      | ~ l1_orders_2(A_28) ) ),
    inference(resolution,[status(thm)],[c_18,c_224])).

tff(c_244,plain,
    ( u1_orders_2('#skF_5') = u1_orders_2('#skF_6')
    | ~ l1_orders_2('#skF_6') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_235])).

tff(c_246,plain,(
    u1_orders_2('#skF_5') = u1_orders_2('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_244])).

tff(c_109,plain,(
    ! [C_109,A_110,D_111,B_112] :
      ( C_109 = A_110
      | g1_orders_2(C_109,D_111) != g1_orders_2(A_110,B_112)
      | ~ m1_subset_1(B_112,k1_zfmisc_1(k2_zfmisc_1(A_110,A_110))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_114,plain,(
    ! [A_113,B_114] :
      ( u1_struct_0('#skF_5') = A_113
      | g1_orders_2(u1_struct_0('#skF_6'),u1_orders_2('#skF_6')) != g1_orders_2(A_113,B_114)
      | ~ m1_subset_1(B_114,k1_zfmisc_1(k2_zfmisc_1(A_113,A_113))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_109])).

tff(c_118,plain,(
    ! [A_28] :
      ( u1_struct_0(A_28) = u1_struct_0('#skF_5')
      | g1_orders_2(u1_struct_0(A_28),u1_orders_2(A_28)) != g1_orders_2(u1_struct_0('#skF_6'),u1_orders_2('#skF_6'))
      | ~ l1_orders_2(A_28) ) ),
    inference(resolution,[status(thm)],[c_18,c_114])).

tff(c_134,plain,
    ( u1_struct_0('#skF_5') = u1_struct_0('#skF_6')
    | ~ l1_orders_2('#skF_6') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_118])).

tff(c_136,plain,(
    u1_struct_0('#skF_5') = u1_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_134])).

tff(c_48,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_148,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_48])).

tff(c_54,plain,(
    v2_waybel_0('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_46,plain,
    ( ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ v2_waybel_7('#skF_7','#skF_6')
    | ~ v13_waybel_0('#skF_7','#skF_6')
    | ~ v2_waybel_0('#skF_7','#skF_6')
    | v1_xboole_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_83,plain,
    ( ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ v2_waybel_7('#skF_7','#skF_6')
    | ~ v13_waybel_0('#skF_7','#skF_6')
    | ~ v2_waybel_0('#skF_7','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_46])).

tff(c_95,plain,(
    ~ v2_waybel_0('#skF_7','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_83])).

tff(c_393,plain,(
    ! [D_146,B_147,A_148] :
      ( v2_waybel_0(D_146,B_147)
      | ~ v2_waybel_0(D_146,A_148)
      | ~ m1_subset_1(D_146,k1_zfmisc_1(u1_struct_0(B_147)))
      | ~ m1_subset_1(D_146,k1_zfmisc_1(u1_struct_0(A_148)))
      | g1_orders_2(u1_struct_0(B_147),u1_orders_2(B_147)) != g1_orders_2(u1_struct_0(A_148),u1_orders_2(A_148))
      | ~ l1_orders_2(B_147)
      | ~ l1_orders_2(A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_395,plain,(
    ! [A_148] :
      ( v2_waybel_0('#skF_7','#skF_6')
      | ~ v2_waybel_0('#skF_7',A_148)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0(A_148)))
      | g1_orders_2(u1_struct_0(A_148),u1_orders_2(A_148)) != g1_orders_2(u1_struct_0('#skF_6'),u1_orders_2('#skF_6'))
      | ~ l1_orders_2('#skF_6')
      | ~ l1_orders_2(A_148) ) ),
    inference(resolution,[status(thm)],[c_148,c_393])).

tff(c_400,plain,(
    ! [A_148] :
      ( v2_waybel_0('#skF_7','#skF_6')
      | ~ v2_waybel_0('#skF_7',A_148)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0(A_148)))
      | g1_orders_2(u1_struct_0(A_148),u1_orders_2(A_148)) != g1_orders_2(u1_struct_0('#skF_6'),u1_orders_2('#skF_6'))
      | ~ l1_orders_2(A_148) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_395])).

tff(c_404,plain,(
    ! [A_149] :
      ( ~ v2_waybel_0('#skF_7',A_149)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0(A_149)))
      | g1_orders_2(u1_struct_0(A_149),u1_orders_2(A_149)) != g1_orders_2(u1_struct_0('#skF_6'),u1_orders_2('#skF_6'))
      | ~ l1_orders_2(A_149) ) ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_400])).

tff(c_408,plain,
    ( ~ v2_waybel_0('#skF_7','#skF_5')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6')))
    | g1_orders_2(u1_struct_0('#skF_5'),u1_orders_2('#skF_5')) != g1_orders_2(u1_struct_0('#skF_6'),u1_orders_2('#skF_6'))
    | ~ l1_orders_2('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_404])).

tff(c_414,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_246,c_136,c_148,c_54,c_408])).

tff(c_415,plain,
    ( ~ v13_waybel_0('#skF_7','#skF_6')
    | ~ v2_waybel_7('#skF_7','#skF_6')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_417,plain,(
    ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_415])).

tff(c_431,plain,(
    ! [D_154,B_155,C_156,A_157] :
      ( D_154 = B_155
      | g1_orders_2(C_156,D_154) != g1_orders_2(A_157,B_155)
      | ~ m1_subset_1(B_155,k1_zfmisc_1(k2_zfmisc_1(A_157,A_157))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_449,plain,(
    ! [B_161,A_162] :
      ( u1_orders_2('#skF_5') = B_161
      | g1_orders_2(u1_struct_0('#skF_6'),u1_orders_2('#skF_6')) != g1_orders_2(A_162,B_161)
      | ~ m1_subset_1(B_161,k1_zfmisc_1(k2_zfmisc_1(A_162,A_162))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_431])).

tff(c_453,plain,(
    ! [A_28] :
      ( u1_orders_2(A_28) = u1_orders_2('#skF_5')
      | g1_orders_2(u1_struct_0(A_28),u1_orders_2(A_28)) != g1_orders_2(u1_struct_0('#skF_6'),u1_orders_2('#skF_6'))
      | ~ l1_orders_2(A_28) ) ),
    inference(resolution,[status(thm)],[c_18,c_449])).

tff(c_462,plain,
    ( u1_orders_2('#skF_5') = u1_orders_2('#skF_6')
    | ~ l1_orders_2('#skF_6') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_453])).

tff(c_464,plain,(
    u1_orders_2('#skF_5') = u1_orders_2('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_462])).

tff(c_479,plain,
    ( m1_subset_1(u1_orders_2('#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_5'))))
    | ~ l1_orders_2('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_464,c_18])).

tff(c_483,plain,(
    m1_subset_1(u1_orders_2('#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_479])).

tff(c_475,plain,(
    g1_orders_2(u1_struct_0('#skF_5'),u1_orders_2('#skF_6')) = g1_orders_2(u1_struct_0('#skF_6'),u1_orders_2('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_464,c_58])).

tff(c_24,plain,(
    ! [C_34,A_30,D_35,B_31] :
      ( C_34 = A_30
      | g1_orders_2(C_34,D_35) != g1_orders_2(A_30,B_31)
      | ~ m1_subset_1(B_31,k1_zfmisc_1(k2_zfmisc_1(A_30,A_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_496,plain,(
    ! [C_34,D_35] :
      ( u1_struct_0('#skF_5') = C_34
      | g1_orders_2(u1_struct_0('#skF_6'),u1_orders_2('#skF_6')) != g1_orders_2(C_34,D_35)
      | ~ m1_subset_1(u1_orders_2('#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_5')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_475,c_24])).

tff(c_502,plain,(
    ! [C_34,D_35] :
      ( u1_struct_0('#skF_5') = C_34
      | g1_orders_2(u1_struct_0('#skF_6'),u1_orders_2('#skF_6')) != g1_orders_2(C_34,D_35) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_483,c_496])).

tff(c_515,plain,(
    u1_struct_0('#skF_5') = u1_struct_0('#skF_6') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_502])).

tff(c_525,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_515,c_48])).

tff(c_527,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_417,c_525])).

tff(c_529,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_415])).

tff(c_52,plain,(
    v13_waybel_0('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_528,plain,
    ( ~ v2_waybel_7('#skF_7','#skF_6')
    | ~ v13_waybel_0('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_415])).

tff(c_530,plain,(
    ~ v13_waybel_0('#skF_7','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_528])).

tff(c_820,plain,(
    ! [D_217,B_218,A_219] :
      ( v13_waybel_0(D_217,B_218)
      | ~ v13_waybel_0(D_217,A_219)
      | ~ m1_subset_1(D_217,k1_zfmisc_1(u1_struct_0(B_218)))
      | ~ m1_subset_1(D_217,k1_zfmisc_1(u1_struct_0(A_219)))
      | g1_orders_2(u1_struct_0(B_218),u1_orders_2(B_218)) != g1_orders_2(u1_struct_0(A_219),u1_orders_2(A_219))
      | ~ l1_orders_2(B_218)
      | ~ l1_orders_2(A_219) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_824,plain,(
    ! [A_219] :
      ( v13_waybel_0('#skF_7','#skF_6')
      | ~ v13_waybel_0('#skF_7',A_219)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0(A_219)))
      | g1_orders_2(u1_struct_0(A_219),u1_orders_2(A_219)) != g1_orders_2(u1_struct_0('#skF_6'),u1_orders_2('#skF_6'))
      | ~ l1_orders_2('#skF_6')
      | ~ l1_orders_2(A_219) ) ),
    inference(resolution,[status(thm)],[c_529,c_820])).

tff(c_829,plain,(
    ! [A_219] :
      ( v13_waybel_0('#skF_7','#skF_6')
      | ~ v13_waybel_0('#skF_7',A_219)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0(A_219)))
      | g1_orders_2(u1_struct_0(A_219),u1_orders_2(A_219)) != g1_orders_2(u1_struct_0('#skF_6'),u1_orders_2('#skF_6'))
      | ~ l1_orders_2(A_219) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_824])).

tff(c_831,plain,(
    ! [A_220] :
      ( ~ v13_waybel_0('#skF_7',A_220)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0(A_220)))
      | g1_orders_2(u1_struct_0(A_220),u1_orders_2(A_220)) != g1_orders_2(u1_struct_0('#skF_6'),u1_orders_2('#skF_6'))
      | ~ l1_orders_2(A_220) ) ),
    inference(negUnitSimplification,[status(thm)],[c_530,c_829])).

tff(c_833,plain,
    ( ~ v13_waybel_0('#skF_7','#skF_5')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6')))
    | g1_orders_2(u1_struct_0('#skF_5'),u1_orders_2('#skF_5')) != g1_orders_2(u1_struct_0('#skF_6'),u1_orders_2('#skF_6'))
    | ~ l1_orders_2('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_574,c_831])).

tff(c_838,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_663,c_574,c_529,c_52,c_833])).

tff(c_839,plain,(
    ~ v2_waybel_7('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_528])).

tff(c_70,plain,(
    v3_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_68,plain,(
    v4_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_66,plain,(
    v5_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_64,plain,(
    v1_lattice3('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_416,plain,(
    v2_waybel_0('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_840,plain,(
    v13_waybel_0('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_528])).

tff(c_50,plain,(
    v2_waybel_7('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_10,plain,(
    ! [A_2,B_16] :
      ( r2_hidden(k13_lattice3(A_2,'#skF_1'(A_2,B_16),'#skF_2'(A_2,B_16)),B_16)
      | v2_waybel_7(B_16,A_2)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(u1_struct_0(A_2)))
      | ~ v13_waybel_0(B_16,A_2)
      | ~ v2_waybel_0(B_16,A_2)
      | v1_xboole_0(B_16)
      | ~ l1_orders_2(A_2)
      | ~ v1_lattice3(A_2)
      | ~ v5_orders_2(A_2)
      | ~ v4_orders_2(A_2)
      | ~ v3_orders_2(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_82,plain,(
    v3_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_80,plain,(
    v4_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_78,plain,(
    v5_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_76,plain,(
    v1_lattice3('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_854,plain,(
    ! [D_225,B_226,C_227,A_228] :
      ( D_225 = B_226
      | g1_orders_2(C_227,D_225) != g1_orders_2(A_228,B_226)
      | ~ m1_subset_1(B_226,k1_zfmisc_1(k2_zfmisc_1(A_228,A_228))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_875,plain,(
    ! [B_232,A_233] :
      ( u1_orders_2('#skF_5') = B_232
      | g1_orders_2(u1_struct_0('#skF_6'),u1_orders_2('#skF_6')) != g1_orders_2(A_233,B_232)
      | ~ m1_subset_1(B_232,k1_zfmisc_1(k2_zfmisc_1(A_233,A_233))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_854])).

tff(c_879,plain,(
    ! [A_28] :
      ( u1_orders_2(A_28) = u1_orders_2('#skF_5')
      | g1_orders_2(u1_struct_0(A_28),u1_orders_2(A_28)) != g1_orders_2(u1_struct_0('#skF_6'),u1_orders_2('#skF_6'))
      | ~ l1_orders_2(A_28) ) ),
    inference(resolution,[status(thm)],[c_18,c_875])).

tff(c_887,plain,
    ( u1_orders_2('#skF_5') = u1_orders_2('#skF_6')
    | ~ l1_orders_2('#skF_6') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_879])).

tff(c_889,plain,(
    u1_orders_2('#skF_5') = u1_orders_2('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_887])).

tff(c_904,plain,
    ( m1_subset_1(u1_orders_2('#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_5'))))
    | ~ l1_orders_2('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_889,c_18])).

tff(c_908,plain,(
    m1_subset_1(u1_orders_2('#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_904])).

tff(c_900,plain,(
    g1_orders_2(u1_struct_0('#skF_5'),u1_orders_2('#skF_6')) = g1_orders_2(u1_struct_0('#skF_6'),u1_orders_2('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_889,c_58])).

tff(c_926,plain,(
    ! [C_34,D_35] :
      ( u1_struct_0('#skF_5') = C_34
      | g1_orders_2(u1_struct_0('#skF_6'),u1_orders_2('#skF_6')) != g1_orders_2(C_34,D_35)
      | ~ m1_subset_1(u1_orders_2('#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_5')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_900,c_24])).

tff(c_932,plain,(
    ! [C_34,D_35] :
      ( u1_struct_0('#skF_5') = C_34
      | g1_orders_2(u1_struct_0('#skF_6'),u1_orders_2('#skF_6')) != g1_orders_2(C_34,D_35) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_908,c_926])).

tff(c_951,plain,(
    u1_struct_0('#skF_5') = u1_struct_0('#skF_6') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_932])).

tff(c_14,plain,(
    ! [A_2,B_16] :
      ( m1_subset_1('#skF_1'(A_2,B_16),u1_struct_0(A_2))
      | v2_waybel_7(B_16,A_2)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(u1_struct_0(A_2)))
      | ~ v13_waybel_0(B_16,A_2)
      | ~ v2_waybel_0(B_16,A_2)
      | v1_xboole_0(B_16)
      | ~ l1_orders_2(A_2)
      | ~ v1_lattice3(A_2)
      | ~ v5_orders_2(A_2)
      | ~ v4_orders_2(A_2)
      | ~ v3_orders_2(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_16,plain,(
    ! [A_27] :
      ( l1_struct_0(A_27)
      | ~ l1_orders_2(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_20,plain,(
    ! [A_29] :
      ( ~ v1_xboole_0(u1_struct_0(A_29))
      | ~ l1_struct_0(A_29)
      | v2_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_978,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_6'))
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_951,c_20])).

tff(c_990,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_978])).

tff(c_995,plain,(
    ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_16,c_990])).

tff(c_999,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_995])).

tff(c_1000,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_978])).

tff(c_1002,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_1000])).

tff(c_1159,plain,(
    ! [A_278,B_279] :
      ( m1_subset_1('#skF_1'(A_278,B_279),u1_struct_0(A_278))
      | v2_waybel_7(B_279,A_278)
      | ~ m1_subset_1(B_279,k1_zfmisc_1(u1_struct_0(A_278)))
      | ~ v13_waybel_0(B_279,A_278)
      | ~ v2_waybel_0(B_279,A_278)
      | v1_xboole_0(B_279)
      | ~ l1_orders_2(A_278)
      | ~ v1_lattice3(A_278)
      | ~ v5_orders_2(A_278)
      | ~ v4_orders_2(A_278)
      | ~ v3_orders_2(A_278) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_26,plain,(
    ! [A_36,B_37,C_38] :
      ( k7_domain_1(A_36,B_37,C_38) = k2_tarski(B_37,C_38)
      | ~ m1_subset_1(C_38,A_36)
      | ~ m1_subset_1(B_37,A_36)
      | v1_xboole_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1451,plain,(
    ! [A_325,B_326,B_327] :
      ( k7_domain_1(u1_struct_0(A_325),B_326,'#skF_1'(A_325,B_327)) = k2_tarski(B_326,'#skF_1'(A_325,B_327))
      | ~ m1_subset_1(B_326,u1_struct_0(A_325))
      | v1_xboole_0(u1_struct_0(A_325))
      | v2_waybel_7(B_327,A_325)
      | ~ m1_subset_1(B_327,k1_zfmisc_1(u1_struct_0(A_325)))
      | ~ v13_waybel_0(B_327,A_325)
      | ~ v2_waybel_0(B_327,A_325)
      | v1_xboole_0(B_327)
      | ~ l1_orders_2(A_325)
      | ~ v1_lattice3(A_325)
      | ~ v5_orders_2(A_325)
      | ~ v4_orders_2(A_325)
      | ~ v3_orders_2(A_325) ) ),
    inference(resolution,[status(thm)],[c_1159,c_26])).

tff(c_1455,plain,(
    ! [B_326] :
      ( k7_domain_1(u1_struct_0('#skF_6'),B_326,'#skF_1'('#skF_6','#skF_7')) = k2_tarski(B_326,'#skF_1'('#skF_6','#skF_7'))
      | ~ m1_subset_1(B_326,u1_struct_0('#skF_6'))
      | v1_xboole_0(u1_struct_0('#skF_6'))
      | v2_waybel_7('#skF_7','#skF_6')
      | ~ v13_waybel_0('#skF_7','#skF_6')
      | ~ v2_waybel_0('#skF_7','#skF_6')
      | v1_xboole_0('#skF_7')
      | ~ l1_orders_2('#skF_6')
      | ~ v1_lattice3('#skF_6')
      | ~ v5_orders_2('#skF_6')
      | ~ v4_orders_2('#skF_6')
      | ~ v3_orders_2('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_529,c_1451])).

tff(c_1461,plain,(
    ! [B_326] :
      ( k7_domain_1(u1_struct_0('#skF_6'),B_326,'#skF_1'('#skF_6','#skF_7')) = k2_tarski(B_326,'#skF_1'('#skF_6','#skF_7'))
      | ~ m1_subset_1(B_326,u1_struct_0('#skF_6'))
      | v1_xboole_0(u1_struct_0('#skF_6'))
      | v2_waybel_7('#skF_7','#skF_6')
      | v1_xboole_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_60,c_416,c_840,c_1455])).

tff(c_1463,plain,(
    ! [B_328] :
      ( k7_domain_1(u1_struct_0('#skF_6'),B_328,'#skF_1'('#skF_6','#skF_7')) = k2_tarski(B_328,'#skF_1'('#skF_6','#skF_7'))
      | ~ m1_subset_1(B_328,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_839,c_1002,c_1461])).

tff(c_42,plain,(
    ! [A_72,B_76,C_78] :
      ( k1_yellow_0(A_72,k7_domain_1(u1_struct_0(A_72),B_76,C_78)) = k13_lattice3(A_72,B_76,C_78)
      | ~ m1_subset_1(C_78,u1_struct_0(A_72))
      | ~ m1_subset_1(B_76,u1_struct_0(A_72))
      | ~ l1_orders_2(A_72)
      | ~ v1_lattice3(A_72)
      | ~ v5_orders_2(A_72)
      | ~ v4_orders_2(A_72)
      | ~ v3_orders_2(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_1472,plain,(
    ! [B_328] :
      ( k1_yellow_0('#skF_6',k2_tarski(B_328,'#skF_1'('#skF_6','#skF_7'))) = k13_lattice3('#skF_6',B_328,'#skF_1'('#skF_6','#skF_7'))
      | ~ m1_subset_1('#skF_1'('#skF_6','#skF_7'),u1_struct_0('#skF_6'))
      | ~ m1_subset_1(B_328,u1_struct_0('#skF_6'))
      | ~ l1_orders_2('#skF_6')
      | ~ v1_lattice3('#skF_6')
      | ~ v5_orders_2('#skF_6')
      | ~ v4_orders_2('#skF_6')
      | ~ v3_orders_2('#skF_6')
      | ~ m1_subset_1(B_328,u1_struct_0('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1463,c_42])).

tff(c_1478,plain,(
    ! [B_328] :
      ( k1_yellow_0('#skF_6',k2_tarski(B_328,'#skF_1'('#skF_6','#skF_7'))) = k13_lattice3('#skF_6',B_328,'#skF_1'('#skF_6','#skF_7'))
      | ~ m1_subset_1('#skF_1'('#skF_6','#skF_7'),u1_struct_0('#skF_6'))
      | ~ m1_subset_1(B_328,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_60,c_1472])).

tff(c_1480,plain,(
    ~ m1_subset_1('#skF_1'('#skF_6','#skF_7'),u1_struct_0('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_1478])).

tff(c_1484,plain,
    ( v2_waybel_7('#skF_7','#skF_6')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ v13_waybel_0('#skF_7','#skF_6')
    | ~ v2_waybel_0('#skF_7','#skF_6')
    | v1_xboole_0('#skF_7')
    | ~ l1_orders_2('#skF_6')
    | ~ v1_lattice3('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6') ),
    inference(resolution,[status(thm)],[c_14,c_1480])).

tff(c_1487,plain,
    ( v2_waybel_7('#skF_7','#skF_6')
    | v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_60,c_416,c_840,c_529,c_1484])).

tff(c_1489,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_839,c_1487])).

tff(c_1491,plain,(
    m1_subset_1('#skF_1'('#skF_6','#skF_7'),u1_struct_0('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_1478])).

tff(c_12,plain,(
    ! [A_2,B_16] :
      ( m1_subset_1('#skF_2'(A_2,B_16),u1_struct_0(A_2))
      | v2_waybel_7(B_16,A_2)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(u1_struct_0(A_2)))
      | ~ v13_waybel_0(B_16,A_2)
      | ~ v2_waybel_0(B_16,A_2)
      | v1_xboole_0(B_16)
      | ~ l1_orders_2(A_2)
      | ~ v1_lattice3(A_2)
      | ~ v5_orders_2(A_2)
      | ~ v4_orders_2(A_2)
      | ~ v3_orders_2(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1198,plain,(
    ! [A_283,B_284] :
      ( m1_subset_1('#skF_2'(A_283,B_284),u1_struct_0(A_283))
      | v2_waybel_7(B_284,A_283)
      | ~ m1_subset_1(B_284,k1_zfmisc_1(u1_struct_0(A_283)))
      | ~ v13_waybel_0(B_284,A_283)
      | ~ v2_waybel_0(B_284,A_283)
      | v1_xboole_0(B_284)
      | ~ l1_orders_2(A_283)
      | ~ v1_lattice3(A_283)
      | ~ v5_orders_2(A_283)
      | ~ v4_orders_2(A_283)
      | ~ v3_orders_2(A_283) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1353,plain,(
    ! [A_317,B_318,B_319] :
      ( k7_domain_1(u1_struct_0(A_317),B_318,'#skF_2'(A_317,B_319)) = k2_tarski(B_318,'#skF_2'(A_317,B_319))
      | ~ m1_subset_1(B_318,u1_struct_0(A_317))
      | v1_xboole_0(u1_struct_0(A_317))
      | v2_waybel_7(B_319,A_317)
      | ~ m1_subset_1(B_319,k1_zfmisc_1(u1_struct_0(A_317)))
      | ~ v13_waybel_0(B_319,A_317)
      | ~ v2_waybel_0(B_319,A_317)
      | v1_xboole_0(B_319)
      | ~ l1_orders_2(A_317)
      | ~ v1_lattice3(A_317)
      | ~ v5_orders_2(A_317)
      | ~ v4_orders_2(A_317)
      | ~ v3_orders_2(A_317) ) ),
    inference(resolution,[status(thm)],[c_1198,c_26])).

tff(c_1357,plain,(
    ! [B_318] :
      ( k7_domain_1(u1_struct_0('#skF_6'),B_318,'#skF_2'('#skF_6','#skF_7')) = k2_tarski(B_318,'#skF_2'('#skF_6','#skF_7'))
      | ~ m1_subset_1(B_318,u1_struct_0('#skF_6'))
      | v1_xboole_0(u1_struct_0('#skF_6'))
      | v2_waybel_7('#skF_7','#skF_6')
      | ~ v13_waybel_0('#skF_7','#skF_6')
      | ~ v2_waybel_0('#skF_7','#skF_6')
      | v1_xboole_0('#skF_7')
      | ~ l1_orders_2('#skF_6')
      | ~ v1_lattice3('#skF_6')
      | ~ v5_orders_2('#skF_6')
      | ~ v4_orders_2('#skF_6')
      | ~ v3_orders_2('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_529,c_1353])).

tff(c_1363,plain,(
    ! [B_318] :
      ( k7_domain_1(u1_struct_0('#skF_6'),B_318,'#skF_2'('#skF_6','#skF_7')) = k2_tarski(B_318,'#skF_2'('#skF_6','#skF_7'))
      | ~ m1_subset_1(B_318,u1_struct_0('#skF_6'))
      | v1_xboole_0(u1_struct_0('#skF_6'))
      | v2_waybel_7('#skF_7','#skF_6')
      | v1_xboole_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_60,c_416,c_840,c_1357])).

tff(c_1365,plain,(
    ! [B_320] :
      ( k7_domain_1(u1_struct_0('#skF_6'),B_320,'#skF_2'('#skF_6','#skF_7')) = k2_tarski(B_320,'#skF_2'('#skF_6','#skF_7'))
      | ~ m1_subset_1(B_320,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_839,c_1002,c_1363])).

tff(c_1374,plain,(
    ! [B_320] :
      ( k1_yellow_0('#skF_6',k2_tarski(B_320,'#skF_2'('#skF_6','#skF_7'))) = k13_lattice3('#skF_6',B_320,'#skF_2'('#skF_6','#skF_7'))
      | ~ m1_subset_1('#skF_2'('#skF_6','#skF_7'),u1_struct_0('#skF_6'))
      | ~ m1_subset_1(B_320,u1_struct_0('#skF_6'))
      | ~ l1_orders_2('#skF_6')
      | ~ v1_lattice3('#skF_6')
      | ~ v5_orders_2('#skF_6')
      | ~ v4_orders_2('#skF_6')
      | ~ v3_orders_2('#skF_6')
      | ~ m1_subset_1(B_320,u1_struct_0('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1365,c_42])).

tff(c_1380,plain,(
    ! [B_320] :
      ( k1_yellow_0('#skF_6',k2_tarski(B_320,'#skF_2'('#skF_6','#skF_7'))) = k13_lattice3('#skF_6',B_320,'#skF_2'('#skF_6','#skF_7'))
      | ~ m1_subset_1('#skF_2'('#skF_6','#skF_7'),u1_struct_0('#skF_6'))
      | ~ m1_subset_1(B_320,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_60,c_1374])).

tff(c_1391,plain,(
    ~ m1_subset_1('#skF_2'('#skF_6','#skF_7'),u1_struct_0('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_1380])).

tff(c_1395,plain,
    ( v2_waybel_7('#skF_7','#skF_6')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ v13_waybel_0('#skF_7','#skF_6')
    | ~ v2_waybel_0('#skF_7','#skF_6')
    | v1_xboole_0('#skF_7')
    | ~ l1_orders_2('#skF_6')
    | ~ v1_lattice3('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6') ),
    inference(resolution,[status(thm)],[c_12,c_1391])).

tff(c_1398,plain,
    ( v2_waybel_7('#skF_7','#skF_6')
    | v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_60,c_416,c_840,c_529,c_1395])).

tff(c_1400,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_839,c_1398])).

tff(c_1402,plain,(
    m1_subset_1('#skF_2'('#skF_6','#skF_7'),u1_struct_0('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_1380])).

tff(c_1023,plain,(
    ! [A_249,B_250,C_251] :
      ( k1_yellow_0(A_249,k7_domain_1(u1_struct_0(A_249),B_250,C_251)) = k13_lattice3(A_249,B_250,C_251)
      | ~ m1_subset_1(C_251,u1_struct_0(A_249))
      | ~ m1_subset_1(B_250,u1_struct_0(A_249))
      | ~ l1_orders_2(A_249)
      | ~ v1_lattice3(A_249)
      | ~ v5_orders_2(A_249)
      | ~ v4_orders_2(A_249)
      | ~ v3_orders_2(A_249) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_1032,plain,(
    ! [B_250,C_251] :
      ( k1_yellow_0('#skF_5',k7_domain_1(u1_struct_0('#skF_6'),B_250,C_251)) = k13_lattice3('#skF_5',B_250,C_251)
      | ~ m1_subset_1(C_251,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_250,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v1_lattice3('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_951,c_1023])).

tff(c_1036,plain,(
    ! [B_250,C_251] :
      ( k1_yellow_0('#skF_5',k7_domain_1(u1_struct_0('#skF_6'),B_250,C_251)) = k13_lattice3('#skF_5',B_250,C_251)
      | ~ m1_subset_1(C_251,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(B_250,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_76,c_72,c_951,c_951,c_1032])).

tff(c_1371,plain,(
    ! [B_320] :
      ( k1_yellow_0('#skF_5',k2_tarski(B_320,'#skF_2'('#skF_6','#skF_7'))) = k13_lattice3('#skF_5',B_320,'#skF_2'('#skF_6','#skF_7'))
      | ~ m1_subset_1('#skF_2'('#skF_6','#skF_7'),u1_struct_0('#skF_6'))
      | ~ m1_subset_1(B_320,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(B_320,u1_struct_0('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1365,c_1036])).

tff(c_1421,plain,(
    ! [B_323] :
      ( k1_yellow_0('#skF_5',k2_tarski(B_323,'#skF_2'('#skF_6','#skF_7'))) = k13_lattice3('#skF_5',B_323,'#skF_2'('#skF_6','#skF_7'))
      | ~ m1_subset_1(B_323,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1402,c_1371])).

tff(c_28,plain,(
    ! [A_39,B_46,C_48] :
      ( r1_yellow_0(A_39,k2_tarski(B_46,C_48))
      | ~ m1_subset_1(C_48,u1_struct_0(A_39))
      | ~ m1_subset_1(B_46,u1_struct_0(A_39))
      | ~ v1_lattice3(A_39)
      | ~ l1_orders_2(A_39)
      | ~ v5_orders_2(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_1006,plain,(
    ! [B_244,C_245,A_246] :
      ( k1_yellow_0(B_244,C_245) = k1_yellow_0(A_246,C_245)
      | ~ r1_yellow_0(A_246,C_245)
      | g1_orders_2(u1_struct_0(B_244),u1_orders_2(B_244)) != g1_orders_2(u1_struct_0(A_246),u1_orders_2(A_246))
      | ~ l1_orders_2(B_244)
      | ~ l1_orders_2(A_246) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_1232,plain,(
    ! [B_292,B_293,C_294,A_295] :
      ( k1_yellow_0(B_292,k2_tarski(B_293,C_294)) = k1_yellow_0(A_295,k2_tarski(B_293,C_294))
      | g1_orders_2(u1_struct_0(B_292),u1_orders_2(B_292)) != g1_orders_2(u1_struct_0(A_295),u1_orders_2(A_295))
      | ~ l1_orders_2(B_292)
      | ~ m1_subset_1(C_294,u1_struct_0(A_295))
      | ~ m1_subset_1(B_293,u1_struct_0(A_295))
      | ~ v1_lattice3(A_295)
      | ~ l1_orders_2(A_295)
      | ~ v5_orders_2(A_295) ) ),
    inference(resolution,[status(thm)],[c_28,c_1006])).

tff(c_1240,plain,(
    ! [B_292,B_293,C_294] :
      ( k1_yellow_0(B_292,k2_tarski(B_293,C_294)) = k1_yellow_0('#skF_5',k2_tarski(B_293,C_294))
      | g1_orders_2(u1_struct_0(B_292),u1_orders_2(B_292)) != g1_orders_2(u1_struct_0('#skF_5'),u1_orders_2('#skF_6'))
      | ~ l1_orders_2(B_292)
      | ~ m1_subset_1(C_294,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_293,u1_struct_0('#skF_5'))
      | ~ v1_lattice3('#skF_5')
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_889,c_1232])).

tff(c_1248,plain,(
    ! [B_292,B_293,C_294] :
      ( k1_yellow_0(B_292,k2_tarski(B_293,C_294)) = k1_yellow_0('#skF_5',k2_tarski(B_293,C_294))
      | g1_orders_2(u1_struct_0(B_292),u1_orders_2(B_292)) != g1_orders_2(u1_struct_0('#skF_6'),u1_orders_2('#skF_6'))
      | ~ l1_orders_2(B_292)
      | ~ m1_subset_1(C_294,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(B_293,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_72,c_76,c_951,c_951,c_951,c_1240])).

tff(c_1251,plain,(
    ! [B_293,C_294] :
      ( k1_yellow_0('#skF_5',k2_tarski(B_293,C_294)) = k1_yellow_0('#skF_6',k2_tarski(B_293,C_294))
      | ~ l1_orders_2('#skF_6')
      | ~ m1_subset_1(C_294,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(B_293,u1_struct_0('#skF_6')) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1248])).

tff(c_1269,plain,(
    ! [B_303,C_304] :
      ( k1_yellow_0('#skF_5',k2_tarski(B_303,C_304)) = k1_yellow_0('#skF_6',k2_tarski(B_303,C_304))
      | ~ m1_subset_1(C_304,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(B_303,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1251])).

tff(c_1274,plain,(
    ! [B_303,B_16] :
      ( k1_yellow_0('#skF_5',k2_tarski(B_303,'#skF_2'('#skF_6',B_16))) = k1_yellow_0('#skF_6',k2_tarski(B_303,'#skF_2'('#skF_6',B_16)))
      | ~ m1_subset_1(B_303,u1_struct_0('#skF_6'))
      | v2_waybel_7(B_16,'#skF_6')
      | ~ m1_subset_1(B_16,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ v13_waybel_0(B_16,'#skF_6')
      | ~ v2_waybel_0(B_16,'#skF_6')
      | v1_xboole_0(B_16)
      | ~ l1_orders_2('#skF_6')
      | ~ v1_lattice3('#skF_6')
      | ~ v5_orders_2('#skF_6')
      | ~ v4_orders_2('#skF_6')
      | ~ v3_orders_2('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_12,c_1269])).

tff(c_1346,plain,(
    ! [B_315,B_316] :
      ( k1_yellow_0('#skF_5',k2_tarski(B_315,'#skF_2'('#skF_6',B_316))) = k1_yellow_0('#skF_6',k2_tarski(B_315,'#skF_2'('#skF_6',B_316)))
      | ~ m1_subset_1(B_315,u1_struct_0('#skF_6'))
      | v2_waybel_7(B_316,'#skF_6')
      | ~ m1_subset_1(B_316,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ v13_waybel_0(B_316,'#skF_6')
      | ~ v2_waybel_0(B_316,'#skF_6')
      | v1_xboole_0(B_316) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_60,c_1274])).

tff(c_1348,plain,(
    ! [B_315] :
      ( k1_yellow_0('#skF_5',k2_tarski(B_315,'#skF_2'('#skF_6','#skF_7'))) = k1_yellow_0('#skF_6',k2_tarski(B_315,'#skF_2'('#skF_6','#skF_7')))
      | ~ m1_subset_1(B_315,u1_struct_0('#skF_6'))
      | v2_waybel_7('#skF_7','#skF_6')
      | ~ v13_waybel_0('#skF_7','#skF_6')
      | ~ v2_waybel_0('#skF_7','#skF_6')
      | v1_xboole_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_529,c_1346])).

tff(c_1351,plain,(
    ! [B_315] :
      ( k1_yellow_0('#skF_5',k2_tarski(B_315,'#skF_2'('#skF_6','#skF_7'))) = k1_yellow_0('#skF_6',k2_tarski(B_315,'#skF_2'('#skF_6','#skF_7')))
      | ~ m1_subset_1(B_315,u1_struct_0('#skF_6'))
      | v2_waybel_7('#skF_7','#skF_6')
      | v1_xboole_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_416,c_840,c_1348])).

tff(c_1352,plain,(
    ! [B_315] :
      ( k1_yellow_0('#skF_5',k2_tarski(B_315,'#skF_2'('#skF_6','#skF_7'))) = k1_yellow_0('#skF_6',k2_tarski(B_315,'#skF_2'('#skF_6','#skF_7')))
      | ~ m1_subset_1(B_315,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_839,c_1351])).

tff(c_1436,plain,(
    ! [B_324] :
      ( k1_yellow_0('#skF_6',k2_tarski(B_324,'#skF_2'('#skF_6','#skF_7'))) = k13_lattice3('#skF_5',B_324,'#skF_2'('#skF_6','#skF_7'))
      | ~ m1_subset_1(B_324,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(B_324,u1_struct_0('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1421,c_1352])).

tff(c_1401,plain,(
    ! [B_320] :
      ( k1_yellow_0('#skF_6',k2_tarski(B_320,'#skF_2'('#skF_6','#skF_7'))) = k13_lattice3('#skF_6',B_320,'#skF_2'('#skF_6','#skF_7'))
      | ~ m1_subset_1(B_320,u1_struct_0('#skF_6')) ) ),
    inference(splitRight,[status(thm)],[c_1380])).

tff(c_1508,plain,(
    ! [B_330] :
      ( k13_lattice3('#skF_5',B_330,'#skF_2'('#skF_6','#skF_7')) = k13_lattice3('#skF_6',B_330,'#skF_2'('#skF_6','#skF_7'))
      | ~ m1_subset_1(B_330,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(B_330,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(B_330,u1_struct_0('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1436,c_1401])).

tff(c_1510,plain,
    ( k13_lattice3('#skF_5','#skF_1'('#skF_6','#skF_7'),'#skF_2'('#skF_6','#skF_7')) = k13_lattice3('#skF_6','#skF_1'('#skF_6','#skF_7'),'#skF_2'('#skF_6','#skF_7'))
    | ~ m1_subset_1('#skF_1'('#skF_6','#skF_7'),u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_1491,c_1508])).

tff(c_1531,plain,(
    k13_lattice3('#skF_5','#skF_1'('#skF_6','#skF_7'),'#skF_2'('#skF_6','#skF_7')) = k13_lattice3('#skF_6','#skF_1'('#skF_6','#skF_7'),'#skF_2'('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1491,c_1510])).

tff(c_4,plain,(
    ! [D_25,B_16,C_23,A_2] :
      ( r2_hidden(D_25,B_16)
      | r2_hidden(C_23,B_16)
      | ~ r2_hidden(k13_lattice3(A_2,C_23,D_25),B_16)
      | ~ m1_subset_1(D_25,u1_struct_0(A_2))
      | ~ m1_subset_1(C_23,u1_struct_0(A_2))
      | ~ v2_waybel_7(B_16,A_2)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(u1_struct_0(A_2)))
      | ~ v13_waybel_0(B_16,A_2)
      | ~ v2_waybel_0(B_16,A_2)
      | v1_xboole_0(B_16)
      | ~ l1_orders_2(A_2)
      | ~ v1_lattice3(A_2)
      | ~ v5_orders_2(A_2)
      | ~ v4_orders_2(A_2)
      | ~ v3_orders_2(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1551,plain,(
    ! [B_16] :
      ( r2_hidden('#skF_2'('#skF_6','#skF_7'),B_16)
      | r2_hidden('#skF_1'('#skF_6','#skF_7'),B_16)
      | ~ r2_hidden(k13_lattice3('#skF_6','#skF_1'('#skF_6','#skF_7'),'#skF_2'('#skF_6','#skF_7')),B_16)
      | ~ m1_subset_1('#skF_2'('#skF_6','#skF_7'),u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_1'('#skF_6','#skF_7'),u1_struct_0('#skF_5'))
      | ~ v2_waybel_7(B_16,'#skF_5')
      | ~ m1_subset_1(B_16,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v13_waybel_0(B_16,'#skF_5')
      | ~ v2_waybel_0(B_16,'#skF_5')
      | v1_xboole_0(B_16)
      | ~ l1_orders_2('#skF_5')
      | ~ v1_lattice3('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1531,c_4])).

tff(c_1683,plain,(
    ! [B_341] :
      ( r2_hidden('#skF_2'('#skF_6','#skF_7'),B_341)
      | r2_hidden('#skF_1'('#skF_6','#skF_7'),B_341)
      | ~ r2_hidden(k13_lattice3('#skF_6','#skF_1'('#skF_6','#skF_7'),'#skF_2'('#skF_6','#skF_7')),B_341)
      | ~ v2_waybel_7(B_341,'#skF_5')
      | ~ m1_subset_1(B_341,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ v13_waybel_0(B_341,'#skF_5')
      | ~ v2_waybel_0(B_341,'#skF_5')
      | v1_xboole_0(B_341) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_76,c_72,c_951,c_1491,c_951,c_1402,c_951,c_1551])).

tff(c_1687,plain,
    ( r2_hidden('#skF_2'('#skF_6','#skF_7'),'#skF_7')
    | r2_hidden('#skF_1'('#skF_6','#skF_7'),'#skF_7')
    | ~ v2_waybel_7('#skF_7','#skF_5')
    | ~ v13_waybel_0('#skF_7','#skF_5')
    | ~ v2_waybel_0('#skF_7','#skF_5')
    | v2_waybel_7('#skF_7','#skF_6')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ v13_waybel_0('#skF_7','#skF_6')
    | ~ v2_waybel_0('#skF_7','#skF_6')
    | v1_xboole_0('#skF_7')
    | ~ l1_orders_2('#skF_6')
    | ~ v1_lattice3('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6') ),
    inference(resolution,[status(thm)],[c_10,c_1683])).

tff(c_1690,plain,
    ( r2_hidden('#skF_2'('#skF_6','#skF_7'),'#skF_7')
    | r2_hidden('#skF_1'('#skF_6','#skF_7'),'#skF_7')
    | v2_waybel_7('#skF_7','#skF_6')
    | v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_60,c_416,c_840,c_529,c_54,c_52,c_50,c_1687])).

tff(c_1691,plain,
    ( r2_hidden('#skF_2'('#skF_6','#skF_7'),'#skF_7')
    | r2_hidden('#skF_1'('#skF_6','#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_839,c_1690])).

tff(c_1692,plain,(
    r2_hidden('#skF_1'('#skF_6','#skF_7'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_1691])).

tff(c_8,plain,(
    ! [A_2,B_16] :
      ( ~ r2_hidden('#skF_1'(A_2,B_16),B_16)
      | v2_waybel_7(B_16,A_2)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(u1_struct_0(A_2)))
      | ~ v13_waybel_0(B_16,A_2)
      | ~ v2_waybel_0(B_16,A_2)
      | v1_xboole_0(B_16)
      | ~ l1_orders_2(A_2)
      | ~ v1_lattice3(A_2)
      | ~ v5_orders_2(A_2)
      | ~ v4_orders_2(A_2)
      | ~ v3_orders_2(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1694,plain,
    ( v2_waybel_7('#skF_7','#skF_6')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ v13_waybel_0('#skF_7','#skF_6')
    | ~ v2_waybel_0('#skF_7','#skF_6')
    | v1_xboole_0('#skF_7')
    | ~ l1_orders_2('#skF_6')
    | ~ v1_lattice3('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6') ),
    inference(resolution,[status(thm)],[c_1692,c_8])).

tff(c_1697,plain,
    ( v2_waybel_7('#skF_7','#skF_6')
    | v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_60,c_416,c_840,c_529,c_1694])).

tff(c_1699,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_839,c_1697])).

tff(c_1700,plain,(
    r2_hidden('#skF_2'('#skF_6','#skF_7'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_1691])).

tff(c_6,plain,(
    ! [A_2,B_16] :
      ( ~ r2_hidden('#skF_2'(A_2,B_16),B_16)
      | v2_waybel_7(B_16,A_2)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(u1_struct_0(A_2)))
      | ~ v13_waybel_0(B_16,A_2)
      | ~ v2_waybel_0(B_16,A_2)
      | v1_xboole_0(B_16)
      | ~ l1_orders_2(A_2)
      | ~ v1_lattice3(A_2)
      | ~ v5_orders_2(A_2)
      | ~ v4_orders_2(A_2)
      | ~ v3_orders_2(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1708,plain,
    ( v2_waybel_7('#skF_7','#skF_6')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ v13_waybel_0('#skF_7','#skF_6')
    | ~ v2_waybel_0('#skF_7','#skF_6')
    | v1_xboole_0('#skF_7')
    | ~ l1_orders_2('#skF_6')
    | ~ v1_lattice3('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6') ),
    inference(resolution,[status(thm)],[c_1700,c_6])).

tff(c_1711,plain,
    ( v2_waybel_7('#skF_7','#skF_6')
    | v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_60,c_416,c_840,c_529,c_1708])).

tff(c_1713,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_839,c_1711])).

tff(c_1714,plain,(
    v2_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_1000])).

tff(c_2,plain,(
    ! [A_1] :
      ( ~ v2_struct_0(A_1)
      | ~ v2_lattice3(A_1)
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1718,plain,
    ( ~ v2_lattice3('#skF_5')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_1714,c_2])).

tff(c_1722,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_74,c_1718])).

%------------------------------------------------------------------------------
