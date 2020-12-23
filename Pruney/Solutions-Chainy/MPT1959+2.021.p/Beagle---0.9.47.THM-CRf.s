%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:00 EST 2020

% Result     : Theorem 12.73s
% Output     : CNFRefutation 12.73s
% Verified   : 
% Statistics : Number of formulae       :  182 ( 490 expanded)
%              Number of leaves         :   50 ( 187 expanded)
%              Depth                    :   26
%              Number of atoms          :  413 (1749 expanded)
%              Number of equality atoms :   33 (  70 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_yellow_0 > r2_hidden > r1_yellow_0 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > l1_orders_2 > k5_waybel_0 > k1_yellow_0 > #nlpp > u1_struct_0 > k3_yellow_0 > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_7 > #skF_3 > #skF_6 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_yellow_0,type,(
    k1_yellow_0: ( $i * $i ) > $i )).

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_waybel_0,type,(
    v2_waybel_0: ( $i * $i ) > $o )).

tff(k3_yellow_0,type,(
    k3_yellow_0: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r2_yellow_0,type,(
    r2_yellow_0: ( $i * $i ) > $o )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(r1_yellow_0,type,(
    r1_yellow_0: ( $i * $i ) > $o )).

tff(k5_waybel_0,type,(
    k5_waybel_0: ( $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(v1_yellow_0,type,(
    v1_yellow_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_34,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_36,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_151,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_180,negated_conjecture,(
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

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( ! [C] :
            ( m1_subset_1(C,A)
           => r2_hidden(C,B) )
       => A = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_subset_1)).

tff(f_144,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( r1_yellow_0(A,k5_waybel_0(A,B))
            & k1_yellow_0(A,k5_waybel_0(A,B)) = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_waybel_0)).

tff(f_79,axiom,(
    ! [A,B] :
      ( l1_orders_2(A)
     => m1_subset_1(k1_yellow_0(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_75,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => k3_yellow_0(A) = k1_yellow_0(A,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_yellow_0)).

tff(f_52,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_107,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v5_orders_2(A)
        & v1_yellow_0(A)
        & l1_orders_2(A) )
     => ( r1_yellow_0(A,k1_xboole_0)
        & r2_yellow_0(A,u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_yellow_0)).

tff(f_94,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( ( r1_tarski(B,C)
            & r1_yellow_0(A,B)
            & r1_yellow_0(A,C) )
         => r1_orders_2(A,k1_yellow_0(A,B),k1_yellow_0(A,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_yellow_0)).

tff(f_126,axiom,(
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

tff(f_64,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_41,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_subset_1)).

tff(c_8,plain,(
    ! [A_6] : k2_subset_1(A_6) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_10,plain,(
    ! [A_7] : m1_subset_1(k2_subset_1(A_7),k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_87,plain,(
    ! [A_7] : m1_subset_1(A_7,k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10])).

tff(c_58,plain,(
    ! [B_61] :
      ( ~ v1_subset_1(B_61,B_61)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(B_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_89,plain,(
    ! [B_61] : ~ v1_subset_1(B_61,B_61) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_58])).

tff(c_60,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_78,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_76,plain,(
    v3_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_74,plain,(
    v4_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_72,plain,(
    v5_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_68,plain,(
    l1_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_18,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1('#skF_3'(A_10,B_11),A_10)
      | B_11 = A_10
      | ~ m1_subset_1(B_11,k1_zfmisc_1(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_22188,plain,(
    ! [A_937,B_938] :
      ( k1_yellow_0(A_937,k5_waybel_0(A_937,B_938)) = B_938
      | ~ m1_subset_1(B_938,u1_struct_0(A_937))
      | ~ l1_orders_2(A_937)
      | ~ v5_orders_2(A_937)
      | ~ v4_orders_2(A_937)
      | ~ v3_orders_2(A_937)
      | v2_struct_0(A_937) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_25897,plain,(
    ! [A_1080,B_1081] :
      ( k1_yellow_0(A_1080,k5_waybel_0(A_1080,'#skF_3'(u1_struct_0(A_1080),B_1081))) = '#skF_3'(u1_struct_0(A_1080),B_1081)
      | ~ l1_orders_2(A_1080)
      | ~ v5_orders_2(A_1080)
      | ~ v4_orders_2(A_1080)
      | ~ v3_orders_2(A_1080)
      | v2_struct_0(A_1080)
      | u1_struct_0(A_1080) = B_1081
      | ~ m1_subset_1(B_1081,k1_zfmisc_1(u1_struct_0(A_1080))) ) ),
    inference(resolution,[status(thm)],[c_18,c_22188])).

tff(c_30,plain,(
    ! [A_23,B_24] :
      ( m1_subset_1(k1_yellow_0(A_23,B_24),u1_struct_0(A_23))
      | ~ l1_orders_2(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_236,plain,(
    ! [C_99,B_100,A_101] :
      ( ~ v1_xboole_0(C_99)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(C_99))
      | ~ r2_hidden(A_101,B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_245,plain,(
    ! [A_101] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_6'))
      | ~ r2_hidden(A_101,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_60,c_236])).

tff(c_283,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_245])).

tff(c_180,plain,(
    ! [A_86,B_87] :
      ( r2_hidden('#skF_1'(A_86,B_87),A_86)
      | r1_tarski(A_86,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_185,plain,(
    ! [A_86] : r1_tarski(A_86,A_86) ),
    inference(resolution,[status(thm)],[c_180,c_4])).

tff(c_1723,plain,(
    ! [A_222,B_223] :
      ( k1_yellow_0(A_222,k5_waybel_0(A_222,B_223)) = B_223
      | ~ m1_subset_1(B_223,u1_struct_0(A_222))
      | ~ l1_orders_2(A_222)
      | ~ v5_orders_2(A_222)
      | ~ v4_orders_2(A_222)
      | ~ v3_orders_2(A_222)
      | v2_struct_0(A_222) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_1766,plain,(
    ! [A_222,B_11] :
      ( k1_yellow_0(A_222,k5_waybel_0(A_222,'#skF_3'(u1_struct_0(A_222),B_11))) = '#skF_3'(u1_struct_0(A_222),B_11)
      | ~ l1_orders_2(A_222)
      | ~ v5_orders_2(A_222)
      | ~ v4_orders_2(A_222)
      | ~ v3_orders_2(A_222)
      | v2_struct_0(A_222)
      | u1_struct_0(A_222) = B_11
      | ~ m1_subset_1(B_11,k1_zfmisc_1(u1_struct_0(A_222))) ) ),
    inference(resolution,[status(thm)],[c_18,c_1723])).

tff(c_54,plain,(
    ! [A_57,B_59] :
      ( r1_yellow_0(A_57,k5_waybel_0(A_57,B_59))
      | ~ m1_subset_1(B_59,u1_struct_0(A_57))
      | ~ l1_orders_2(A_57)
      | ~ v5_orders_2(A_57)
      | ~ v4_orders_2(A_57)
      | ~ v3_orders_2(A_57)
      | v2_struct_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_1778,plain,(
    ! [A_23,B_24] :
      ( k1_yellow_0(A_23,k5_waybel_0(A_23,k1_yellow_0(A_23,B_24))) = k1_yellow_0(A_23,B_24)
      | ~ v5_orders_2(A_23)
      | ~ v4_orders_2(A_23)
      | ~ v3_orders_2(A_23)
      | v2_struct_0(A_23)
      | ~ l1_orders_2(A_23) ) ),
    inference(resolution,[status(thm)],[c_30,c_1723])).

tff(c_62,plain,(
    v13_waybel_0('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_66,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_117,plain,(
    ! [A_73,B_74] :
      ( r2_hidden(A_73,B_74)
      | v1_xboole_0(B_74)
      | ~ m1_subset_1(A_73,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_86,plain,
    ( v1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ r2_hidden(k3_yellow_0('#skF_6'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_114,plain,(
    ~ r2_hidden(k3_yellow_0('#skF_6'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_124,plain,
    ( v1_xboole_0('#skF_7')
    | ~ m1_subset_1(k3_yellow_0('#skF_6'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_117,c_114])).

tff(c_128,plain,(
    ~ m1_subset_1(k3_yellow_0('#skF_6'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_124])).

tff(c_80,plain,
    ( r2_hidden(k3_yellow_0('#skF_6'),'#skF_7')
    | ~ v1_subset_1('#skF_7',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_116,plain,(
    ~ v1_subset_1('#skF_7',u1_struct_0('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_114,c_80])).

tff(c_142,plain,(
    ! [B_80,A_81] :
      ( v1_subset_1(B_80,A_81)
      | B_80 = A_81
      | ~ m1_subset_1(B_80,k1_zfmisc_1(A_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_145,plain,
    ( v1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | u1_struct_0('#skF_6') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_60,c_142])).

tff(c_157,plain,(
    u1_struct_0('#skF_6') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_145])).

tff(c_104,plain,(
    ! [A_69] :
      ( k1_yellow_0(A_69,k1_xboole_0) = k3_yellow_0(A_69)
      | ~ l1_orders_2(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_108,plain,(
    k1_yellow_0('#skF_6',k1_xboole_0) = k3_yellow_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_68,c_104])).

tff(c_129,plain,(
    ! [A_75,B_76] :
      ( m1_subset_1(k1_yellow_0(A_75,B_76),u1_struct_0(A_75))
      | ~ l1_orders_2(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_132,plain,
    ( m1_subset_1(k3_yellow_0('#skF_6'),u1_struct_0('#skF_6'))
    | ~ l1_orders_2('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_129])).

tff(c_134,plain,(
    m1_subset_1(k3_yellow_0('#skF_6'),u1_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_132])).

tff(c_164,plain,(
    m1_subset_1(k3_yellow_0('#skF_6'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_134])).

tff(c_168,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_128,c_164])).

tff(c_170,plain,(
    r2_hidden(k3_yellow_0('#skF_6'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_20,plain,(
    ! [A_13] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_248,plain,(
    ! [A_13,A_101] :
      ( ~ v1_xboole_0(A_13)
      | ~ r2_hidden(A_101,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_20,c_236])).

tff(c_267,plain,(
    ! [A_104] : ~ r2_hidden(A_104,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_248])).

tff(c_281,plain,(
    ! [B_2] : r1_tarski(k1_xboole_0,B_2) ),
    inference(resolution,[status(thm)],[c_6,c_267])).

tff(c_70,plain,(
    v1_yellow_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_38,plain,(
    ! [A_31] :
      ( r1_yellow_0(A_31,k1_xboole_0)
      | ~ l1_orders_2(A_31)
      | ~ v1_yellow_0(A_31)
      | ~ v5_orders_2(A_31)
      | v2_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1621,plain,(
    ! [A_213,B_214,C_215] :
      ( r1_orders_2(A_213,k1_yellow_0(A_213,B_214),k1_yellow_0(A_213,C_215))
      | ~ r1_yellow_0(A_213,C_215)
      | ~ r1_yellow_0(A_213,B_214)
      | ~ r1_tarski(B_214,C_215)
      | ~ l1_orders_2(A_213) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1624,plain,(
    ! [C_215] :
      ( r1_orders_2('#skF_6',k3_yellow_0('#skF_6'),k1_yellow_0('#skF_6',C_215))
      | ~ r1_yellow_0('#skF_6',C_215)
      | ~ r1_yellow_0('#skF_6',k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,C_215)
      | ~ l1_orders_2('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_1621])).

tff(c_1629,plain,(
    ! [C_215] :
      ( r1_orders_2('#skF_6',k3_yellow_0('#skF_6'),k1_yellow_0('#skF_6',C_215))
      | ~ r1_yellow_0('#skF_6',C_215)
      | ~ r1_yellow_0('#skF_6',k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_281,c_1624])).

tff(c_1979,plain,(
    ~ r1_yellow_0('#skF_6',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1629])).

tff(c_1982,plain,
    ( ~ l1_orders_2('#skF_6')
    | ~ v1_yellow_0('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_38,c_1979])).

tff(c_1985,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_1982])).

tff(c_1987,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1985])).

tff(c_1989,plain,(
    r1_yellow_0('#skF_6',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_1629])).

tff(c_187,plain,(
    ! [A_89,B_90] :
      ( m1_subset_1(k1_yellow_0(A_89,B_90),u1_struct_0(A_89))
      | ~ l1_orders_2(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_190,plain,
    ( m1_subset_1(k3_yellow_0('#skF_6'),u1_struct_0('#skF_6'))
    | ~ l1_orders_2('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_187])).

tff(c_192,plain,(
    m1_subset_1(k3_yellow_0('#skF_6'),u1_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_190])).

tff(c_34,plain,(
    ! [A_26,B_29,C_30] :
      ( r1_orders_2(A_26,k1_yellow_0(A_26,B_29),k1_yellow_0(A_26,C_30))
      | ~ r1_yellow_0(A_26,C_30)
      | ~ r1_yellow_0(A_26,B_29)
      | ~ r1_tarski(B_29,C_30)
      | ~ l1_orders_2(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1972,plain,(
    ! [D_232,B_233,A_234,C_235] :
      ( r2_hidden(D_232,B_233)
      | ~ r1_orders_2(A_234,C_235,D_232)
      | ~ r2_hidden(C_235,B_233)
      | ~ m1_subset_1(D_232,u1_struct_0(A_234))
      | ~ m1_subset_1(C_235,u1_struct_0(A_234))
      | ~ v13_waybel_0(B_233,A_234)
      | ~ m1_subset_1(B_233,k1_zfmisc_1(u1_struct_0(A_234)))
      | ~ l1_orders_2(A_234) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_5314,plain,(
    ! [A_399,C_400,B_401,B_402] :
      ( r2_hidden(k1_yellow_0(A_399,C_400),B_401)
      | ~ r2_hidden(k1_yellow_0(A_399,B_402),B_401)
      | ~ m1_subset_1(k1_yellow_0(A_399,C_400),u1_struct_0(A_399))
      | ~ m1_subset_1(k1_yellow_0(A_399,B_402),u1_struct_0(A_399))
      | ~ v13_waybel_0(B_401,A_399)
      | ~ m1_subset_1(B_401,k1_zfmisc_1(u1_struct_0(A_399)))
      | ~ r1_yellow_0(A_399,C_400)
      | ~ r1_yellow_0(A_399,B_402)
      | ~ r1_tarski(B_402,C_400)
      | ~ l1_orders_2(A_399) ) ),
    inference(resolution,[status(thm)],[c_34,c_1972])).

tff(c_5351,plain,(
    ! [C_400,B_401] :
      ( r2_hidden(k1_yellow_0('#skF_6',C_400),B_401)
      | ~ r2_hidden(k3_yellow_0('#skF_6'),B_401)
      | ~ m1_subset_1(k1_yellow_0('#skF_6',C_400),u1_struct_0('#skF_6'))
      | ~ m1_subset_1(k1_yellow_0('#skF_6',k1_xboole_0),u1_struct_0('#skF_6'))
      | ~ v13_waybel_0(B_401,'#skF_6')
      | ~ m1_subset_1(B_401,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ r1_yellow_0('#skF_6',C_400)
      | ~ r1_yellow_0('#skF_6',k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,C_400)
      | ~ l1_orders_2('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_5314])).

tff(c_9816,plain,(
    ! [C_598,B_599] :
      ( r2_hidden(k1_yellow_0('#skF_6',C_598),B_599)
      | ~ r2_hidden(k3_yellow_0('#skF_6'),B_599)
      | ~ m1_subset_1(k1_yellow_0('#skF_6',C_598),u1_struct_0('#skF_6'))
      | ~ v13_waybel_0(B_599,'#skF_6')
      | ~ m1_subset_1(B_599,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ r1_yellow_0('#skF_6',C_598) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_281,c_1989,c_192,c_108,c_5351])).

tff(c_9865,plain,(
    ! [B_24,B_599] :
      ( r2_hidden(k1_yellow_0('#skF_6',B_24),B_599)
      | ~ r2_hidden(k3_yellow_0('#skF_6'),B_599)
      | ~ v13_waybel_0(B_599,'#skF_6')
      | ~ m1_subset_1(B_599,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ r1_yellow_0('#skF_6',B_24)
      | ~ l1_orders_2('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_30,c_9816])).

tff(c_16212,plain,(
    ! [B_815,B_816] :
      ( r2_hidden(k1_yellow_0('#skF_6',B_815),B_816)
      | ~ r2_hidden(k3_yellow_0('#skF_6'),B_816)
      | ~ v13_waybel_0(B_816,'#skF_6')
      | ~ m1_subset_1(B_816,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ r1_yellow_0('#skF_6',B_815) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_9865])).

tff(c_16247,plain,(
    ! [B_815] :
      ( r2_hidden(k1_yellow_0('#skF_6',B_815),'#skF_7')
      | ~ r2_hidden(k3_yellow_0('#skF_6'),'#skF_7')
      | ~ v13_waybel_0('#skF_7','#skF_6')
      | ~ r1_yellow_0('#skF_6',B_815) ) ),
    inference(resolution,[status(thm)],[c_60,c_16212])).

tff(c_16279,plain,(
    ! [B_817] :
      ( r2_hidden(k1_yellow_0('#skF_6',B_817),'#skF_7')
      | ~ r1_yellow_0('#skF_6',B_817) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_170,c_16247])).

tff(c_16337,plain,(
    ! [B_24] :
      ( r2_hidden(k1_yellow_0('#skF_6',B_24),'#skF_7')
      | ~ r1_yellow_0('#skF_6',k5_waybel_0('#skF_6',k1_yellow_0('#skF_6',B_24)))
      | ~ v5_orders_2('#skF_6')
      | ~ v4_orders_2('#skF_6')
      | ~ v3_orders_2('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ l1_orders_2('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1778,c_16279])).

tff(c_16388,plain,(
    ! [B_24] :
      ( r2_hidden(k1_yellow_0('#skF_6',B_24),'#skF_7')
      | ~ r1_yellow_0('#skF_6',k5_waybel_0('#skF_6',k1_yellow_0('#skF_6',B_24)))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_76,c_74,c_72,c_16337])).

tff(c_17571,plain,(
    ! [B_832] :
      ( r2_hidden(k1_yellow_0('#skF_6',B_832),'#skF_7')
      | ~ r1_yellow_0('#skF_6',k5_waybel_0('#skF_6',k1_yellow_0('#skF_6',B_832))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_16388])).

tff(c_17647,plain,(
    ! [B_832] :
      ( r2_hidden(k1_yellow_0('#skF_6',B_832),'#skF_7')
      | ~ m1_subset_1(k1_yellow_0('#skF_6',B_832),u1_struct_0('#skF_6'))
      | ~ l1_orders_2('#skF_6')
      | ~ v5_orders_2('#skF_6')
      | ~ v4_orders_2('#skF_6')
      | ~ v3_orders_2('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_54,c_17571])).

tff(c_17678,plain,(
    ! [B_832] :
      ( r2_hidden(k1_yellow_0('#skF_6',B_832),'#skF_7')
      | ~ m1_subset_1(k1_yellow_0('#skF_6',B_832),u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_68,c_17647])).

tff(c_18002,plain,(
    ! [B_843] :
      ( r2_hidden(k1_yellow_0('#skF_6',B_843),'#skF_7')
      | ~ m1_subset_1(k1_yellow_0('#skF_6',B_843),u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_17678])).

tff(c_18096,plain,(
    ! [B_24] :
      ( r2_hidden(k1_yellow_0('#skF_6',B_24),'#skF_7')
      | ~ l1_orders_2('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_30,c_18002])).

tff(c_18143,plain,(
    ! [B_844] : r2_hidden(k1_yellow_0('#skF_6',B_844),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_18096])).

tff(c_18187,plain,(
    ! [B_11] :
      ( r2_hidden('#skF_3'(u1_struct_0('#skF_6'),B_11),'#skF_7')
      | ~ l1_orders_2('#skF_6')
      | ~ v5_orders_2('#skF_6')
      | ~ v4_orders_2('#skF_6')
      | ~ v3_orders_2('#skF_6')
      | v2_struct_0('#skF_6')
      | u1_struct_0('#skF_6') = B_11
      | ~ m1_subset_1(B_11,k1_zfmisc_1(u1_struct_0('#skF_6'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1766,c_18143])).

tff(c_18233,plain,(
    ! [B_11] :
      ( r2_hidden('#skF_3'(u1_struct_0('#skF_6'),B_11),'#skF_7')
      | v2_struct_0('#skF_6')
      | u1_struct_0('#skF_6') = B_11
      | ~ m1_subset_1(B_11,k1_zfmisc_1(u1_struct_0('#skF_6'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_68,c_18187])).

tff(c_21730,plain,(
    ! [B_925] :
      ( r2_hidden('#skF_3'(u1_struct_0('#skF_6'),B_925),'#skF_7')
      | u1_struct_0('#skF_6') = B_925
      | ~ m1_subset_1(B_925,k1_zfmisc_1(u1_struct_0('#skF_6'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_18233])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( ~ r2_hidden('#skF_3'(A_10,B_11),B_11)
      | B_11 = A_10
      | ~ m1_subset_1(B_11,k1_zfmisc_1(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_21743,plain,
    ( u1_struct_0('#skF_6') = '#skF_7'
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(resolution,[status(thm)],[c_21730,c_16])).

tff(c_21763,plain,(
    u1_struct_0('#skF_6') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_21743])).

tff(c_301,plain,(
    ! [A_109,C_110,B_111] :
      ( m1_subset_1(A_109,C_110)
      | ~ m1_subset_1(B_111,k1_zfmisc_1(C_110))
      | ~ r2_hidden(A_109,B_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_310,plain,(
    ! [A_109] :
      ( m1_subset_1(A_109,u1_struct_0('#skF_6'))
      | ~ r2_hidden(A_109,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_60,c_301])).

tff(c_222,plain,(
    ! [C_95,B_96,A_97] :
      ( r2_hidden(C_95,B_96)
      | ~ r2_hidden(C_95,A_97)
      | ~ r1_tarski(A_97,B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_849,plain,(
    ! [A_161,B_162,B_163] :
      ( r2_hidden('#skF_1'(A_161,B_162),B_163)
      | ~ r1_tarski(A_161,B_163)
      | r1_tarski(A_161,B_162) ) ),
    inference(resolution,[status(thm)],[c_6,c_222])).

tff(c_174,plain,(
    ! [A_84,B_85] :
      ( r2_hidden(A_84,B_85)
      | v1_xboole_0(B_85)
      | ~ m1_subset_1(A_84,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_432,plain,(
    ! [A_130,B_131] :
      ( r1_tarski(A_130,B_131)
      | v1_xboole_0(B_131)
      | ~ m1_subset_1('#skF_1'(A_130,B_131),B_131) ) ),
    inference(resolution,[status(thm)],[c_174,c_4])).

tff(c_440,plain,(
    ! [A_130] :
      ( r1_tarski(A_130,u1_struct_0('#skF_6'))
      | v1_xboole_0(u1_struct_0('#skF_6'))
      | ~ r2_hidden('#skF_1'(A_130,u1_struct_0('#skF_6')),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_310,c_432])).

tff(c_445,plain,(
    ! [A_130] :
      ( r1_tarski(A_130,u1_struct_0('#skF_6'))
      | ~ r2_hidden('#skF_1'(A_130,u1_struct_0('#skF_6')),'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_283,c_440])).

tff(c_927,plain,(
    ! [A_168] :
      ( ~ r1_tarski(A_168,'#skF_7')
      | r1_tarski(A_168,u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_849,c_445])).

tff(c_22,plain,(
    ! [A_14,B_15] :
      ( r2_hidden(A_14,B_15)
      | v1_xboole_0(B_15)
      | ~ m1_subset_1(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_230,plain,(
    ! [A_14,B_96,B_15] :
      ( r2_hidden(A_14,B_96)
      | ~ r1_tarski(B_15,B_96)
      | v1_xboole_0(B_15)
      | ~ m1_subset_1(A_14,B_15) ) ),
    inference(resolution,[status(thm)],[c_22,c_222])).

tff(c_1517,plain,(
    ! [A_210,A_211] :
      ( r2_hidden(A_210,u1_struct_0('#skF_6'))
      | v1_xboole_0(A_211)
      | ~ m1_subset_1(A_210,A_211)
      | ~ r1_tarski(A_211,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_927,c_230])).

tff(c_1537,plain,(
    ! [A_109] :
      ( r2_hidden(A_109,u1_struct_0('#skF_6'))
      | v1_xboole_0(u1_struct_0('#skF_6'))
      | ~ r1_tarski(u1_struct_0('#skF_6'),'#skF_7')
      | ~ r2_hidden(A_109,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_310,c_1517])).

tff(c_1568,plain,(
    ! [A_109] :
      ( r2_hidden(A_109,u1_struct_0('#skF_6'))
      | ~ r1_tarski(u1_struct_0('#skF_6'),'#skF_7')
      | ~ r2_hidden(A_109,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_283,c_1537])).

tff(c_1578,plain,(
    ~ r1_tarski(u1_struct_0('#skF_6'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_1568])).

tff(c_21891,plain,(
    ~ r1_tarski('#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21763,c_1578])).

tff(c_21927,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_21891])).

tff(c_21929,plain,(
    r1_tarski(u1_struct_0('#skF_6'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_1568])).

tff(c_21937,plain,(
    ! [A_14] :
      ( r2_hidden(A_14,'#skF_7')
      | v1_xboole_0(u1_struct_0('#skF_6'))
      | ~ m1_subset_1(A_14,u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_21929,c_230])).

tff(c_22016,plain,(
    ! [A_928] :
      ( r2_hidden(A_928,'#skF_7')
      | ~ m1_subset_1(A_928,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_283,c_21937])).

tff(c_22057,plain,(
    ! [B_24] :
      ( r2_hidden(k1_yellow_0('#skF_6',B_24),'#skF_7')
      | ~ l1_orders_2('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_30,c_22016])).

tff(c_22081,plain,(
    ! [B_24] : r2_hidden(k1_yellow_0('#skF_6',B_24),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_22057])).

tff(c_25962,plain,(
    ! [B_1081] :
      ( r2_hidden('#skF_3'(u1_struct_0('#skF_6'),B_1081),'#skF_7')
      | ~ l1_orders_2('#skF_6')
      | ~ v5_orders_2('#skF_6')
      | ~ v4_orders_2('#skF_6')
      | ~ v3_orders_2('#skF_6')
      | v2_struct_0('#skF_6')
      | u1_struct_0('#skF_6') = B_1081
      | ~ m1_subset_1(B_1081,k1_zfmisc_1(u1_struct_0('#skF_6'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25897,c_22081])).

tff(c_26031,plain,(
    ! [B_1081] :
      ( r2_hidden('#skF_3'(u1_struct_0('#skF_6'),B_1081),'#skF_7')
      | v2_struct_0('#skF_6')
      | u1_struct_0('#skF_6') = B_1081
      | ~ m1_subset_1(B_1081,k1_zfmisc_1(u1_struct_0('#skF_6'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_68,c_25962])).

tff(c_26113,plain,(
    ! [B_1084] :
      ( r2_hidden('#skF_3'(u1_struct_0('#skF_6'),B_1084),'#skF_7')
      | u1_struct_0('#skF_6') = B_1084
      | ~ m1_subset_1(B_1084,k1_zfmisc_1(u1_struct_0('#skF_6'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_26031])).

tff(c_26124,plain,
    ( u1_struct_0('#skF_6') = '#skF_7'
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(resolution,[status(thm)],[c_26113,c_16])).

tff(c_26138,plain,(
    u1_struct_0('#skF_6') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_26124])).

tff(c_489,plain,(
    ! [A_138] :
      ( r1_tarski(A_138,u1_struct_0('#skF_6'))
      | ~ r2_hidden('#skF_1'(A_138,u1_struct_0('#skF_6')),'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_283,c_440])).

tff(c_497,plain,(
    r1_tarski('#skF_7',u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_6,c_489])).

tff(c_780,plain,(
    ! [A_154,B_155,B_156] :
      ( r2_hidden(A_154,B_155)
      | ~ r1_tarski(B_156,B_155)
      | v1_xboole_0(B_156)
      | ~ m1_subset_1(A_154,B_156) ) ),
    inference(resolution,[status(thm)],[c_22,c_222])).

tff(c_786,plain,(
    ! [A_154] :
      ( r2_hidden(A_154,u1_struct_0('#skF_6'))
      | v1_xboole_0('#skF_7')
      | ~ m1_subset_1(A_154,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_497,c_780])).

tff(c_811,plain,(
    ! [A_157] :
      ( r2_hidden(A_157,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(A_157,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_786])).

tff(c_986,plain,(
    ! [A_172] :
      ( u1_struct_0('#skF_6') = A_172
      | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(A_172))
      | ~ m1_subset_1('#skF_3'(A_172,u1_struct_0('#skF_6')),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_811,c_16])).

tff(c_991,plain,
    ( u1_struct_0('#skF_6') = '#skF_7'
    | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_18,c_986])).

tff(c_992,plain,(
    ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_991])).

tff(c_26188,plain,(
    ~ m1_subset_1('#skF_7',k1_zfmisc_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26138,c_992])).

tff(c_26220,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_26188])).

tff(c_26221,plain,(
    u1_struct_0('#skF_6') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_991])).

tff(c_169,plain,(
    v1_subset_1('#skF_7',u1_struct_0('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_26242,plain,(
    v1_subset_1('#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26221,c_169])).

tff(c_26248,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_26242])).

tff(c_26249,plain,(
    ! [A_101] : ~ r2_hidden(A_101,'#skF_7') ),
    inference(splitRight,[status(thm)],[c_245])).

tff(c_26252,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26249,c_170])).

tff(c_26253,plain,(
    ! [A_13] : ~ v1_xboole_0(A_13) ),
    inference(splitRight,[status(thm)],[c_248])).

tff(c_12,plain,(
    ! [A_8] : v1_xboole_0('#skF_2'(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_26256,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26253,c_12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:15:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.73/5.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.73/5.56  
% 12.73/5.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.73/5.57  %$ r1_orders_2 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_yellow_0 > r2_hidden > r1_yellow_0 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > l1_orders_2 > k5_waybel_0 > k1_yellow_0 > #nlpp > u1_struct_0 > k3_yellow_0 > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_7 > #skF_3 > #skF_6 > #skF_1 > #skF_5 > #skF_4
% 12.73/5.57  
% 12.73/5.57  %Foreground sorts:
% 12.73/5.57  
% 12.73/5.57  
% 12.73/5.57  %Background operators:
% 12.73/5.57  
% 12.73/5.57  
% 12.73/5.57  %Foreground operators:
% 12.73/5.57  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 12.73/5.57  tff(k1_yellow_0, type, k1_yellow_0: ($i * $i) > $i).
% 12.73/5.57  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 12.73/5.57  tff('#skF_2', type, '#skF_2': $i > $i).
% 12.73/5.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.73/5.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.73/5.57  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 12.73/5.57  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 12.73/5.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.73/5.57  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 12.73/5.57  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 12.73/5.57  tff('#skF_7', type, '#skF_7': $i).
% 12.73/5.57  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 12.73/5.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.73/5.57  tff('#skF_6', type, '#skF_6': $i).
% 12.73/5.57  tff(r2_yellow_0, type, r2_yellow_0: ($i * $i) > $o).
% 12.73/5.57  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 12.73/5.57  tff(r1_yellow_0, type, r1_yellow_0: ($i * $i) > $o).
% 12.73/5.57  tff(k5_waybel_0, type, k5_waybel_0: ($i * $i) > $i).
% 12.73/5.57  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 12.73/5.57  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.73/5.57  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 12.73/5.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.73/5.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.73/5.57  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 12.73/5.57  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 12.73/5.57  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 12.73/5.57  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 12.73/5.57  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 12.73/5.57  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 12.73/5.57  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 12.73/5.57  tff(v1_yellow_0, type, v1_yellow_0: $i > $o).
% 12.73/5.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.73/5.57  
% 12.73/5.59  tff(f_34, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 12.73/5.59  tff(f_36, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 12.73/5.59  tff(f_151, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 12.73/5.59  tff(f_180, negated_conjecture, ~(![A]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, A)) & v13_waybel_0(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_subset_1(B, u1_struct_0(A)) <=> ~r2_hidden(k3_yellow_0(A), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_waybel_7)).
% 12.73/5.59  tff(f_50, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ((![C]: (m1_subset_1(C, A) => r2_hidden(C, B))) => (A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_subset_1)).
% 12.73/5.59  tff(f_144, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (r1_yellow_0(A, k5_waybel_0(A, B)) & (k1_yellow_0(A, k5_waybel_0(A, B)) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_waybel_0)).
% 12.73/5.59  tff(f_79, axiom, (![A, B]: (l1_orders_2(A) => m1_subset_1(k1_yellow_0(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_yellow_0)).
% 12.73/5.59  tff(f_71, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 12.73/5.59  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 12.73/5.59  tff(f_58, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 12.73/5.59  tff(f_75, axiom, (![A]: (l1_orders_2(A) => (k3_yellow_0(A) = k1_yellow_0(A, k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_yellow_0)).
% 12.73/5.59  tff(f_52, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 12.73/5.59  tff(f_107, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (r1_yellow_0(A, k1_xboole_0) & r2_yellow_0(A, u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_yellow_0)).
% 12.73/5.59  tff(f_94, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (((r1_tarski(B, C) & r1_yellow_0(A, B)) & r1_yellow_0(A, C)) => r1_orders_2(A, k1_yellow_0(A, B), k1_yellow_0(A, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_yellow_0)).
% 12.73/5.59  tff(f_126, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v13_waybel_0(B, A) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r2_hidden(C, B) & r1_orders_2(A, C, D)) => r2_hidden(D, B))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d20_waybel_0)).
% 12.73/5.59  tff(f_64, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 12.73/5.59  tff(f_41, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & v1_xboole_0(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc2_subset_1)).
% 12.73/5.59  tff(c_8, plain, (![A_6]: (k2_subset_1(A_6)=A_6)), inference(cnfTransformation, [status(thm)], [f_34])).
% 12.73/5.59  tff(c_10, plain, (![A_7]: (m1_subset_1(k2_subset_1(A_7), k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 12.73/5.59  tff(c_87, plain, (![A_7]: (m1_subset_1(A_7, k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10])).
% 12.73/5.59  tff(c_58, plain, (![B_61]: (~v1_subset_1(B_61, B_61) | ~m1_subset_1(B_61, k1_zfmisc_1(B_61)))), inference(cnfTransformation, [status(thm)], [f_151])).
% 12.73/5.59  tff(c_89, plain, (![B_61]: (~v1_subset_1(B_61, B_61))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_58])).
% 12.73/5.59  tff(c_60, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_6')))), inference(cnfTransformation, [status(thm)], [f_180])).
% 12.73/5.59  tff(c_78, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_180])).
% 12.73/5.59  tff(c_76, plain, (v3_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_180])).
% 12.73/5.59  tff(c_74, plain, (v4_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_180])).
% 12.73/5.59  tff(c_72, plain, (v5_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_180])).
% 12.73/5.59  tff(c_68, plain, (l1_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_180])).
% 12.73/5.59  tff(c_18, plain, (![A_10, B_11]: (m1_subset_1('#skF_3'(A_10, B_11), A_10) | B_11=A_10 | ~m1_subset_1(B_11, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 12.73/5.59  tff(c_22188, plain, (![A_937, B_938]: (k1_yellow_0(A_937, k5_waybel_0(A_937, B_938))=B_938 | ~m1_subset_1(B_938, u1_struct_0(A_937)) | ~l1_orders_2(A_937) | ~v5_orders_2(A_937) | ~v4_orders_2(A_937) | ~v3_orders_2(A_937) | v2_struct_0(A_937))), inference(cnfTransformation, [status(thm)], [f_144])).
% 12.73/5.59  tff(c_25897, plain, (![A_1080, B_1081]: (k1_yellow_0(A_1080, k5_waybel_0(A_1080, '#skF_3'(u1_struct_0(A_1080), B_1081)))='#skF_3'(u1_struct_0(A_1080), B_1081) | ~l1_orders_2(A_1080) | ~v5_orders_2(A_1080) | ~v4_orders_2(A_1080) | ~v3_orders_2(A_1080) | v2_struct_0(A_1080) | u1_struct_0(A_1080)=B_1081 | ~m1_subset_1(B_1081, k1_zfmisc_1(u1_struct_0(A_1080))))), inference(resolution, [status(thm)], [c_18, c_22188])).
% 12.73/5.59  tff(c_30, plain, (![A_23, B_24]: (m1_subset_1(k1_yellow_0(A_23, B_24), u1_struct_0(A_23)) | ~l1_orders_2(A_23))), inference(cnfTransformation, [status(thm)], [f_79])).
% 12.73/5.59  tff(c_236, plain, (![C_99, B_100, A_101]: (~v1_xboole_0(C_99) | ~m1_subset_1(B_100, k1_zfmisc_1(C_99)) | ~r2_hidden(A_101, B_100))), inference(cnfTransformation, [status(thm)], [f_71])).
% 12.73/5.59  tff(c_245, plain, (![A_101]: (~v1_xboole_0(u1_struct_0('#skF_6')) | ~r2_hidden(A_101, '#skF_7'))), inference(resolution, [status(thm)], [c_60, c_236])).
% 12.73/5.59  tff(c_283, plain, (~v1_xboole_0(u1_struct_0('#skF_6'))), inference(splitLeft, [status(thm)], [c_245])).
% 12.73/5.59  tff(c_180, plain, (![A_86, B_87]: (r2_hidden('#skF_1'(A_86, B_87), A_86) | r1_tarski(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_32])).
% 12.73/5.59  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 12.73/5.59  tff(c_185, plain, (![A_86]: (r1_tarski(A_86, A_86))), inference(resolution, [status(thm)], [c_180, c_4])).
% 12.73/5.59  tff(c_1723, plain, (![A_222, B_223]: (k1_yellow_0(A_222, k5_waybel_0(A_222, B_223))=B_223 | ~m1_subset_1(B_223, u1_struct_0(A_222)) | ~l1_orders_2(A_222) | ~v5_orders_2(A_222) | ~v4_orders_2(A_222) | ~v3_orders_2(A_222) | v2_struct_0(A_222))), inference(cnfTransformation, [status(thm)], [f_144])).
% 12.73/5.59  tff(c_1766, plain, (![A_222, B_11]: (k1_yellow_0(A_222, k5_waybel_0(A_222, '#skF_3'(u1_struct_0(A_222), B_11)))='#skF_3'(u1_struct_0(A_222), B_11) | ~l1_orders_2(A_222) | ~v5_orders_2(A_222) | ~v4_orders_2(A_222) | ~v3_orders_2(A_222) | v2_struct_0(A_222) | u1_struct_0(A_222)=B_11 | ~m1_subset_1(B_11, k1_zfmisc_1(u1_struct_0(A_222))))), inference(resolution, [status(thm)], [c_18, c_1723])).
% 12.73/5.59  tff(c_54, plain, (![A_57, B_59]: (r1_yellow_0(A_57, k5_waybel_0(A_57, B_59)) | ~m1_subset_1(B_59, u1_struct_0(A_57)) | ~l1_orders_2(A_57) | ~v5_orders_2(A_57) | ~v4_orders_2(A_57) | ~v3_orders_2(A_57) | v2_struct_0(A_57))), inference(cnfTransformation, [status(thm)], [f_144])).
% 12.73/5.59  tff(c_1778, plain, (![A_23, B_24]: (k1_yellow_0(A_23, k5_waybel_0(A_23, k1_yellow_0(A_23, B_24)))=k1_yellow_0(A_23, B_24) | ~v5_orders_2(A_23) | ~v4_orders_2(A_23) | ~v3_orders_2(A_23) | v2_struct_0(A_23) | ~l1_orders_2(A_23))), inference(resolution, [status(thm)], [c_30, c_1723])).
% 12.73/5.59  tff(c_62, plain, (v13_waybel_0('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_180])).
% 12.73/5.59  tff(c_66, plain, (~v1_xboole_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_180])).
% 12.73/5.59  tff(c_117, plain, (![A_73, B_74]: (r2_hidden(A_73, B_74) | v1_xboole_0(B_74) | ~m1_subset_1(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_58])).
% 12.73/5.59  tff(c_86, plain, (v1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~r2_hidden(k3_yellow_0('#skF_6'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_180])).
% 12.73/5.59  tff(c_114, plain, (~r2_hidden(k3_yellow_0('#skF_6'), '#skF_7')), inference(splitLeft, [status(thm)], [c_86])).
% 12.73/5.59  tff(c_124, plain, (v1_xboole_0('#skF_7') | ~m1_subset_1(k3_yellow_0('#skF_6'), '#skF_7')), inference(resolution, [status(thm)], [c_117, c_114])).
% 12.73/5.59  tff(c_128, plain, (~m1_subset_1(k3_yellow_0('#skF_6'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_66, c_124])).
% 12.73/5.59  tff(c_80, plain, (r2_hidden(k3_yellow_0('#skF_6'), '#skF_7') | ~v1_subset_1('#skF_7', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_180])).
% 12.73/5.59  tff(c_116, plain, (~v1_subset_1('#skF_7', u1_struct_0('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_114, c_80])).
% 12.73/5.59  tff(c_142, plain, (![B_80, A_81]: (v1_subset_1(B_80, A_81) | B_80=A_81 | ~m1_subset_1(B_80, k1_zfmisc_1(A_81)))), inference(cnfTransformation, [status(thm)], [f_151])).
% 12.73/5.59  tff(c_145, plain, (v1_subset_1('#skF_7', u1_struct_0('#skF_6')) | u1_struct_0('#skF_6')='#skF_7'), inference(resolution, [status(thm)], [c_60, c_142])).
% 12.73/5.59  tff(c_157, plain, (u1_struct_0('#skF_6')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_116, c_145])).
% 12.73/5.59  tff(c_104, plain, (![A_69]: (k1_yellow_0(A_69, k1_xboole_0)=k3_yellow_0(A_69) | ~l1_orders_2(A_69))), inference(cnfTransformation, [status(thm)], [f_75])).
% 12.73/5.59  tff(c_108, plain, (k1_yellow_0('#skF_6', k1_xboole_0)=k3_yellow_0('#skF_6')), inference(resolution, [status(thm)], [c_68, c_104])).
% 12.73/5.59  tff(c_129, plain, (![A_75, B_76]: (m1_subset_1(k1_yellow_0(A_75, B_76), u1_struct_0(A_75)) | ~l1_orders_2(A_75))), inference(cnfTransformation, [status(thm)], [f_79])).
% 12.73/5.59  tff(c_132, plain, (m1_subset_1(k3_yellow_0('#skF_6'), u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_108, c_129])).
% 12.73/5.59  tff(c_134, plain, (m1_subset_1(k3_yellow_0('#skF_6'), u1_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_132])).
% 12.73/5.59  tff(c_164, plain, (m1_subset_1(k3_yellow_0('#skF_6'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_157, c_134])).
% 12.73/5.59  tff(c_168, plain, $false, inference(negUnitSimplification, [status(thm)], [c_128, c_164])).
% 12.73/5.59  tff(c_170, plain, (r2_hidden(k3_yellow_0('#skF_6'), '#skF_7')), inference(splitRight, [status(thm)], [c_86])).
% 12.73/5.59  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 12.73/5.59  tff(c_20, plain, (![A_13]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 12.73/5.59  tff(c_248, plain, (![A_13, A_101]: (~v1_xboole_0(A_13) | ~r2_hidden(A_101, k1_xboole_0))), inference(resolution, [status(thm)], [c_20, c_236])).
% 12.73/5.59  tff(c_267, plain, (![A_104]: (~r2_hidden(A_104, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_248])).
% 12.73/5.59  tff(c_281, plain, (![B_2]: (r1_tarski(k1_xboole_0, B_2))), inference(resolution, [status(thm)], [c_6, c_267])).
% 12.73/5.59  tff(c_70, plain, (v1_yellow_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_180])).
% 12.73/5.59  tff(c_38, plain, (![A_31]: (r1_yellow_0(A_31, k1_xboole_0) | ~l1_orders_2(A_31) | ~v1_yellow_0(A_31) | ~v5_orders_2(A_31) | v2_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_107])).
% 12.73/5.59  tff(c_1621, plain, (![A_213, B_214, C_215]: (r1_orders_2(A_213, k1_yellow_0(A_213, B_214), k1_yellow_0(A_213, C_215)) | ~r1_yellow_0(A_213, C_215) | ~r1_yellow_0(A_213, B_214) | ~r1_tarski(B_214, C_215) | ~l1_orders_2(A_213))), inference(cnfTransformation, [status(thm)], [f_94])).
% 12.73/5.59  tff(c_1624, plain, (![C_215]: (r1_orders_2('#skF_6', k3_yellow_0('#skF_6'), k1_yellow_0('#skF_6', C_215)) | ~r1_yellow_0('#skF_6', C_215) | ~r1_yellow_0('#skF_6', k1_xboole_0) | ~r1_tarski(k1_xboole_0, C_215) | ~l1_orders_2('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_108, c_1621])).
% 12.73/5.59  tff(c_1629, plain, (![C_215]: (r1_orders_2('#skF_6', k3_yellow_0('#skF_6'), k1_yellow_0('#skF_6', C_215)) | ~r1_yellow_0('#skF_6', C_215) | ~r1_yellow_0('#skF_6', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_281, c_1624])).
% 12.73/5.59  tff(c_1979, plain, (~r1_yellow_0('#skF_6', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_1629])).
% 12.73/5.59  tff(c_1982, plain, (~l1_orders_2('#skF_6') | ~v1_yellow_0('#skF_6') | ~v5_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_38, c_1979])).
% 12.73/5.59  tff(c_1985, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_1982])).
% 12.73/5.59  tff(c_1987, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_1985])).
% 12.73/5.59  tff(c_1989, plain, (r1_yellow_0('#skF_6', k1_xboole_0)), inference(splitRight, [status(thm)], [c_1629])).
% 12.73/5.59  tff(c_187, plain, (![A_89, B_90]: (m1_subset_1(k1_yellow_0(A_89, B_90), u1_struct_0(A_89)) | ~l1_orders_2(A_89))), inference(cnfTransformation, [status(thm)], [f_79])).
% 12.73/5.59  tff(c_190, plain, (m1_subset_1(k3_yellow_0('#skF_6'), u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_108, c_187])).
% 12.73/5.59  tff(c_192, plain, (m1_subset_1(k3_yellow_0('#skF_6'), u1_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_190])).
% 12.73/5.59  tff(c_34, plain, (![A_26, B_29, C_30]: (r1_orders_2(A_26, k1_yellow_0(A_26, B_29), k1_yellow_0(A_26, C_30)) | ~r1_yellow_0(A_26, C_30) | ~r1_yellow_0(A_26, B_29) | ~r1_tarski(B_29, C_30) | ~l1_orders_2(A_26))), inference(cnfTransformation, [status(thm)], [f_94])).
% 12.73/5.59  tff(c_1972, plain, (![D_232, B_233, A_234, C_235]: (r2_hidden(D_232, B_233) | ~r1_orders_2(A_234, C_235, D_232) | ~r2_hidden(C_235, B_233) | ~m1_subset_1(D_232, u1_struct_0(A_234)) | ~m1_subset_1(C_235, u1_struct_0(A_234)) | ~v13_waybel_0(B_233, A_234) | ~m1_subset_1(B_233, k1_zfmisc_1(u1_struct_0(A_234))) | ~l1_orders_2(A_234))), inference(cnfTransformation, [status(thm)], [f_126])).
% 12.73/5.59  tff(c_5314, plain, (![A_399, C_400, B_401, B_402]: (r2_hidden(k1_yellow_0(A_399, C_400), B_401) | ~r2_hidden(k1_yellow_0(A_399, B_402), B_401) | ~m1_subset_1(k1_yellow_0(A_399, C_400), u1_struct_0(A_399)) | ~m1_subset_1(k1_yellow_0(A_399, B_402), u1_struct_0(A_399)) | ~v13_waybel_0(B_401, A_399) | ~m1_subset_1(B_401, k1_zfmisc_1(u1_struct_0(A_399))) | ~r1_yellow_0(A_399, C_400) | ~r1_yellow_0(A_399, B_402) | ~r1_tarski(B_402, C_400) | ~l1_orders_2(A_399))), inference(resolution, [status(thm)], [c_34, c_1972])).
% 12.73/5.59  tff(c_5351, plain, (![C_400, B_401]: (r2_hidden(k1_yellow_0('#skF_6', C_400), B_401) | ~r2_hidden(k3_yellow_0('#skF_6'), B_401) | ~m1_subset_1(k1_yellow_0('#skF_6', C_400), u1_struct_0('#skF_6')) | ~m1_subset_1(k1_yellow_0('#skF_6', k1_xboole_0), u1_struct_0('#skF_6')) | ~v13_waybel_0(B_401, '#skF_6') | ~m1_subset_1(B_401, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~r1_yellow_0('#skF_6', C_400) | ~r1_yellow_0('#skF_6', k1_xboole_0) | ~r1_tarski(k1_xboole_0, C_400) | ~l1_orders_2('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_108, c_5314])).
% 12.73/5.59  tff(c_9816, plain, (![C_598, B_599]: (r2_hidden(k1_yellow_0('#skF_6', C_598), B_599) | ~r2_hidden(k3_yellow_0('#skF_6'), B_599) | ~m1_subset_1(k1_yellow_0('#skF_6', C_598), u1_struct_0('#skF_6')) | ~v13_waybel_0(B_599, '#skF_6') | ~m1_subset_1(B_599, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~r1_yellow_0('#skF_6', C_598))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_281, c_1989, c_192, c_108, c_5351])).
% 12.73/5.59  tff(c_9865, plain, (![B_24, B_599]: (r2_hidden(k1_yellow_0('#skF_6', B_24), B_599) | ~r2_hidden(k3_yellow_0('#skF_6'), B_599) | ~v13_waybel_0(B_599, '#skF_6') | ~m1_subset_1(B_599, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~r1_yellow_0('#skF_6', B_24) | ~l1_orders_2('#skF_6'))), inference(resolution, [status(thm)], [c_30, c_9816])).
% 12.73/5.59  tff(c_16212, plain, (![B_815, B_816]: (r2_hidden(k1_yellow_0('#skF_6', B_815), B_816) | ~r2_hidden(k3_yellow_0('#skF_6'), B_816) | ~v13_waybel_0(B_816, '#skF_6') | ~m1_subset_1(B_816, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~r1_yellow_0('#skF_6', B_815))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_9865])).
% 12.73/5.59  tff(c_16247, plain, (![B_815]: (r2_hidden(k1_yellow_0('#skF_6', B_815), '#skF_7') | ~r2_hidden(k3_yellow_0('#skF_6'), '#skF_7') | ~v13_waybel_0('#skF_7', '#skF_6') | ~r1_yellow_0('#skF_6', B_815))), inference(resolution, [status(thm)], [c_60, c_16212])).
% 12.73/5.59  tff(c_16279, plain, (![B_817]: (r2_hidden(k1_yellow_0('#skF_6', B_817), '#skF_7') | ~r1_yellow_0('#skF_6', B_817))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_170, c_16247])).
% 12.73/5.59  tff(c_16337, plain, (![B_24]: (r2_hidden(k1_yellow_0('#skF_6', B_24), '#skF_7') | ~r1_yellow_0('#skF_6', k5_waybel_0('#skF_6', k1_yellow_0('#skF_6', B_24))) | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6') | ~l1_orders_2('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1778, c_16279])).
% 12.73/5.59  tff(c_16388, plain, (![B_24]: (r2_hidden(k1_yellow_0('#skF_6', B_24), '#skF_7') | ~r1_yellow_0('#skF_6', k5_waybel_0('#skF_6', k1_yellow_0('#skF_6', B_24))) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_76, c_74, c_72, c_16337])).
% 12.73/5.59  tff(c_17571, plain, (![B_832]: (r2_hidden(k1_yellow_0('#skF_6', B_832), '#skF_7') | ~r1_yellow_0('#skF_6', k5_waybel_0('#skF_6', k1_yellow_0('#skF_6', B_832))))), inference(negUnitSimplification, [status(thm)], [c_78, c_16388])).
% 12.73/5.59  tff(c_17647, plain, (![B_832]: (r2_hidden(k1_yellow_0('#skF_6', B_832), '#skF_7') | ~m1_subset_1(k1_yellow_0('#skF_6', B_832), u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_54, c_17571])).
% 12.73/5.59  tff(c_17678, plain, (![B_832]: (r2_hidden(k1_yellow_0('#skF_6', B_832), '#skF_7') | ~m1_subset_1(k1_yellow_0('#skF_6', B_832), u1_struct_0('#skF_6')) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_68, c_17647])).
% 12.73/5.59  tff(c_18002, plain, (![B_843]: (r2_hidden(k1_yellow_0('#skF_6', B_843), '#skF_7') | ~m1_subset_1(k1_yellow_0('#skF_6', B_843), u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_78, c_17678])).
% 12.73/5.59  tff(c_18096, plain, (![B_24]: (r2_hidden(k1_yellow_0('#skF_6', B_24), '#skF_7') | ~l1_orders_2('#skF_6'))), inference(resolution, [status(thm)], [c_30, c_18002])).
% 12.73/5.59  tff(c_18143, plain, (![B_844]: (r2_hidden(k1_yellow_0('#skF_6', B_844), '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_18096])).
% 12.73/5.59  tff(c_18187, plain, (![B_11]: (r2_hidden('#skF_3'(u1_struct_0('#skF_6'), B_11), '#skF_7') | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6') | u1_struct_0('#skF_6')=B_11 | ~m1_subset_1(B_11, k1_zfmisc_1(u1_struct_0('#skF_6'))))), inference(superposition, [status(thm), theory('equality')], [c_1766, c_18143])).
% 12.73/5.59  tff(c_18233, plain, (![B_11]: (r2_hidden('#skF_3'(u1_struct_0('#skF_6'), B_11), '#skF_7') | v2_struct_0('#skF_6') | u1_struct_0('#skF_6')=B_11 | ~m1_subset_1(B_11, k1_zfmisc_1(u1_struct_0('#skF_6'))))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_68, c_18187])).
% 12.73/5.59  tff(c_21730, plain, (![B_925]: (r2_hidden('#skF_3'(u1_struct_0('#skF_6'), B_925), '#skF_7') | u1_struct_0('#skF_6')=B_925 | ~m1_subset_1(B_925, k1_zfmisc_1(u1_struct_0('#skF_6'))))), inference(negUnitSimplification, [status(thm)], [c_78, c_18233])).
% 12.73/5.59  tff(c_16, plain, (![A_10, B_11]: (~r2_hidden('#skF_3'(A_10, B_11), B_11) | B_11=A_10 | ~m1_subset_1(B_11, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 12.73/5.59  tff(c_21743, plain, (u1_struct_0('#skF_6')='#skF_7' | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_21730, c_16])).
% 12.73/5.59  tff(c_21763, plain, (u1_struct_0('#skF_6')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_21743])).
% 12.73/5.59  tff(c_301, plain, (![A_109, C_110, B_111]: (m1_subset_1(A_109, C_110) | ~m1_subset_1(B_111, k1_zfmisc_1(C_110)) | ~r2_hidden(A_109, B_111))), inference(cnfTransformation, [status(thm)], [f_64])).
% 12.73/5.59  tff(c_310, plain, (![A_109]: (m1_subset_1(A_109, u1_struct_0('#skF_6')) | ~r2_hidden(A_109, '#skF_7'))), inference(resolution, [status(thm)], [c_60, c_301])).
% 12.73/5.59  tff(c_222, plain, (![C_95, B_96, A_97]: (r2_hidden(C_95, B_96) | ~r2_hidden(C_95, A_97) | ~r1_tarski(A_97, B_96))), inference(cnfTransformation, [status(thm)], [f_32])).
% 12.73/5.59  tff(c_849, plain, (![A_161, B_162, B_163]: (r2_hidden('#skF_1'(A_161, B_162), B_163) | ~r1_tarski(A_161, B_163) | r1_tarski(A_161, B_162))), inference(resolution, [status(thm)], [c_6, c_222])).
% 12.73/5.59  tff(c_174, plain, (![A_84, B_85]: (r2_hidden(A_84, B_85) | v1_xboole_0(B_85) | ~m1_subset_1(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_58])).
% 12.73/5.59  tff(c_432, plain, (![A_130, B_131]: (r1_tarski(A_130, B_131) | v1_xboole_0(B_131) | ~m1_subset_1('#skF_1'(A_130, B_131), B_131))), inference(resolution, [status(thm)], [c_174, c_4])).
% 12.73/5.59  tff(c_440, plain, (![A_130]: (r1_tarski(A_130, u1_struct_0('#skF_6')) | v1_xboole_0(u1_struct_0('#skF_6')) | ~r2_hidden('#skF_1'(A_130, u1_struct_0('#skF_6')), '#skF_7'))), inference(resolution, [status(thm)], [c_310, c_432])).
% 12.73/5.59  tff(c_445, plain, (![A_130]: (r1_tarski(A_130, u1_struct_0('#skF_6')) | ~r2_hidden('#skF_1'(A_130, u1_struct_0('#skF_6')), '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_283, c_440])).
% 12.73/5.59  tff(c_927, plain, (![A_168]: (~r1_tarski(A_168, '#skF_7') | r1_tarski(A_168, u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_849, c_445])).
% 12.73/5.59  tff(c_22, plain, (![A_14, B_15]: (r2_hidden(A_14, B_15) | v1_xboole_0(B_15) | ~m1_subset_1(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_58])).
% 12.73/5.59  tff(c_230, plain, (![A_14, B_96, B_15]: (r2_hidden(A_14, B_96) | ~r1_tarski(B_15, B_96) | v1_xboole_0(B_15) | ~m1_subset_1(A_14, B_15))), inference(resolution, [status(thm)], [c_22, c_222])).
% 12.73/5.59  tff(c_1517, plain, (![A_210, A_211]: (r2_hidden(A_210, u1_struct_0('#skF_6')) | v1_xboole_0(A_211) | ~m1_subset_1(A_210, A_211) | ~r1_tarski(A_211, '#skF_7'))), inference(resolution, [status(thm)], [c_927, c_230])).
% 12.73/5.59  tff(c_1537, plain, (![A_109]: (r2_hidden(A_109, u1_struct_0('#skF_6')) | v1_xboole_0(u1_struct_0('#skF_6')) | ~r1_tarski(u1_struct_0('#skF_6'), '#skF_7') | ~r2_hidden(A_109, '#skF_7'))), inference(resolution, [status(thm)], [c_310, c_1517])).
% 12.73/5.59  tff(c_1568, plain, (![A_109]: (r2_hidden(A_109, u1_struct_0('#skF_6')) | ~r1_tarski(u1_struct_0('#skF_6'), '#skF_7') | ~r2_hidden(A_109, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_283, c_1537])).
% 12.73/5.59  tff(c_1578, plain, (~r1_tarski(u1_struct_0('#skF_6'), '#skF_7')), inference(splitLeft, [status(thm)], [c_1568])).
% 12.73/5.59  tff(c_21891, plain, (~r1_tarski('#skF_7', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_21763, c_1578])).
% 12.73/5.59  tff(c_21927, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_185, c_21891])).
% 12.73/5.59  tff(c_21929, plain, (r1_tarski(u1_struct_0('#skF_6'), '#skF_7')), inference(splitRight, [status(thm)], [c_1568])).
% 12.73/5.59  tff(c_21937, plain, (![A_14]: (r2_hidden(A_14, '#skF_7') | v1_xboole_0(u1_struct_0('#skF_6')) | ~m1_subset_1(A_14, u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_21929, c_230])).
% 12.73/5.59  tff(c_22016, plain, (![A_928]: (r2_hidden(A_928, '#skF_7') | ~m1_subset_1(A_928, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_283, c_21937])).
% 12.73/5.59  tff(c_22057, plain, (![B_24]: (r2_hidden(k1_yellow_0('#skF_6', B_24), '#skF_7') | ~l1_orders_2('#skF_6'))), inference(resolution, [status(thm)], [c_30, c_22016])).
% 12.73/5.59  tff(c_22081, plain, (![B_24]: (r2_hidden(k1_yellow_0('#skF_6', B_24), '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_22057])).
% 12.73/5.59  tff(c_25962, plain, (![B_1081]: (r2_hidden('#skF_3'(u1_struct_0('#skF_6'), B_1081), '#skF_7') | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6') | u1_struct_0('#skF_6')=B_1081 | ~m1_subset_1(B_1081, k1_zfmisc_1(u1_struct_0('#skF_6'))))), inference(superposition, [status(thm), theory('equality')], [c_25897, c_22081])).
% 12.73/5.59  tff(c_26031, plain, (![B_1081]: (r2_hidden('#skF_3'(u1_struct_0('#skF_6'), B_1081), '#skF_7') | v2_struct_0('#skF_6') | u1_struct_0('#skF_6')=B_1081 | ~m1_subset_1(B_1081, k1_zfmisc_1(u1_struct_0('#skF_6'))))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_68, c_25962])).
% 12.73/5.59  tff(c_26113, plain, (![B_1084]: (r2_hidden('#skF_3'(u1_struct_0('#skF_6'), B_1084), '#skF_7') | u1_struct_0('#skF_6')=B_1084 | ~m1_subset_1(B_1084, k1_zfmisc_1(u1_struct_0('#skF_6'))))), inference(negUnitSimplification, [status(thm)], [c_78, c_26031])).
% 12.73/5.59  tff(c_26124, plain, (u1_struct_0('#skF_6')='#skF_7' | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_26113, c_16])).
% 12.73/5.59  tff(c_26138, plain, (u1_struct_0('#skF_6')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_26124])).
% 12.73/5.59  tff(c_489, plain, (![A_138]: (r1_tarski(A_138, u1_struct_0('#skF_6')) | ~r2_hidden('#skF_1'(A_138, u1_struct_0('#skF_6')), '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_283, c_440])).
% 12.73/5.59  tff(c_497, plain, (r1_tarski('#skF_7', u1_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_6, c_489])).
% 12.73/5.59  tff(c_780, plain, (![A_154, B_155, B_156]: (r2_hidden(A_154, B_155) | ~r1_tarski(B_156, B_155) | v1_xboole_0(B_156) | ~m1_subset_1(A_154, B_156))), inference(resolution, [status(thm)], [c_22, c_222])).
% 12.73/5.59  tff(c_786, plain, (![A_154]: (r2_hidden(A_154, u1_struct_0('#skF_6')) | v1_xboole_0('#skF_7') | ~m1_subset_1(A_154, '#skF_7'))), inference(resolution, [status(thm)], [c_497, c_780])).
% 12.73/5.59  tff(c_811, plain, (![A_157]: (r2_hidden(A_157, u1_struct_0('#skF_6')) | ~m1_subset_1(A_157, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_66, c_786])).
% 12.73/5.59  tff(c_986, plain, (![A_172]: (u1_struct_0('#skF_6')=A_172 | ~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(A_172)) | ~m1_subset_1('#skF_3'(A_172, u1_struct_0('#skF_6')), '#skF_7'))), inference(resolution, [status(thm)], [c_811, c_16])).
% 12.73/5.59  tff(c_991, plain, (u1_struct_0('#skF_6')='#skF_7' | ~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1('#skF_7'))), inference(resolution, [status(thm)], [c_18, c_986])).
% 12.73/5.59  tff(c_992, plain, (~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_991])).
% 12.73/5.59  tff(c_26188, plain, (~m1_subset_1('#skF_7', k1_zfmisc_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_26138, c_992])).
% 12.73/5.59  tff(c_26220, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_87, c_26188])).
% 12.73/5.59  tff(c_26221, plain, (u1_struct_0('#skF_6')='#skF_7'), inference(splitRight, [status(thm)], [c_991])).
% 12.73/5.59  tff(c_169, plain, (v1_subset_1('#skF_7', u1_struct_0('#skF_6'))), inference(splitRight, [status(thm)], [c_86])).
% 12.73/5.59  tff(c_26242, plain, (v1_subset_1('#skF_7', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_26221, c_169])).
% 12.73/5.59  tff(c_26248, plain, $false, inference(negUnitSimplification, [status(thm)], [c_89, c_26242])).
% 12.73/5.59  tff(c_26249, plain, (![A_101]: (~r2_hidden(A_101, '#skF_7'))), inference(splitRight, [status(thm)], [c_245])).
% 12.73/5.59  tff(c_26252, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26249, c_170])).
% 12.73/5.59  tff(c_26253, plain, (![A_13]: (~v1_xboole_0(A_13))), inference(splitRight, [status(thm)], [c_248])).
% 12.73/5.59  tff(c_12, plain, (![A_8]: (v1_xboole_0('#skF_2'(A_8)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 12.73/5.59  tff(c_26256, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26253, c_12])).
% 12.73/5.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.73/5.59  
% 12.73/5.59  Inference rules
% 12.73/5.59  ----------------------
% 12.73/5.59  #Ref     : 0
% 12.73/5.59  #Sup     : 5786
% 12.73/5.59  #Fact    : 0
% 12.73/5.59  #Define  : 0
% 12.73/5.59  #Split   : 55
% 12.73/5.59  #Chain   : 0
% 12.73/5.59  #Close   : 0
% 12.73/5.59  
% 12.73/5.59  Ordering : KBO
% 12.73/5.59  
% 12.73/5.59  Simplification rules
% 12.73/5.59  ----------------------
% 12.73/5.59  #Subsume      : 2264
% 12.73/5.59  #Demod        : 5837
% 12.73/5.59  #Tautology    : 1221
% 12.73/5.59  #SimpNegUnit  : 1032
% 12.73/5.59  #BackRed      : 275
% 12.73/5.59  
% 12.73/5.59  #Partial instantiations: 0
% 12.73/5.59  #Strategies tried      : 1
% 12.73/5.59  
% 12.73/5.59  Timing (in seconds)
% 12.73/5.59  ----------------------
% 12.73/5.60  Preprocessing        : 0.37
% 12.73/5.60  Parsing              : 0.19
% 12.73/5.60  CNF conversion       : 0.03
% 12.73/5.60  Main loop            : 4.44
% 12.73/5.60  Inferencing          : 1.07
% 12.73/5.60  Reduction            : 1.55
% 12.73/5.60  Demodulation         : 1.10
% 12.73/5.60  BG Simplification    : 0.10
% 12.73/5.60  Subsumption          : 1.46
% 12.73/5.60  Abstraction          : 0.15
% 12.73/5.60  MUC search           : 0.00
% 12.73/5.60  Cooper               : 0.00
% 12.73/5.60  Total                : 4.87
% 12.73/5.60  Index Insertion      : 0.00
% 12.73/5.60  Index Deletion       : 0.00
% 12.73/5.60  Index Matching       : 0.00
% 12.73/5.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
