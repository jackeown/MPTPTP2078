%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:00 EST 2020

% Result     : Theorem 28.29s
% Output     : CNFRefutation 28.34s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 296 expanded)
%              Number of leaves         :   45 ( 123 expanded)
%              Depth                    :   27
%              Number of atoms          :  337 (1115 expanded)
%              Number of equality atoms :   23 (  53 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_yellow_0 > r2_hidden > r1_yellow_0 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > l1_orders_2 > k5_waybel_0 > k1_yellow_0 > #nlpp > u1_struct_0 > k3_yellow_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v13_waybel_0,type,(
    v13_waybel_0: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(v1_yellow_0,type,(
    v1_yellow_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_145,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_174,negated_conjecture,(
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

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( ! [C] :
            ( m1_subset_1(C,A)
           => r2_hidden(C,B) )
       => A = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_subset_1)).

tff(f_138,axiom,(
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

tff(f_73,axiom,(
    ! [A,B] :
      ( l1_orders_2(A)
     => m1_subset_1(k1_yellow_0(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_69,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => k3_yellow_0(A) = k1_yellow_0(A,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_yellow_0)).

tff(f_101,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v5_orders_2(A)
        & v1_yellow_0(A)
        & l1_orders_2(A) )
     => ( r1_yellow_0(A,k1_xboole_0)
        & r2_yellow_0(A,u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_yellow_0)).

tff(f_88,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( ( r1_tarski(B,C)
            & r1_yellow_0(A,B)
            & r1_yellow_0(A,C) )
         => r1_orders_2(A,k1_yellow_0(A,B),k1_yellow_0(A,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_yellow_0)).

tff(f_120,axiom,(
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

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_169,plain,(
    ! [A_87,B_88] :
      ( ~ r2_hidden('#skF_1'(A_87,B_88),B_88)
      | r1_tarski(A_87,B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_178,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_169])).

tff(c_18,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,k1_zfmisc_1(B_12))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_93,plain,(
    ! [B_63] :
      ( ~ v1_subset_1(B_63,B_63)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(B_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_98,plain,(
    ! [B_12] :
      ( ~ v1_subset_1(B_12,B_12)
      | ~ r1_tarski(B_12,B_12) ) ),
    inference(resolution,[status(thm)],[c_18,c_93])).

tff(c_181,plain,(
    ! [B_12] : ~ v1_subset_1(B_12,B_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_98])).

tff(c_56,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_72,plain,(
    v3_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_70,plain,(
    v4_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_68,plain,(
    v5_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_64,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1('#skF_2'(A_6,B_7),A_6)
      | B_7 = A_6
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_52740,plain,(
    ! [A_1679,B_1680] :
      ( k1_yellow_0(A_1679,k5_waybel_0(A_1679,B_1680)) = B_1680
      | ~ m1_subset_1(B_1680,u1_struct_0(A_1679))
      | ~ l1_orders_2(A_1679)
      | ~ v5_orders_2(A_1679)
      | ~ v4_orders_2(A_1679)
      | ~ v3_orders_2(A_1679)
      | v2_struct_0(A_1679) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_52793,plain,(
    ! [A_1679,B_7] :
      ( k1_yellow_0(A_1679,k5_waybel_0(A_1679,'#skF_2'(u1_struct_0(A_1679),B_7))) = '#skF_2'(u1_struct_0(A_1679),B_7)
      | ~ l1_orders_2(A_1679)
      | ~ v5_orders_2(A_1679)
      | ~ v4_orders_2(A_1679)
      | ~ v3_orders_2(A_1679)
      | v2_struct_0(A_1679)
      | u1_struct_0(A_1679) = B_7
      | ~ m1_subset_1(B_7,k1_zfmisc_1(u1_struct_0(A_1679))) ) ),
    inference(resolution,[status(thm)],[c_12,c_52740])).

tff(c_26,plain,(
    ! [A_20,B_21] :
      ( m1_subset_1(k1_yellow_0(A_20,B_21),u1_struct_0(A_20))
      | ~ l1_orders_2(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_192,plain,(
    ! [C_93,B_94,A_95] :
      ( ~ v1_xboole_0(C_93)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(C_93))
      | ~ r2_hidden(A_95,B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_214,plain,(
    ! [B_100,A_101,A_102] :
      ( ~ v1_xboole_0(B_100)
      | ~ r2_hidden(A_101,A_102)
      | ~ r1_tarski(A_102,B_100) ) ),
    inference(resolution,[status(thm)],[c_18,c_192])).

tff(c_237,plain,(
    ! [B_104,A_105,B_106] :
      ( ~ v1_xboole_0(B_104)
      | ~ r1_tarski(A_105,B_104)
      | r1_tarski(A_105,B_106) ) ),
    inference(resolution,[status(thm)],[c_6,c_214])).

tff(c_242,plain,(
    ! [A_1,B_106] :
      ( ~ v1_xboole_0(A_1)
      | r1_tarski(A_1,B_106) ) ),
    inference(resolution,[status(thm)],[c_178,c_237])).

tff(c_50,plain,(
    ! [A_54,B_56] :
      ( r1_yellow_0(A_54,k5_waybel_0(A_54,B_56))
      | ~ m1_subset_1(B_56,u1_struct_0(A_54))
      | ~ l1_orders_2(A_54)
      | ~ v5_orders_2(A_54)
      | ~ v4_orders_2(A_54)
      | ~ v3_orders_2(A_54)
      | v2_struct_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_52803,plain,(
    ! [A_20,B_21] :
      ( k1_yellow_0(A_20,k5_waybel_0(A_20,k1_yellow_0(A_20,B_21))) = k1_yellow_0(A_20,B_21)
      | ~ v5_orders_2(A_20)
      | ~ v4_orders_2(A_20)
      | ~ v3_orders_2(A_20)
      | v2_struct_0(A_20)
      | ~ l1_orders_2(A_20) ) ),
    inference(resolution,[status(thm)],[c_26,c_52740])).

tff(c_58,plain,(
    v13_waybel_0('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_62,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( r2_hidden(A_9,B_10)
      | v1_xboole_0(B_10)
      | ~ m1_subset_1(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_76,plain,
    ( r2_hidden(k3_yellow_0('#skF_5'),'#skF_6')
    | ~ v1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_110,plain,(
    ~ v1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_82,plain,
    ( v1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ r2_hidden(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_118,plain,(
    ~ r2_hidden(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_82])).

tff(c_121,plain,
    ( v1_xboole_0('#skF_6')
    | ~ m1_subset_1(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_14,c_118])).

tff(c_124,plain,(
    ~ m1_subset_1(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_121])).

tff(c_148,plain,(
    ! [B_81,A_82] :
      ( v1_subset_1(B_81,A_82)
      | B_81 = A_82
      | ~ m1_subset_1(B_81,k1_zfmisc_1(A_82)) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_154,plain,
    ( v1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | u1_struct_0('#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_56,c_148])).

tff(c_158,plain,(
    u1_struct_0('#skF_5') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_154])).

tff(c_84,plain,(
    ! [A_62] :
      ( k1_yellow_0(A_62,k1_xboole_0) = k3_yellow_0(A_62)
      | ~ l1_orders_2(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_88,plain,(
    k1_yellow_0('#skF_5',k1_xboole_0) = k3_yellow_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_84])).

tff(c_112,plain,(
    ! [A_70,B_71] :
      ( m1_subset_1(k1_yellow_0(A_70,B_71),u1_struct_0(A_70))
      | ~ l1_orders_2(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_115,plain,
    ( m1_subset_1(k3_yellow_0('#skF_5'),u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_112])).

tff(c_117,plain,(
    m1_subset_1(k3_yellow_0('#skF_5'),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_115])).

tff(c_159,plain,(
    m1_subset_1(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_117])).

tff(c_164,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_159])).

tff(c_165,plain,(
    r2_hidden(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_66,plain,(
    v1_yellow_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_34,plain,(
    ! [A_28] :
      ( r1_yellow_0(A_28,k1_xboole_0)
      | ~ l1_orders_2(A_28)
      | ~ v1_yellow_0(A_28)
      | ~ v5_orders_2(A_28)
      | v2_struct_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_52479,plain,(
    ! [A_1649,B_1650,C_1651] :
      ( r1_orders_2(A_1649,k1_yellow_0(A_1649,B_1650),k1_yellow_0(A_1649,C_1651))
      | ~ r1_yellow_0(A_1649,C_1651)
      | ~ r1_yellow_0(A_1649,B_1650)
      | ~ r1_tarski(B_1650,C_1651)
      | ~ l1_orders_2(A_1649) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_52485,plain,(
    ! [B_1650] :
      ( r1_orders_2('#skF_5',k1_yellow_0('#skF_5',B_1650),k3_yellow_0('#skF_5'))
      | ~ r1_yellow_0('#skF_5',k1_xboole_0)
      | ~ r1_yellow_0('#skF_5',B_1650)
      | ~ r1_tarski(B_1650,k1_xboole_0)
      | ~ l1_orders_2('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_52479])).

tff(c_52489,plain,(
    ! [B_1650] :
      ( r1_orders_2('#skF_5',k1_yellow_0('#skF_5',B_1650),k3_yellow_0('#skF_5'))
      | ~ r1_yellow_0('#skF_5',k1_xboole_0)
      | ~ r1_yellow_0('#skF_5',B_1650)
      | ~ r1_tarski(B_1650,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_52485])).

tff(c_54652,plain,(
    ~ r1_yellow_0('#skF_5',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_52489])).

tff(c_54656,plain,
    ( ~ l1_orders_2('#skF_5')
    | ~ v1_yellow_0('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_54652])).

tff(c_54659,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_54656])).

tff(c_54661,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_54659])).

tff(c_54663,plain,(
    r1_yellow_0('#skF_5',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_52489])).

tff(c_186,plain,(
    ! [A_91,B_92] :
      ( m1_subset_1(k1_yellow_0(A_91,B_92),u1_struct_0(A_91))
      | ~ l1_orders_2(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_189,plain,
    ( m1_subset_1(k3_yellow_0('#skF_5'),u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_186])).

tff(c_191,plain,(
    m1_subset_1(k3_yellow_0('#skF_5'),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_189])).

tff(c_30,plain,(
    ! [A_23,B_26,C_27] :
      ( r1_orders_2(A_23,k1_yellow_0(A_23,B_26),k1_yellow_0(A_23,C_27))
      | ~ r1_yellow_0(A_23,C_27)
      | ~ r1_yellow_0(A_23,B_26)
      | ~ r1_tarski(B_26,C_27)
      | ~ l1_orders_2(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_53084,plain,(
    ! [D_1693,B_1694,A_1695,C_1696] :
      ( r2_hidden(D_1693,B_1694)
      | ~ r1_orders_2(A_1695,C_1696,D_1693)
      | ~ r2_hidden(C_1696,B_1694)
      | ~ m1_subset_1(D_1693,u1_struct_0(A_1695))
      | ~ m1_subset_1(C_1696,u1_struct_0(A_1695))
      | ~ v13_waybel_0(B_1694,A_1695)
      | ~ m1_subset_1(B_1694,k1_zfmisc_1(u1_struct_0(A_1695)))
      | ~ l1_orders_2(A_1695) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_56561,plain,(
    ! [A_1838,C_1839,B_1840,B_1841] :
      ( r2_hidden(k1_yellow_0(A_1838,C_1839),B_1840)
      | ~ r2_hidden(k1_yellow_0(A_1838,B_1841),B_1840)
      | ~ m1_subset_1(k1_yellow_0(A_1838,C_1839),u1_struct_0(A_1838))
      | ~ m1_subset_1(k1_yellow_0(A_1838,B_1841),u1_struct_0(A_1838))
      | ~ v13_waybel_0(B_1840,A_1838)
      | ~ m1_subset_1(B_1840,k1_zfmisc_1(u1_struct_0(A_1838)))
      | ~ r1_yellow_0(A_1838,C_1839)
      | ~ r1_yellow_0(A_1838,B_1841)
      | ~ r1_tarski(B_1841,C_1839)
      | ~ l1_orders_2(A_1838) ) ),
    inference(resolution,[status(thm)],[c_30,c_53084])).

tff(c_56597,plain,(
    ! [C_1839,B_1840] :
      ( r2_hidden(k1_yellow_0('#skF_5',C_1839),B_1840)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_1840)
      | ~ m1_subset_1(k1_yellow_0('#skF_5',C_1839),u1_struct_0('#skF_5'))
      | ~ m1_subset_1(k1_yellow_0('#skF_5',k1_xboole_0),u1_struct_0('#skF_5'))
      | ~ v13_waybel_0(B_1840,'#skF_5')
      | ~ m1_subset_1(B_1840,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_yellow_0('#skF_5',C_1839)
      | ~ r1_yellow_0('#skF_5',k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,C_1839)
      | ~ l1_orders_2('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_56561])).

tff(c_62231,plain,(
    ! [C_2069,B_2070] :
      ( r2_hidden(k1_yellow_0('#skF_5',C_2069),B_2070)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_2070)
      | ~ m1_subset_1(k1_yellow_0('#skF_5',C_2069),u1_struct_0('#skF_5'))
      | ~ v13_waybel_0(B_2070,'#skF_5')
      | ~ m1_subset_1(B_2070,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_yellow_0('#skF_5',C_2069)
      | ~ r1_tarski(k1_xboole_0,C_2069) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_54663,c_191,c_88,c_56597])).

tff(c_62281,plain,(
    ! [B_21,B_2070] :
      ( r2_hidden(k1_yellow_0('#skF_5',B_21),B_2070)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_2070)
      | ~ v13_waybel_0(B_2070,'#skF_5')
      | ~ m1_subset_1(B_2070,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_yellow_0('#skF_5',B_21)
      | ~ r1_tarski(k1_xboole_0,B_21)
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_26,c_62231])).

tff(c_76058,plain,(
    ! [B_2546,B_2547] :
      ( r2_hidden(k1_yellow_0('#skF_5',B_2546),B_2547)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_2547)
      | ~ v13_waybel_0(B_2547,'#skF_5')
      | ~ m1_subset_1(B_2547,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_yellow_0('#skF_5',B_2546)
      | ~ r1_tarski(k1_xboole_0,B_2546) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62281])).

tff(c_76107,plain,(
    ! [B_2546] :
      ( r2_hidden(k1_yellow_0('#skF_5',B_2546),'#skF_6')
      | ~ r2_hidden(k3_yellow_0('#skF_5'),'#skF_6')
      | ~ v13_waybel_0('#skF_6','#skF_5')
      | ~ r1_yellow_0('#skF_5',B_2546)
      | ~ r1_tarski(k1_xboole_0,B_2546) ) ),
    inference(resolution,[status(thm)],[c_56,c_76058])).

tff(c_76128,plain,(
    ! [B_2548] :
      ( r2_hidden(k1_yellow_0('#skF_5',B_2548),'#skF_6')
      | ~ r1_yellow_0('#skF_5',B_2548)
      | ~ r1_tarski(k1_xboole_0,B_2548) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_165,c_76107])).

tff(c_76184,plain,(
    ! [B_21] :
      ( r2_hidden(k1_yellow_0('#skF_5',B_21),'#skF_6')
      | ~ r1_yellow_0('#skF_5',k5_waybel_0('#skF_5',k1_yellow_0('#skF_5',B_21)))
      | ~ r1_tarski(k1_xboole_0,k5_waybel_0('#skF_5',k1_yellow_0('#skF_5',B_21)))
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ l1_orders_2('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52803,c_76128])).

tff(c_76249,plain,(
    ! [B_21] :
      ( r2_hidden(k1_yellow_0('#skF_5',B_21),'#skF_6')
      | ~ r1_yellow_0('#skF_5',k5_waybel_0('#skF_5',k1_yellow_0('#skF_5',B_21)))
      | ~ r1_tarski(k1_xboole_0,k5_waybel_0('#skF_5',k1_yellow_0('#skF_5',B_21)))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_72,c_70,c_68,c_76184])).

tff(c_76507,plain,(
    ! [B_2552] :
      ( r2_hidden(k1_yellow_0('#skF_5',B_2552),'#skF_6')
      | ~ r1_yellow_0('#skF_5',k5_waybel_0('#skF_5',k1_yellow_0('#skF_5',B_2552)))
      | ~ r1_tarski(k1_xboole_0,k5_waybel_0('#skF_5',k1_yellow_0('#skF_5',B_2552))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_76249])).

tff(c_76584,plain,(
    ! [B_2552] :
      ( r2_hidden(k1_yellow_0('#skF_5',B_2552),'#skF_6')
      | ~ r1_tarski(k1_xboole_0,k5_waybel_0('#skF_5',k1_yellow_0('#skF_5',B_2552)))
      | ~ m1_subset_1(k1_yellow_0('#skF_5',B_2552),u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_50,c_76507])).

tff(c_76618,plain,(
    ! [B_2552] :
      ( r2_hidden(k1_yellow_0('#skF_5',B_2552),'#skF_6')
      | ~ r1_tarski(k1_xboole_0,k5_waybel_0('#skF_5',k1_yellow_0('#skF_5',B_2552)))
      | ~ m1_subset_1(k1_yellow_0('#skF_5',B_2552),u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_64,c_76584])).

tff(c_77474,plain,(
    ! [B_2563] :
      ( r2_hidden(k1_yellow_0('#skF_5',B_2563),'#skF_6')
      | ~ r1_tarski(k1_xboole_0,k5_waybel_0('#skF_5',k1_yellow_0('#skF_5',B_2563)))
      | ~ m1_subset_1(k1_yellow_0('#skF_5',B_2563),u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_76618])).

tff(c_77551,plain,(
    ! [B_2563] :
      ( r2_hidden(k1_yellow_0('#skF_5',B_2563),'#skF_6')
      | ~ m1_subset_1(k1_yellow_0('#skF_5',B_2563),u1_struct_0('#skF_5'))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_242,c_77474])).

tff(c_77814,plain,(
    ! [B_2573] :
      ( r2_hidden(k1_yellow_0('#skF_5',B_2573),'#skF_6')
      | ~ m1_subset_1(k1_yellow_0('#skF_5',B_2573),u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_77551])).

tff(c_77909,plain,(
    ! [B_21] :
      ( r2_hidden(k1_yellow_0('#skF_5',B_21),'#skF_6')
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_26,c_77814])).

tff(c_77959,plain,(
    ! [B_2574] : r2_hidden(k1_yellow_0('#skF_5',B_2574),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_77909])).

tff(c_78006,plain,(
    ! [B_7] :
      ( r2_hidden('#skF_2'(u1_struct_0('#skF_5'),B_7),'#skF_6')
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5')
      | u1_struct_0('#skF_5') = B_7
      | ~ m1_subset_1(B_7,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52793,c_77959])).

tff(c_78062,plain,(
    ! [B_7] :
      ( r2_hidden('#skF_2'(u1_struct_0('#skF_5'),B_7),'#skF_6')
      | v2_struct_0('#skF_5')
      | u1_struct_0('#skF_5') = B_7
      | ~ m1_subset_1(B_7,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_64,c_78006])).

tff(c_83477,plain,(
    ! [B_2688] :
      ( r2_hidden('#skF_2'(u1_struct_0('#skF_5'),B_2688),'#skF_6')
      | u1_struct_0('#skF_5') = B_2688
      | ~ m1_subset_1(B_2688,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_78062])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( ~ r2_hidden('#skF_2'(A_6,B_7),B_7)
      | B_7 = A_6
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_83496,plain,
    ( u1_struct_0('#skF_5') = '#skF_6'
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_83477,c_10])).

tff(c_83519,plain,(
    u1_struct_0('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_83496])).

tff(c_99,plain,(
    ! [A_64,B_65] :
      ( r1_tarski(A_64,B_65)
      | ~ m1_subset_1(A_64,k1_zfmisc_1(B_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_107,plain,(
    r1_tarski('#skF_6',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_56,c_99])).

tff(c_200,plain,(
    ! [C_96,B_97,A_98] :
      ( r2_hidden(C_96,B_97)
      | ~ r2_hidden(C_96,A_98)
      | ~ r1_tarski(A_98,B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_489,plain,(
    ! [A_146,B_147,B_148] :
      ( r2_hidden(A_146,B_147)
      | ~ r1_tarski(B_148,B_147)
      | v1_xboole_0(B_148)
      | ~ m1_subset_1(A_146,B_148) ) ),
    inference(resolution,[status(thm)],[c_14,c_200])).

tff(c_497,plain,(
    ! [A_146] :
      ( r2_hidden(A_146,u1_struct_0('#skF_5'))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(A_146,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_107,c_489])).

tff(c_504,plain,(
    ! [A_149] :
      ( r2_hidden(A_149,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(A_149,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_497])).

tff(c_682,plain,(
    ! [A_170] :
      ( u1_struct_0('#skF_5') = A_170
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_170))
      | ~ m1_subset_1('#skF_2'(A_170,u1_struct_0('#skF_5')),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_504,c_10])).

tff(c_687,plain,
    ( u1_struct_0('#skF_5') = '#skF_6'
    | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_12,c_682])).

tff(c_688,plain,(
    ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_687])).

tff(c_692,plain,(
    ~ r1_tarski(u1_struct_0('#skF_5'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_18,c_688])).

tff(c_83690,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_83519,c_692])).

tff(c_83717,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_83690])).

tff(c_83718,plain,(
    u1_struct_0('#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_687])).

tff(c_166,plain,(
    v1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_83736,plain,(
    v1_subset_1('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_83718,c_166])).

tff(c_83741,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_181,c_83736])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n016.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:36:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 28.29/18.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 28.34/18.18  
% 28.34/18.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 28.34/18.18  %$ r1_orders_2 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_yellow_0 > r2_hidden > r1_yellow_0 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > l1_orders_2 > k5_waybel_0 > k1_yellow_0 > #nlpp > u1_struct_0 > k3_yellow_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4
% 28.34/18.18  
% 28.34/18.18  %Foreground sorts:
% 28.34/18.18  
% 28.34/18.18  
% 28.34/18.18  %Background operators:
% 28.34/18.18  
% 28.34/18.18  
% 28.34/18.18  %Foreground operators:
% 28.34/18.18  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 28.34/18.18  tff(k1_yellow_0, type, k1_yellow_0: ($i * $i) > $i).
% 28.34/18.18  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 28.34/18.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 28.34/18.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 28.34/18.18  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 28.34/18.18  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 28.34/18.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 28.34/18.18  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 28.34/18.18  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 28.34/18.18  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 28.34/18.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 28.34/18.18  tff('#skF_5', type, '#skF_5': $i).
% 28.34/18.18  tff('#skF_6', type, '#skF_6': $i).
% 28.34/18.18  tff(r2_yellow_0, type, r2_yellow_0: ($i * $i) > $o).
% 28.34/18.18  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 28.34/18.18  tff(r1_yellow_0, type, r1_yellow_0: ($i * $i) > $o).
% 28.34/18.18  tff(k5_waybel_0, type, k5_waybel_0: ($i * $i) > $i).
% 28.34/18.18  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 28.34/18.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 28.34/18.18  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 28.34/18.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 28.34/18.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 28.34/18.18  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 28.34/18.18  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 28.34/18.18  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 28.34/18.18  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 28.34/18.18  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 28.34/18.18  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 28.34/18.18  tff(v1_yellow_0, type, v1_yellow_0: $i > $o).
% 28.34/18.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 28.34/18.18  
% 28.34/18.20  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 28.34/18.20  tff(f_52, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 28.34/18.20  tff(f_145, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 28.34/18.20  tff(f_174, negated_conjecture, ~(![A]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, A)) & v13_waybel_0(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_subset_1(B, u1_struct_0(A)) <=> ~r2_hidden(k3_yellow_0(A), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_waybel_7)).
% 28.34/18.20  tff(f_42, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ((![C]: (m1_subset_1(C, A) => r2_hidden(C, B))) => (A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_subset_1)).
% 28.34/18.20  tff(f_138, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (r1_yellow_0(A, k5_waybel_0(A, B)) & (k1_yellow_0(A, k5_waybel_0(A, B)) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_waybel_0)).
% 28.34/18.20  tff(f_73, axiom, (![A, B]: (l1_orders_2(A) => m1_subset_1(k1_yellow_0(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_yellow_0)).
% 28.34/18.20  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 28.34/18.20  tff(f_65, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 28.34/18.20  tff(f_48, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 28.34/18.20  tff(f_69, axiom, (![A]: (l1_orders_2(A) => (k3_yellow_0(A) = k1_yellow_0(A, k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_yellow_0)).
% 28.34/18.20  tff(f_101, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (r1_yellow_0(A, k1_xboole_0) & r2_yellow_0(A, u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_yellow_0)).
% 28.34/18.20  tff(f_88, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (((r1_tarski(B, C) & r1_yellow_0(A, B)) & r1_yellow_0(A, C)) => r1_orders_2(A, k1_yellow_0(A, B), k1_yellow_0(A, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_yellow_0)).
% 28.34/18.20  tff(f_120, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v13_waybel_0(B, A) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r2_hidden(C, B) & r1_orders_2(A, C, D)) => r2_hidden(D, B))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d20_waybel_0)).
% 28.34/18.20  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 28.34/18.20  tff(c_169, plain, (![A_87, B_88]: (~r2_hidden('#skF_1'(A_87, B_88), B_88) | r1_tarski(A_87, B_88))), inference(cnfTransformation, [status(thm)], [f_32])).
% 28.34/18.20  tff(c_178, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_169])).
% 28.34/18.20  tff(c_18, plain, (![A_11, B_12]: (m1_subset_1(A_11, k1_zfmisc_1(B_12)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_52])).
% 28.34/18.20  tff(c_93, plain, (![B_63]: (~v1_subset_1(B_63, B_63) | ~m1_subset_1(B_63, k1_zfmisc_1(B_63)))), inference(cnfTransformation, [status(thm)], [f_145])).
% 28.34/18.20  tff(c_98, plain, (![B_12]: (~v1_subset_1(B_12, B_12) | ~r1_tarski(B_12, B_12))), inference(resolution, [status(thm)], [c_18, c_93])).
% 28.34/18.20  tff(c_181, plain, (![B_12]: (~v1_subset_1(B_12, B_12))), inference(demodulation, [status(thm), theory('equality')], [c_178, c_98])).
% 28.34/18.20  tff(c_56, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_174])).
% 28.34/18.20  tff(c_74, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_174])).
% 28.34/18.20  tff(c_72, plain, (v3_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_174])).
% 28.34/18.20  tff(c_70, plain, (v4_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_174])).
% 28.34/18.20  tff(c_68, plain, (v5_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_174])).
% 28.34/18.20  tff(c_64, plain, (l1_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_174])).
% 28.34/18.20  tff(c_12, plain, (![A_6, B_7]: (m1_subset_1('#skF_2'(A_6, B_7), A_6) | B_7=A_6 | ~m1_subset_1(B_7, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 28.34/18.20  tff(c_52740, plain, (![A_1679, B_1680]: (k1_yellow_0(A_1679, k5_waybel_0(A_1679, B_1680))=B_1680 | ~m1_subset_1(B_1680, u1_struct_0(A_1679)) | ~l1_orders_2(A_1679) | ~v5_orders_2(A_1679) | ~v4_orders_2(A_1679) | ~v3_orders_2(A_1679) | v2_struct_0(A_1679))), inference(cnfTransformation, [status(thm)], [f_138])).
% 28.34/18.20  tff(c_52793, plain, (![A_1679, B_7]: (k1_yellow_0(A_1679, k5_waybel_0(A_1679, '#skF_2'(u1_struct_0(A_1679), B_7)))='#skF_2'(u1_struct_0(A_1679), B_7) | ~l1_orders_2(A_1679) | ~v5_orders_2(A_1679) | ~v4_orders_2(A_1679) | ~v3_orders_2(A_1679) | v2_struct_0(A_1679) | u1_struct_0(A_1679)=B_7 | ~m1_subset_1(B_7, k1_zfmisc_1(u1_struct_0(A_1679))))), inference(resolution, [status(thm)], [c_12, c_52740])).
% 28.34/18.20  tff(c_26, plain, (![A_20, B_21]: (m1_subset_1(k1_yellow_0(A_20, B_21), u1_struct_0(A_20)) | ~l1_orders_2(A_20))), inference(cnfTransformation, [status(thm)], [f_73])).
% 28.34/18.20  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 28.34/18.20  tff(c_192, plain, (![C_93, B_94, A_95]: (~v1_xboole_0(C_93) | ~m1_subset_1(B_94, k1_zfmisc_1(C_93)) | ~r2_hidden(A_95, B_94))), inference(cnfTransformation, [status(thm)], [f_65])).
% 28.34/18.20  tff(c_214, plain, (![B_100, A_101, A_102]: (~v1_xboole_0(B_100) | ~r2_hidden(A_101, A_102) | ~r1_tarski(A_102, B_100))), inference(resolution, [status(thm)], [c_18, c_192])).
% 28.34/18.20  tff(c_237, plain, (![B_104, A_105, B_106]: (~v1_xboole_0(B_104) | ~r1_tarski(A_105, B_104) | r1_tarski(A_105, B_106))), inference(resolution, [status(thm)], [c_6, c_214])).
% 28.34/18.20  tff(c_242, plain, (![A_1, B_106]: (~v1_xboole_0(A_1) | r1_tarski(A_1, B_106))), inference(resolution, [status(thm)], [c_178, c_237])).
% 28.34/18.20  tff(c_50, plain, (![A_54, B_56]: (r1_yellow_0(A_54, k5_waybel_0(A_54, B_56)) | ~m1_subset_1(B_56, u1_struct_0(A_54)) | ~l1_orders_2(A_54) | ~v5_orders_2(A_54) | ~v4_orders_2(A_54) | ~v3_orders_2(A_54) | v2_struct_0(A_54))), inference(cnfTransformation, [status(thm)], [f_138])).
% 28.34/18.20  tff(c_52803, plain, (![A_20, B_21]: (k1_yellow_0(A_20, k5_waybel_0(A_20, k1_yellow_0(A_20, B_21)))=k1_yellow_0(A_20, B_21) | ~v5_orders_2(A_20) | ~v4_orders_2(A_20) | ~v3_orders_2(A_20) | v2_struct_0(A_20) | ~l1_orders_2(A_20))), inference(resolution, [status(thm)], [c_26, c_52740])).
% 28.34/18.20  tff(c_58, plain, (v13_waybel_0('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_174])).
% 28.34/18.20  tff(c_62, plain, (~v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_174])).
% 28.34/18.20  tff(c_14, plain, (![A_9, B_10]: (r2_hidden(A_9, B_10) | v1_xboole_0(B_10) | ~m1_subset_1(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 28.34/18.20  tff(c_76, plain, (r2_hidden(k3_yellow_0('#skF_5'), '#skF_6') | ~v1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_174])).
% 28.34/18.20  tff(c_110, plain, (~v1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_76])).
% 28.34/18.20  tff(c_82, plain, (v1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~r2_hidden(k3_yellow_0('#skF_5'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_174])).
% 28.34/18.20  tff(c_118, plain, (~r2_hidden(k3_yellow_0('#skF_5'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_110, c_82])).
% 28.34/18.20  tff(c_121, plain, (v1_xboole_0('#skF_6') | ~m1_subset_1(k3_yellow_0('#skF_5'), '#skF_6')), inference(resolution, [status(thm)], [c_14, c_118])).
% 28.34/18.20  tff(c_124, plain, (~m1_subset_1(k3_yellow_0('#skF_5'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_62, c_121])).
% 28.34/18.20  tff(c_148, plain, (![B_81, A_82]: (v1_subset_1(B_81, A_82) | B_81=A_82 | ~m1_subset_1(B_81, k1_zfmisc_1(A_82)))), inference(cnfTransformation, [status(thm)], [f_145])).
% 28.34/18.20  tff(c_154, plain, (v1_subset_1('#skF_6', u1_struct_0('#skF_5')) | u1_struct_0('#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_56, c_148])).
% 28.34/18.20  tff(c_158, plain, (u1_struct_0('#skF_5')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_110, c_154])).
% 28.34/18.20  tff(c_84, plain, (![A_62]: (k1_yellow_0(A_62, k1_xboole_0)=k3_yellow_0(A_62) | ~l1_orders_2(A_62))), inference(cnfTransformation, [status(thm)], [f_69])).
% 28.34/18.20  tff(c_88, plain, (k1_yellow_0('#skF_5', k1_xboole_0)=k3_yellow_0('#skF_5')), inference(resolution, [status(thm)], [c_64, c_84])).
% 28.34/18.20  tff(c_112, plain, (![A_70, B_71]: (m1_subset_1(k1_yellow_0(A_70, B_71), u1_struct_0(A_70)) | ~l1_orders_2(A_70))), inference(cnfTransformation, [status(thm)], [f_73])).
% 28.34/18.20  tff(c_115, plain, (m1_subset_1(k3_yellow_0('#skF_5'), u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_88, c_112])).
% 28.34/18.20  tff(c_117, plain, (m1_subset_1(k3_yellow_0('#skF_5'), u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_115])).
% 28.34/18.20  tff(c_159, plain, (m1_subset_1(k3_yellow_0('#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_158, c_117])).
% 28.34/18.20  tff(c_164, plain, $false, inference(negUnitSimplification, [status(thm)], [c_124, c_159])).
% 28.34/18.20  tff(c_165, plain, (r2_hidden(k3_yellow_0('#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_76])).
% 28.34/18.20  tff(c_66, plain, (v1_yellow_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_174])).
% 28.34/18.20  tff(c_34, plain, (![A_28]: (r1_yellow_0(A_28, k1_xboole_0) | ~l1_orders_2(A_28) | ~v1_yellow_0(A_28) | ~v5_orders_2(A_28) | v2_struct_0(A_28))), inference(cnfTransformation, [status(thm)], [f_101])).
% 28.34/18.20  tff(c_52479, plain, (![A_1649, B_1650, C_1651]: (r1_orders_2(A_1649, k1_yellow_0(A_1649, B_1650), k1_yellow_0(A_1649, C_1651)) | ~r1_yellow_0(A_1649, C_1651) | ~r1_yellow_0(A_1649, B_1650) | ~r1_tarski(B_1650, C_1651) | ~l1_orders_2(A_1649))), inference(cnfTransformation, [status(thm)], [f_88])).
% 28.34/18.20  tff(c_52485, plain, (![B_1650]: (r1_orders_2('#skF_5', k1_yellow_0('#skF_5', B_1650), k3_yellow_0('#skF_5')) | ~r1_yellow_0('#skF_5', k1_xboole_0) | ~r1_yellow_0('#skF_5', B_1650) | ~r1_tarski(B_1650, k1_xboole_0) | ~l1_orders_2('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_88, c_52479])).
% 28.34/18.20  tff(c_52489, plain, (![B_1650]: (r1_orders_2('#skF_5', k1_yellow_0('#skF_5', B_1650), k3_yellow_0('#skF_5')) | ~r1_yellow_0('#skF_5', k1_xboole_0) | ~r1_yellow_0('#skF_5', B_1650) | ~r1_tarski(B_1650, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_52485])).
% 28.34/18.20  tff(c_54652, plain, (~r1_yellow_0('#skF_5', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_52489])).
% 28.34/18.20  tff(c_54656, plain, (~l1_orders_2('#skF_5') | ~v1_yellow_0('#skF_5') | ~v5_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_34, c_54652])).
% 28.34/18.20  tff(c_54659, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_54656])).
% 28.34/18.20  tff(c_54661, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_54659])).
% 28.34/18.20  tff(c_54663, plain, (r1_yellow_0('#skF_5', k1_xboole_0)), inference(splitRight, [status(thm)], [c_52489])).
% 28.34/18.20  tff(c_186, plain, (![A_91, B_92]: (m1_subset_1(k1_yellow_0(A_91, B_92), u1_struct_0(A_91)) | ~l1_orders_2(A_91))), inference(cnfTransformation, [status(thm)], [f_73])).
% 28.34/18.20  tff(c_189, plain, (m1_subset_1(k3_yellow_0('#skF_5'), u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_88, c_186])).
% 28.34/18.20  tff(c_191, plain, (m1_subset_1(k3_yellow_0('#skF_5'), u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_189])).
% 28.34/18.20  tff(c_30, plain, (![A_23, B_26, C_27]: (r1_orders_2(A_23, k1_yellow_0(A_23, B_26), k1_yellow_0(A_23, C_27)) | ~r1_yellow_0(A_23, C_27) | ~r1_yellow_0(A_23, B_26) | ~r1_tarski(B_26, C_27) | ~l1_orders_2(A_23))), inference(cnfTransformation, [status(thm)], [f_88])).
% 28.34/18.20  tff(c_53084, plain, (![D_1693, B_1694, A_1695, C_1696]: (r2_hidden(D_1693, B_1694) | ~r1_orders_2(A_1695, C_1696, D_1693) | ~r2_hidden(C_1696, B_1694) | ~m1_subset_1(D_1693, u1_struct_0(A_1695)) | ~m1_subset_1(C_1696, u1_struct_0(A_1695)) | ~v13_waybel_0(B_1694, A_1695) | ~m1_subset_1(B_1694, k1_zfmisc_1(u1_struct_0(A_1695))) | ~l1_orders_2(A_1695))), inference(cnfTransformation, [status(thm)], [f_120])).
% 28.34/18.20  tff(c_56561, plain, (![A_1838, C_1839, B_1840, B_1841]: (r2_hidden(k1_yellow_0(A_1838, C_1839), B_1840) | ~r2_hidden(k1_yellow_0(A_1838, B_1841), B_1840) | ~m1_subset_1(k1_yellow_0(A_1838, C_1839), u1_struct_0(A_1838)) | ~m1_subset_1(k1_yellow_0(A_1838, B_1841), u1_struct_0(A_1838)) | ~v13_waybel_0(B_1840, A_1838) | ~m1_subset_1(B_1840, k1_zfmisc_1(u1_struct_0(A_1838))) | ~r1_yellow_0(A_1838, C_1839) | ~r1_yellow_0(A_1838, B_1841) | ~r1_tarski(B_1841, C_1839) | ~l1_orders_2(A_1838))), inference(resolution, [status(thm)], [c_30, c_53084])).
% 28.34/18.20  tff(c_56597, plain, (![C_1839, B_1840]: (r2_hidden(k1_yellow_0('#skF_5', C_1839), B_1840) | ~r2_hidden(k3_yellow_0('#skF_5'), B_1840) | ~m1_subset_1(k1_yellow_0('#skF_5', C_1839), u1_struct_0('#skF_5')) | ~m1_subset_1(k1_yellow_0('#skF_5', k1_xboole_0), u1_struct_0('#skF_5')) | ~v13_waybel_0(B_1840, '#skF_5') | ~m1_subset_1(B_1840, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r1_yellow_0('#skF_5', C_1839) | ~r1_yellow_0('#skF_5', k1_xboole_0) | ~r1_tarski(k1_xboole_0, C_1839) | ~l1_orders_2('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_88, c_56561])).
% 28.34/18.20  tff(c_62231, plain, (![C_2069, B_2070]: (r2_hidden(k1_yellow_0('#skF_5', C_2069), B_2070) | ~r2_hidden(k3_yellow_0('#skF_5'), B_2070) | ~m1_subset_1(k1_yellow_0('#skF_5', C_2069), u1_struct_0('#skF_5')) | ~v13_waybel_0(B_2070, '#skF_5') | ~m1_subset_1(B_2070, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r1_yellow_0('#skF_5', C_2069) | ~r1_tarski(k1_xboole_0, C_2069))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_54663, c_191, c_88, c_56597])).
% 28.34/18.20  tff(c_62281, plain, (![B_21, B_2070]: (r2_hidden(k1_yellow_0('#skF_5', B_21), B_2070) | ~r2_hidden(k3_yellow_0('#skF_5'), B_2070) | ~v13_waybel_0(B_2070, '#skF_5') | ~m1_subset_1(B_2070, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r1_yellow_0('#skF_5', B_21) | ~r1_tarski(k1_xboole_0, B_21) | ~l1_orders_2('#skF_5'))), inference(resolution, [status(thm)], [c_26, c_62231])).
% 28.34/18.20  tff(c_76058, plain, (![B_2546, B_2547]: (r2_hidden(k1_yellow_0('#skF_5', B_2546), B_2547) | ~r2_hidden(k3_yellow_0('#skF_5'), B_2547) | ~v13_waybel_0(B_2547, '#skF_5') | ~m1_subset_1(B_2547, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r1_yellow_0('#skF_5', B_2546) | ~r1_tarski(k1_xboole_0, B_2546))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62281])).
% 28.34/18.20  tff(c_76107, plain, (![B_2546]: (r2_hidden(k1_yellow_0('#skF_5', B_2546), '#skF_6') | ~r2_hidden(k3_yellow_0('#skF_5'), '#skF_6') | ~v13_waybel_0('#skF_6', '#skF_5') | ~r1_yellow_0('#skF_5', B_2546) | ~r1_tarski(k1_xboole_0, B_2546))), inference(resolution, [status(thm)], [c_56, c_76058])).
% 28.34/18.20  tff(c_76128, plain, (![B_2548]: (r2_hidden(k1_yellow_0('#skF_5', B_2548), '#skF_6') | ~r1_yellow_0('#skF_5', B_2548) | ~r1_tarski(k1_xboole_0, B_2548))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_165, c_76107])).
% 28.34/18.20  tff(c_76184, plain, (![B_21]: (r2_hidden(k1_yellow_0('#skF_5', B_21), '#skF_6') | ~r1_yellow_0('#skF_5', k5_waybel_0('#skF_5', k1_yellow_0('#skF_5', B_21))) | ~r1_tarski(k1_xboole_0, k5_waybel_0('#skF_5', k1_yellow_0('#skF_5', B_21))) | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5') | ~l1_orders_2('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_52803, c_76128])).
% 28.34/18.20  tff(c_76249, plain, (![B_21]: (r2_hidden(k1_yellow_0('#skF_5', B_21), '#skF_6') | ~r1_yellow_0('#skF_5', k5_waybel_0('#skF_5', k1_yellow_0('#skF_5', B_21))) | ~r1_tarski(k1_xboole_0, k5_waybel_0('#skF_5', k1_yellow_0('#skF_5', B_21))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_72, c_70, c_68, c_76184])).
% 28.34/18.21  tff(c_76507, plain, (![B_2552]: (r2_hidden(k1_yellow_0('#skF_5', B_2552), '#skF_6') | ~r1_yellow_0('#skF_5', k5_waybel_0('#skF_5', k1_yellow_0('#skF_5', B_2552))) | ~r1_tarski(k1_xboole_0, k5_waybel_0('#skF_5', k1_yellow_0('#skF_5', B_2552))))), inference(negUnitSimplification, [status(thm)], [c_74, c_76249])).
% 28.34/18.21  tff(c_76584, plain, (![B_2552]: (r2_hidden(k1_yellow_0('#skF_5', B_2552), '#skF_6') | ~r1_tarski(k1_xboole_0, k5_waybel_0('#skF_5', k1_yellow_0('#skF_5', B_2552))) | ~m1_subset_1(k1_yellow_0('#skF_5', B_2552), u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_50, c_76507])).
% 28.34/18.21  tff(c_76618, plain, (![B_2552]: (r2_hidden(k1_yellow_0('#skF_5', B_2552), '#skF_6') | ~r1_tarski(k1_xboole_0, k5_waybel_0('#skF_5', k1_yellow_0('#skF_5', B_2552))) | ~m1_subset_1(k1_yellow_0('#skF_5', B_2552), u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_64, c_76584])).
% 28.34/18.21  tff(c_77474, plain, (![B_2563]: (r2_hidden(k1_yellow_0('#skF_5', B_2563), '#skF_6') | ~r1_tarski(k1_xboole_0, k5_waybel_0('#skF_5', k1_yellow_0('#skF_5', B_2563))) | ~m1_subset_1(k1_yellow_0('#skF_5', B_2563), u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_74, c_76618])).
% 28.34/18.21  tff(c_77551, plain, (![B_2563]: (r2_hidden(k1_yellow_0('#skF_5', B_2563), '#skF_6') | ~m1_subset_1(k1_yellow_0('#skF_5', B_2563), u1_struct_0('#skF_5')) | ~v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_242, c_77474])).
% 28.34/18.21  tff(c_77814, plain, (![B_2573]: (r2_hidden(k1_yellow_0('#skF_5', B_2573), '#skF_6') | ~m1_subset_1(k1_yellow_0('#skF_5', B_2573), u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_77551])).
% 28.34/18.21  tff(c_77909, plain, (![B_21]: (r2_hidden(k1_yellow_0('#skF_5', B_21), '#skF_6') | ~l1_orders_2('#skF_5'))), inference(resolution, [status(thm)], [c_26, c_77814])).
% 28.34/18.21  tff(c_77959, plain, (![B_2574]: (r2_hidden(k1_yellow_0('#skF_5', B_2574), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_77909])).
% 28.34/18.21  tff(c_78006, plain, (![B_7]: (r2_hidden('#skF_2'(u1_struct_0('#skF_5'), B_7), '#skF_6') | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5') | u1_struct_0('#skF_5')=B_7 | ~m1_subset_1(B_7, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(superposition, [status(thm), theory('equality')], [c_52793, c_77959])).
% 28.34/18.21  tff(c_78062, plain, (![B_7]: (r2_hidden('#skF_2'(u1_struct_0('#skF_5'), B_7), '#skF_6') | v2_struct_0('#skF_5') | u1_struct_0('#skF_5')=B_7 | ~m1_subset_1(B_7, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_64, c_78006])).
% 28.34/18.21  tff(c_83477, plain, (![B_2688]: (r2_hidden('#skF_2'(u1_struct_0('#skF_5'), B_2688), '#skF_6') | u1_struct_0('#skF_5')=B_2688 | ~m1_subset_1(B_2688, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_74, c_78062])).
% 28.34/18.21  tff(c_10, plain, (![A_6, B_7]: (~r2_hidden('#skF_2'(A_6, B_7), B_7) | B_7=A_6 | ~m1_subset_1(B_7, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 28.34/18.21  tff(c_83496, plain, (u1_struct_0('#skF_5')='#skF_6' | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_83477, c_10])).
% 28.34/18.21  tff(c_83519, plain, (u1_struct_0('#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_83496])).
% 28.34/18.21  tff(c_99, plain, (![A_64, B_65]: (r1_tarski(A_64, B_65) | ~m1_subset_1(A_64, k1_zfmisc_1(B_65)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 28.34/18.21  tff(c_107, plain, (r1_tarski('#skF_6', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_56, c_99])).
% 28.34/18.21  tff(c_200, plain, (![C_96, B_97, A_98]: (r2_hidden(C_96, B_97) | ~r2_hidden(C_96, A_98) | ~r1_tarski(A_98, B_97))), inference(cnfTransformation, [status(thm)], [f_32])).
% 28.34/18.21  tff(c_489, plain, (![A_146, B_147, B_148]: (r2_hidden(A_146, B_147) | ~r1_tarski(B_148, B_147) | v1_xboole_0(B_148) | ~m1_subset_1(A_146, B_148))), inference(resolution, [status(thm)], [c_14, c_200])).
% 28.34/18.21  tff(c_497, plain, (![A_146]: (r2_hidden(A_146, u1_struct_0('#skF_5')) | v1_xboole_0('#skF_6') | ~m1_subset_1(A_146, '#skF_6'))), inference(resolution, [status(thm)], [c_107, c_489])).
% 28.34/18.21  tff(c_504, plain, (![A_149]: (r2_hidden(A_149, u1_struct_0('#skF_5')) | ~m1_subset_1(A_149, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_62, c_497])).
% 28.34/18.21  tff(c_682, plain, (![A_170]: (u1_struct_0('#skF_5')=A_170 | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(A_170)) | ~m1_subset_1('#skF_2'(A_170, u1_struct_0('#skF_5')), '#skF_6'))), inference(resolution, [status(thm)], [c_504, c_10])).
% 28.34/18.21  tff(c_687, plain, (u1_struct_0('#skF_5')='#skF_6' | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1('#skF_6'))), inference(resolution, [status(thm)], [c_12, c_682])).
% 28.34/18.21  tff(c_688, plain, (~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_687])).
% 28.34/18.21  tff(c_692, plain, (~r1_tarski(u1_struct_0('#skF_5'), '#skF_6')), inference(resolution, [status(thm)], [c_18, c_688])).
% 28.34/18.21  tff(c_83690, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_83519, c_692])).
% 28.34/18.21  tff(c_83717, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_178, c_83690])).
% 28.34/18.21  tff(c_83718, plain, (u1_struct_0('#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_687])).
% 28.34/18.21  tff(c_166, plain, (v1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_76])).
% 28.34/18.21  tff(c_83736, plain, (v1_subset_1('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_83718, c_166])).
% 28.34/18.21  tff(c_83741, plain, $false, inference(negUnitSimplification, [status(thm)], [c_181, c_83736])).
% 28.34/18.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 28.34/18.21  
% 28.34/18.21  Inference rules
% 28.34/18.21  ----------------------
% 28.34/18.21  #Ref     : 0
% 28.34/18.21  #Sup     : 19882
% 28.34/18.21  #Fact    : 8
% 28.34/18.21  #Define  : 0
% 28.34/18.21  #Split   : 144
% 28.34/18.21  #Chain   : 0
% 28.34/18.21  #Close   : 0
% 28.34/18.21  
% 28.34/18.21  Ordering : KBO
% 28.34/18.21  
% 28.34/18.21  Simplification rules
% 28.34/18.21  ----------------------
% 28.34/18.21  #Subsume      : 10910
% 28.34/18.21  #Demod        : 13691
% 28.34/18.21  #Tautology    : 1788
% 28.34/18.21  #SimpNegUnit  : 4510
% 28.34/18.21  #BackRed      : 1694
% 28.34/18.21  
% 28.34/18.21  #Partial instantiations: 0
% 28.34/18.21  #Strategies tried      : 1
% 28.34/18.21  
% 28.34/18.21  Timing (in seconds)
% 28.34/18.21  ----------------------
% 28.34/18.21  Preprocessing        : 0.37
% 28.34/18.21  Parsing              : 0.19
% 28.34/18.21  CNF conversion       : 0.03
% 28.34/18.21  Main loop            : 17.07
% 28.34/18.21  Inferencing          : 3.05
% 28.34/18.21  Reduction            : 4.76
% 28.34/18.21  Demodulation         : 3.22
% 28.34/18.21  BG Simplification    : 0.26
% 28.34/18.21  Subsumption          : 7.90
% 28.34/18.21  Abstraction          : 0.44
% 28.34/18.21  MUC search           : 0.00
% 28.34/18.21  Cooper               : 0.00
% 28.34/18.21  Total                : 17.48
% 28.34/18.21  Index Insertion      : 0.00
% 28.34/18.21  Index Deletion       : 0.00
% 28.34/18.21  Index Matching       : 0.00
% 28.34/18.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
