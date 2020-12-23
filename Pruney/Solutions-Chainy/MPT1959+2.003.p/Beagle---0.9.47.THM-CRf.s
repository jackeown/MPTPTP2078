%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:58 EST 2020

% Result     : Theorem 3.85s
% Output     : CNFRefutation 4.13s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 588 expanded)
%              Number of leaves         :   38 ( 219 expanded)
%              Depth                    :   17
%              Number of atoms          :  213 (2734 expanded)
%              Number of equality atoms :   26 (  78 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > l1_orders_2 > #nlpp > u1_struct_0 > k3_yellow_0 > k2_subset_1 > k1_zfmisc_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4

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

tff(f_34,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_44,axiom,(
    ! [A] : ~ v1_subset_1(k2_subset_1(A),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_subset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

tff(f_48,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_133,negated_conjecture,(
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

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_104,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(k3_yellow_0(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow_0)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_78,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v5_orders_2(A)
        & v1_yellow_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => r1_orders_2(A,k3_yellow_0(A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_yellow_0)).

tff(f_97,axiom,(
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

tff(f_41,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(c_10,plain,(
    ! [A_4] : k2_subset_1(A_4) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_14,plain,(
    ! [A_8] : ~ v1_subset_1(k2_subset_1(A_8),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_69,plain,(
    ! [A_8] : ~ v1_subset_1(A_8,A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_14])).

tff(c_175,plain,(
    ! [A_75,B_76] :
      ( r2_hidden('#skF_1'(A_75,B_76),B_76)
      | r2_hidden('#skF_2'(A_75,B_76),A_75)
      | B_76 = A_75 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,B_10)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_187,plain,(
    ! [A_75,B_76] :
      ( m1_subset_1('#skF_1'(A_75,B_76),B_76)
      | r2_hidden('#skF_2'(A_75,B_76),A_75)
      | B_76 = A_75 ) ),
    inference(resolution,[status(thm)],[c_175,c_16])).

tff(c_44,plain,(
    v13_waybel_0('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_48,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_83,plain,(
    ! [A_53,B_54] :
      ( r2_hidden(A_53,B_54)
      | v1_xboole_0(B_54)
      | ~ m1_subset_1(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_68,plain,
    ( v1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ r2_hidden(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_82,plain,(
    ~ r2_hidden(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_86,plain,
    ( v1_xboole_0('#skF_6')
    | ~ m1_subset_1(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_83,c_82])).

tff(c_92,plain,(
    ~ m1_subset_1(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_86])).

tff(c_50,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_62,plain,
    ( r2_hidden(k3_yellow_0('#skF_5'),'#skF_6')
    | ~ v1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_101,plain,(
    ~ v1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_62])).

tff(c_42,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_102,plain,(
    ! [B_57,A_58] :
      ( v1_subset_1(B_57,A_58)
      | B_57 = A_58
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_105,plain,
    ( v1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | u1_struct_0('#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_42,c_102])).

tff(c_108,plain,(
    u1_struct_0('#skF_5') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_105])).

tff(c_22,plain,(
    ! [A_16] :
      ( m1_subset_1(k3_yellow_0(A_16),u1_struct_0(A_16))
      | ~ l1_orders_2(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_115,plain,
    ( m1_subset_1(k3_yellow_0('#skF_5'),'#skF_6')
    | ~ l1_orders_2('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_22])).

tff(c_119,plain,(
    m1_subset_1(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_115])).

tff(c_121,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_119])).

tff(c_123,plain,(
    r2_hidden(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_54,plain,(
    v5_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_52,plain,(
    v1_yellow_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_148,plain,(
    ! [A_65,C_66,B_67] :
      ( m1_subset_1(A_65,C_66)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(C_66))
      | ~ r2_hidden(A_65,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_151,plain,(
    ! [A_65] :
      ( m1_subset_1(A_65,u1_struct_0('#skF_5'))
      | ~ r2_hidden(A_65,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_42,c_148])).

tff(c_24,plain,(
    ! [A_17,B_19] :
      ( r1_orders_2(A_17,k3_yellow_0(A_17),B_19)
      | ~ m1_subset_1(B_19,u1_struct_0(A_17))
      | ~ l1_orders_2(A_17)
      | ~ v1_yellow_0(A_17)
      | ~ v5_orders_2(A_17)
      | v2_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_652,plain,(
    ! [D_128,B_129,A_130,C_131] :
      ( r2_hidden(D_128,B_129)
      | ~ r1_orders_2(A_130,C_131,D_128)
      | ~ r2_hidden(C_131,B_129)
      | ~ m1_subset_1(D_128,u1_struct_0(A_130))
      | ~ m1_subset_1(C_131,u1_struct_0(A_130))
      | ~ v13_waybel_0(B_129,A_130)
      | ~ m1_subset_1(B_129,k1_zfmisc_1(u1_struct_0(A_130)))
      | ~ l1_orders_2(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_833,plain,(
    ! [B_147,B_148,A_149] :
      ( r2_hidden(B_147,B_148)
      | ~ r2_hidden(k3_yellow_0(A_149),B_148)
      | ~ m1_subset_1(k3_yellow_0(A_149),u1_struct_0(A_149))
      | ~ v13_waybel_0(B_148,A_149)
      | ~ m1_subset_1(B_148,k1_zfmisc_1(u1_struct_0(A_149)))
      | ~ m1_subset_1(B_147,u1_struct_0(A_149))
      | ~ l1_orders_2(A_149)
      | ~ v1_yellow_0(A_149)
      | ~ v5_orders_2(A_149)
      | v2_struct_0(A_149) ) ),
    inference(resolution,[status(thm)],[c_24,c_652])).

tff(c_836,plain,(
    ! [B_147,B_148] :
      ( r2_hidden(B_147,B_148)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_148)
      | ~ v13_waybel_0(B_148,'#skF_5')
      | ~ m1_subset_1(B_148,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_147,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v1_yellow_0('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r2_hidden(k3_yellow_0('#skF_5'),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_151,c_833])).

tff(c_841,plain,(
    ! [B_147,B_148] :
      ( r2_hidden(B_147,B_148)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_148)
      | ~ v13_waybel_0(B_148,'#skF_5')
      | ~ m1_subset_1(B_148,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_147,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_54,c_52,c_50,c_836])).

tff(c_844,plain,(
    ! [B_150,B_151] :
      ( r2_hidden(B_150,B_151)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_151)
      | ~ v13_waybel_0(B_151,'#skF_5')
      | ~ m1_subset_1(B_151,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_150,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_841])).

tff(c_873,plain,(
    ! [B_150] :
      ( r2_hidden(B_150,'#skF_6')
      | ~ r2_hidden(k3_yellow_0('#skF_5'),'#skF_6')
      | ~ v13_waybel_0('#skF_6','#skF_5')
      | ~ m1_subset_1(B_150,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_42,c_844])).

tff(c_886,plain,(
    ! [B_152] :
      ( r2_hidden(B_152,'#skF_6')
      | ~ m1_subset_1(B_152,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_123,c_873])).

tff(c_1096,plain,(
    ! [A_157] :
      ( r2_hidden('#skF_1'(A_157,u1_struct_0('#skF_5')),'#skF_6')
      | r2_hidden('#skF_2'(A_157,u1_struct_0('#skF_5')),A_157)
      | u1_struct_0('#skF_5') = A_157 ) ),
    inference(resolution,[status(thm)],[c_187,c_886])).

tff(c_128,plain,(
    ! [B_59,A_60] :
      ( v1_xboole_0(B_59)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(A_60))
      | ~ v1_xboole_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_131,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_42,c_128])).

tff(c_134,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_131])).

tff(c_18,plain,(
    ! [A_11,B_12] :
      ( r2_hidden(A_11,B_12)
      | v1_xboole_0(B_12)
      | ~ m1_subset_1(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_153,plain,(
    ! [A_69,B_70] :
      ( r2_hidden('#skF_1'(A_69,B_70),B_70)
      | ~ r2_hidden('#skF_2'(A_69,B_70),B_70)
      | B_70 = A_69 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_306,plain,(
    ! [A_89,B_90] :
      ( r2_hidden('#skF_1'(A_89,B_90),B_90)
      | B_90 = A_89
      | v1_xboole_0(B_90)
      | ~ m1_subset_1('#skF_2'(A_89,B_90),B_90) ) ),
    inference(resolution,[status(thm)],[c_18,c_153])).

tff(c_363,plain,(
    ! [A_95,B_96] :
      ( m1_subset_1('#skF_1'(A_95,B_96),B_96)
      | B_96 = A_95
      | v1_xboole_0(B_96)
      | ~ m1_subset_1('#skF_2'(A_95,B_96),B_96) ) ),
    inference(resolution,[status(thm)],[c_306,c_16])).

tff(c_377,plain,(
    ! [A_95] :
      ( m1_subset_1('#skF_1'(A_95,u1_struct_0('#skF_5')),u1_struct_0('#skF_5'))
      | u1_struct_0('#skF_5') = A_95
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_2'(A_95,u1_struct_0('#skF_5')),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_151,c_363])).

tff(c_384,plain,(
    ! [A_95] :
      ( m1_subset_1('#skF_1'(A_95,u1_struct_0('#skF_5')),u1_struct_0('#skF_5'))
      | u1_struct_0('#skF_5') = A_95
      | ~ r2_hidden('#skF_2'(A_95,u1_struct_0('#skF_5')),'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_134,c_377])).

tff(c_948,plain,(
    ! [A_95] :
      ( r2_hidden('#skF_1'(A_95,u1_struct_0('#skF_5')),'#skF_6')
      | u1_struct_0('#skF_5') = A_95
      | ~ r2_hidden('#skF_2'(A_95,u1_struct_0('#skF_5')),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_384,c_886])).

tff(c_1123,plain,
    ( r2_hidden('#skF_1'('#skF_6',u1_struct_0('#skF_5')),'#skF_6')
    | u1_struct_0('#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1096,c_948])).

tff(c_1133,plain,(
    u1_struct_0('#skF_5') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_1123])).

tff(c_122,plain,(
    v1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_1145,plain,(
    v1_subset_1('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1133,c_122])).

tff(c_1148,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_1145])).

tff(c_1150,plain,(
    u1_struct_0('#skF_5') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1123])).

tff(c_1149,plain,(
    r2_hidden('#skF_1'('#skF_6',u1_struct_0('#skF_5')),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_1123])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r2_hidden('#skF_2'(A_1,B_2),A_1)
      | B_2 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1170,plain,(
    m1_subset_1('#skF_1'('#skF_6',u1_struct_0('#skF_5')),'#skF_6') ),
    inference(resolution,[status(thm)],[c_1149,c_16])).

tff(c_170,plain,(
    ! [A_73,B_74] :
      ( ~ r2_hidden('#skF_1'(A_73,B_74),A_73)
      | ~ r2_hidden('#skF_2'(A_73,B_74),B_74)
      | B_74 = A_73 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_287,plain,(
    ! [B_87,B_88] :
      ( ~ r2_hidden('#skF_2'(B_87,B_88),B_88)
      | B_88 = B_87
      | v1_xboole_0(B_87)
      | ~ m1_subset_1('#skF_1'(B_87,B_88),B_87) ) ),
    inference(resolution,[status(thm)],[c_18,c_170])).

tff(c_305,plain,(
    ! [B_87,B_12] :
      ( B_87 = B_12
      | v1_xboole_0(B_87)
      | ~ m1_subset_1('#skF_1'(B_87,B_12),B_87)
      | v1_xboole_0(B_12)
      | ~ m1_subset_1('#skF_2'(B_87,B_12),B_12) ) ),
    inference(resolution,[status(thm)],[c_18,c_287])).

tff(c_1192,plain,
    ( u1_struct_0('#skF_5') = '#skF_6'
    | v1_xboole_0('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_2'('#skF_6',u1_struct_0('#skF_5')),u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_1170,c_305])).

tff(c_1195,plain,(
    ~ m1_subset_1('#skF_2'('#skF_6',u1_struct_0('#skF_5')),u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_134,c_48,c_1150,c_1192])).

tff(c_1205,plain,(
    ~ r2_hidden('#skF_2'('#skF_6',u1_struct_0('#skF_5')),'#skF_6') ),
    inference(resolution,[status(thm)],[c_151,c_1195])).

tff(c_1213,plain,
    ( ~ r2_hidden('#skF_1'('#skF_6',u1_struct_0('#skF_5')),'#skF_6')
    | u1_struct_0('#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_6,c_1205])).

tff(c_1222,plain,(
    u1_struct_0('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1149,c_1213])).

tff(c_1224,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1150,c_1222])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:25:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.85/1.67  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.13/1.68  
% 4.13/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.13/1.69  %$ r1_orders_2 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > l1_orders_2 > #nlpp > u1_struct_0 > k3_yellow_0 > k2_subset_1 > k1_zfmisc_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4
% 4.13/1.69  
% 4.13/1.69  %Foreground sorts:
% 4.13/1.69  
% 4.13/1.69  
% 4.13/1.69  %Background operators:
% 4.13/1.69  
% 4.13/1.69  
% 4.13/1.69  %Foreground operators:
% 4.13/1.69  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.13/1.69  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 4.13/1.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.13/1.69  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.13/1.69  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 4.13/1.69  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 4.13/1.69  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 4.13/1.69  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 4.13/1.69  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.13/1.69  tff('#skF_5', type, '#skF_5': $i).
% 4.13/1.69  tff('#skF_6', type, '#skF_6': $i).
% 4.13/1.69  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 4.13/1.69  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 4.13/1.69  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.13/1.69  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 4.13/1.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.13/1.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.13/1.69  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.13/1.69  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 4.13/1.69  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.13/1.69  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.13/1.69  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.13/1.69  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.13/1.69  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.13/1.69  tff(v1_yellow_0, type, v1_yellow_0: $i > $o).
% 4.13/1.69  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.13/1.69  
% 4.13/1.70  tff(f_34, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 4.13/1.70  tff(f_44, axiom, (![A]: ~v1_subset_1(k2_subset_1(A), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc14_subset_1)).
% 4.13/1.70  tff(f_32, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 4.13/1.70  tff(f_48, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 4.13/1.70  tff(f_133, negated_conjecture, ~(![A]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, A)) & v13_waybel_0(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_subset_1(B, u1_struct_0(A)) <=> ~r2_hidden(k3_yellow_0(A), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_waybel_7)).
% 4.13/1.70  tff(f_54, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 4.13/1.70  tff(f_104, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 4.13/1.70  tff(f_64, axiom, (![A]: (l1_orders_2(A) => m1_subset_1(k3_yellow_0(A), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_yellow_0)).
% 4.13/1.70  tff(f_60, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 4.13/1.70  tff(f_78, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r1_orders_2(A, k3_yellow_0(A), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_yellow_0)).
% 4.13/1.70  tff(f_97, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v13_waybel_0(B, A) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r2_hidden(C, B) & r1_orders_2(A, C, D)) => r2_hidden(D, B))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d20_waybel_0)).
% 4.13/1.70  tff(f_41, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 4.13/1.70  tff(c_10, plain, (![A_4]: (k2_subset_1(A_4)=A_4)), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.13/1.70  tff(c_14, plain, (![A_8]: (~v1_subset_1(k2_subset_1(A_8), A_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.13/1.70  tff(c_69, plain, (![A_8]: (~v1_subset_1(A_8, A_8))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_14])).
% 4.13/1.70  tff(c_175, plain, (![A_75, B_76]: (r2_hidden('#skF_1'(A_75, B_76), B_76) | r2_hidden('#skF_2'(A_75, B_76), A_75) | B_76=A_75)), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.13/1.70  tff(c_16, plain, (![A_9, B_10]: (m1_subset_1(A_9, B_10) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.13/1.70  tff(c_187, plain, (![A_75, B_76]: (m1_subset_1('#skF_1'(A_75, B_76), B_76) | r2_hidden('#skF_2'(A_75, B_76), A_75) | B_76=A_75)), inference(resolution, [status(thm)], [c_175, c_16])).
% 4.13/1.70  tff(c_44, plain, (v13_waybel_0('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.13/1.70  tff(c_48, plain, (~v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.13/1.70  tff(c_83, plain, (![A_53, B_54]: (r2_hidden(A_53, B_54) | v1_xboole_0(B_54) | ~m1_subset_1(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.13/1.70  tff(c_68, plain, (v1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~r2_hidden(k3_yellow_0('#skF_5'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.13/1.70  tff(c_82, plain, (~r2_hidden(k3_yellow_0('#skF_5'), '#skF_6')), inference(splitLeft, [status(thm)], [c_68])).
% 4.13/1.70  tff(c_86, plain, (v1_xboole_0('#skF_6') | ~m1_subset_1(k3_yellow_0('#skF_5'), '#skF_6')), inference(resolution, [status(thm)], [c_83, c_82])).
% 4.13/1.70  tff(c_92, plain, (~m1_subset_1(k3_yellow_0('#skF_5'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_48, c_86])).
% 4.13/1.70  tff(c_50, plain, (l1_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.13/1.70  tff(c_62, plain, (r2_hidden(k3_yellow_0('#skF_5'), '#skF_6') | ~v1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.13/1.70  tff(c_101, plain, (~v1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_82, c_62])).
% 4.13/1.70  tff(c_42, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.13/1.70  tff(c_102, plain, (![B_57, A_58]: (v1_subset_1(B_57, A_58) | B_57=A_58 | ~m1_subset_1(B_57, k1_zfmisc_1(A_58)))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.13/1.70  tff(c_105, plain, (v1_subset_1('#skF_6', u1_struct_0('#skF_5')) | u1_struct_0('#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_42, c_102])).
% 4.13/1.70  tff(c_108, plain, (u1_struct_0('#skF_5')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_101, c_105])).
% 4.13/1.70  tff(c_22, plain, (![A_16]: (m1_subset_1(k3_yellow_0(A_16), u1_struct_0(A_16)) | ~l1_orders_2(A_16))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.13/1.70  tff(c_115, plain, (m1_subset_1(k3_yellow_0('#skF_5'), '#skF_6') | ~l1_orders_2('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_108, c_22])).
% 4.13/1.70  tff(c_119, plain, (m1_subset_1(k3_yellow_0('#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_115])).
% 4.13/1.70  tff(c_121, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_119])).
% 4.13/1.70  tff(c_123, plain, (r2_hidden(k3_yellow_0('#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_68])).
% 4.13/1.70  tff(c_60, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.13/1.70  tff(c_54, plain, (v5_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.13/1.70  tff(c_52, plain, (v1_yellow_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.13/1.70  tff(c_148, plain, (![A_65, C_66, B_67]: (m1_subset_1(A_65, C_66) | ~m1_subset_1(B_67, k1_zfmisc_1(C_66)) | ~r2_hidden(A_65, B_67))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.13/1.70  tff(c_151, plain, (![A_65]: (m1_subset_1(A_65, u1_struct_0('#skF_5')) | ~r2_hidden(A_65, '#skF_6'))), inference(resolution, [status(thm)], [c_42, c_148])).
% 4.13/1.70  tff(c_24, plain, (![A_17, B_19]: (r1_orders_2(A_17, k3_yellow_0(A_17), B_19) | ~m1_subset_1(B_19, u1_struct_0(A_17)) | ~l1_orders_2(A_17) | ~v1_yellow_0(A_17) | ~v5_orders_2(A_17) | v2_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.13/1.70  tff(c_652, plain, (![D_128, B_129, A_130, C_131]: (r2_hidden(D_128, B_129) | ~r1_orders_2(A_130, C_131, D_128) | ~r2_hidden(C_131, B_129) | ~m1_subset_1(D_128, u1_struct_0(A_130)) | ~m1_subset_1(C_131, u1_struct_0(A_130)) | ~v13_waybel_0(B_129, A_130) | ~m1_subset_1(B_129, k1_zfmisc_1(u1_struct_0(A_130))) | ~l1_orders_2(A_130))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.13/1.70  tff(c_833, plain, (![B_147, B_148, A_149]: (r2_hidden(B_147, B_148) | ~r2_hidden(k3_yellow_0(A_149), B_148) | ~m1_subset_1(k3_yellow_0(A_149), u1_struct_0(A_149)) | ~v13_waybel_0(B_148, A_149) | ~m1_subset_1(B_148, k1_zfmisc_1(u1_struct_0(A_149))) | ~m1_subset_1(B_147, u1_struct_0(A_149)) | ~l1_orders_2(A_149) | ~v1_yellow_0(A_149) | ~v5_orders_2(A_149) | v2_struct_0(A_149))), inference(resolution, [status(thm)], [c_24, c_652])).
% 4.13/1.70  tff(c_836, plain, (![B_147, B_148]: (r2_hidden(B_147, B_148) | ~r2_hidden(k3_yellow_0('#skF_5'), B_148) | ~v13_waybel_0(B_148, '#skF_5') | ~m1_subset_1(B_148, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_147, u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5') | ~v1_yellow_0('#skF_5') | ~v5_orders_2('#skF_5') | v2_struct_0('#skF_5') | ~r2_hidden(k3_yellow_0('#skF_5'), '#skF_6'))), inference(resolution, [status(thm)], [c_151, c_833])).
% 4.13/1.70  tff(c_841, plain, (![B_147, B_148]: (r2_hidden(B_147, B_148) | ~r2_hidden(k3_yellow_0('#skF_5'), B_148) | ~v13_waybel_0(B_148, '#skF_5') | ~m1_subset_1(B_148, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_147, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_123, c_54, c_52, c_50, c_836])).
% 4.13/1.70  tff(c_844, plain, (![B_150, B_151]: (r2_hidden(B_150, B_151) | ~r2_hidden(k3_yellow_0('#skF_5'), B_151) | ~v13_waybel_0(B_151, '#skF_5') | ~m1_subset_1(B_151, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_150, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_60, c_841])).
% 4.13/1.70  tff(c_873, plain, (![B_150]: (r2_hidden(B_150, '#skF_6') | ~r2_hidden(k3_yellow_0('#skF_5'), '#skF_6') | ~v13_waybel_0('#skF_6', '#skF_5') | ~m1_subset_1(B_150, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_42, c_844])).
% 4.13/1.70  tff(c_886, plain, (![B_152]: (r2_hidden(B_152, '#skF_6') | ~m1_subset_1(B_152, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_123, c_873])).
% 4.13/1.70  tff(c_1096, plain, (![A_157]: (r2_hidden('#skF_1'(A_157, u1_struct_0('#skF_5')), '#skF_6') | r2_hidden('#skF_2'(A_157, u1_struct_0('#skF_5')), A_157) | u1_struct_0('#skF_5')=A_157)), inference(resolution, [status(thm)], [c_187, c_886])).
% 4.13/1.70  tff(c_128, plain, (![B_59, A_60]: (v1_xboole_0(B_59) | ~m1_subset_1(B_59, k1_zfmisc_1(A_60)) | ~v1_xboole_0(A_60))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.13/1.70  tff(c_131, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_42, c_128])).
% 4.13/1.70  tff(c_134, plain, (~v1_xboole_0(u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_48, c_131])).
% 4.13/1.70  tff(c_18, plain, (![A_11, B_12]: (r2_hidden(A_11, B_12) | v1_xboole_0(B_12) | ~m1_subset_1(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.13/1.70  tff(c_153, plain, (![A_69, B_70]: (r2_hidden('#skF_1'(A_69, B_70), B_70) | ~r2_hidden('#skF_2'(A_69, B_70), B_70) | B_70=A_69)), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.13/1.70  tff(c_306, plain, (![A_89, B_90]: (r2_hidden('#skF_1'(A_89, B_90), B_90) | B_90=A_89 | v1_xboole_0(B_90) | ~m1_subset_1('#skF_2'(A_89, B_90), B_90))), inference(resolution, [status(thm)], [c_18, c_153])).
% 4.13/1.70  tff(c_363, plain, (![A_95, B_96]: (m1_subset_1('#skF_1'(A_95, B_96), B_96) | B_96=A_95 | v1_xboole_0(B_96) | ~m1_subset_1('#skF_2'(A_95, B_96), B_96))), inference(resolution, [status(thm)], [c_306, c_16])).
% 4.13/1.70  tff(c_377, plain, (![A_95]: (m1_subset_1('#skF_1'(A_95, u1_struct_0('#skF_5')), u1_struct_0('#skF_5')) | u1_struct_0('#skF_5')=A_95 | v1_xboole_0(u1_struct_0('#skF_5')) | ~r2_hidden('#skF_2'(A_95, u1_struct_0('#skF_5')), '#skF_6'))), inference(resolution, [status(thm)], [c_151, c_363])).
% 4.13/1.70  tff(c_384, plain, (![A_95]: (m1_subset_1('#skF_1'(A_95, u1_struct_0('#skF_5')), u1_struct_0('#skF_5')) | u1_struct_0('#skF_5')=A_95 | ~r2_hidden('#skF_2'(A_95, u1_struct_0('#skF_5')), '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_134, c_377])).
% 4.13/1.70  tff(c_948, plain, (![A_95]: (r2_hidden('#skF_1'(A_95, u1_struct_0('#skF_5')), '#skF_6') | u1_struct_0('#skF_5')=A_95 | ~r2_hidden('#skF_2'(A_95, u1_struct_0('#skF_5')), '#skF_6'))), inference(resolution, [status(thm)], [c_384, c_886])).
% 4.13/1.70  tff(c_1123, plain, (r2_hidden('#skF_1'('#skF_6', u1_struct_0('#skF_5')), '#skF_6') | u1_struct_0('#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_1096, c_948])).
% 4.13/1.70  tff(c_1133, plain, (u1_struct_0('#skF_5')='#skF_6'), inference(splitLeft, [status(thm)], [c_1123])).
% 4.13/1.70  tff(c_122, plain, (v1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_68])).
% 4.13/1.70  tff(c_1145, plain, (v1_subset_1('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1133, c_122])).
% 4.13/1.70  tff(c_1148, plain, $false, inference(negUnitSimplification, [status(thm)], [c_69, c_1145])).
% 4.13/1.70  tff(c_1150, plain, (u1_struct_0('#skF_5')!='#skF_6'), inference(splitRight, [status(thm)], [c_1123])).
% 4.13/1.70  tff(c_1149, plain, (r2_hidden('#skF_1'('#skF_6', u1_struct_0('#skF_5')), '#skF_6')), inference(splitRight, [status(thm)], [c_1123])).
% 4.13/1.70  tff(c_6, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), A_1) | r2_hidden('#skF_2'(A_1, B_2), A_1) | B_2=A_1)), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.13/1.70  tff(c_1170, plain, (m1_subset_1('#skF_1'('#skF_6', u1_struct_0('#skF_5')), '#skF_6')), inference(resolution, [status(thm)], [c_1149, c_16])).
% 4.13/1.70  tff(c_170, plain, (![A_73, B_74]: (~r2_hidden('#skF_1'(A_73, B_74), A_73) | ~r2_hidden('#skF_2'(A_73, B_74), B_74) | B_74=A_73)), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.13/1.70  tff(c_287, plain, (![B_87, B_88]: (~r2_hidden('#skF_2'(B_87, B_88), B_88) | B_88=B_87 | v1_xboole_0(B_87) | ~m1_subset_1('#skF_1'(B_87, B_88), B_87))), inference(resolution, [status(thm)], [c_18, c_170])).
% 4.13/1.70  tff(c_305, plain, (![B_87, B_12]: (B_87=B_12 | v1_xboole_0(B_87) | ~m1_subset_1('#skF_1'(B_87, B_12), B_87) | v1_xboole_0(B_12) | ~m1_subset_1('#skF_2'(B_87, B_12), B_12))), inference(resolution, [status(thm)], [c_18, c_287])).
% 4.13/1.70  tff(c_1192, plain, (u1_struct_0('#skF_5')='#skF_6' | v1_xboole_0('#skF_6') | v1_xboole_0(u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_2'('#skF_6', u1_struct_0('#skF_5')), u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_1170, c_305])).
% 4.13/1.70  tff(c_1195, plain, (~m1_subset_1('#skF_2'('#skF_6', u1_struct_0('#skF_5')), u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_134, c_48, c_1150, c_1192])).
% 4.13/1.70  tff(c_1205, plain, (~r2_hidden('#skF_2'('#skF_6', u1_struct_0('#skF_5')), '#skF_6')), inference(resolution, [status(thm)], [c_151, c_1195])).
% 4.13/1.70  tff(c_1213, plain, (~r2_hidden('#skF_1'('#skF_6', u1_struct_0('#skF_5')), '#skF_6') | u1_struct_0('#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_6, c_1205])).
% 4.13/1.70  tff(c_1222, plain, (u1_struct_0('#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1149, c_1213])).
% 4.13/1.70  tff(c_1224, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1150, c_1222])).
% 4.13/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.13/1.70  
% 4.13/1.70  Inference rules
% 4.13/1.70  ----------------------
% 4.13/1.70  #Ref     : 0
% 4.13/1.70  #Sup     : 225
% 4.13/1.70  #Fact    : 0
% 4.13/1.70  #Define  : 0
% 4.13/1.70  #Split   : 2
% 4.13/1.70  #Chain   : 0
% 4.13/1.70  #Close   : 0
% 4.13/1.70  
% 4.13/1.70  Ordering : KBO
% 4.13/1.71  
% 4.13/1.71  Simplification rules
% 4.13/1.71  ----------------------
% 4.13/1.71  #Subsume      : 21
% 4.13/1.71  #Demod        : 55
% 4.13/1.71  #Tautology    : 43
% 4.13/1.71  #SimpNegUnit  : 26
% 4.13/1.71  #BackRed      : 16
% 4.13/1.71  
% 4.13/1.71  #Partial instantiations: 0
% 4.13/1.71  #Strategies tried      : 1
% 4.13/1.71  
% 4.13/1.71  Timing (in seconds)
% 4.13/1.71  ----------------------
% 4.13/1.71  Preprocessing        : 0.33
% 4.13/1.71  Parsing              : 0.18
% 4.13/1.71  CNF conversion       : 0.03
% 4.13/1.71  Main loop            : 0.61
% 4.13/1.71  Inferencing          : 0.21
% 4.13/1.71  Reduction            : 0.16
% 4.13/1.71  Demodulation         : 0.11
% 4.13/1.71  BG Simplification    : 0.03
% 4.13/1.71  Subsumption          : 0.15
% 4.13/1.71  Abstraction          : 0.03
% 4.13/1.71  MUC search           : 0.00
% 4.13/1.71  Cooper               : 0.00
% 4.13/1.71  Total                : 0.98
% 4.13/1.71  Index Insertion      : 0.00
% 4.13/1.71  Index Deletion       : 0.00
% 4.13/1.71  Index Matching       : 0.00
% 4.13/1.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
