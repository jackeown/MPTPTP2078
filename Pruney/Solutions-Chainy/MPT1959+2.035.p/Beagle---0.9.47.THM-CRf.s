%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:02 EST 2020

% Result     : Theorem 6.36s
% Output     : CNFRefutation 6.67s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 949 expanded)
%              Number of leaves         :   39 ( 336 expanded)
%              Depth                    :   21
%              Number of atoms          :  342 (3280 expanded)
%              Number of equality atoms :   45 ( 275 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > l1_orders_2 > k1_yellow_0 > #nlpp > u1_struct_0 > k3_yellow_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_5 > #skF_6 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_yellow_0,type,(
    k1_yellow_0: ( $i * $i ) > $i )).

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(f_119,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_148,negated_conjecture,(
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

tff(f_71,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

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

tff(f_64,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_75,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => k3_yellow_0(A) = k1_yellow_0(A,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_yellow_0)).

tff(f_79,axiom,(
    ! [A,B] :
      ( l1_orders_2(A)
     => m1_subset_1(k1_yellow_0(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).

tff(f_93,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v5_orders_2(A)
        & v1_yellow_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => r1_orders_2(A,k3_yellow_0(A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_yellow_0)).

tff(f_112,axiom,(
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

tff(c_14,plain,(
    ! [A_12] : ~ v1_subset_1('#skF_2'(A_12),A_12) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_16,plain,(
    ! [A_12] : m1_subset_1('#skF_2'(A_12),k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_175,plain,(
    ! [B_82,A_83] :
      ( v1_subset_1(B_82,A_83)
      | B_82 = A_83
      | ~ m1_subset_1(B_82,k1_zfmisc_1(A_83)) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_178,plain,(
    ! [A_12] :
      ( v1_subset_1('#skF_2'(A_12),A_12)
      | '#skF_2'(A_12) = A_12 ) ),
    inference(resolution,[status(thm)],[c_16,c_175])).

tff(c_184,plain,(
    ! [A_12] : '#skF_2'(A_12) = A_12 ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_178])).

tff(c_196,plain,(
    ! [A_12] : ~ v1_subset_1(A_12,A_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_14])).

tff(c_195,plain,(
    ! [A_12] : m1_subset_1(A_12,k1_zfmisc_1(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_16])).

tff(c_46,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_161,plain,(
    ! [C_77,B_78,A_79] :
      ( ~ v1_xboole_0(C_77)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(C_77))
      | ~ r2_hidden(A_79,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_167,plain,(
    ! [A_79] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ r2_hidden(A_79,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_46,c_161])).

tff(c_174,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_167])).

tff(c_692,plain,(
    ! [A_171,B_172,C_173] :
      ( r2_hidden('#skF_1'(A_171,B_172,C_173),B_172)
      | r2_hidden('#skF_1'(A_171,B_172,C_173),C_173)
      | C_173 = B_172
      | ~ m1_subset_1(C_173,k1_zfmisc_1(A_171))
      | ~ m1_subset_1(B_172,k1_zfmisc_1(A_171)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_246,plain,(
    ! [A_94,C_95,B_96] :
      ( m1_subset_1(A_94,C_95)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(C_95))
      | ~ r2_hidden(A_94,B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_251,plain,(
    ! [A_94,A_12] :
      ( m1_subset_1(A_94,A_12)
      | ~ r2_hidden(A_94,A_12) ) ),
    inference(resolution,[status(thm)],[c_195,c_246])).

tff(c_1060,plain,(
    ! [A_206,B_207,C_208] :
      ( m1_subset_1('#skF_1'(A_206,B_207,C_208),C_208)
      | r2_hidden('#skF_1'(A_206,B_207,C_208),B_207)
      | C_208 = B_207
      | ~ m1_subset_1(C_208,k1_zfmisc_1(A_206))
      | ~ m1_subset_1(B_207,k1_zfmisc_1(A_206)) ) ),
    inference(resolution,[status(thm)],[c_692,c_251])).

tff(c_1146,plain,(
    ! [A_206,B_207,C_208] :
      ( m1_subset_1('#skF_1'(A_206,B_207,C_208),B_207)
      | m1_subset_1('#skF_1'(A_206,B_207,C_208),C_208)
      | C_208 = B_207
      | ~ m1_subset_1(C_208,k1_zfmisc_1(A_206))
      | ~ m1_subset_1(B_207,k1_zfmisc_1(A_206)) ) ),
    inference(resolution,[status(thm)],[c_1060,c_251])).

tff(c_52,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_18,plain,(
    ! [A_14,B_15] :
      ( r2_hidden(A_14,B_15)
      | v1_xboole_0(B_15)
      | ~ m1_subset_1(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_187,plain,(
    ! [C_84,A_85,B_86] :
      ( r2_hidden(C_84,A_85)
      | ~ r2_hidden(C_84,B_86)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(A_85)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_297,plain,(
    ! [A_104,A_105,B_106] :
      ( r2_hidden(A_104,A_105)
      | ~ m1_subset_1(B_106,k1_zfmisc_1(A_105))
      | v1_xboole_0(B_106)
      | ~ m1_subset_1(A_104,B_106) ) ),
    inference(resolution,[status(thm)],[c_18,c_187])).

tff(c_304,plain,(
    ! [A_104] :
      ( r2_hidden(A_104,u1_struct_0('#skF_5'))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(A_104,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_46,c_297])).

tff(c_310,plain,(
    ! [A_107] :
      ( r2_hidden(A_107,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(A_107,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_304])).

tff(c_319,plain,(
    ! [A_107] :
      ( m1_subset_1(A_107,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(A_107,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_310,c_251])).

tff(c_48,plain,(
    v13_waybel_0('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_93,plain,(
    ! [A_62,B_63] :
      ( r2_hidden(A_62,B_63)
      | v1_xboole_0(B_63)
      | ~ m1_subset_1(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_66,plain,
    ( r2_hidden(k3_yellow_0('#skF_5'),'#skF_6')
    | ~ v1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_85,plain,(
    ~ v1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_72,plain,
    ( v1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ r2_hidden(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_86,plain,(
    ~ r2_hidden(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_72])).

tff(c_96,plain,
    ( v1_xboole_0('#skF_6')
    | ~ m1_subset_1(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_93,c_86])).

tff(c_99,plain,(
    ~ m1_subset_1(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_96])).

tff(c_114,plain,(
    ! [B_69,A_70] :
      ( v1_subset_1(B_69,A_70)
      | B_69 = A_70
      | ~ m1_subset_1(B_69,k1_zfmisc_1(A_70)) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_120,plain,
    ( v1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | u1_struct_0('#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_46,c_114])).

tff(c_126,plain,(
    u1_struct_0('#skF_5') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_120])).

tff(c_54,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_76,plain,(
    ! [A_59] :
      ( k1_yellow_0(A_59,k1_xboole_0) = k3_yellow_0(A_59)
      | ~ l1_orders_2(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_80,plain,(
    k1_yellow_0('#skF_5',k1_xboole_0) = k3_yellow_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_76])).

tff(c_87,plain,(
    ! [A_60,B_61] :
      ( m1_subset_1(k1_yellow_0(A_60,B_61),u1_struct_0(A_60))
      | ~ l1_orders_2(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_90,plain,
    ( m1_subset_1(k3_yellow_0('#skF_5'),u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_87])).

tff(c_92,plain,(
    m1_subset_1(k3_yellow_0('#skF_5'),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_90])).

tff(c_140,plain,(
    m1_subset_1(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_92])).

tff(c_144,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_140])).

tff(c_145,plain,(
    r2_hidden(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_58,plain,(
    v5_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_56,plain,(
    v1_yellow_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_252,plain,(
    ! [A_94] :
      ( m1_subset_1(A_94,u1_struct_0('#skF_5'))
      | ~ r2_hidden(A_94,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_46,c_246])).

tff(c_28,plain,(
    ! [A_25,B_27] :
      ( r1_orders_2(A_25,k3_yellow_0(A_25),B_27)
      | ~ m1_subset_1(B_27,u1_struct_0(A_25))
      | ~ l1_orders_2(A_25)
      | ~ v1_yellow_0(A_25)
      | ~ v5_orders_2(A_25)
      | v2_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_806,plain,(
    ! [D_180,B_181,A_182,C_183] :
      ( r2_hidden(D_180,B_181)
      | ~ r1_orders_2(A_182,C_183,D_180)
      | ~ r2_hidden(C_183,B_181)
      | ~ m1_subset_1(D_180,u1_struct_0(A_182))
      | ~ m1_subset_1(C_183,u1_struct_0(A_182))
      | ~ v13_waybel_0(B_181,A_182)
      | ~ m1_subset_1(B_181,k1_zfmisc_1(u1_struct_0(A_182)))
      | ~ l1_orders_2(A_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_2954,plain,(
    ! [B_307,B_308,A_309] :
      ( r2_hidden(B_307,B_308)
      | ~ r2_hidden(k3_yellow_0(A_309),B_308)
      | ~ m1_subset_1(k3_yellow_0(A_309),u1_struct_0(A_309))
      | ~ v13_waybel_0(B_308,A_309)
      | ~ m1_subset_1(B_308,k1_zfmisc_1(u1_struct_0(A_309)))
      | ~ m1_subset_1(B_307,u1_struct_0(A_309))
      | ~ l1_orders_2(A_309)
      | ~ v1_yellow_0(A_309)
      | ~ v5_orders_2(A_309)
      | v2_struct_0(A_309) ) ),
    inference(resolution,[status(thm)],[c_28,c_806])).

tff(c_2963,plain,(
    ! [B_307,B_308] :
      ( r2_hidden(B_307,B_308)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_308)
      | ~ v13_waybel_0(B_308,'#skF_5')
      | ~ m1_subset_1(B_308,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_307,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v1_yellow_0('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r2_hidden(k3_yellow_0('#skF_5'),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_252,c_2954])).

tff(c_2976,plain,(
    ! [B_307,B_308] :
      ( r2_hidden(B_307,B_308)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_308)
      | ~ v13_waybel_0(B_308,'#skF_5')
      | ~ m1_subset_1(B_308,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_307,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_58,c_56,c_54,c_2963])).

tff(c_2982,plain,(
    ! [B_310,B_311] :
      ( r2_hidden(B_310,B_311)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_311)
      | ~ v13_waybel_0(B_311,'#skF_5')
      | ~ m1_subset_1(B_311,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_310,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_2976])).

tff(c_3029,plain,(
    ! [B_310] :
      ( r2_hidden(B_310,'#skF_6')
      | ~ r2_hidden(k3_yellow_0('#skF_5'),'#skF_6')
      | ~ v13_waybel_0('#skF_6','#skF_5')
      | ~ m1_subset_1(B_310,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_46,c_2982])).

tff(c_3050,plain,(
    ! [B_312] :
      ( r2_hidden(B_312,'#skF_6')
      | ~ m1_subset_1(B_312,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_145,c_3029])).

tff(c_3160,plain,(
    ! [A_107] :
      ( r2_hidden(A_107,'#skF_6')
      | ~ m1_subset_1(A_107,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_319,c_3050])).

tff(c_742,plain,(
    ! [A_171,B_172,C_173] :
      ( m1_subset_1('#skF_1'(A_171,B_172,C_173),B_172)
      | r2_hidden('#skF_1'(A_171,B_172,C_173),C_173)
      | C_173 = B_172
      | ~ m1_subset_1(C_173,k1_zfmisc_1(A_171))
      | ~ m1_subset_1(B_172,k1_zfmisc_1(A_171)) ) ),
    inference(resolution,[status(thm)],[c_692,c_251])).

tff(c_4,plain,(
    ! [A_5,B_6,C_10] :
      ( m1_subset_1('#skF_1'(A_5,B_6,C_10),A_5)
      | C_10 = B_6
      | ~ m1_subset_1(C_10,k1_zfmisc_1(A_5))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_616,plain,(
    ! [A_159,B_160,C_161] :
      ( ~ r2_hidden('#skF_1'(A_159,B_160,C_161),C_161)
      | ~ r2_hidden('#skF_1'(A_159,B_160,C_161),B_160)
      | C_161 = B_160
      | ~ m1_subset_1(C_161,k1_zfmisc_1(A_159))
      | ~ m1_subset_1(B_160,k1_zfmisc_1(A_159)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1149,plain,(
    ! [A_209,B_210,B_211] :
      ( ~ r2_hidden('#skF_1'(A_209,B_210,B_211),B_210)
      | B_211 = B_210
      | ~ m1_subset_1(B_211,k1_zfmisc_1(A_209))
      | ~ m1_subset_1(B_210,k1_zfmisc_1(A_209))
      | v1_xboole_0(B_211)
      | ~ m1_subset_1('#skF_1'(A_209,B_210,B_211),B_211) ) ),
    inference(resolution,[status(thm)],[c_18,c_616])).

tff(c_3848,plain,(
    ! [B_352,B_351,A_353] :
      ( B_352 = B_351
      | ~ m1_subset_1(B_351,k1_zfmisc_1(A_353))
      | ~ m1_subset_1(B_352,k1_zfmisc_1(A_353))
      | v1_xboole_0(B_351)
      | ~ m1_subset_1('#skF_1'(A_353,B_352,B_351),B_351)
      | v1_xboole_0(B_352)
      | ~ m1_subset_1('#skF_1'(A_353,B_352,B_351),B_352) ) ),
    inference(resolution,[status(thm)],[c_18,c_1149])).

tff(c_3873,plain,(
    ! [A_5,B_6] :
      ( v1_xboole_0(A_5)
      | v1_xboole_0(B_6)
      | ~ m1_subset_1('#skF_1'(A_5,B_6,A_5),B_6)
      | B_6 = A_5
      | ~ m1_subset_1(A_5,k1_zfmisc_1(A_5))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(resolution,[status(thm)],[c_4,c_3848])).

tff(c_3903,plain,(
    ! [A_354,B_355] :
      ( v1_xboole_0(A_354)
      | v1_xboole_0(B_355)
      | ~ m1_subset_1('#skF_1'(A_354,B_355,A_354),B_355)
      | B_355 = A_354
      | ~ m1_subset_1(B_355,k1_zfmisc_1(A_354)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_3873])).

tff(c_3929,plain,(
    ! [C_173,B_172] :
      ( v1_xboole_0(C_173)
      | v1_xboole_0(B_172)
      | r2_hidden('#skF_1'(C_173,B_172,C_173),C_173)
      | C_173 = B_172
      | ~ m1_subset_1(C_173,k1_zfmisc_1(C_173))
      | ~ m1_subset_1(B_172,k1_zfmisc_1(C_173)) ) ),
    inference(resolution,[status(thm)],[c_742,c_3903])).

tff(c_3987,plain,(
    ! [C_356,B_357] :
      ( v1_xboole_0(C_356)
      | v1_xboole_0(B_357)
      | r2_hidden('#skF_1'(C_356,B_357,C_356),C_356)
      | C_356 = B_357
      | ~ m1_subset_1(B_357,k1_zfmisc_1(C_356)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_3929])).

tff(c_6,plain,(
    ! [A_5,B_6,C_10] :
      ( ~ r2_hidden('#skF_1'(A_5,B_6,C_10),C_10)
      | ~ r2_hidden('#skF_1'(A_5,B_6,C_10),B_6)
      | C_10 = B_6
      | ~ m1_subset_1(C_10,k1_zfmisc_1(A_5))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4015,plain,(
    ! [C_356,B_357] :
      ( ~ r2_hidden('#skF_1'(C_356,B_357,C_356),B_357)
      | ~ m1_subset_1(C_356,k1_zfmisc_1(C_356))
      | v1_xboole_0(C_356)
      | v1_xboole_0(B_357)
      | C_356 = B_357
      | ~ m1_subset_1(B_357,k1_zfmisc_1(C_356)) ) ),
    inference(resolution,[status(thm)],[c_3987,c_6])).

tff(c_4196,plain,(
    ! [C_360,B_361] :
      ( ~ r2_hidden('#skF_1'(C_360,B_361,C_360),B_361)
      | v1_xboole_0(C_360)
      | v1_xboole_0(B_361)
      | C_360 = B_361
      | ~ m1_subset_1(B_361,k1_zfmisc_1(C_360)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_4015])).

tff(c_4208,plain,(
    ! [C_360] :
      ( v1_xboole_0(C_360)
      | v1_xboole_0('#skF_6')
      | C_360 = '#skF_6'
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(C_360))
      | ~ m1_subset_1('#skF_1'(C_360,'#skF_6',C_360),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_3160,c_4196])).

tff(c_4322,plain,(
    ! [C_362] :
      ( v1_xboole_0(C_362)
      | C_362 = '#skF_6'
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(C_362))
      | ~ m1_subset_1('#skF_1'(C_362,'#skF_6',C_362),'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_4208])).

tff(c_4342,plain,(
    ! [C_208] :
      ( v1_xboole_0(C_208)
      | m1_subset_1('#skF_1'(C_208,'#skF_6',C_208),C_208)
      | C_208 = '#skF_6'
      | ~ m1_subset_1(C_208,k1_zfmisc_1(C_208))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(C_208)) ) ),
    inference(resolution,[status(thm)],[c_1146,c_4322])).

tff(c_4399,plain,(
    ! [C_363] :
      ( v1_xboole_0(C_363)
      | m1_subset_1('#skF_1'(C_363,'#skF_6',C_363),C_363)
      | C_363 = '#skF_6'
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(C_363)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_4342])).

tff(c_3049,plain,(
    ! [B_310] :
      ( r2_hidden(B_310,'#skF_6')
      | ~ m1_subset_1(B_310,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_145,c_3029])).

tff(c_4424,plain,
    ( r2_hidden('#skF_1'(u1_struct_0('#skF_5'),'#skF_6',u1_struct_0('#skF_5')),'#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_5'))
    | u1_struct_0('#skF_5') = '#skF_6'
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_4399,c_3049])).

tff(c_4504,plain,
    ( r2_hidden('#skF_1'(u1_struct_0('#skF_5'),'#skF_6',u1_struct_0('#skF_5')),'#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_5'))
    | u1_struct_0('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_4424])).

tff(c_4505,plain,
    ( r2_hidden('#skF_1'(u1_struct_0('#skF_5'),'#skF_6',u1_struct_0('#skF_5')),'#skF_6')
    | u1_struct_0('#skF_5') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_174,c_4504])).

tff(c_4531,plain,(
    u1_struct_0('#skF_5') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_4505])).

tff(c_309,plain,(
    ! [A_104] :
      ( r2_hidden(A_104,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(A_104,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_304])).

tff(c_1352,plain,(
    ! [B_223,A_224] :
      ( u1_struct_0('#skF_5') = B_223
      | ~ m1_subset_1(B_223,k1_zfmisc_1(A_224))
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_224))
      | v1_xboole_0(B_223)
      | ~ m1_subset_1('#skF_1'(A_224,u1_struct_0('#skF_5'),B_223),B_223)
      | ~ m1_subset_1('#skF_1'(A_224,u1_struct_0('#skF_5'),B_223),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_309,c_1149])).

tff(c_1365,plain,(
    ! [A_5] :
      ( v1_xboole_0(A_5)
      | ~ m1_subset_1('#skF_1'(A_5,u1_struct_0('#skF_5'),A_5),'#skF_6')
      | u1_struct_0('#skF_5') = A_5
      | ~ m1_subset_1(A_5,k1_zfmisc_1(A_5))
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_5)) ) ),
    inference(resolution,[status(thm)],[c_4,c_1352])).

tff(c_1387,plain,(
    ! [A_225] :
      ( v1_xboole_0(A_225)
      | ~ m1_subset_1('#skF_1'(A_225,u1_struct_0('#skF_5'),A_225),'#skF_6')
      | u1_struct_0('#skF_5') = A_225
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_225)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_1365])).

tff(c_1397,plain,
    ( v1_xboole_0('#skF_6')
    | u1_struct_0('#skF_5') = '#skF_6'
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6'))
    | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_4,c_1387])).

tff(c_1404,plain,
    ( v1_xboole_0('#skF_6')
    | u1_struct_0('#skF_5') = '#skF_6'
    | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_1397])).

tff(c_1405,plain,
    ( u1_struct_0('#skF_5') = '#skF_6'
    | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1404])).

tff(c_1406,plain,(
    ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_1405])).

tff(c_4545,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4531,c_1406])).

tff(c_4571,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_4545])).

tff(c_4573,plain,(
    u1_struct_0('#skF_5') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_4505])).

tff(c_4572,plain,(
    r2_hidden('#skF_1'(u1_struct_0('#skF_5'),'#skF_6',u1_struct_0('#skF_5')),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_4505])).

tff(c_4050,plain,(
    ! [C_356,B_357] :
      ( ~ r2_hidden('#skF_1'(C_356,B_357,C_356),B_357)
      | v1_xboole_0(C_356)
      | v1_xboole_0(B_357)
      | C_356 = B_357
      | ~ m1_subset_1(B_357,k1_zfmisc_1(C_356)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_4015])).

tff(c_4649,plain,
    ( v1_xboole_0(u1_struct_0('#skF_5'))
    | v1_xboole_0('#skF_6')
    | u1_struct_0('#skF_5') = '#skF_6'
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_4572,c_4050])).

tff(c_4668,plain,
    ( v1_xboole_0(u1_struct_0('#skF_5'))
    | v1_xboole_0('#skF_6')
    | u1_struct_0('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_4649])).

tff(c_4670,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4573,c_52,c_174,c_4668])).

tff(c_4671,plain,(
    u1_struct_0('#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1405])).

tff(c_146,plain,(
    v1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_4691,plain,(
    v1_subset_1('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4671,c_146])).

tff(c_4696,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_196,c_4691])).

tff(c_4697,plain,(
    ! [A_79] : ~ r2_hidden(A_79,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_167])).

tff(c_4700,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4697,c_145])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:36:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.36/2.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.36/2.28  
% 6.36/2.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.36/2.29  %$ r1_orders_2 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > l1_orders_2 > k1_yellow_0 > #nlpp > u1_struct_0 > k3_yellow_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_5 > #skF_6 > #skF_4
% 6.36/2.29  
% 6.36/2.29  %Foreground sorts:
% 6.36/2.29  
% 6.36/2.29  
% 6.36/2.29  %Background operators:
% 6.36/2.29  
% 6.36/2.29  
% 6.36/2.29  %Foreground operators:
% 6.36/2.29  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.36/2.29  tff(k1_yellow_0, type, k1_yellow_0: ($i * $i) > $i).
% 6.36/2.29  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 6.36/2.29  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 6.36/2.29  tff('#skF_2', type, '#skF_2': $i > $i).
% 6.36/2.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.36/2.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.36/2.29  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 6.36/2.29  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 6.36/2.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.36/2.29  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 6.36/2.29  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 6.36/2.29  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 6.36/2.29  tff('#skF_5', type, '#skF_5': $i).
% 6.36/2.29  tff('#skF_6', type, '#skF_6': $i).
% 6.36/2.29  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 6.36/2.29  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 6.36/2.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.36/2.29  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 6.36/2.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.36/2.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.36/2.29  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 6.36/2.29  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.36/2.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.36/2.29  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 6.36/2.29  tff(v1_yellow_0, type, v1_yellow_0: $i > $o).
% 6.36/2.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.36/2.29  
% 6.67/2.31  tff(f_52, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & ~v1_subset_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc3_subset_1)).
% 6.67/2.31  tff(f_119, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 6.67/2.31  tff(f_148, negated_conjecture, ~(![A]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, A)) & v13_waybel_0(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_subset_1(B, u1_struct_0(A)) <=> ~r2_hidden(k3_yellow_0(A), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_waybel_7)).
% 6.67/2.31  tff(f_71, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 6.67/2.31  tff(f_46, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) <=> r2_hidden(D, C)))) => (B = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_subset_1)).
% 6.67/2.31  tff(f_64, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 6.67/2.31  tff(f_58, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 6.67/2.31  tff(f_32, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 6.67/2.31  tff(f_75, axiom, (![A]: (l1_orders_2(A) => (k3_yellow_0(A) = k1_yellow_0(A, k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_yellow_0)).
% 6.67/2.31  tff(f_79, axiom, (![A, B]: (l1_orders_2(A) => m1_subset_1(k1_yellow_0(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_yellow_0)).
% 6.67/2.31  tff(f_93, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r1_orders_2(A, k3_yellow_0(A), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_yellow_0)).
% 6.67/2.31  tff(f_112, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v13_waybel_0(B, A) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r2_hidden(C, B) & r1_orders_2(A, C, D)) => r2_hidden(D, B))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d20_waybel_0)).
% 6.67/2.31  tff(c_14, plain, (![A_12]: (~v1_subset_1('#skF_2'(A_12), A_12))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.67/2.31  tff(c_16, plain, (![A_12]: (m1_subset_1('#skF_2'(A_12), k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.67/2.31  tff(c_175, plain, (![B_82, A_83]: (v1_subset_1(B_82, A_83) | B_82=A_83 | ~m1_subset_1(B_82, k1_zfmisc_1(A_83)))), inference(cnfTransformation, [status(thm)], [f_119])).
% 6.67/2.31  tff(c_178, plain, (![A_12]: (v1_subset_1('#skF_2'(A_12), A_12) | '#skF_2'(A_12)=A_12)), inference(resolution, [status(thm)], [c_16, c_175])).
% 6.67/2.31  tff(c_184, plain, (![A_12]: ('#skF_2'(A_12)=A_12)), inference(negUnitSimplification, [status(thm)], [c_14, c_178])).
% 6.67/2.31  tff(c_196, plain, (![A_12]: (~v1_subset_1(A_12, A_12))), inference(demodulation, [status(thm), theory('equality')], [c_184, c_14])).
% 6.67/2.31  tff(c_195, plain, (![A_12]: (m1_subset_1(A_12, k1_zfmisc_1(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_184, c_16])).
% 6.67/2.31  tff(c_46, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_148])).
% 6.67/2.31  tff(c_161, plain, (![C_77, B_78, A_79]: (~v1_xboole_0(C_77) | ~m1_subset_1(B_78, k1_zfmisc_1(C_77)) | ~r2_hidden(A_79, B_78))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.67/2.31  tff(c_167, plain, (![A_79]: (~v1_xboole_0(u1_struct_0('#skF_5')) | ~r2_hidden(A_79, '#skF_6'))), inference(resolution, [status(thm)], [c_46, c_161])).
% 6.67/2.31  tff(c_174, plain, (~v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_167])).
% 6.67/2.31  tff(c_692, plain, (![A_171, B_172, C_173]: (r2_hidden('#skF_1'(A_171, B_172, C_173), B_172) | r2_hidden('#skF_1'(A_171, B_172, C_173), C_173) | C_173=B_172 | ~m1_subset_1(C_173, k1_zfmisc_1(A_171)) | ~m1_subset_1(B_172, k1_zfmisc_1(A_171)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.67/2.31  tff(c_246, plain, (![A_94, C_95, B_96]: (m1_subset_1(A_94, C_95) | ~m1_subset_1(B_96, k1_zfmisc_1(C_95)) | ~r2_hidden(A_94, B_96))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.67/2.31  tff(c_251, plain, (![A_94, A_12]: (m1_subset_1(A_94, A_12) | ~r2_hidden(A_94, A_12))), inference(resolution, [status(thm)], [c_195, c_246])).
% 6.67/2.31  tff(c_1060, plain, (![A_206, B_207, C_208]: (m1_subset_1('#skF_1'(A_206, B_207, C_208), C_208) | r2_hidden('#skF_1'(A_206, B_207, C_208), B_207) | C_208=B_207 | ~m1_subset_1(C_208, k1_zfmisc_1(A_206)) | ~m1_subset_1(B_207, k1_zfmisc_1(A_206)))), inference(resolution, [status(thm)], [c_692, c_251])).
% 6.67/2.31  tff(c_1146, plain, (![A_206, B_207, C_208]: (m1_subset_1('#skF_1'(A_206, B_207, C_208), B_207) | m1_subset_1('#skF_1'(A_206, B_207, C_208), C_208) | C_208=B_207 | ~m1_subset_1(C_208, k1_zfmisc_1(A_206)) | ~m1_subset_1(B_207, k1_zfmisc_1(A_206)))), inference(resolution, [status(thm)], [c_1060, c_251])).
% 6.67/2.31  tff(c_52, plain, (~v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_148])).
% 6.67/2.31  tff(c_18, plain, (![A_14, B_15]: (r2_hidden(A_14, B_15) | v1_xboole_0(B_15) | ~m1_subset_1(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.67/2.31  tff(c_187, plain, (![C_84, A_85, B_86]: (r2_hidden(C_84, A_85) | ~r2_hidden(C_84, B_86) | ~m1_subset_1(B_86, k1_zfmisc_1(A_85)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.67/2.31  tff(c_297, plain, (![A_104, A_105, B_106]: (r2_hidden(A_104, A_105) | ~m1_subset_1(B_106, k1_zfmisc_1(A_105)) | v1_xboole_0(B_106) | ~m1_subset_1(A_104, B_106))), inference(resolution, [status(thm)], [c_18, c_187])).
% 6.67/2.31  tff(c_304, plain, (![A_104]: (r2_hidden(A_104, u1_struct_0('#skF_5')) | v1_xboole_0('#skF_6') | ~m1_subset_1(A_104, '#skF_6'))), inference(resolution, [status(thm)], [c_46, c_297])).
% 6.67/2.31  tff(c_310, plain, (![A_107]: (r2_hidden(A_107, u1_struct_0('#skF_5')) | ~m1_subset_1(A_107, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_52, c_304])).
% 6.67/2.31  tff(c_319, plain, (![A_107]: (m1_subset_1(A_107, u1_struct_0('#skF_5')) | ~m1_subset_1(A_107, '#skF_6'))), inference(resolution, [status(thm)], [c_310, c_251])).
% 6.67/2.31  tff(c_48, plain, (v13_waybel_0('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_148])).
% 6.67/2.31  tff(c_93, plain, (![A_62, B_63]: (r2_hidden(A_62, B_63) | v1_xboole_0(B_63) | ~m1_subset_1(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.67/2.31  tff(c_66, plain, (r2_hidden(k3_yellow_0('#skF_5'), '#skF_6') | ~v1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_148])).
% 6.67/2.31  tff(c_85, plain, (~v1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_66])).
% 6.67/2.31  tff(c_72, plain, (v1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~r2_hidden(k3_yellow_0('#skF_5'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_148])).
% 6.67/2.31  tff(c_86, plain, (~r2_hidden(k3_yellow_0('#skF_5'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_85, c_72])).
% 6.67/2.31  tff(c_96, plain, (v1_xboole_0('#skF_6') | ~m1_subset_1(k3_yellow_0('#skF_5'), '#skF_6')), inference(resolution, [status(thm)], [c_93, c_86])).
% 6.67/2.31  tff(c_99, plain, (~m1_subset_1(k3_yellow_0('#skF_5'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_52, c_96])).
% 6.67/2.31  tff(c_114, plain, (![B_69, A_70]: (v1_subset_1(B_69, A_70) | B_69=A_70 | ~m1_subset_1(B_69, k1_zfmisc_1(A_70)))), inference(cnfTransformation, [status(thm)], [f_119])).
% 6.67/2.31  tff(c_120, plain, (v1_subset_1('#skF_6', u1_struct_0('#skF_5')) | u1_struct_0('#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_46, c_114])).
% 6.67/2.31  tff(c_126, plain, (u1_struct_0('#skF_5')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_85, c_120])).
% 6.67/2.31  tff(c_54, plain, (l1_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_148])).
% 6.67/2.31  tff(c_76, plain, (![A_59]: (k1_yellow_0(A_59, k1_xboole_0)=k3_yellow_0(A_59) | ~l1_orders_2(A_59))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.67/2.31  tff(c_80, plain, (k1_yellow_0('#skF_5', k1_xboole_0)=k3_yellow_0('#skF_5')), inference(resolution, [status(thm)], [c_54, c_76])).
% 6.67/2.31  tff(c_87, plain, (![A_60, B_61]: (m1_subset_1(k1_yellow_0(A_60, B_61), u1_struct_0(A_60)) | ~l1_orders_2(A_60))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.67/2.31  tff(c_90, plain, (m1_subset_1(k3_yellow_0('#skF_5'), u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_80, c_87])).
% 6.67/2.31  tff(c_92, plain, (m1_subset_1(k3_yellow_0('#skF_5'), u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_90])).
% 6.67/2.31  tff(c_140, plain, (m1_subset_1(k3_yellow_0('#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_126, c_92])).
% 6.67/2.31  tff(c_144, plain, $false, inference(negUnitSimplification, [status(thm)], [c_99, c_140])).
% 6.67/2.31  tff(c_145, plain, (r2_hidden(k3_yellow_0('#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_66])).
% 6.67/2.31  tff(c_64, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_148])).
% 6.67/2.31  tff(c_58, plain, (v5_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_148])).
% 6.67/2.31  tff(c_56, plain, (v1_yellow_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_148])).
% 6.67/2.31  tff(c_252, plain, (![A_94]: (m1_subset_1(A_94, u1_struct_0('#skF_5')) | ~r2_hidden(A_94, '#skF_6'))), inference(resolution, [status(thm)], [c_46, c_246])).
% 6.67/2.31  tff(c_28, plain, (![A_25, B_27]: (r1_orders_2(A_25, k3_yellow_0(A_25), B_27) | ~m1_subset_1(B_27, u1_struct_0(A_25)) | ~l1_orders_2(A_25) | ~v1_yellow_0(A_25) | ~v5_orders_2(A_25) | v2_struct_0(A_25))), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.67/2.31  tff(c_806, plain, (![D_180, B_181, A_182, C_183]: (r2_hidden(D_180, B_181) | ~r1_orders_2(A_182, C_183, D_180) | ~r2_hidden(C_183, B_181) | ~m1_subset_1(D_180, u1_struct_0(A_182)) | ~m1_subset_1(C_183, u1_struct_0(A_182)) | ~v13_waybel_0(B_181, A_182) | ~m1_subset_1(B_181, k1_zfmisc_1(u1_struct_0(A_182))) | ~l1_orders_2(A_182))), inference(cnfTransformation, [status(thm)], [f_112])).
% 6.67/2.31  tff(c_2954, plain, (![B_307, B_308, A_309]: (r2_hidden(B_307, B_308) | ~r2_hidden(k3_yellow_0(A_309), B_308) | ~m1_subset_1(k3_yellow_0(A_309), u1_struct_0(A_309)) | ~v13_waybel_0(B_308, A_309) | ~m1_subset_1(B_308, k1_zfmisc_1(u1_struct_0(A_309))) | ~m1_subset_1(B_307, u1_struct_0(A_309)) | ~l1_orders_2(A_309) | ~v1_yellow_0(A_309) | ~v5_orders_2(A_309) | v2_struct_0(A_309))), inference(resolution, [status(thm)], [c_28, c_806])).
% 6.67/2.31  tff(c_2963, plain, (![B_307, B_308]: (r2_hidden(B_307, B_308) | ~r2_hidden(k3_yellow_0('#skF_5'), B_308) | ~v13_waybel_0(B_308, '#skF_5') | ~m1_subset_1(B_308, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_307, u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5') | ~v1_yellow_0('#skF_5') | ~v5_orders_2('#skF_5') | v2_struct_0('#skF_5') | ~r2_hidden(k3_yellow_0('#skF_5'), '#skF_6'))), inference(resolution, [status(thm)], [c_252, c_2954])).
% 6.67/2.31  tff(c_2976, plain, (![B_307, B_308]: (r2_hidden(B_307, B_308) | ~r2_hidden(k3_yellow_0('#skF_5'), B_308) | ~v13_waybel_0(B_308, '#skF_5') | ~m1_subset_1(B_308, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_307, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_145, c_58, c_56, c_54, c_2963])).
% 6.67/2.31  tff(c_2982, plain, (![B_310, B_311]: (r2_hidden(B_310, B_311) | ~r2_hidden(k3_yellow_0('#skF_5'), B_311) | ~v13_waybel_0(B_311, '#skF_5') | ~m1_subset_1(B_311, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_310, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_64, c_2976])).
% 6.67/2.31  tff(c_3029, plain, (![B_310]: (r2_hidden(B_310, '#skF_6') | ~r2_hidden(k3_yellow_0('#skF_5'), '#skF_6') | ~v13_waybel_0('#skF_6', '#skF_5') | ~m1_subset_1(B_310, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_46, c_2982])).
% 6.67/2.31  tff(c_3050, plain, (![B_312]: (r2_hidden(B_312, '#skF_6') | ~m1_subset_1(B_312, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_145, c_3029])).
% 6.67/2.31  tff(c_3160, plain, (![A_107]: (r2_hidden(A_107, '#skF_6') | ~m1_subset_1(A_107, '#skF_6'))), inference(resolution, [status(thm)], [c_319, c_3050])).
% 6.67/2.31  tff(c_742, plain, (![A_171, B_172, C_173]: (m1_subset_1('#skF_1'(A_171, B_172, C_173), B_172) | r2_hidden('#skF_1'(A_171, B_172, C_173), C_173) | C_173=B_172 | ~m1_subset_1(C_173, k1_zfmisc_1(A_171)) | ~m1_subset_1(B_172, k1_zfmisc_1(A_171)))), inference(resolution, [status(thm)], [c_692, c_251])).
% 6.67/2.31  tff(c_4, plain, (![A_5, B_6, C_10]: (m1_subset_1('#skF_1'(A_5, B_6, C_10), A_5) | C_10=B_6 | ~m1_subset_1(C_10, k1_zfmisc_1(A_5)) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.67/2.31  tff(c_616, plain, (![A_159, B_160, C_161]: (~r2_hidden('#skF_1'(A_159, B_160, C_161), C_161) | ~r2_hidden('#skF_1'(A_159, B_160, C_161), B_160) | C_161=B_160 | ~m1_subset_1(C_161, k1_zfmisc_1(A_159)) | ~m1_subset_1(B_160, k1_zfmisc_1(A_159)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.67/2.31  tff(c_1149, plain, (![A_209, B_210, B_211]: (~r2_hidden('#skF_1'(A_209, B_210, B_211), B_210) | B_211=B_210 | ~m1_subset_1(B_211, k1_zfmisc_1(A_209)) | ~m1_subset_1(B_210, k1_zfmisc_1(A_209)) | v1_xboole_0(B_211) | ~m1_subset_1('#skF_1'(A_209, B_210, B_211), B_211))), inference(resolution, [status(thm)], [c_18, c_616])).
% 6.67/2.31  tff(c_3848, plain, (![B_352, B_351, A_353]: (B_352=B_351 | ~m1_subset_1(B_351, k1_zfmisc_1(A_353)) | ~m1_subset_1(B_352, k1_zfmisc_1(A_353)) | v1_xboole_0(B_351) | ~m1_subset_1('#skF_1'(A_353, B_352, B_351), B_351) | v1_xboole_0(B_352) | ~m1_subset_1('#skF_1'(A_353, B_352, B_351), B_352))), inference(resolution, [status(thm)], [c_18, c_1149])).
% 6.67/2.31  tff(c_3873, plain, (![A_5, B_6]: (v1_xboole_0(A_5) | v1_xboole_0(B_6) | ~m1_subset_1('#skF_1'(A_5, B_6, A_5), B_6) | B_6=A_5 | ~m1_subset_1(A_5, k1_zfmisc_1(A_5)) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(resolution, [status(thm)], [c_4, c_3848])).
% 6.67/2.31  tff(c_3903, plain, (![A_354, B_355]: (v1_xboole_0(A_354) | v1_xboole_0(B_355) | ~m1_subset_1('#skF_1'(A_354, B_355, A_354), B_355) | B_355=A_354 | ~m1_subset_1(B_355, k1_zfmisc_1(A_354)))), inference(demodulation, [status(thm), theory('equality')], [c_195, c_3873])).
% 6.67/2.31  tff(c_3929, plain, (![C_173, B_172]: (v1_xboole_0(C_173) | v1_xboole_0(B_172) | r2_hidden('#skF_1'(C_173, B_172, C_173), C_173) | C_173=B_172 | ~m1_subset_1(C_173, k1_zfmisc_1(C_173)) | ~m1_subset_1(B_172, k1_zfmisc_1(C_173)))), inference(resolution, [status(thm)], [c_742, c_3903])).
% 6.67/2.31  tff(c_3987, plain, (![C_356, B_357]: (v1_xboole_0(C_356) | v1_xboole_0(B_357) | r2_hidden('#skF_1'(C_356, B_357, C_356), C_356) | C_356=B_357 | ~m1_subset_1(B_357, k1_zfmisc_1(C_356)))), inference(demodulation, [status(thm), theory('equality')], [c_195, c_3929])).
% 6.67/2.31  tff(c_6, plain, (![A_5, B_6, C_10]: (~r2_hidden('#skF_1'(A_5, B_6, C_10), C_10) | ~r2_hidden('#skF_1'(A_5, B_6, C_10), B_6) | C_10=B_6 | ~m1_subset_1(C_10, k1_zfmisc_1(A_5)) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.67/2.31  tff(c_4015, plain, (![C_356, B_357]: (~r2_hidden('#skF_1'(C_356, B_357, C_356), B_357) | ~m1_subset_1(C_356, k1_zfmisc_1(C_356)) | v1_xboole_0(C_356) | v1_xboole_0(B_357) | C_356=B_357 | ~m1_subset_1(B_357, k1_zfmisc_1(C_356)))), inference(resolution, [status(thm)], [c_3987, c_6])).
% 6.67/2.31  tff(c_4196, plain, (![C_360, B_361]: (~r2_hidden('#skF_1'(C_360, B_361, C_360), B_361) | v1_xboole_0(C_360) | v1_xboole_0(B_361) | C_360=B_361 | ~m1_subset_1(B_361, k1_zfmisc_1(C_360)))), inference(demodulation, [status(thm), theory('equality')], [c_195, c_4015])).
% 6.67/2.31  tff(c_4208, plain, (![C_360]: (v1_xboole_0(C_360) | v1_xboole_0('#skF_6') | C_360='#skF_6' | ~m1_subset_1('#skF_6', k1_zfmisc_1(C_360)) | ~m1_subset_1('#skF_1'(C_360, '#skF_6', C_360), '#skF_6'))), inference(resolution, [status(thm)], [c_3160, c_4196])).
% 6.67/2.31  tff(c_4322, plain, (![C_362]: (v1_xboole_0(C_362) | C_362='#skF_6' | ~m1_subset_1('#skF_6', k1_zfmisc_1(C_362)) | ~m1_subset_1('#skF_1'(C_362, '#skF_6', C_362), '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_52, c_4208])).
% 6.67/2.31  tff(c_4342, plain, (![C_208]: (v1_xboole_0(C_208) | m1_subset_1('#skF_1'(C_208, '#skF_6', C_208), C_208) | C_208='#skF_6' | ~m1_subset_1(C_208, k1_zfmisc_1(C_208)) | ~m1_subset_1('#skF_6', k1_zfmisc_1(C_208)))), inference(resolution, [status(thm)], [c_1146, c_4322])).
% 6.67/2.31  tff(c_4399, plain, (![C_363]: (v1_xboole_0(C_363) | m1_subset_1('#skF_1'(C_363, '#skF_6', C_363), C_363) | C_363='#skF_6' | ~m1_subset_1('#skF_6', k1_zfmisc_1(C_363)))), inference(demodulation, [status(thm), theory('equality')], [c_195, c_4342])).
% 6.67/2.31  tff(c_3049, plain, (![B_310]: (r2_hidden(B_310, '#skF_6') | ~m1_subset_1(B_310, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_145, c_3029])).
% 6.67/2.31  tff(c_4424, plain, (r2_hidden('#skF_1'(u1_struct_0('#skF_5'), '#skF_6', u1_struct_0('#skF_5')), '#skF_6') | v1_xboole_0(u1_struct_0('#skF_5')) | u1_struct_0('#skF_5')='#skF_6' | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_4399, c_3049])).
% 6.67/2.31  tff(c_4504, plain, (r2_hidden('#skF_1'(u1_struct_0('#skF_5'), '#skF_6', u1_struct_0('#skF_5')), '#skF_6') | v1_xboole_0(u1_struct_0('#skF_5')) | u1_struct_0('#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_4424])).
% 6.67/2.31  tff(c_4505, plain, (r2_hidden('#skF_1'(u1_struct_0('#skF_5'), '#skF_6', u1_struct_0('#skF_5')), '#skF_6') | u1_struct_0('#skF_5')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_174, c_4504])).
% 6.67/2.31  tff(c_4531, plain, (u1_struct_0('#skF_5')='#skF_6'), inference(splitLeft, [status(thm)], [c_4505])).
% 6.67/2.31  tff(c_309, plain, (![A_104]: (r2_hidden(A_104, u1_struct_0('#skF_5')) | ~m1_subset_1(A_104, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_52, c_304])).
% 6.67/2.31  tff(c_1352, plain, (![B_223, A_224]: (u1_struct_0('#skF_5')=B_223 | ~m1_subset_1(B_223, k1_zfmisc_1(A_224)) | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(A_224)) | v1_xboole_0(B_223) | ~m1_subset_1('#skF_1'(A_224, u1_struct_0('#skF_5'), B_223), B_223) | ~m1_subset_1('#skF_1'(A_224, u1_struct_0('#skF_5'), B_223), '#skF_6'))), inference(resolution, [status(thm)], [c_309, c_1149])).
% 6.67/2.31  tff(c_1365, plain, (![A_5]: (v1_xboole_0(A_5) | ~m1_subset_1('#skF_1'(A_5, u1_struct_0('#skF_5'), A_5), '#skF_6') | u1_struct_0('#skF_5')=A_5 | ~m1_subset_1(A_5, k1_zfmisc_1(A_5)) | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(A_5)))), inference(resolution, [status(thm)], [c_4, c_1352])).
% 6.67/2.31  tff(c_1387, plain, (![A_225]: (v1_xboole_0(A_225) | ~m1_subset_1('#skF_1'(A_225, u1_struct_0('#skF_5'), A_225), '#skF_6') | u1_struct_0('#skF_5')=A_225 | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(A_225)))), inference(demodulation, [status(thm), theory('equality')], [c_195, c_1365])).
% 6.67/2.31  tff(c_1397, plain, (v1_xboole_0('#skF_6') | u1_struct_0('#skF_5')='#skF_6' | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6')) | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1('#skF_6'))), inference(resolution, [status(thm)], [c_4, c_1387])).
% 6.67/2.31  tff(c_1404, plain, (v1_xboole_0('#skF_6') | u1_struct_0('#skF_5')='#skF_6' | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_195, c_1397])).
% 6.67/2.31  tff(c_1405, plain, (u1_struct_0('#skF_5')='#skF_6' | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_52, c_1404])).
% 6.67/2.31  tff(c_1406, plain, (~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_1405])).
% 6.67/2.31  tff(c_4545, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_4531, c_1406])).
% 6.67/2.31  tff(c_4571, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_195, c_4545])).
% 6.67/2.31  tff(c_4573, plain, (u1_struct_0('#skF_5')!='#skF_6'), inference(splitRight, [status(thm)], [c_4505])).
% 6.67/2.31  tff(c_4572, plain, (r2_hidden('#skF_1'(u1_struct_0('#skF_5'), '#skF_6', u1_struct_0('#skF_5')), '#skF_6')), inference(splitRight, [status(thm)], [c_4505])).
% 6.67/2.31  tff(c_4050, plain, (![C_356, B_357]: (~r2_hidden('#skF_1'(C_356, B_357, C_356), B_357) | v1_xboole_0(C_356) | v1_xboole_0(B_357) | C_356=B_357 | ~m1_subset_1(B_357, k1_zfmisc_1(C_356)))), inference(demodulation, [status(thm), theory('equality')], [c_195, c_4015])).
% 6.67/2.31  tff(c_4649, plain, (v1_xboole_0(u1_struct_0('#skF_5')) | v1_xboole_0('#skF_6') | u1_struct_0('#skF_5')='#skF_6' | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_4572, c_4050])).
% 6.67/2.31  tff(c_4668, plain, (v1_xboole_0(u1_struct_0('#skF_5')) | v1_xboole_0('#skF_6') | u1_struct_0('#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_4649])).
% 6.67/2.31  tff(c_4670, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4573, c_52, c_174, c_4668])).
% 6.67/2.31  tff(c_4671, plain, (u1_struct_0('#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_1405])).
% 6.67/2.31  tff(c_146, plain, (v1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_66])).
% 6.67/2.31  tff(c_4691, plain, (v1_subset_1('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4671, c_146])).
% 6.67/2.31  tff(c_4696, plain, $false, inference(negUnitSimplification, [status(thm)], [c_196, c_4691])).
% 6.67/2.31  tff(c_4697, plain, (![A_79]: (~r2_hidden(A_79, '#skF_6'))), inference(splitRight, [status(thm)], [c_167])).
% 6.67/2.31  tff(c_4700, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4697, c_145])).
% 6.67/2.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.67/2.31  
% 6.67/2.31  Inference rules
% 6.67/2.31  ----------------------
% 6.67/2.31  #Ref     : 0
% 6.67/2.31  #Sup     : 937
% 6.67/2.31  #Fact    : 8
% 6.67/2.31  #Define  : 0
% 6.67/2.31  #Split   : 14
% 6.67/2.31  #Chain   : 0
% 6.67/2.31  #Close   : 0
% 6.67/2.31  
% 6.67/2.31  Ordering : KBO
% 6.67/2.31  
% 6.67/2.31  Simplification rules
% 6.67/2.31  ----------------------
% 6.67/2.31  #Subsume      : 216
% 6.67/2.31  #Demod        : 257
% 6.67/2.31  #Tautology    : 112
% 6.67/2.31  #SimpNegUnit  : 53
% 6.67/2.31  #BackRed      : 62
% 6.67/2.31  
% 6.67/2.31  #Partial instantiations: 0
% 6.67/2.31  #Strategies tried      : 1
% 6.67/2.31  
% 6.67/2.31  Timing (in seconds)
% 6.67/2.31  ----------------------
% 6.67/2.31  Preprocessing        : 0.34
% 6.67/2.31  Parsing              : 0.18
% 6.67/2.31  CNF conversion       : 0.02
% 6.67/2.31  Main loop            : 1.18
% 6.67/2.31  Inferencing          : 0.37
% 6.67/2.31  Reduction            : 0.30
% 6.67/2.31  Demodulation         : 0.20
% 6.67/2.31  BG Simplification    : 0.05
% 6.67/2.31  Subsumption          : 0.38
% 6.67/2.31  Abstraction          : 0.06
% 6.67/2.31  MUC search           : 0.00
% 6.67/2.31  Cooper               : 0.00
% 6.67/2.31  Total                : 1.57
% 6.67/2.31  Index Insertion      : 0.00
% 6.67/2.31  Index Deletion       : 0.00
% 6.67/2.31  Index Matching       : 0.00
% 6.67/2.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
