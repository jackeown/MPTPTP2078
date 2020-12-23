%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:17 EST 2020

% Result     : Theorem 3.49s
% Output     : CNFRefutation 3.49s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 292 expanded)
%              Number of leaves         :   38 ( 126 expanded)
%              Depth                    :   20
%              Number of atoms          :  420 (1634 expanded)
%              Number of equality atoms :    3 (  82 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_waybel_0 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_xboole_0 > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k2_relset_1 > u1_waybel_0 > k2_pre_topc > k10_yellow_6 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k10_yellow_6,type,(
    k10_yellow_6: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v7_waybel_0,type,(
    v7_waybel_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_waybel_0,type,(
    r1_waybel_0: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(u1_waybel_0,type,(
    u1_waybel_0: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(l1_waybel_0,type,(
    l1_waybel_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_195,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & v4_orders_2(C)
                  & v7_waybel_0(C)
                  & l1_waybel_0(C,A) )
               => ( r2_hidden(B,k10_yellow_6(A,C))
                 => ! [D] :
                      ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                     => ( D = k2_relset_1(u1_struct_0(C),u1_struct_0(A),u1_waybel_0(A,C))
                       => r2_hidden(B,k2_pre_topc(A,D)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_waybel_9)).

tff(f_35,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_165,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_waybel_0(B,A) )
         => r1_waybel_0(A,B,k2_relset_1(u1_struct_0(B),u1_struct_0(A),u1_waybel_0(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_9)).

tff(f_60,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r2_hidden(C,k2_pre_topc(A,B))
              <=> ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                   => ~ ( v3_pre_topc(D,A)
                        & r2_hidden(C,D)
                        & r1_xboole_0(B,D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_tops_1)).

tff(f_129,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & v4_orders_2(B)
        & v7_waybel_0(B)
        & l1_waybel_0(B,A) )
     => m1_subset_1(k10_yellow_6(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_yellow_6)).

tff(f_79,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( ( v3_pre_topc(B,A)
                  & r2_hidden(C,B) )
               => m1_connsp_2(B,A,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_connsp_2)).

tff(f_111,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v4_orders_2(B)
            & v7_waybel_0(B)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = k10_yellow_6(A,B)
              <=> ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( r2_hidden(D,C)
                    <=> ! [E] :
                          ( m1_connsp_2(E,A,D)
                         => r1_waybel_0(A,B,E) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_yellow_6)).

tff(f_152,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v4_orders_2(B)
            & v7_waybel_0(B)
            & l1_waybel_0(B,A) )
         => ! [C,D] :
              ~ ( r1_waybel_0(A,B,C)
                & r1_waybel_0(A,B,D)
                & r1_xboole_0(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_yellow_6)).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_56,plain,(
    v4_orders_2('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_54,plain,(
    v7_waybel_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_52,plain,(
    l1_waybel_0('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_62,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_4,plain,(
    ! [A_4] :
      ( l1_struct_0(A_4)
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_46,plain,(
    k2_relset_1(u1_struct_0('#skF_7'),u1_struct_0('#skF_5'),u1_waybel_0('#skF_5','#skF_7')) = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_77,plain,(
    ! [A_150,B_151] :
      ( r1_waybel_0(A_150,B_151,k2_relset_1(u1_struct_0(B_151),u1_struct_0(A_150),u1_waybel_0(A_150,B_151)))
      | ~ l1_waybel_0(B_151,A_150)
      | v2_struct_0(B_151)
      | ~ l1_struct_0(A_150)
      | v2_struct_0(A_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_80,plain,
    ( r1_waybel_0('#skF_5','#skF_7','#skF_8')
    | ~ l1_waybel_0('#skF_7','#skF_5')
    | v2_struct_0('#skF_7')
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_77])).

tff(c_82,plain,
    ( r1_waybel_0('#skF_5','#skF_7','#skF_8')
    | v2_struct_0('#skF_7')
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_80])).

tff(c_83,plain,
    ( r1_waybel_0('#skF_5','#skF_7','#skF_8')
    | ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_58,c_82])).

tff(c_84,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_83])).

tff(c_87,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_84])).

tff(c_91,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_87])).

tff(c_92,plain,(
    r1_waybel_0('#skF_5','#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_50,plain,(
    r2_hidden('#skF_6',k10_yellow_6('#skF_5','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_44,plain,(
    ~ r2_hidden('#skF_6',k2_pre_topc('#skF_5','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_60,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_64,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_48,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_167,plain,(
    ! [A_174,B_175,C_176] :
      ( v3_pre_topc('#skF_1'(A_174,B_175,C_176),A_174)
      | r2_hidden(C_176,k2_pre_topc(A_174,B_175))
      | ~ m1_subset_1(C_176,u1_struct_0(A_174))
      | ~ m1_subset_1(B_175,k1_zfmisc_1(u1_struct_0(A_174)))
      | ~ l1_pre_topc(A_174)
      | ~ v2_pre_topc(A_174)
      | v2_struct_0(A_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_171,plain,(
    ! [C_176] :
      ( v3_pre_topc('#skF_1'('#skF_5','#skF_8',C_176),'#skF_5')
      | r2_hidden(C_176,k2_pre_topc('#skF_5','#skF_8'))
      | ~ m1_subset_1(C_176,u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_48,c_167])).

tff(c_175,plain,(
    ! [C_176] :
      ( v3_pre_topc('#skF_1'('#skF_5','#skF_8',C_176),'#skF_5')
      | r2_hidden(C_176,k2_pre_topc('#skF_5','#skF_8'))
      | ~ m1_subset_1(C_176,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_171])).

tff(c_176,plain,(
    ! [C_176] :
      ( v3_pre_topc('#skF_1'('#skF_5','#skF_8',C_176),'#skF_5')
      | r2_hidden(C_176,k2_pre_topc('#skF_5','#skF_8'))
      | ~ m1_subset_1(C_176,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_175])).

tff(c_14,plain,(
    ! [A_5,B_17,C_23] :
      ( m1_subset_1('#skF_1'(A_5,B_17,C_23),k1_zfmisc_1(u1_struct_0(A_5)))
      | r2_hidden(C_23,k2_pre_topc(A_5,B_17))
      | ~ m1_subset_1(C_23,u1_struct_0(A_5))
      | ~ m1_subset_1(B_17,k1_zfmisc_1(u1_struct_0(A_5)))
      | ~ l1_pre_topc(A_5)
      | ~ v2_pre_topc(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_133,plain,(
    ! [B_165,A_166,C_167] :
      ( r1_xboole_0(B_165,'#skF_1'(A_166,B_165,C_167))
      | r2_hidden(C_167,k2_pre_topc(A_166,B_165))
      | ~ m1_subset_1(C_167,u1_struct_0(A_166))
      | ~ m1_subset_1(B_165,k1_zfmisc_1(u1_struct_0(A_166)))
      | ~ l1_pre_topc(A_166)
      | ~ v2_pre_topc(A_166)
      | v2_struct_0(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_137,plain,(
    ! [C_167] :
      ( r1_xboole_0('#skF_8','#skF_1'('#skF_5','#skF_8',C_167))
      | r2_hidden(C_167,k2_pre_topc('#skF_5','#skF_8'))
      | ~ m1_subset_1(C_167,u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_48,c_133])).

tff(c_141,plain,(
    ! [C_167] :
      ( r1_xboole_0('#skF_8','#skF_1'('#skF_5','#skF_8',C_167))
      | r2_hidden(C_167,k2_pre_topc('#skF_5','#skF_8'))
      | ~ m1_subset_1(C_167,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_137])).

tff(c_144,plain,(
    ! [C_168] :
      ( r1_xboole_0('#skF_8','#skF_1'('#skF_5','#skF_8',C_168))
      | r2_hidden(C_168,k2_pre_topc('#skF_5','#skF_8'))
      | ~ m1_subset_1(C_168,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_141])).

tff(c_147,plain,
    ( r1_xboole_0('#skF_8','#skF_1'('#skF_5','#skF_8','#skF_6'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_144,c_44])).

tff(c_150,plain,(
    r1_xboole_0('#skF_8','#skF_1'('#skF_5','#skF_8','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_147])).

tff(c_260,plain,(
    ! [B_197,D_198,C_199,A_200] :
      ( ~ r1_xboole_0(B_197,D_198)
      | ~ r2_hidden(C_199,D_198)
      | ~ v3_pre_topc(D_198,A_200)
      | ~ m1_subset_1(D_198,k1_zfmisc_1(u1_struct_0(A_200)))
      | ~ r2_hidden(C_199,k2_pre_topc(A_200,B_197))
      | ~ m1_subset_1(C_199,u1_struct_0(A_200))
      | ~ m1_subset_1(B_197,k1_zfmisc_1(u1_struct_0(A_200)))
      | ~ l1_pre_topc(A_200)
      | ~ v2_pre_topc(A_200)
      | v2_struct_0(A_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_325,plain,(
    ! [C_225,A_226] :
      ( ~ r2_hidden(C_225,'#skF_1'('#skF_5','#skF_8','#skF_6'))
      | ~ v3_pre_topc('#skF_1'('#skF_5','#skF_8','#skF_6'),A_226)
      | ~ m1_subset_1('#skF_1'('#skF_5','#skF_8','#skF_6'),k1_zfmisc_1(u1_struct_0(A_226)))
      | ~ r2_hidden(C_225,k2_pre_topc(A_226,'#skF_8'))
      | ~ m1_subset_1(C_225,u1_struct_0(A_226))
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0(A_226)))
      | ~ l1_pre_topc(A_226)
      | ~ v2_pre_topc(A_226)
      | v2_struct_0(A_226) ) ),
    inference(resolution,[status(thm)],[c_150,c_260])).

tff(c_328,plain,(
    ! [C_225] :
      ( ~ r2_hidden(C_225,'#skF_1'('#skF_5','#skF_8','#skF_6'))
      | ~ v3_pre_topc('#skF_1'('#skF_5','#skF_8','#skF_6'),'#skF_5')
      | ~ r2_hidden(C_225,k2_pre_topc('#skF_5','#skF_8'))
      | ~ m1_subset_1(C_225,u1_struct_0('#skF_5'))
      | r2_hidden('#skF_6',k2_pre_topc('#skF_5','#skF_8'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_14,c_325])).

tff(c_331,plain,(
    ! [C_225] :
      ( ~ r2_hidden(C_225,'#skF_1'('#skF_5','#skF_8','#skF_6'))
      | ~ v3_pre_topc('#skF_1'('#skF_5','#skF_8','#skF_6'),'#skF_5')
      | ~ r2_hidden(C_225,k2_pre_topc('#skF_5','#skF_8'))
      | ~ m1_subset_1(C_225,u1_struct_0('#skF_5'))
      | r2_hidden('#skF_6',k2_pre_topc('#skF_5','#skF_8'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_48,c_60,c_328])).

tff(c_332,plain,(
    ! [C_225] :
      ( ~ r2_hidden(C_225,'#skF_1'('#skF_5','#skF_8','#skF_6'))
      | ~ v3_pre_topc('#skF_1'('#skF_5','#skF_8','#skF_6'),'#skF_5')
      | ~ r2_hidden(C_225,k2_pre_topc('#skF_5','#skF_8'))
      | ~ m1_subset_1(C_225,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_44,c_331])).

tff(c_333,plain,(
    ~ v3_pre_topc('#skF_1'('#skF_5','#skF_8','#skF_6'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_332])).

tff(c_354,plain,
    ( r2_hidden('#skF_6',k2_pre_topc('#skF_5','#skF_8'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_176,c_333])).

tff(c_357,plain,(
    r2_hidden('#skF_6',k2_pre_topc('#skF_5','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_354])).

tff(c_359,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_357])).

tff(c_361,plain,(
    v3_pre_topc('#skF_1'('#skF_5','#skF_8','#skF_6'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_332])).

tff(c_178,plain,(
    ! [C_178,A_179,B_180] :
      ( r2_hidden(C_178,'#skF_1'(A_179,B_180,C_178))
      | r2_hidden(C_178,k2_pre_topc(A_179,B_180))
      | ~ m1_subset_1(C_178,u1_struct_0(A_179))
      | ~ m1_subset_1(B_180,k1_zfmisc_1(u1_struct_0(A_179)))
      | ~ l1_pre_topc(A_179)
      | ~ v2_pre_topc(A_179)
      | v2_struct_0(A_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_182,plain,(
    ! [C_178] :
      ( r2_hidden(C_178,'#skF_1'('#skF_5','#skF_8',C_178))
      | r2_hidden(C_178,k2_pre_topc('#skF_5','#skF_8'))
      | ~ m1_subset_1(C_178,u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_48,c_178])).

tff(c_186,plain,(
    ! [C_178] :
      ( r2_hidden(C_178,'#skF_1'('#skF_5','#skF_8',C_178))
      | r2_hidden(C_178,k2_pre_topc('#skF_5','#skF_8'))
      | ~ m1_subset_1(C_178,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_182])).

tff(c_188,plain,(
    ! [C_181] :
      ( r2_hidden(C_181,'#skF_1'('#skF_5','#skF_8',C_181))
      | r2_hidden(C_181,k2_pre_topc('#skF_5','#skF_8'))
      | ~ m1_subset_1(C_181,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_186])).

tff(c_191,plain,
    ( r2_hidden('#skF_6','#skF_1'('#skF_5','#skF_8','#skF_6'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_188,c_44])).

tff(c_194,plain,(
    r2_hidden('#skF_6','#skF_1'('#skF_5','#skF_8','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_191])).

tff(c_93,plain,(
    l1_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_38,plain,(
    ! [A_118,B_119] :
      ( m1_subset_1(k10_yellow_6(A_118,B_119),k1_zfmisc_1(u1_struct_0(A_118)))
      | ~ l1_waybel_0(B_119,A_118)
      | ~ v7_waybel_0(B_119)
      | ~ v4_orders_2(B_119)
      | v2_struct_0(B_119)
      | ~ l1_pre_topc(A_118)
      | ~ v2_pre_topc(A_118)
      | v2_struct_0(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_195,plain,(
    ! [A_182,B_183,C_184] :
      ( m1_subset_1('#skF_1'(A_182,B_183,C_184),k1_zfmisc_1(u1_struct_0(A_182)))
      | r2_hidden(C_184,k2_pre_topc(A_182,B_183))
      | ~ m1_subset_1(C_184,u1_struct_0(A_182))
      | ~ m1_subset_1(B_183,k1_zfmisc_1(u1_struct_0(A_182)))
      | ~ l1_pre_topc(A_182)
      | ~ v2_pre_topc(A_182)
      | v2_struct_0(A_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_107,plain,(
    ! [B_161,A_162,C_163] :
      ( m1_connsp_2(B_161,A_162,C_163)
      | ~ r2_hidden(C_163,B_161)
      | ~ v3_pre_topc(B_161,A_162)
      | ~ m1_subset_1(C_163,u1_struct_0(A_162))
      | ~ m1_subset_1(B_161,k1_zfmisc_1(u1_struct_0(A_162)))
      | ~ l1_pre_topc(A_162)
      | ~ v2_pre_topc(A_162)
      | v2_struct_0(A_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_111,plain,(
    ! [B_161] :
      ( m1_connsp_2(B_161,'#skF_5','#skF_6')
      | ~ r2_hidden('#skF_6',B_161)
      | ~ v3_pre_topc(B_161,'#skF_5')
      | ~ m1_subset_1(B_161,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_60,c_107])).

tff(c_118,plain,(
    ! [B_161] :
      ( m1_connsp_2(B_161,'#skF_5','#skF_6')
      | ~ r2_hidden('#skF_6',B_161)
      | ~ v3_pre_topc(B_161,'#skF_5')
      | ~ m1_subset_1(B_161,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_111])).

tff(c_119,plain,(
    ! [B_161] :
      ( m1_connsp_2(B_161,'#skF_5','#skF_6')
      | ~ r2_hidden('#skF_6',B_161)
      | ~ v3_pre_topc(B_161,'#skF_5')
      | ~ m1_subset_1(B_161,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_118])).

tff(c_208,plain,(
    ! [B_183,C_184] :
      ( m1_connsp_2('#skF_1'('#skF_5',B_183,C_184),'#skF_5','#skF_6')
      | ~ r2_hidden('#skF_6','#skF_1'('#skF_5',B_183,C_184))
      | ~ v3_pre_topc('#skF_1'('#skF_5',B_183,C_184),'#skF_5')
      | r2_hidden(C_184,k2_pre_topc('#skF_5',B_183))
      | ~ m1_subset_1(C_184,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_183,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_195,c_119])).

tff(c_220,plain,(
    ! [B_183,C_184] :
      ( m1_connsp_2('#skF_1'('#skF_5',B_183,C_184),'#skF_5','#skF_6')
      | ~ r2_hidden('#skF_6','#skF_1'('#skF_5',B_183,C_184))
      | ~ v3_pre_topc('#skF_1'('#skF_5',B_183,C_184),'#skF_5')
      | r2_hidden(C_184,k2_pre_topc('#skF_5',B_183))
      | ~ m1_subset_1(C_184,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_183,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_208])).

tff(c_241,plain,(
    ! [B_194,C_195] :
      ( m1_connsp_2('#skF_1'('#skF_5',B_194,C_195),'#skF_5','#skF_6')
      | ~ r2_hidden('#skF_6','#skF_1'('#skF_5',B_194,C_195))
      | ~ v3_pre_topc('#skF_1'('#skF_5',B_194,C_195),'#skF_5')
      | r2_hidden(C_195,k2_pre_topc('#skF_5',B_194))
      | ~ m1_subset_1(C_195,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_194,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_220])).

tff(c_258,plain,(
    ! [C_195] :
      ( m1_connsp_2('#skF_1'('#skF_5','#skF_8',C_195),'#skF_5','#skF_6')
      | ~ r2_hidden('#skF_6','#skF_1'('#skF_5','#skF_8',C_195))
      | ~ v3_pre_topc('#skF_1'('#skF_5','#skF_8',C_195),'#skF_5')
      | r2_hidden(C_195,k2_pre_topc('#skF_5','#skF_8'))
      | ~ m1_subset_1(C_195,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_48,c_241])).

tff(c_296,plain,(
    ! [A_218,B_219,E_220,D_221] :
      ( r1_waybel_0(A_218,B_219,E_220)
      | ~ m1_connsp_2(E_220,A_218,D_221)
      | ~ r2_hidden(D_221,k10_yellow_6(A_218,B_219))
      | ~ m1_subset_1(D_221,u1_struct_0(A_218))
      | ~ m1_subset_1(k10_yellow_6(A_218,B_219),k1_zfmisc_1(u1_struct_0(A_218)))
      | ~ l1_waybel_0(B_219,A_218)
      | ~ v7_waybel_0(B_219)
      | ~ v4_orders_2(B_219)
      | v2_struct_0(B_219)
      | ~ l1_pre_topc(A_218)
      | ~ v2_pre_topc(A_218)
      | v2_struct_0(A_218) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_300,plain,(
    ! [B_219,C_195] :
      ( r1_waybel_0('#skF_5',B_219,'#skF_1'('#skF_5','#skF_8',C_195))
      | ~ r2_hidden('#skF_6',k10_yellow_6('#skF_5',B_219))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
      | ~ m1_subset_1(k10_yellow_6('#skF_5',B_219),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_waybel_0(B_219,'#skF_5')
      | ~ v7_waybel_0(B_219)
      | ~ v4_orders_2(B_219)
      | v2_struct_0(B_219)
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r2_hidden('#skF_6','#skF_1'('#skF_5','#skF_8',C_195))
      | ~ v3_pre_topc('#skF_1'('#skF_5','#skF_8',C_195),'#skF_5')
      | r2_hidden(C_195,k2_pre_topc('#skF_5','#skF_8'))
      | ~ m1_subset_1(C_195,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_258,c_296])).

tff(c_311,plain,(
    ! [B_219,C_195] :
      ( r1_waybel_0('#skF_5',B_219,'#skF_1'('#skF_5','#skF_8',C_195))
      | ~ r2_hidden('#skF_6',k10_yellow_6('#skF_5',B_219))
      | ~ m1_subset_1(k10_yellow_6('#skF_5',B_219),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_waybel_0(B_219,'#skF_5')
      | ~ v7_waybel_0(B_219)
      | ~ v4_orders_2(B_219)
      | v2_struct_0(B_219)
      | v2_struct_0('#skF_5')
      | ~ r2_hidden('#skF_6','#skF_1'('#skF_5','#skF_8',C_195))
      | ~ v3_pre_topc('#skF_1'('#skF_5','#skF_8',C_195),'#skF_5')
      | r2_hidden(C_195,k2_pre_topc('#skF_5','#skF_8'))
      | ~ m1_subset_1(C_195,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_300])).

tff(c_504,plain,(
    ! [B_284,C_285] :
      ( r1_waybel_0('#skF_5',B_284,'#skF_1'('#skF_5','#skF_8',C_285))
      | ~ r2_hidden('#skF_6',k10_yellow_6('#skF_5',B_284))
      | ~ m1_subset_1(k10_yellow_6('#skF_5',B_284),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_waybel_0(B_284,'#skF_5')
      | ~ v7_waybel_0(B_284)
      | ~ v4_orders_2(B_284)
      | v2_struct_0(B_284)
      | ~ r2_hidden('#skF_6','#skF_1'('#skF_5','#skF_8',C_285))
      | ~ v3_pre_topc('#skF_1'('#skF_5','#skF_8',C_285),'#skF_5')
      | r2_hidden(C_285,k2_pre_topc('#skF_5','#skF_8'))
      | ~ m1_subset_1(C_285,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_311])).

tff(c_507,plain,(
    ! [B_119,C_285] :
      ( r1_waybel_0('#skF_5',B_119,'#skF_1'('#skF_5','#skF_8',C_285))
      | ~ r2_hidden('#skF_6',k10_yellow_6('#skF_5',B_119))
      | ~ r2_hidden('#skF_6','#skF_1'('#skF_5','#skF_8',C_285))
      | ~ v3_pre_topc('#skF_1'('#skF_5','#skF_8',C_285),'#skF_5')
      | r2_hidden(C_285,k2_pre_topc('#skF_5','#skF_8'))
      | ~ m1_subset_1(C_285,u1_struct_0('#skF_5'))
      | ~ l1_waybel_0(B_119,'#skF_5')
      | ~ v7_waybel_0(B_119)
      | ~ v4_orders_2(B_119)
      | v2_struct_0(B_119)
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_38,c_504])).

tff(c_510,plain,(
    ! [B_119,C_285] :
      ( r1_waybel_0('#skF_5',B_119,'#skF_1'('#skF_5','#skF_8',C_285))
      | ~ r2_hidden('#skF_6',k10_yellow_6('#skF_5',B_119))
      | ~ r2_hidden('#skF_6','#skF_1'('#skF_5','#skF_8',C_285))
      | ~ v3_pre_topc('#skF_1'('#skF_5','#skF_8',C_285),'#skF_5')
      | r2_hidden(C_285,k2_pre_topc('#skF_5','#skF_8'))
      | ~ m1_subset_1(C_285,u1_struct_0('#skF_5'))
      | ~ l1_waybel_0(B_119,'#skF_5')
      | ~ v7_waybel_0(B_119)
      | ~ v4_orders_2(B_119)
      | v2_struct_0(B_119)
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_507])).

tff(c_512,plain,(
    ! [B_286,C_287] :
      ( r1_waybel_0('#skF_5',B_286,'#skF_1'('#skF_5','#skF_8',C_287))
      | ~ r2_hidden('#skF_6',k10_yellow_6('#skF_5',B_286))
      | ~ r2_hidden('#skF_6','#skF_1'('#skF_5','#skF_8',C_287))
      | ~ v3_pre_topc('#skF_1'('#skF_5','#skF_8',C_287),'#skF_5')
      | r2_hidden(C_287,k2_pre_topc('#skF_5','#skF_8'))
      | ~ m1_subset_1(C_287,u1_struct_0('#skF_5'))
      | ~ l1_waybel_0(B_286,'#skF_5')
      | ~ v7_waybel_0(B_286)
      | ~ v4_orders_2(B_286)
      | v2_struct_0(B_286) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_510])).

tff(c_40,plain,(
    ! [C_129,D_130,A_120,B_126] :
      ( ~ r1_xboole_0(C_129,D_130)
      | ~ r1_waybel_0(A_120,B_126,D_130)
      | ~ r1_waybel_0(A_120,B_126,C_129)
      | ~ l1_waybel_0(B_126,A_120)
      | ~ v7_waybel_0(B_126)
      | ~ v4_orders_2(B_126)
      | v2_struct_0(B_126)
      | ~ l1_struct_0(A_120)
      | v2_struct_0(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_164,plain,(
    ! [A_120,B_126] :
      ( ~ r1_waybel_0(A_120,B_126,'#skF_1'('#skF_5','#skF_8','#skF_6'))
      | ~ r1_waybel_0(A_120,B_126,'#skF_8')
      | ~ l1_waybel_0(B_126,A_120)
      | ~ v7_waybel_0(B_126)
      | ~ v4_orders_2(B_126)
      | v2_struct_0(B_126)
      | ~ l1_struct_0(A_120)
      | v2_struct_0(A_120) ) ),
    inference(resolution,[status(thm)],[c_150,c_40])).

tff(c_516,plain,(
    ! [B_286] :
      ( ~ r1_waybel_0('#skF_5',B_286,'#skF_8')
      | ~ l1_struct_0('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r2_hidden('#skF_6',k10_yellow_6('#skF_5',B_286))
      | ~ r2_hidden('#skF_6','#skF_1'('#skF_5','#skF_8','#skF_6'))
      | ~ v3_pre_topc('#skF_1'('#skF_5','#skF_8','#skF_6'),'#skF_5')
      | r2_hidden('#skF_6',k2_pre_topc('#skF_5','#skF_8'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
      | ~ l1_waybel_0(B_286,'#skF_5')
      | ~ v7_waybel_0(B_286)
      | ~ v4_orders_2(B_286)
      | v2_struct_0(B_286) ) ),
    inference(resolution,[status(thm)],[c_512,c_164])).

tff(c_519,plain,(
    ! [B_286] :
      ( ~ r1_waybel_0('#skF_5',B_286,'#skF_8')
      | v2_struct_0('#skF_5')
      | ~ r2_hidden('#skF_6',k10_yellow_6('#skF_5',B_286))
      | r2_hidden('#skF_6',k2_pre_topc('#skF_5','#skF_8'))
      | ~ l1_waybel_0(B_286,'#skF_5')
      | ~ v7_waybel_0(B_286)
      | ~ v4_orders_2(B_286)
      | v2_struct_0(B_286) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_361,c_194,c_93,c_516])).

tff(c_521,plain,(
    ! [B_288] :
      ( ~ r1_waybel_0('#skF_5',B_288,'#skF_8')
      | ~ r2_hidden('#skF_6',k10_yellow_6('#skF_5',B_288))
      | ~ l1_waybel_0(B_288,'#skF_5')
      | ~ v7_waybel_0(B_288)
      | ~ v4_orders_2(B_288)
      | v2_struct_0(B_288) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_66,c_519])).

tff(c_524,plain,
    ( ~ r1_waybel_0('#skF_5','#skF_7','#skF_8')
    | ~ l1_waybel_0('#skF_7','#skF_5')
    | ~ v7_waybel_0('#skF_7')
    | ~ v4_orders_2('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_50,c_521])).

tff(c_527,plain,(
    v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_92,c_524])).

tff(c_529,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_527])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:39:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.49/1.53  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.49/1.54  
% 3.49/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.49/1.54  %$ r1_waybel_0 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_xboole_0 > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k2_relset_1 > u1_waybel_0 > k2_pre_topc > k10_yellow_6 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_3
% 3.49/1.54  
% 3.49/1.54  %Foreground sorts:
% 3.49/1.54  
% 3.49/1.54  
% 3.49/1.54  %Background operators:
% 3.49/1.54  
% 3.49/1.54  
% 3.49/1.54  %Foreground operators:
% 3.49/1.54  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.49/1.54  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.49/1.54  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 3.49/1.54  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.49/1.54  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.49/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.49/1.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.49/1.54  tff(k10_yellow_6, type, k10_yellow_6: ($i * $i) > $i).
% 3.49/1.54  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.49/1.54  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 3.49/1.54  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.49/1.54  tff('#skF_7', type, '#skF_7': $i).
% 3.49/1.54  tff('#skF_5', type, '#skF_5': $i).
% 3.49/1.54  tff(r1_waybel_0, type, r1_waybel_0: ($i * $i * $i) > $o).
% 3.49/1.54  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.49/1.54  tff('#skF_6', type, '#skF_6': $i).
% 3.49/1.54  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.49/1.54  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.49/1.54  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.49/1.54  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.49/1.54  tff(u1_waybel_0, type, u1_waybel_0: ($i * $i) > $i).
% 3.49/1.54  tff('#skF_8', type, '#skF_8': $i).
% 3.49/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.49/1.54  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 3.49/1.54  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.49/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.49/1.54  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.49/1.54  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.49/1.54  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.49/1.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.49/1.54  
% 3.49/1.56  tff(f_195, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((((~v2_struct_0(C) & v4_orders_2(C)) & v7_waybel_0(C)) & l1_waybel_0(C, A)) => (r2_hidden(B, k10_yellow_6(A, C)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ((D = k2_relset_1(u1_struct_0(C), u1_struct_0(A), u1_waybel_0(A, C))) => r2_hidden(B, k2_pre_topc(A, D)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_waybel_9)).
% 3.49/1.56  tff(f_35, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.49/1.56  tff(f_165, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => r1_waybel_0(A, B, k2_relset_1(u1_struct_0(B), u1_struct_0(A), u1_waybel_0(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_waybel_9)).
% 3.49/1.56  tff(f_60, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, k2_pre_topc(A, B)) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~((v3_pre_topc(D, A) & r2_hidden(C, D)) & r1_xboole_0(B, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_tops_1)).
% 3.49/1.56  tff(f_129, axiom, (![A, B]: (((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => m1_subset_1(k10_yellow_6(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k10_yellow_6)).
% 3.49/1.56  tff(f_79, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((v3_pre_topc(B, A) & r2_hidden(C, B)) => m1_connsp_2(B, A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_connsp_2)).
% 3.49/1.56  tff(f_111, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = k10_yellow_6(A, B)) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) <=> (![E]: (m1_connsp_2(E, A, D) => r1_waybel_0(A, B, E))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_yellow_6)).
% 3.49/1.56  tff(f_152, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C, D]: ~((r1_waybel_0(A, B, C) & r1_waybel_0(A, B, D)) & r1_xboole_0(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_yellow_6)).
% 3.49/1.56  tff(c_58, plain, (~v2_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_195])).
% 3.49/1.56  tff(c_56, plain, (v4_orders_2('#skF_7')), inference(cnfTransformation, [status(thm)], [f_195])).
% 3.49/1.56  tff(c_54, plain, (v7_waybel_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_195])).
% 3.49/1.56  tff(c_52, plain, (l1_waybel_0('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_195])).
% 3.49/1.56  tff(c_62, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_195])).
% 3.49/1.56  tff(c_4, plain, (![A_4]: (l1_struct_0(A_4) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.49/1.56  tff(c_66, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_195])).
% 3.49/1.56  tff(c_46, plain, (k2_relset_1(u1_struct_0('#skF_7'), u1_struct_0('#skF_5'), u1_waybel_0('#skF_5', '#skF_7'))='#skF_8'), inference(cnfTransformation, [status(thm)], [f_195])).
% 3.49/1.56  tff(c_77, plain, (![A_150, B_151]: (r1_waybel_0(A_150, B_151, k2_relset_1(u1_struct_0(B_151), u1_struct_0(A_150), u1_waybel_0(A_150, B_151))) | ~l1_waybel_0(B_151, A_150) | v2_struct_0(B_151) | ~l1_struct_0(A_150) | v2_struct_0(A_150))), inference(cnfTransformation, [status(thm)], [f_165])).
% 3.49/1.56  tff(c_80, plain, (r1_waybel_0('#skF_5', '#skF_7', '#skF_8') | ~l1_waybel_0('#skF_7', '#skF_5') | v2_struct_0('#skF_7') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_46, c_77])).
% 3.49/1.56  tff(c_82, plain, (r1_waybel_0('#skF_5', '#skF_7', '#skF_8') | v2_struct_0('#skF_7') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_80])).
% 3.49/1.56  tff(c_83, plain, (r1_waybel_0('#skF_5', '#skF_7', '#skF_8') | ~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_66, c_58, c_82])).
% 3.49/1.56  tff(c_84, plain, (~l1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_83])).
% 3.49/1.56  tff(c_87, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_4, c_84])).
% 3.49/1.56  tff(c_91, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_87])).
% 3.49/1.56  tff(c_92, plain, (r1_waybel_0('#skF_5', '#skF_7', '#skF_8')), inference(splitRight, [status(thm)], [c_83])).
% 3.49/1.56  tff(c_50, plain, (r2_hidden('#skF_6', k10_yellow_6('#skF_5', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_195])).
% 3.49/1.56  tff(c_44, plain, (~r2_hidden('#skF_6', k2_pre_topc('#skF_5', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_195])).
% 3.49/1.56  tff(c_60, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_195])).
% 3.49/1.56  tff(c_64, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_195])).
% 3.49/1.56  tff(c_48, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_195])).
% 3.49/1.56  tff(c_167, plain, (![A_174, B_175, C_176]: (v3_pre_topc('#skF_1'(A_174, B_175, C_176), A_174) | r2_hidden(C_176, k2_pre_topc(A_174, B_175)) | ~m1_subset_1(C_176, u1_struct_0(A_174)) | ~m1_subset_1(B_175, k1_zfmisc_1(u1_struct_0(A_174))) | ~l1_pre_topc(A_174) | ~v2_pre_topc(A_174) | v2_struct_0(A_174))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.49/1.56  tff(c_171, plain, (![C_176]: (v3_pre_topc('#skF_1'('#skF_5', '#skF_8', C_176), '#skF_5') | r2_hidden(C_176, k2_pre_topc('#skF_5', '#skF_8')) | ~m1_subset_1(C_176, u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_48, c_167])).
% 3.49/1.56  tff(c_175, plain, (![C_176]: (v3_pre_topc('#skF_1'('#skF_5', '#skF_8', C_176), '#skF_5') | r2_hidden(C_176, k2_pre_topc('#skF_5', '#skF_8')) | ~m1_subset_1(C_176, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_171])).
% 3.49/1.56  tff(c_176, plain, (![C_176]: (v3_pre_topc('#skF_1'('#skF_5', '#skF_8', C_176), '#skF_5') | r2_hidden(C_176, k2_pre_topc('#skF_5', '#skF_8')) | ~m1_subset_1(C_176, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_66, c_175])).
% 3.49/1.56  tff(c_14, plain, (![A_5, B_17, C_23]: (m1_subset_1('#skF_1'(A_5, B_17, C_23), k1_zfmisc_1(u1_struct_0(A_5))) | r2_hidden(C_23, k2_pre_topc(A_5, B_17)) | ~m1_subset_1(C_23, u1_struct_0(A_5)) | ~m1_subset_1(B_17, k1_zfmisc_1(u1_struct_0(A_5))) | ~l1_pre_topc(A_5) | ~v2_pre_topc(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.49/1.56  tff(c_133, plain, (![B_165, A_166, C_167]: (r1_xboole_0(B_165, '#skF_1'(A_166, B_165, C_167)) | r2_hidden(C_167, k2_pre_topc(A_166, B_165)) | ~m1_subset_1(C_167, u1_struct_0(A_166)) | ~m1_subset_1(B_165, k1_zfmisc_1(u1_struct_0(A_166))) | ~l1_pre_topc(A_166) | ~v2_pre_topc(A_166) | v2_struct_0(A_166))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.49/1.56  tff(c_137, plain, (![C_167]: (r1_xboole_0('#skF_8', '#skF_1'('#skF_5', '#skF_8', C_167)) | r2_hidden(C_167, k2_pre_topc('#skF_5', '#skF_8')) | ~m1_subset_1(C_167, u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_48, c_133])).
% 3.49/1.56  tff(c_141, plain, (![C_167]: (r1_xboole_0('#skF_8', '#skF_1'('#skF_5', '#skF_8', C_167)) | r2_hidden(C_167, k2_pre_topc('#skF_5', '#skF_8')) | ~m1_subset_1(C_167, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_137])).
% 3.49/1.56  tff(c_144, plain, (![C_168]: (r1_xboole_0('#skF_8', '#skF_1'('#skF_5', '#skF_8', C_168)) | r2_hidden(C_168, k2_pre_topc('#skF_5', '#skF_8')) | ~m1_subset_1(C_168, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_66, c_141])).
% 3.49/1.56  tff(c_147, plain, (r1_xboole_0('#skF_8', '#skF_1'('#skF_5', '#skF_8', '#skF_6')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_144, c_44])).
% 3.49/1.56  tff(c_150, plain, (r1_xboole_0('#skF_8', '#skF_1'('#skF_5', '#skF_8', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_147])).
% 3.49/1.56  tff(c_260, plain, (![B_197, D_198, C_199, A_200]: (~r1_xboole_0(B_197, D_198) | ~r2_hidden(C_199, D_198) | ~v3_pre_topc(D_198, A_200) | ~m1_subset_1(D_198, k1_zfmisc_1(u1_struct_0(A_200))) | ~r2_hidden(C_199, k2_pre_topc(A_200, B_197)) | ~m1_subset_1(C_199, u1_struct_0(A_200)) | ~m1_subset_1(B_197, k1_zfmisc_1(u1_struct_0(A_200))) | ~l1_pre_topc(A_200) | ~v2_pre_topc(A_200) | v2_struct_0(A_200))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.49/1.56  tff(c_325, plain, (![C_225, A_226]: (~r2_hidden(C_225, '#skF_1'('#skF_5', '#skF_8', '#skF_6')) | ~v3_pre_topc('#skF_1'('#skF_5', '#skF_8', '#skF_6'), A_226) | ~m1_subset_1('#skF_1'('#skF_5', '#skF_8', '#skF_6'), k1_zfmisc_1(u1_struct_0(A_226))) | ~r2_hidden(C_225, k2_pre_topc(A_226, '#skF_8')) | ~m1_subset_1(C_225, u1_struct_0(A_226)) | ~m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0(A_226))) | ~l1_pre_topc(A_226) | ~v2_pre_topc(A_226) | v2_struct_0(A_226))), inference(resolution, [status(thm)], [c_150, c_260])).
% 3.49/1.56  tff(c_328, plain, (![C_225]: (~r2_hidden(C_225, '#skF_1'('#skF_5', '#skF_8', '#skF_6')) | ~v3_pre_topc('#skF_1'('#skF_5', '#skF_8', '#skF_6'), '#skF_5') | ~r2_hidden(C_225, k2_pre_topc('#skF_5', '#skF_8')) | ~m1_subset_1(C_225, u1_struct_0('#skF_5')) | r2_hidden('#skF_6', k2_pre_topc('#skF_5', '#skF_8')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_14, c_325])).
% 3.49/1.56  tff(c_331, plain, (![C_225]: (~r2_hidden(C_225, '#skF_1'('#skF_5', '#skF_8', '#skF_6')) | ~v3_pre_topc('#skF_1'('#skF_5', '#skF_8', '#skF_6'), '#skF_5') | ~r2_hidden(C_225, k2_pre_topc('#skF_5', '#skF_8')) | ~m1_subset_1(C_225, u1_struct_0('#skF_5')) | r2_hidden('#skF_6', k2_pre_topc('#skF_5', '#skF_8')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_48, c_60, c_328])).
% 3.49/1.56  tff(c_332, plain, (![C_225]: (~r2_hidden(C_225, '#skF_1'('#skF_5', '#skF_8', '#skF_6')) | ~v3_pre_topc('#skF_1'('#skF_5', '#skF_8', '#skF_6'), '#skF_5') | ~r2_hidden(C_225, k2_pre_topc('#skF_5', '#skF_8')) | ~m1_subset_1(C_225, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_66, c_44, c_331])).
% 3.49/1.56  tff(c_333, plain, (~v3_pre_topc('#skF_1'('#skF_5', '#skF_8', '#skF_6'), '#skF_5')), inference(splitLeft, [status(thm)], [c_332])).
% 3.49/1.56  tff(c_354, plain, (r2_hidden('#skF_6', k2_pre_topc('#skF_5', '#skF_8')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_176, c_333])).
% 3.49/1.56  tff(c_357, plain, (r2_hidden('#skF_6', k2_pre_topc('#skF_5', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_354])).
% 3.49/1.56  tff(c_359, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_357])).
% 3.49/1.56  tff(c_361, plain, (v3_pre_topc('#skF_1'('#skF_5', '#skF_8', '#skF_6'), '#skF_5')), inference(splitRight, [status(thm)], [c_332])).
% 3.49/1.56  tff(c_178, plain, (![C_178, A_179, B_180]: (r2_hidden(C_178, '#skF_1'(A_179, B_180, C_178)) | r2_hidden(C_178, k2_pre_topc(A_179, B_180)) | ~m1_subset_1(C_178, u1_struct_0(A_179)) | ~m1_subset_1(B_180, k1_zfmisc_1(u1_struct_0(A_179))) | ~l1_pre_topc(A_179) | ~v2_pre_topc(A_179) | v2_struct_0(A_179))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.49/1.56  tff(c_182, plain, (![C_178]: (r2_hidden(C_178, '#skF_1'('#skF_5', '#skF_8', C_178)) | r2_hidden(C_178, k2_pre_topc('#skF_5', '#skF_8')) | ~m1_subset_1(C_178, u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_48, c_178])).
% 3.49/1.56  tff(c_186, plain, (![C_178]: (r2_hidden(C_178, '#skF_1'('#skF_5', '#skF_8', C_178)) | r2_hidden(C_178, k2_pre_topc('#skF_5', '#skF_8')) | ~m1_subset_1(C_178, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_182])).
% 3.49/1.56  tff(c_188, plain, (![C_181]: (r2_hidden(C_181, '#skF_1'('#skF_5', '#skF_8', C_181)) | r2_hidden(C_181, k2_pre_topc('#skF_5', '#skF_8')) | ~m1_subset_1(C_181, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_66, c_186])).
% 3.49/1.56  tff(c_191, plain, (r2_hidden('#skF_6', '#skF_1'('#skF_5', '#skF_8', '#skF_6')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_188, c_44])).
% 3.49/1.56  tff(c_194, plain, (r2_hidden('#skF_6', '#skF_1'('#skF_5', '#skF_8', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_191])).
% 3.49/1.56  tff(c_93, plain, (l1_struct_0('#skF_5')), inference(splitRight, [status(thm)], [c_83])).
% 3.49/1.56  tff(c_38, plain, (![A_118, B_119]: (m1_subset_1(k10_yellow_6(A_118, B_119), k1_zfmisc_1(u1_struct_0(A_118))) | ~l1_waybel_0(B_119, A_118) | ~v7_waybel_0(B_119) | ~v4_orders_2(B_119) | v2_struct_0(B_119) | ~l1_pre_topc(A_118) | ~v2_pre_topc(A_118) | v2_struct_0(A_118))), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.49/1.56  tff(c_195, plain, (![A_182, B_183, C_184]: (m1_subset_1('#skF_1'(A_182, B_183, C_184), k1_zfmisc_1(u1_struct_0(A_182))) | r2_hidden(C_184, k2_pre_topc(A_182, B_183)) | ~m1_subset_1(C_184, u1_struct_0(A_182)) | ~m1_subset_1(B_183, k1_zfmisc_1(u1_struct_0(A_182))) | ~l1_pre_topc(A_182) | ~v2_pre_topc(A_182) | v2_struct_0(A_182))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.49/1.56  tff(c_107, plain, (![B_161, A_162, C_163]: (m1_connsp_2(B_161, A_162, C_163) | ~r2_hidden(C_163, B_161) | ~v3_pre_topc(B_161, A_162) | ~m1_subset_1(C_163, u1_struct_0(A_162)) | ~m1_subset_1(B_161, k1_zfmisc_1(u1_struct_0(A_162))) | ~l1_pre_topc(A_162) | ~v2_pre_topc(A_162) | v2_struct_0(A_162))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.49/1.56  tff(c_111, plain, (![B_161]: (m1_connsp_2(B_161, '#skF_5', '#skF_6') | ~r2_hidden('#skF_6', B_161) | ~v3_pre_topc(B_161, '#skF_5') | ~m1_subset_1(B_161, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_60, c_107])).
% 3.49/1.56  tff(c_118, plain, (![B_161]: (m1_connsp_2(B_161, '#skF_5', '#skF_6') | ~r2_hidden('#skF_6', B_161) | ~v3_pre_topc(B_161, '#skF_5') | ~m1_subset_1(B_161, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_111])).
% 3.49/1.56  tff(c_119, plain, (![B_161]: (m1_connsp_2(B_161, '#skF_5', '#skF_6') | ~r2_hidden('#skF_6', B_161) | ~v3_pre_topc(B_161, '#skF_5') | ~m1_subset_1(B_161, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_66, c_118])).
% 3.49/1.56  tff(c_208, plain, (![B_183, C_184]: (m1_connsp_2('#skF_1'('#skF_5', B_183, C_184), '#skF_5', '#skF_6') | ~r2_hidden('#skF_6', '#skF_1'('#skF_5', B_183, C_184)) | ~v3_pre_topc('#skF_1'('#skF_5', B_183, C_184), '#skF_5') | r2_hidden(C_184, k2_pre_topc('#skF_5', B_183)) | ~m1_subset_1(C_184, u1_struct_0('#skF_5')) | ~m1_subset_1(B_183, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_195, c_119])).
% 3.49/1.56  tff(c_220, plain, (![B_183, C_184]: (m1_connsp_2('#skF_1'('#skF_5', B_183, C_184), '#skF_5', '#skF_6') | ~r2_hidden('#skF_6', '#skF_1'('#skF_5', B_183, C_184)) | ~v3_pre_topc('#skF_1'('#skF_5', B_183, C_184), '#skF_5') | r2_hidden(C_184, k2_pre_topc('#skF_5', B_183)) | ~m1_subset_1(C_184, u1_struct_0('#skF_5')) | ~m1_subset_1(B_183, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_208])).
% 3.49/1.56  tff(c_241, plain, (![B_194, C_195]: (m1_connsp_2('#skF_1'('#skF_5', B_194, C_195), '#skF_5', '#skF_6') | ~r2_hidden('#skF_6', '#skF_1'('#skF_5', B_194, C_195)) | ~v3_pre_topc('#skF_1'('#skF_5', B_194, C_195), '#skF_5') | r2_hidden(C_195, k2_pre_topc('#skF_5', B_194)) | ~m1_subset_1(C_195, u1_struct_0('#skF_5')) | ~m1_subset_1(B_194, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_66, c_220])).
% 3.49/1.56  tff(c_258, plain, (![C_195]: (m1_connsp_2('#skF_1'('#skF_5', '#skF_8', C_195), '#skF_5', '#skF_6') | ~r2_hidden('#skF_6', '#skF_1'('#skF_5', '#skF_8', C_195)) | ~v3_pre_topc('#skF_1'('#skF_5', '#skF_8', C_195), '#skF_5') | r2_hidden(C_195, k2_pre_topc('#skF_5', '#skF_8')) | ~m1_subset_1(C_195, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_48, c_241])).
% 3.49/1.56  tff(c_296, plain, (![A_218, B_219, E_220, D_221]: (r1_waybel_0(A_218, B_219, E_220) | ~m1_connsp_2(E_220, A_218, D_221) | ~r2_hidden(D_221, k10_yellow_6(A_218, B_219)) | ~m1_subset_1(D_221, u1_struct_0(A_218)) | ~m1_subset_1(k10_yellow_6(A_218, B_219), k1_zfmisc_1(u1_struct_0(A_218))) | ~l1_waybel_0(B_219, A_218) | ~v7_waybel_0(B_219) | ~v4_orders_2(B_219) | v2_struct_0(B_219) | ~l1_pre_topc(A_218) | ~v2_pre_topc(A_218) | v2_struct_0(A_218))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.49/1.56  tff(c_300, plain, (![B_219, C_195]: (r1_waybel_0('#skF_5', B_219, '#skF_1'('#skF_5', '#skF_8', C_195)) | ~r2_hidden('#skF_6', k10_yellow_6('#skF_5', B_219)) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~m1_subset_1(k10_yellow_6('#skF_5', B_219), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_waybel_0(B_219, '#skF_5') | ~v7_waybel_0(B_219) | ~v4_orders_2(B_219) | v2_struct_0(B_219) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~r2_hidden('#skF_6', '#skF_1'('#skF_5', '#skF_8', C_195)) | ~v3_pre_topc('#skF_1'('#skF_5', '#skF_8', C_195), '#skF_5') | r2_hidden(C_195, k2_pre_topc('#skF_5', '#skF_8')) | ~m1_subset_1(C_195, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_258, c_296])).
% 3.49/1.56  tff(c_311, plain, (![B_219, C_195]: (r1_waybel_0('#skF_5', B_219, '#skF_1'('#skF_5', '#skF_8', C_195)) | ~r2_hidden('#skF_6', k10_yellow_6('#skF_5', B_219)) | ~m1_subset_1(k10_yellow_6('#skF_5', B_219), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_waybel_0(B_219, '#skF_5') | ~v7_waybel_0(B_219) | ~v4_orders_2(B_219) | v2_struct_0(B_219) | v2_struct_0('#skF_5') | ~r2_hidden('#skF_6', '#skF_1'('#skF_5', '#skF_8', C_195)) | ~v3_pre_topc('#skF_1'('#skF_5', '#skF_8', C_195), '#skF_5') | r2_hidden(C_195, k2_pre_topc('#skF_5', '#skF_8')) | ~m1_subset_1(C_195, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_300])).
% 3.49/1.56  tff(c_504, plain, (![B_284, C_285]: (r1_waybel_0('#skF_5', B_284, '#skF_1'('#skF_5', '#skF_8', C_285)) | ~r2_hidden('#skF_6', k10_yellow_6('#skF_5', B_284)) | ~m1_subset_1(k10_yellow_6('#skF_5', B_284), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_waybel_0(B_284, '#skF_5') | ~v7_waybel_0(B_284) | ~v4_orders_2(B_284) | v2_struct_0(B_284) | ~r2_hidden('#skF_6', '#skF_1'('#skF_5', '#skF_8', C_285)) | ~v3_pre_topc('#skF_1'('#skF_5', '#skF_8', C_285), '#skF_5') | r2_hidden(C_285, k2_pre_topc('#skF_5', '#skF_8')) | ~m1_subset_1(C_285, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_66, c_311])).
% 3.49/1.56  tff(c_507, plain, (![B_119, C_285]: (r1_waybel_0('#skF_5', B_119, '#skF_1'('#skF_5', '#skF_8', C_285)) | ~r2_hidden('#skF_6', k10_yellow_6('#skF_5', B_119)) | ~r2_hidden('#skF_6', '#skF_1'('#skF_5', '#skF_8', C_285)) | ~v3_pre_topc('#skF_1'('#skF_5', '#skF_8', C_285), '#skF_5') | r2_hidden(C_285, k2_pre_topc('#skF_5', '#skF_8')) | ~m1_subset_1(C_285, u1_struct_0('#skF_5')) | ~l1_waybel_0(B_119, '#skF_5') | ~v7_waybel_0(B_119) | ~v4_orders_2(B_119) | v2_struct_0(B_119) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_38, c_504])).
% 3.49/1.56  tff(c_510, plain, (![B_119, C_285]: (r1_waybel_0('#skF_5', B_119, '#skF_1'('#skF_5', '#skF_8', C_285)) | ~r2_hidden('#skF_6', k10_yellow_6('#skF_5', B_119)) | ~r2_hidden('#skF_6', '#skF_1'('#skF_5', '#skF_8', C_285)) | ~v3_pre_topc('#skF_1'('#skF_5', '#skF_8', C_285), '#skF_5') | r2_hidden(C_285, k2_pre_topc('#skF_5', '#skF_8')) | ~m1_subset_1(C_285, u1_struct_0('#skF_5')) | ~l1_waybel_0(B_119, '#skF_5') | ~v7_waybel_0(B_119) | ~v4_orders_2(B_119) | v2_struct_0(B_119) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_507])).
% 3.49/1.56  tff(c_512, plain, (![B_286, C_287]: (r1_waybel_0('#skF_5', B_286, '#skF_1'('#skF_5', '#skF_8', C_287)) | ~r2_hidden('#skF_6', k10_yellow_6('#skF_5', B_286)) | ~r2_hidden('#skF_6', '#skF_1'('#skF_5', '#skF_8', C_287)) | ~v3_pre_topc('#skF_1'('#skF_5', '#skF_8', C_287), '#skF_5') | r2_hidden(C_287, k2_pre_topc('#skF_5', '#skF_8')) | ~m1_subset_1(C_287, u1_struct_0('#skF_5')) | ~l1_waybel_0(B_286, '#skF_5') | ~v7_waybel_0(B_286) | ~v4_orders_2(B_286) | v2_struct_0(B_286))), inference(negUnitSimplification, [status(thm)], [c_66, c_510])).
% 3.49/1.56  tff(c_40, plain, (![C_129, D_130, A_120, B_126]: (~r1_xboole_0(C_129, D_130) | ~r1_waybel_0(A_120, B_126, D_130) | ~r1_waybel_0(A_120, B_126, C_129) | ~l1_waybel_0(B_126, A_120) | ~v7_waybel_0(B_126) | ~v4_orders_2(B_126) | v2_struct_0(B_126) | ~l1_struct_0(A_120) | v2_struct_0(A_120))), inference(cnfTransformation, [status(thm)], [f_152])).
% 3.49/1.56  tff(c_164, plain, (![A_120, B_126]: (~r1_waybel_0(A_120, B_126, '#skF_1'('#skF_5', '#skF_8', '#skF_6')) | ~r1_waybel_0(A_120, B_126, '#skF_8') | ~l1_waybel_0(B_126, A_120) | ~v7_waybel_0(B_126) | ~v4_orders_2(B_126) | v2_struct_0(B_126) | ~l1_struct_0(A_120) | v2_struct_0(A_120))), inference(resolution, [status(thm)], [c_150, c_40])).
% 3.49/1.56  tff(c_516, plain, (![B_286]: (~r1_waybel_0('#skF_5', B_286, '#skF_8') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5') | ~r2_hidden('#skF_6', k10_yellow_6('#skF_5', B_286)) | ~r2_hidden('#skF_6', '#skF_1'('#skF_5', '#skF_8', '#skF_6')) | ~v3_pre_topc('#skF_1'('#skF_5', '#skF_8', '#skF_6'), '#skF_5') | r2_hidden('#skF_6', k2_pre_topc('#skF_5', '#skF_8')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l1_waybel_0(B_286, '#skF_5') | ~v7_waybel_0(B_286) | ~v4_orders_2(B_286) | v2_struct_0(B_286))), inference(resolution, [status(thm)], [c_512, c_164])).
% 3.49/1.56  tff(c_519, plain, (![B_286]: (~r1_waybel_0('#skF_5', B_286, '#skF_8') | v2_struct_0('#skF_5') | ~r2_hidden('#skF_6', k10_yellow_6('#skF_5', B_286)) | r2_hidden('#skF_6', k2_pre_topc('#skF_5', '#skF_8')) | ~l1_waybel_0(B_286, '#skF_5') | ~v7_waybel_0(B_286) | ~v4_orders_2(B_286) | v2_struct_0(B_286))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_361, c_194, c_93, c_516])).
% 3.49/1.56  tff(c_521, plain, (![B_288]: (~r1_waybel_0('#skF_5', B_288, '#skF_8') | ~r2_hidden('#skF_6', k10_yellow_6('#skF_5', B_288)) | ~l1_waybel_0(B_288, '#skF_5') | ~v7_waybel_0(B_288) | ~v4_orders_2(B_288) | v2_struct_0(B_288))), inference(negUnitSimplification, [status(thm)], [c_44, c_66, c_519])).
% 3.49/1.56  tff(c_524, plain, (~r1_waybel_0('#skF_5', '#skF_7', '#skF_8') | ~l1_waybel_0('#skF_7', '#skF_5') | ~v7_waybel_0('#skF_7') | ~v4_orders_2('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_50, c_521])).
% 3.49/1.56  tff(c_527, plain, (v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_92, c_524])).
% 3.49/1.56  tff(c_529, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_527])).
% 3.49/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.49/1.56  
% 3.49/1.56  Inference rules
% 3.49/1.56  ----------------------
% 3.49/1.56  #Ref     : 0
% 3.49/1.56  #Sup     : 79
% 3.49/1.56  #Fact    : 0
% 3.49/1.56  #Define  : 0
% 3.49/1.56  #Split   : 3
% 3.49/1.56  #Chain   : 0
% 3.49/1.56  #Close   : 0
% 3.49/1.56  
% 3.49/1.56  Ordering : KBO
% 3.49/1.56  
% 3.49/1.56  Simplification rules
% 3.49/1.56  ----------------------
% 3.49/1.56  #Subsume      : 6
% 3.49/1.56  #Demod        : 98
% 3.49/1.56  #Tautology    : 12
% 3.49/1.56  #SimpNegUnit  : 38
% 3.49/1.56  #BackRed      : 0
% 3.49/1.56  
% 3.49/1.56  #Partial instantiations: 0
% 3.49/1.56  #Strategies tried      : 1
% 3.49/1.56  
% 3.49/1.56  Timing (in seconds)
% 3.49/1.56  ----------------------
% 3.49/1.57  Preprocessing        : 0.36
% 3.49/1.57  Parsing              : 0.19
% 3.49/1.57  CNF conversion       : 0.04
% 3.49/1.57  Main loop            : 0.42
% 3.49/1.57  Inferencing          : 0.17
% 3.49/1.57  Reduction            : 0.12
% 3.49/1.57  Demodulation         : 0.08
% 3.49/1.57  BG Simplification    : 0.03
% 3.49/1.57  Subsumption          : 0.08
% 3.49/1.57  Abstraction          : 0.02
% 3.49/1.57  MUC search           : 0.00
% 3.49/1.57  Cooper               : 0.00
% 3.49/1.57  Total                : 0.83
% 3.49/1.57  Index Insertion      : 0.00
% 3.49/1.57  Index Deletion       : 0.00
% 3.49/1.57  Index Matching       : 0.00
% 3.49/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
