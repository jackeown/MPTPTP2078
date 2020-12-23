%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:38 EST 2020

% Result     : Theorem 4.19s
% Output     : CNFRefutation 4.69s
% Verified   : 
% Statistics : Number of formulae       :  181 (1066 expanded)
%              Number of leaves         :   37 ( 402 expanded)
%              Depth                    :   36
%              Number of atoms          :  837 (7198 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   20 (   7 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_waybel_7 > r1_waybel_0 > v4_pre_topc > v3_yellow_6 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k2_pre_topc > k10_yellow_6 > #nlpp > u1_struct_0 > k3_yellow_1 > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k3_yellow_1,type,(
    k3_yellow_1: $i > $i )).

tff(v2_waybel_0,type,(
    v2_waybel_0: ( $i * $i ) > $o )).

tff(k10_yellow_6,type,(
    k10_yellow_6: ( $i * $i ) > $i )).

tff(v3_yellow_6,type,(
    v3_yellow_6: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v7_waybel_0,type,(
    v7_waybel_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_waybel_0,type,(
    r1_waybel_0: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(r1_waybel_7,type,(
    r1_waybel_7: ( $i * $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(l1_waybel_0,type,(
    l1_waybel_0: ( $i * $i ) > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v13_waybel_0,type,(
    v13_waybel_0: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_154,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> ! [C] :
                  ( ( ~ v1_xboole_0(C)
                    & v1_subset_1(C,u1_struct_0(k3_yellow_1(k2_struct_0(A))))
                    & v2_waybel_0(C,k3_yellow_1(k2_struct_0(A)))
                    & v13_waybel_0(C,k3_yellow_1(k2_struct_0(A)))
                    & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))))) )
                 => ( r2_hidden(B,C)
                   => ! [D] :
                        ( m1_subset_1(D,u1_struct_0(A))
                       => ( r1_waybel_7(A,C,D)
                         => r2_hidden(D,B) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_yellow19)).

tff(f_89,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> ! [C] :
                ( ( ~ v2_struct_0(C)
                  & v4_orders_2(C)
                  & v7_waybel_0(C)
                  & v3_yellow_6(C,A)
                  & l1_waybel_0(C,A) )
               => ( r1_waybel_0(A,C,B)
                 => ! [D] :
                      ( m1_subset_1(D,u1_struct_0(A))
                     => ( r2_hidden(D,k10_yellow_6(A,C))
                       => r2_hidden(D,B) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_yellow19)).

tff(f_56,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r2_hidden(C,k2_pre_topc(A,B))
              <=> ? [D] :
                    ( ~ v2_struct_0(D)
                    & v4_orders_2(D)
                    & v7_waybel_0(D)
                    & v3_yellow_6(D,A)
                    & l1_waybel_0(D,A)
                    & r1_waybel_0(A,D,B)
                    & r2_hidden(C,k10_yellow_6(A,D)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_yellow19)).

tff(f_120,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r2_hidden(C,k2_pre_topc(A,B))
              <=> ? [D] :
                    ( ~ v1_xboole_0(D)
                    & v1_subset_1(D,u1_struct_0(k3_yellow_1(k2_struct_0(A))))
                    & v2_waybel_0(D,k3_yellow_1(k2_struct_0(A)))
                    & v13_waybel_0(D,k3_yellow_1(k2_struct_0(A)))
                    & m1_subset_1(D,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))
                    & r2_hidden(B,D)
                    & r1_waybel_7(A,D,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_yellow19)).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_58,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_56,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_54,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_78,plain,
    ( ~ v1_xboole_0('#skF_7')
    | ~ v4_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_101,plain,(
    ~ v4_pre_topc('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_24,plain,(
    ! [A_23,B_37] :
      ( m1_subset_1('#skF_3'(A_23,B_37),u1_struct_0(A_23))
      | v4_pre_topc(B_37,A_23)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_102,plain,(
    ! [A_93,B_94] :
      ( ~ v2_struct_0('#skF_2'(A_93,B_94))
      | v4_pre_topc(B_94,A_93)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ l1_pre_topc(A_93)
      | ~ v2_pre_topc(A_93)
      | v2_struct_0(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_105,plain,
    ( ~ v2_struct_0('#skF_2'('#skF_5','#skF_6'))
    | v4_pre_topc('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_102])).

tff(c_108,plain,
    ( ~ v2_struct_0('#skF_2'('#skF_5','#skF_6'))
    | v4_pre_topc('#skF_6','#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_105])).

tff(c_109,plain,(
    ~ v2_struct_0('#skF_2'('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_101,c_108])).

tff(c_110,plain,(
    ! [A_95,B_96] :
      ( v4_orders_2('#skF_2'(A_95,B_96))
      | v4_pre_topc(B_96,A_95)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ l1_pre_topc(A_95)
      | ~ v2_pre_topc(A_95)
      | v2_struct_0(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_113,plain,
    ( v4_orders_2('#skF_2'('#skF_5','#skF_6'))
    | v4_pre_topc('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_110])).

tff(c_116,plain,
    ( v4_orders_2('#skF_2'('#skF_5','#skF_6'))
    | v4_pre_topc('#skF_6','#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_113])).

tff(c_117,plain,(
    v4_orders_2('#skF_2'('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_101,c_116])).

tff(c_118,plain,(
    ! [A_97,B_98] :
      ( v7_waybel_0('#skF_2'(A_97,B_98))
      | v4_pre_topc(B_98,A_97)
      | ~ m1_subset_1(B_98,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ l1_pre_topc(A_97)
      | ~ v2_pre_topc(A_97)
      | v2_struct_0(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_121,plain,
    ( v7_waybel_0('#skF_2'('#skF_5','#skF_6'))
    | v4_pre_topc('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_118])).

tff(c_124,plain,
    ( v7_waybel_0('#skF_2'('#skF_5','#skF_6'))
    | v4_pre_topc('#skF_6','#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_121])).

tff(c_125,plain,(
    v7_waybel_0('#skF_2'('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_101,c_124])).

tff(c_134,plain,(
    ! [A_101,B_102] :
      ( v3_yellow_6('#skF_2'(A_101,B_102),A_101)
      | v4_pre_topc(B_102,A_101)
      | ~ m1_subset_1(B_102,k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ l1_pre_topc(A_101)
      | ~ v2_pre_topc(A_101)
      | v2_struct_0(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_136,plain,
    ( v3_yellow_6('#skF_2'('#skF_5','#skF_6'),'#skF_5')
    | v4_pre_topc('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_134])).

tff(c_139,plain,
    ( v3_yellow_6('#skF_2'('#skF_5','#skF_6'),'#skF_5')
    | v4_pre_topc('#skF_6','#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_136])).

tff(c_140,plain,(
    v3_yellow_6('#skF_2'('#skF_5','#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_101,c_139])).

tff(c_127,plain,(
    ! [A_99,B_100] :
      ( l1_waybel_0('#skF_2'(A_99,B_100),A_99)
      | v4_pre_topc(B_100,A_99)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ l1_pre_topc(A_99)
      | ~ v2_pre_topc(A_99)
      | v2_struct_0(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_129,plain,
    ( l1_waybel_0('#skF_2'('#skF_5','#skF_6'),'#skF_5')
    | v4_pre_topc('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_127])).

tff(c_132,plain,
    ( l1_waybel_0('#skF_2'('#skF_5','#skF_6'),'#skF_5')
    | v4_pre_topc('#skF_6','#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_129])).

tff(c_133,plain,(
    l1_waybel_0('#skF_2'('#skF_5','#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_101,c_132])).

tff(c_143,plain,(
    ! [A_107,B_108] :
      ( r1_waybel_0(A_107,'#skF_2'(A_107,B_108),B_108)
      | v4_pre_topc(B_108,A_107)
      | ~ m1_subset_1(B_108,k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ l1_pre_topc(A_107)
      | ~ v2_pre_topc(A_107)
      | v2_struct_0(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_145,plain,
    ( r1_waybel_0('#skF_5','#skF_2'('#skF_5','#skF_6'),'#skF_6')
    | v4_pre_topc('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_143])).

tff(c_148,plain,
    ( r1_waybel_0('#skF_5','#skF_2'('#skF_5','#skF_6'),'#skF_6')
    | v4_pre_topc('#skF_6','#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_145])).

tff(c_149,plain,(
    r1_waybel_0('#skF_5','#skF_2'('#skF_5','#skF_6'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_101,c_148])).

tff(c_22,plain,(
    ! [A_23,B_37] :
      ( r2_hidden('#skF_3'(A_23,B_37),k10_yellow_6(A_23,'#skF_2'(A_23,B_37)))
      | v4_pre_topc(B_37,A_23)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_223,plain,(
    ! [C_158,A_159,B_160,D_161] :
      ( r2_hidden(C_158,k2_pre_topc(A_159,B_160))
      | ~ r2_hidden(C_158,k10_yellow_6(A_159,D_161))
      | ~ r1_waybel_0(A_159,D_161,B_160)
      | ~ l1_waybel_0(D_161,A_159)
      | ~ v3_yellow_6(D_161,A_159)
      | ~ v7_waybel_0(D_161)
      | ~ v4_orders_2(D_161)
      | v2_struct_0(D_161)
      | ~ m1_subset_1(C_158,u1_struct_0(A_159))
      | ~ m1_subset_1(B_160,k1_zfmisc_1(u1_struct_0(A_159)))
      | ~ l1_pre_topc(A_159)
      | ~ v2_pre_topc(A_159)
      | v2_struct_0(A_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_229,plain,(
    ! [A_23,B_37,B_160] :
      ( r2_hidden('#skF_3'(A_23,B_37),k2_pre_topc(A_23,B_160))
      | ~ r1_waybel_0(A_23,'#skF_2'(A_23,B_37),B_160)
      | ~ l1_waybel_0('#skF_2'(A_23,B_37),A_23)
      | ~ v3_yellow_6('#skF_2'(A_23,B_37),A_23)
      | ~ v7_waybel_0('#skF_2'(A_23,B_37))
      | ~ v4_orders_2('#skF_2'(A_23,B_37))
      | v2_struct_0('#skF_2'(A_23,B_37))
      | ~ m1_subset_1('#skF_3'(A_23,B_37),u1_struct_0(A_23))
      | ~ m1_subset_1(B_160,k1_zfmisc_1(u1_struct_0(A_23)))
      | v4_pre_topc(B_37,A_23)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23)
      | v2_struct_0(A_23) ) ),
    inference(resolution,[status(thm)],[c_22,c_223])).

tff(c_287,plain,(
    ! [A_193,B_194,B_195] :
      ( r2_hidden('#skF_3'(A_193,B_194),k2_pre_topc(A_193,B_195))
      | ~ r1_waybel_0(A_193,'#skF_2'(A_193,B_194),B_195)
      | ~ l1_waybel_0('#skF_2'(A_193,B_194),A_193)
      | ~ v3_yellow_6('#skF_2'(A_193,B_194),A_193)
      | ~ v7_waybel_0('#skF_2'(A_193,B_194))
      | ~ v4_orders_2('#skF_2'(A_193,B_194))
      | v2_struct_0('#skF_2'(A_193,B_194))
      | ~ m1_subset_1('#skF_3'(A_193,B_194),u1_struct_0(A_193))
      | ~ m1_subset_1(B_195,k1_zfmisc_1(u1_struct_0(A_193)))
      | v4_pre_topc(B_194,A_193)
      | ~ m1_subset_1(B_194,k1_zfmisc_1(u1_struct_0(A_193)))
      | ~ l1_pre_topc(A_193)
      | ~ v2_pre_topc(A_193)
      | v2_struct_0(A_193) ) ),
    inference(resolution,[status(thm)],[c_22,c_223])).

tff(c_42,plain,(
    ! [B_60,A_48,C_66] :
      ( r2_hidden(B_60,'#skF_4'(A_48,B_60,C_66))
      | ~ r2_hidden(C_66,k2_pre_topc(A_48,B_60))
      | ~ m1_subset_1(C_66,u1_struct_0(A_48))
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ l1_pre_topc(A_48)
      | ~ v2_pre_topc(A_48)
      | v2_struct_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_394,plain,(
    ! [B_235,A_236,B_237] :
      ( r2_hidden(B_235,'#skF_4'(A_236,B_235,'#skF_3'(A_236,B_237)))
      | ~ r1_waybel_0(A_236,'#skF_2'(A_236,B_237),B_235)
      | ~ l1_waybel_0('#skF_2'(A_236,B_237),A_236)
      | ~ v3_yellow_6('#skF_2'(A_236,B_237),A_236)
      | ~ v7_waybel_0('#skF_2'(A_236,B_237))
      | ~ v4_orders_2('#skF_2'(A_236,B_237))
      | v2_struct_0('#skF_2'(A_236,B_237))
      | ~ m1_subset_1('#skF_3'(A_236,B_237),u1_struct_0(A_236))
      | ~ m1_subset_1(B_235,k1_zfmisc_1(u1_struct_0(A_236)))
      | v4_pre_topc(B_237,A_236)
      | ~ m1_subset_1(B_237,k1_zfmisc_1(u1_struct_0(A_236)))
      | ~ l1_pre_topc(A_236)
      | ~ v2_pre_topc(A_236)
      | v2_struct_0(A_236) ) ),
    inference(resolution,[status(thm)],[c_287,c_42])).

tff(c_46,plain,(
    ! [A_48,B_60,C_66] :
      ( v13_waybel_0('#skF_4'(A_48,B_60,C_66),k3_yellow_1(k2_struct_0(A_48)))
      | ~ r2_hidden(C_66,k2_pre_topc(A_48,B_60))
      | ~ m1_subset_1(C_66,u1_struct_0(A_48))
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ l1_pre_topc(A_48)
      | ~ v2_pre_topc(A_48)
      | v2_struct_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_48,plain,(
    ! [A_48,B_60,C_66] :
      ( v2_waybel_0('#skF_4'(A_48,B_60,C_66),k3_yellow_1(k2_struct_0(A_48)))
      | ~ r2_hidden(C_66,k2_pre_topc(A_48,B_60))
      | ~ m1_subset_1(C_66,u1_struct_0(A_48))
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ l1_pre_topc(A_48)
      | ~ v2_pre_topc(A_48)
      | v2_struct_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_50,plain,(
    ! [A_48,B_60,C_66] :
      ( v1_subset_1('#skF_4'(A_48,B_60,C_66),u1_struct_0(k3_yellow_1(k2_struct_0(A_48))))
      | ~ r2_hidden(C_66,k2_pre_topc(A_48,B_60))
      | ~ m1_subset_1(C_66,u1_struct_0(A_48))
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ l1_pre_topc(A_48)
      | ~ v2_pre_topc(A_48)
      | v2_struct_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_44,plain,(
    ! [A_48,B_60,C_66] :
      ( m1_subset_1('#skF_4'(A_48,B_60,C_66),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_48)))))
      | ~ r2_hidden(C_66,k2_pre_topc(A_48,B_60))
      | ~ m1_subset_1(C_66,u1_struct_0(A_48))
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ l1_pre_topc(A_48)
      | ~ v2_pre_topc(A_48)
      | v2_struct_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_175,plain,(
    ! [A_137,B_138,C_139] :
      ( r1_waybel_7(A_137,'#skF_4'(A_137,B_138,C_139),C_139)
      | ~ r2_hidden(C_139,k2_pre_topc(A_137,B_138))
      | ~ m1_subset_1(C_139,u1_struct_0(A_137))
      | ~ m1_subset_1(B_138,k1_zfmisc_1(u1_struct_0(A_137)))
      | ~ l1_pre_topc(A_137)
      | ~ v2_pre_topc(A_137)
      | v2_struct_0(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_177,plain,(
    ! [C_139] :
      ( r1_waybel_7('#skF_5','#skF_4'('#skF_5','#skF_6',C_139),C_139)
      | ~ r2_hidden(C_139,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_139,u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_54,c_175])).

tff(c_180,plain,(
    ! [C_139] :
      ( r1_waybel_7('#skF_5','#skF_4'('#skF_5','#skF_6',C_139),C_139)
      | ~ r2_hidden(C_139,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_139,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_177])).

tff(c_181,plain,(
    ! [C_139] :
      ( r1_waybel_7('#skF_5','#skF_4'('#skF_5','#skF_6',C_139),C_139)
      | ~ r2_hidden(C_139,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_139,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_180])).

tff(c_100,plain,(
    ! [D_92,C_90] :
      ( v4_pre_topc('#skF_6','#skF_5')
      | r2_hidden(D_92,'#skF_6')
      | ~ r1_waybel_7('#skF_5',C_90,D_92)
      | ~ m1_subset_1(D_92,u1_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_6',C_90)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))))
      | ~ v13_waybel_0(C_90,k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v2_waybel_0(C_90,k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v1_subset_1(C_90,u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))
      | v1_xboole_0(C_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_186,plain,(
    ! [D_147,C_148] :
      ( r2_hidden(D_147,'#skF_6')
      | ~ r1_waybel_7('#skF_5',C_148,D_147)
      | ~ m1_subset_1(D_147,u1_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_6',C_148)
      | ~ m1_subset_1(C_148,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))))
      | ~ v13_waybel_0(C_148,k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v2_waybel_0(C_148,k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v1_subset_1(C_148,u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))
      | v1_xboole_0(C_148) ) ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_100])).

tff(c_250,plain,(
    ! [C_188] :
      ( r2_hidden(C_188,'#skF_6')
      | ~ r2_hidden('#skF_6','#skF_4'('#skF_5','#skF_6',C_188))
      | ~ m1_subset_1('#skF_4'('#skF_5','#skF_6',C_188),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))))
      | ~ v13_waybel_0('#skF_4'('#skF_5','#skF_6',C_188),k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v2_waybel_0('#skF_4'('#skF_5','#skF_6',C_188),k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v1_subset_1('#skF_4'('#skF_5','#skF_6',C_188),u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))
      | v1_xboole_0('#skF_4'('#skF_5','#skF_6',C_188))
      | ~ r2_hidden(C_188,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_188,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_181,c_186])).

tff(c_254,plain,(
    ! [C_66] :
      ( r2_hidden(C_66,'#skF_6')
      | ~ r2_hidden('#skF_6','#skF_4'('#skF_5','#skF_6',C_66))
      | ~ v13_waybel_0('#skF_4'('#skF_5','#skF_6',C_66),k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v2_waybel_0('#skF_4'('#skF_5','#skF_6',C_66),k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v1_subset_1('#skF_4'('#skF_5','#skF_6',C_66),u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))
      | v1_xboole_0('#skF_4'('#skF_5','#skF_6',C_66))
      | ~ r2_hidden(C_66,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_66,u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_44,c_250])).

tff(c_257,plain,(
    ! [C_66] :
      ( r2_hidden(C_66,'#skF_6')
      | ~ r2_hidden('#skF_6','#skF_4'('#skF_5','#skF_6',C_66))
      | ~ v13_waybel_0('#skF_4'('#skF_5','#skF_6',C_66),k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v2_waybel_0('#skF_4'('#skF_5','#skF_6',C_66),k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v1_subset_1('#skF_4'('#skF_5','#skF_6',C_66),u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))
      | v1_xboole_0('#skF_4'('#skF_5','#skF_6',C_66))
      | ~ r2_hidden(C_66,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_66,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_254])).

tff(c_259,plain,(
    ! [C_189] :
      ( r2_hidden(C_189,'#skF_6')
      | ~ r2_hidden('#skF_6','#skF_4'('#skF_5','#skF_6',C_189))
      | ~ v13_waybel_0('#skF_4'('#skF_5','#skF_6',C_189),k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v2_waybel_0('#skF_4'('#skF_5','#skF_6',C_189),k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v1_subset_1('#skF_4'('#skF_5','#skF_6',C_189),u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))
      | v1_xboole_0('#skF_4'('#skF_5','#skF_6',C_189))
      | ~ r2_hidden(C_189,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_189,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_257])).

tff(c_263,plain,(
    ! [C_66] :
      ( r2_hidden(C_66,'#skF_6')
      | ~ r2_hidden('#skF_6','#skF_4'('#skF_5','#skF_6',C_66))
      | ~ v13_waybel_0('#skF_4'('#skF_5','#skF_6',C_66),k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v2_waybel_0('#skF_4'('#skF_5','#skF_6',C_66),k3_yellow_1(k2_struct_0('#skF_5')))
      | v1_xboole_0('#skF_4'('#skF_5','#skF_6',C_66))
      | ~ r2_hidden(C_66,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_66,u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_50,c_259])).

tff(c_266,plain,(
    ! [C_66] :
      ( r2_hidden(C_66,'#skF_6')
      | ~ r2_hidden('#skF_6','#skF_4'('#skF_5','#skF_6',C_66))
      | ~ v13_waybel_0('#skF_4'('#skF_5','#skF_6',C_66),k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v2_waybel_0('#skF_4'('#skF_5','#skF_6',C_66),k3_yellow_1(k2_struct_0('#skF_5')))
      | v1_xboole_0('#skF_4'('#skF_5','#skF_6',C_66))
      | ~ r2_hidden(C_66,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_66,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_263])).

tff(c_268,plain,(
    ! [C_190] :
      ( r2_hidden(C_190,'#skF_6')
      | ~ r2_hidden('#skF_6','#skF_4'('#skF_5','#skF_6',C_190))
      | ~ v13_waybel_0('#skF_4'('#skF_5','#skF_6',C_190),k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v2_waybel_0('#skF_4'('#skF_5','#skF_6',C_190),k3_yellow_1(k2_struct_0('#skF_5')))
      | v1_xboole_0('#skF_4'('#skF_5','#skF_6',C_190))
      | ~ r2_hidden(C_190,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_190,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_266])).

tff(c_272,plain,(
    ! [C_66] :
      ( r2_hidden(C_66,'#skF_6')
      | ~ r2_hidden('#skF_6','#skF_4'('#skF_5','#skF_6',C_66))
      | ~ v13_waybel_0('#skF_4'('#skF_5','#skF_6',C_66),k3_yellow_1(k2_struct_0('#skF_5')))
      | v1_xboole_0('#skF_4'('#skF_5','#skF_6',C_66))
      | ~ r2_hidden(C_66,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_66,u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_48,c_268])).

tff(c_275,plain,(
    ! [C_66] :
      ( r2_hidden(C_66,'#skF_6')
      | ~ r2_hidden('#skF_6','#skF_4'('#skF_5','#skF_6',C_66))
      | ~ v13_waybel_0('#skF_4'('#skF_5','#skF_6',C_66),k3_yellow_1(k2_struct_0('#skF_5')))
      | v1_xboole_0('#skF_4'('#skF_5','#skF_6',C_66))
      | ~ r2_hidden(C_66,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_66,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_272])).

tff(c_277,plain,(
    ! [C_191] :
      ( r2_hidden(C_191,'#skF_6')
      | ~ r2_hidden('#skF_6','#skF_4'('#skF_5','#skF_6',C_191))
      | ~ v13_waybel_0('#skF_4'('#skF_5','#skF_6',C_191),k3_yellow_1(k2_struct_0('#skF_5')))
      | v1_xboole_0('#skF_4'('#skF_5','#skF_6',C_191))
      | ~ r2_hidden(C_191,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_191,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_275])).

tff(c_281,plain,(
    ! [C_66] :
      ( r2_hidden(C_66,'#skF_6')
      | ~ r2_hidden('#skF_6','#skF_4'('#skF_5','#skF_6',C_66))
      | v1_xboole_0('#skF_4'('#skF_5','#skF_6',C_66))
      | ~ r2_hidden(C_66,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_66,u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_46,c_277])).

tff(c_284,plain,(
    ! [C_66] :
      ( r2_hidden(C_66,'#skF_6')
      | ~ r2_hidden('#skF_6','#skF_4'('#skF_5','#skF_6',C_66))
      | v1_xboole_0('#skF_4'('#skF_5','#skF_6',C_66))
      | ~ r2_hidden(C_66,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_66,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_281])).

tff(c_285,plain,(
    ! [C_66] :
      ( r2_hidden(C_66,'#skF_6')
      | ~ r2_hidden('#skF_6','#skF_4'('#skF_5','#skF_6',C_66))
      | v1_xboole_0('#skF_4'('#skF_5','#skF_6',C_66))
      | ~ r2_hidden(C_66,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_66,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_284])).

tff(c_400,plain,(
    ! [B_237] :
      ( r2_hidden('#skF_3'('#skF_5',B_237),'#skF_6')
      | v1_xboole_0('#skF_4'('#skF_5','#skF_6','#skF_3'('#skF_5',B_237)))
      | ~ r2_hidden('#skF_3'('#skF_5',B_237),k2_pre_topc('#skF_5','#skF_6'))
      | ~ r1_waybel_0('#skF_5','#skF_2'('#skF_5',B_237),'#skF_6')
      | ~ l1_waybel_0('#skF_2'('#skF_5',B_237),'#skF_5')
      | ~ v3_yellow_6('#skF_2'('#skF_5',B_237),'#skF_5')
      | ~ v7_waybel_0('#skF_2'('#skF_5',B_237))
      | ~ v4_orders_2('#skF_2'('#skF_5',B_237))
      | v2_struct_0('#skF_2'('#skF_5',B_237))
      | ~ m1_subset_1('#skF_3'('#skF_5',B_237),u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v4_pre_topc(B_237,'#skF_5')
      | ~ m1_subset_1(B_237,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_394,c_285])).

tff(c_407,plain,(
    ! [B_237] :
      ( r2_hidden('#skF_3'('#skF_5',B_237),'#skF_6')
      | v1_xboole_0('#skF_4'('#skF_5','#skF_6','#skF_3'('#skF_5',B_237)))
      | ~ r2_hidden('#skF_3'('#skF_5',B_237),k2_pre_topc('#skF_5','#skF_6'))
      | ~ r1_waybel_0('#skF_5','#skF_2'('#skF_5',B_237),'#skF_6')
      | ~ l1_waybel_0('#skF_2'('#skF_5',B_237),'#skF_5')
      | ~ v3_yellow_6('#skF_2'('#skF_5',B_237),'#skF_5')
      | ~ v7_waybel_0('#skF_2'('#skF_5',B_237))
      | ~ v4_orders_2('#skF_2'('#skF_5',B_237))
      | v2_struct_0('#skF_2'('#skF_5',B_237))
      | ~ m1_subset_1('#skF_3'('#skF_5',B_237),u1_struct_0('#skF_5'))
      | v4_pre_topc(B_237,'#skF_5')
      | ~ m1_subset_1(B_237,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_400])).

tff(c_409,plain,(
    ! [B_238] :
      ( r2_hidden('#skF_3'('#skF_5',B_238),'#skF_6')
      | v1_xboole_0('#skF_4'('#skF_5','#skF_6','#skF_3'('#skF_5',B_238)))
      | ~ r2_hidden('#skF_3'('#skF_5',B_238),k2_pre_topc('#skF_5','#skF_6'))
      | ~ r1_waybel_0('#skF_5','#skF_2'('#skF_5',B_238),'#skF_6')
      | ~ l1_waybel_0('#skF_2'('#skF_5',B_238),'#skF_5')
      | ~ v3_yellow_6('#skF_2'('#skF_5',B_238),'#skF_5')
      | ~ v7_waybel_0('#skF_2'('#skF_5',B_238))
      | ~ v4_orders_2('#skF_2'('#skF_5',B_238))
      | v2_struct_0('#skF_2'('#skF_5',B_238))
      | ~ m1_subset_1('#skF_3'('#skF_5',B_238),u1_struct_0('#skF_5'))
      | v4_pre_topc(B_238,'#skF_5')
      | ~ m1_subset_1(B_238,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_407])).

tff(c_413,plain,(
    ! [B_37] :
      ( r2_hidden('#skF_3'('#skF_5',B_37),'#skF_6')
      | v1_xboole_0('#skF_4'('#skF_5','#skF_6','#skF_3'('#skF_5',B_37)))
      | ~ r1_waybel_0('#skF_5','#skF_2'('#skF_5',B_37),'#skF_6')
      | ~ l1_waybel_0('#skF_2'('#skF_5',B_37),'#skF_5')
      | ~ v3_yellow_6('#skF_2'('#skF_5',B_37),'#skF_5')
      | ~ v7_waybel_0('#skF_2'('#skF_5',B_37))
      | ~ v4_orders_2('#skF_2'('#skF_5',B_37))
      | v2_struct_0('#skF_2'('#skF_5',B_37))
      | ~ m1_subset_1('#skF_3'('#skF_5',B_37),u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v4_pre_topc(B_37,'#skF_5')
      | ~ m1_subset_1(B_37,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_229,c_409])).

tff(c_416,plain,(
    ! [B_37] :
      ( r2_hidden('#skF_3'('#skF_5',B_37),'#skF_6')
      | v1_xboole_0('#skF_4'('#skF_5','#skF_6','#skF_3'('#skF_5',B_37)))
      | ~ r1_waybel_0('#skF_5','#skF_2'('#skF_5',B_37),'#skF_6')
      | ~ l1_waybel_0('#skF_2'('#skF_5',B_37),'#skF_5')
      | ~ v3_yellow_6('#skF_2'('#skF_5',B_37),'#skF_5')
      | ~ v7_waybel_0('#skF_2'('#skF_5',B_37))
      | ~ v4_orders_2('#skF_2'('#skF_5',B_37))
      | v2_struct_0('#skF_2'('#skF_5',B_37))
      | ~ m1_subset_1('#skF_3'('#skF_5',B_37),u1_struct_0('#skF_5'))
      | v4_pre_topc(B_37,'#skF_5')
      | ~ m1_subset_1(B_37,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_413])).

tff(c_418,plain,(
    ! [B_239] :
      ( r2_hidden('#skF_3'('#skF_5',B_239),'#skF_6')
      | v1_xboole_0('#skF_4'('#skF_5','#skF_6','#skF_3'('#skF_5',B_239)))
      | ~ r1_waybel_0('#skF_5','#skF_2'('#skF_5',B_239),'#skF_6')
      | ~ l1_waybel_0('#skF_2'('#skF_5',B_239),'#skF_5')
      | ~ v3_yellow_6('#skF_2'('#skF_5',B_239),'#skF_5')
      | ~ v7_waybel_0('#skF_2'('#skF_5',B_239))
      | ~ v4_orders_2('#skF_2'('#skF_5',B_239))
      | v2_struct_0('#skF_2'('#skF_5',B_239))
      | ~ m1_subset_1('#skF_3'('#skF_5',B_239),u1_struct_0('#skF_5'))
      | v4_pre_topc(B_239,'#skF_5')
      | ~ m1_subset_1(B_239,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_416])).

tff(c_422,plain,(
    ! [B_37] :
      ( r2_hidden('#skF_3'('#skF_5',B_37),'#skF_6')
      | v1_xboole_0('#skF_4'('#skF_5','#skF_6','#skF_3'('#skF_5',B_37)))
      | ~ r1_waybel_0('#skF_5','#skF_2'('#skF_5',B_37),'#skF_6')
      | ~ l1_waybel_0('#skF_2'('#skF_5',B_37),'#skF_5')
      | ~ v3_yellow_6('#skF_2'('#skF_5',B_37),'#skF_5')
      | ~ v7_waybel_0('#skF_2'('#skF_5',B_37))
      | ~ v4_orders_2('#skF_2'('#skF_5',B_37))
      | v2_struct_0('#skF_2'('#skF_5',B_37))
      | v4_pre_topc(B_37,'#skF_5')
      | ~ m1_subset_1(B_37,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_24,c_418])).

tff(c_425,plain,(
    ! [B_37] :
      ( r2_hidden('#skF_3'('#skF_5',B_37),'#skF_6')
      | v1_xboole_0('#skF_4'('#skF_5','#skF_6','#skF_3'('#skF_5',B_37)))
      | ~ r1_waybel_0('#skF_5','#skF_2'('#skF_5',B_37),'#skF_6')
      | ~ l1_waybel_0('#skF_2'('#skF_5',B_37),'#skF_5')
      | ~ v3_yellow_6('#skF_2'('#skF_5',B_37),'#skF_5')
      | ~ v7_waybel_0('#skF_2'('#skF_5',B_37))
      | ~ v4_orders_2('#skF_2'('#skF_5',B_37))
      | v2_struct_0('#skF_2'('#skF_5',B_37))
      | v4_pre_topc(B_37,'#skF_5')
      | ~ m1_subset_1(B_37,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_422])).

tff(c_431,plain,(
    ! [B_244] :
      ( r2_hidden('#skF_3'('#skF_5',B_244),'#skF_6')
      | v1_xboole_0('#skF_4'('#skF_5','#skF_6','#skF_3'('#skF_5',B_244)))
      | ~ r1_waybel_0('#skF_5','#skF_2'('#skF_5',B_244),'#skF_6')
      | ~ l1_waybel_0('#skF_2'('#skF_5',B_244),'#skF_5')
      | ~ v3_yellow_6('#skF_2'('#skF_5',B_244),'#skF_5')
      | ~ v7_waybel_0('#skF_2'('#skF_5',B_244))
      | ~ v4_orders_2('#skF_2'('#skF_5',B_244))
      | v2_struct_0('#skF_2'('#skF_5',B_244))
      | v4_pre_topc(B_244,'#skF_5')
      | ~ m1_subset_1(B_244,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_425])).

tff(c_434,plain,
    ( r2_hidden('#skF_3'('#skF_5','#skF_6'),'#skF_6')
    | v1_xboole_0('#skF_4'('#skF_5','#skF_6','#skF_3'('#skF_5','#skF_6')))
    | ~ r1_waybel_0('#skF_5','#skF_2'('#skF_5','#skF_6'),'#skF_6')
    | ~ l1_waybel_0('#skF_2'('#skF_5','#skF_6'),'#skF_5')
    | ~ v3_yellow_6('#skF_2'('#skF_5','#skF_6'),'#skF_5')
    | ~ v7_waybel_0('#skF_2'('#skF_5','#skF_6'))
    | ~ v4_orders_2('#skF_2'('#skF_5','#skF_6'))
    | v2_struct_0('#skF_2'('#skF_5','#skF_6'))
    | v4_pre_topc('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_431])).

tff(c_437,plain,
    ( r2_hidden('#skF_3'('#skF_5','#skF_6'),'#skF_6')
    | v1_xboole_0('#skF_4'('#skF_5','#skF_6','#skF_3'('#skF_5','#skF_6')))
    | v2_struct_0('#skF_2'('#skF_5','#skF_6'))
    | v4_pre_topc('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_125,c_140,c_133,c_149,c_434])).

tff(c_438,plain,
    ( r2_hidden('#skF_3'('#skF_5','#skF_6'),'#skF_6')
    | v1_xboole_0('#skF_4'('#skF_5','#skF_6','#skF_3'('#skF_5','#skF_6'))) ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_109,c_437])).

tff(c_439,plain,(
    v1_xboole_0('#skF_4'('#skF_5','#skF_6','#skF_3'('#skF_5','#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_438])).

tff(c_52,plain,(
    ! [A_48,B_60,C_66] :
      ( ~ v1_xboole_0('#skF_4'(A_48,B_60,C_66))
      | ~ r2_hidden(C_66,k2_pre_topc(A_48,B_60))
      | ~ m1_subset_1(C_66,u1_struct_0(A_48))
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ l1_pre_topc(A_48)
      | ~ v2_pre_topc(A_48)
      | v2_struct_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_308,plain,(
    ! [A_193,B_195,B_194] :
      ( ~ v1_xboole_0('#skF_4'(A_193,B_195,'#skF_3'(A_193,B_194)))
      | ~ r1_waybel_0(A_193,'#skF_2'(A_193,B_194),B_195)
      | ~ l1_waybel_0('#skF_2'(A_193,B_194),A_193)
      | ~ v3_yellow_6('#skF_2'(A_193,B_194),A_193)
      | ~ v7_waybel_0('#skF_2'(A_193,B_194))
      | ~ v4_orders_2('#skF_2'(A_193,B_194))
      | v2_struct_0('#skF_2'(A_193,B_194))
      | ~ m1_subset_1('#skF_3'(A_193,B_194),u1_struct_0(A_193))
      | ~ m1_subset_1(B_195,k1_zfmisc_1(u1_struct_0(A_193)))
      | v4_pre_topc(B_194,A_193)
      | ~ m1_subset_1(B_194,k1_zfmisc_1(u1_struct_0(A_193)))
      | ~ l1_pre_topc(A_193)
      | ~ v2_pre_topc(A_193)
      | v2_struct_0(A_193) ) ),
    inference(resolution,[status(thm)],[c_287,c_52])).

tff(c_441,plain,
    ( ~ r1_waybel_0('#skF_5','#skF_2'('#skF_5','#skF_6'),'#skF_6')
    | ~ l1_waybel_0('#skF_2'('#skF_5','#skF_6'),'#skF_5')
    | ~ v3_yellow_6('#skF_2'('#skF_5','#skF_6'),'#skF_5')
    | ~ v7_waybel_0('#skF_2'('#skF_5','#skF_6'))
    | ~ v4_orders_2('#skF_2'('#skF_5','#skF_6'))
    | v2_struct_0('#skF_2'('#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_3'('#skF_5','#skF_6'),u1_struct_0('#skF_5'))
    | v4_pre_topc('#skF_6','#skF_5')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_439,c_308])).

tff(c_444,plain,
    ( v2_struct_0('#skF_2'('#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_3'('#skF_5','#skF_6'),u1_struct_0('#skF_5'))
    | v4_pre_topc('#skF_6','#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_117,c_125,c_140,c_133,c_149,c_441])).

tff(c_445,plain,(
    ~ m1_subset_1('#skF_3'('#skF_5','#skF_6'),u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_101,c_109,c_444])).

tff(c_448,plain,
    ( v4_pre_topc('#skF_6','#skF_5')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_24,c_445])).

tff(c_451,plain,
    ( v4_pre_topc('#skF_6','#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_448])).

tff(c_453,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_101,c_451])).

tff(c_454,plain,(
    r2_hidden('#skF_3'('#skF_5','#skF_6'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_438])).

tff(c_20,plain,(
    ! [A_23,B_37] :
      ( ~ r2_hidden('#skF_3'(A_23,B_37),B_37)
      | v4_pre_topc(B_37,A_23)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_457,plain,
    ( v4_pre_topc('#skF_6','#skF_5')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_454,c_20])).

tff(c_460,plain,
    ( v4_pre_topc('#skF_6','#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_457])).

tff(c_462,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_101,c_460])).

tff(c_464,plain,(
    v4_pre_topc('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_66,plain,
    ( m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ v4_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_472,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_464,c_66])).

tff(c_68,plain,
    ( r2_hidden('#skF_6','#skF_7')
    | ~ v4_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_468,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_464,c_68])).

tff(c_463,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_76,plain,
    ( v1_subset_1('#skF_7',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))
    | ~ v4_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_478,plain,(
    v1_subset_1('#skF_7',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_464,c_76])).

tff(c_74,plain,
    ( v2_waybel_0('#skF_7',k3_yellow_1(k2_struct_0('#skF_5')))
    | ~ v4_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_476,plain,(
    v2_waybel_0('#skF_7',k3_yellow_1(k2_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_464,c_74])).

tff(c_72,plain,
    ( v13_waybel_0('#skF_7',k3_yellow_1(k2_struct_0('#skF_5')))
    | ~ v4_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_474,plain,(
    v13_waybel_0('#skF_7',k3_yellow_1(k2_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_464,c_72])).

tff(c_70,plain,
    ( m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))))
    | ~ v4_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_480,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_464,c_70])).

tff(c_64,plain,
    ( r1_waybel_7('#skF_5','#skF_7','#skF_8')
    | ~ v4_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_470,plain,(
    r1_waybel_7('#skF_5','#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_464,c_64])).

tff(c_649,plain,(
    ! [C_322,A_323,B_324,D_325] :
      ( r2_hidden(C_322,k2_pre_topc(A_323,B_324))
      | ~ r1_waybel_7(A_323,D_325,C_322)
      | ~ r2_hidden(B_324,D_325)
      | ~ m1_subset_1(D_325,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_323)))))
      | ~ v13_waybel_0(D_325,k3_yellow_1(k2_struct_0(A_323)))
      | ~ v2_waybel_0(D_325,k3_yellow_1(k2_struct_0(A_323)))
      | ~ v1_subset_1(D_325,u1_struct_0(k3_yellow_1(k2_struct_0(A_323))))
      | v1_xboole_0(D_325)
      | ~ m1_subset_1(C_322,u1_struct_0(A_323))
      | ~ m1_subset_1(B_324,k1_zfmisc_1(u1_struct_0(A_323)))
      | ~ l1_pre_topc(A_323)
      | ~ v2_pre_topc(A_323)
      | v2_struct_0(A_323) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_653,plain,(
    ! [B_324] :
      ( r2_hidden('#skF_8',k2_pre_topc('#skF_5',B_324))
      | ~ r2_hidden(B_324,'#skF_7')
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))))
      | ~ v13_waybel_0('#skF_7',k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v2_waybel_0('#skF_7',k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v1_subset_1('#skF_7',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))
      | v1_xboole_0('#skF_7')
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_324,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_470,c_649])).

tff(c_660,plain,(
    ! [B_324] :
      ( r2_hidden('#skF_8',k2_pre_topc('#skF_5',B_324))
      | ~ r2_hidden(B_324,'#skF_7')
      | v1_xboole_0('#skF_7')
      | ~ m1_subset_1(B_324,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_472,c_478,c_476,c_474,c_480,c_653])).

tff(c_662,plain,(
    ! [B_326] :
      ( r2_hidden('#skF_8',k2_pre_topc('#skF_5',B_326))
      | ~ r2_hidden(B_326,'#skF_7')
      | ~ m1_subset_1(B_326,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_463,c_660])).

tff(c_665,plain,
    ( r2_hidden('#skF_8',k2_pre_topc('#skF_5','#skF_6'))
    | ~ r2_hidden('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_54,c_662])).

tff(c_668,plain,(
    r2_hidden('#skF_8',k2_pre_topc('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_468,c_665])).

tff(c_16,plain,(
    ! [A_1,B_13,C_19] :
      ( ~ v2_struct_0('#skF_1'(A_1,B_13,C_19))
      | ~ r2_hidden(C_19,k2_pre_topc(A_1,B_13))
      | ~ m1_subset_1(C_19,u1_struct_0(A_1))
      | ~ m1_subset_1(B_13,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_680,plain,
    ( ~ v2_struct_0('#skF_1'('#skF_5','#skF_6','#skF_8'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_668,c_16])).

tff(c_703,plain,
    ( ~ v2_struct_0('#skF_1'('#skF_5','#skF_6','#skF_8'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_472,c_680])).

tff(c_704,plain,(
    ~ v2_struct_0('#skF_1'('#skF_5','#skF_6','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_703])).

tff(c_62,plain,
    ( ~ r2_hidden('#skF_8','#skF_6')
    | ~ v4_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_466,plain,(
    ~ r2_hidden('#skF_8','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_464,c_62])).

tff(c_14,plain,(
    ! [A_1,B_13,C_19] :
      ( v4_orders_2('#skF_1'(A_1,B_13,C_19))
      | ~ r2_hidden(C_19,k2_pre_topc(A_1,B_13))
      | ~ m1_subset_1(C_19,u1_struct_0(A_1))
      | ~ m1_subset_1(B_13,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_676,plain,
    ( v4_orders_2('#skF_1'('#skF_5','#skF_6','#skF_8'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_668,c_14])).

tff(c_695,plain,
    ( v4_orders_2('#skF_1'('#skF_5','#skF_6','#skF_8'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_472,c_676])).

tff(c_696,plain,(
    v4_orders_2('#skF_1'('#skF_5','#skF_6','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_695])).

tff(c_12,plain,(
    ! [A_1,B_13,C_19] :
      ( v7_waybel_0('#skF_1'(A_1,B_13,C_19))
      | ~ r2_hidden(C_19,k2_pre_topc(A_1,B_13))
      | ~ m1_subset_1(C_19,u1_struct_0(A_1))
      | ~ m1_subset_1(B_13,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_674,plain,
    ( v7_waybel_0('#skF_1'('#skF_5','#skF_6','#skF_8'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_668,c_12])).

tff(c_691,plain,
    ( v7_waybel_0('#skF_1'('#skF_5','#skF_6','#skF_8'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_472,c_674])).

tff(c_692,plain,(
    v7_waybel_0('#skF_1'('#skF_5','#skF_6','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_691])).

tff(c_8,plain,(
    ! [A_1,B_13,C_19] :
      ( l1_waybel_0('#skF_1'(A_1,B_13,C_19),A_1)
      | ~ r2_hidden(C_19,k2_pre_topc(A_1,B_13))
      | ~ m1_subset_1(C_19,u1_struct_0(A_1))
      | ~ m1_subset_1(B_13,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_672,plain,
    ( l1_waybel_0('#skF_1'('#skF_5','#skF_6','#skF_8'),'#skF_5')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_668,c_8])).

tff(c_687,plain,
    ( l1_waybel_0('#skF_1'('#skF_5','#skF_6','#skF_8'),'#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_472,c_672])).

tff(c_688,plain,(
    l1_waybel_0('#skF_1'('#skF_5','#skF_6','#skF_8'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_687])).

tff(c_556,plain,(
    ! [A_275,B_276,C_277] :
      ( v3_yellow_6('#skF_1'(A_275,B_276,C_277),A_275)
      | ~ r2_hidden(C_277,k2_pre_topc(A_275,B_276))
      | ~ m1_subset_1(C_277,u1_struct_0(A_275))
      | ~ m1_subset_1(B_276,k1_zfmisc_1(u1_struct_0(A_275)))
      | ~ l1_pre_topc(A_275)
      | ~ v2_pre_topc(A_275)
      | v2_struct_0(A_275) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_560,plain,(
    ! [C_277] :
      ( v3_yellow_6('#skF_1'('#skF_5','#skF_6',C_277),'#skF_5')
      | ~ r2_hidden(C_277,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_277,u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_54,c_556])).

tff(c_564,plain,(
    ! [C_277] :
      ( v3_yellow_6('#skF_1'('#skF_5','#skF_6',C_277),'#skF_5')
      | ~ r2_hidden(C_277,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_277,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_560])).

tff(c_565,plain,(
    ! [C_277] :
      ( v3_yellow_6('#skF_1'('#skF_5','#skF_6',C_277),'#skF_5')
      | ~ r2_hidden(C_277,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_277,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_564])).

tff(c_580,plain,(
    ! [A_289,B_290,C_291] :
      ( r1_waybel_0(A_289,'#skF_1'(A_289,B_290,C_291),B_290)
      | ~ r2_hidden(C_291,k2_pre_topc(A_289,B_290))
      | ~ m1_subset_1(C_291,u1_struct_0(A_289))
      | ~ m1_subset_1(B_290,k1_zfmisc_1(u1_struct_0(A_289)))
      | ~ l1_pre_topc(A_289)
      | ~ v2_pre_topc(A_289)
      | v2_struct_0(A_289) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_584,plain,(
    ! [C_291] :
      ( r1_waybel_0('#skF_5','#skF_1'('#skF_5','#skF_6',C_291),'#skF_6')
      | ~ r2_hidden(C_291,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_291,u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_54,c_580])).

tff(c_588,plain,(
    ! [C_291] :
      ( r1_waybel_0('#skF_5','#skF_1'('#skF_5','#skF_6',C_291),'#skF_6')
      | ~ r2_hidden(C_291,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_291,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_584])).

tff(c_589,plain,(
    ! [C_291] :
      ( r1_waybel_0('#skF_5','#skF_1'('#skF_5','#skF_6',C_291),'#skF_6')
      | ~ r2_hidden(C_291,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_291,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_588])).

tff(c_4,plain,(
    ! [C_19,A_1,B_13] :
      ( r2_hidden(C_19,k10_yellow_6(A_1,'#skF_1'(A_1,B_13,C_19)))
      | ~ r2_hidden(C_19,k2_pre_topc(A_1,B_13))
      | ~ m1_subset_1(C_19,u1_struct_0(A_1))
      | ~ m1_subset_1(B_13,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_634,plain,(
    ! [D_312,B_313,A_314,C_315] :
      ( r2_hidden(D_312,B_313)
      | ~ r2_hidden(D_312,k10_yellow_6(A_314,C_315))
      | ~ m1_subset_1(D_312,u1_struct_0(A_314))
      | ~ r1_waybel_0(A_314,C_315,B_313)
      | ~ l1_waybel_0(C_315,A_314)
      | ~ v3_yellow_6(C_315,A_314)
      | ~ v7_waybel_0(C_315)
      | ~ v4_orders_2(C_315)
      | v2_struct_0(C_315)
      | ~ v4_pre_topc(B_313,A_314)
      | ~ m1_subset_1(B_313,k1_zfmisc_1(u1_struct_0(A_314)))
      | ~ l1_pre_topc(A_314)
      | ~ v2_pre_topc(A_314)
      | v2_struct_0(A_314) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_842,plain,(
    ! [C_396,B_397,A_398,B_399] :
      ( r2_hidden(C_396,B_397)
      | ~ r1_waybel_0(A_398,'#skF_1'(A_398,B_399,C_396),B_397)
      | ~ l1_waybel_0('#skF_1'(A_398,B_399,C_396),A_398)
      | ~ v3_yellow_6('#skF_1'(A_398,B_399,C_396),A_398)
      | ~ v7_waybel_0('#skF_1'(A_398,B_399,C_396))
      | ~ v4_orders_2('#skF_1'(A_398,B_399,C_396))
      | v2_struct_0('#skF_1'(A_398,B_399,C_396))
      | ~ v4_pre_topc(B_397,A_398)
      | ~ m1_subset_1(B_397,k1_zfmisc_1(u1_struct_0(A_398)))
      | ~ r2_hidden(C_396,k2_pre_topc(A_398,B_399))
      | ~ m1_subset_1(C_396,u1_struct_0(A_398))
      | ~ m1_subset_1(B_399,k1_zfmisc_1(u1_struct_0(A_398)))
      | ~ l1_pre_topc(A_398)
      | ~ v2_pre_topc(A_398)
      | v2_struct_0(A_398) ) ),
    inference(resolution,[status(thm)],[c_4,c_634])).

tff(c_846,plain,(
    ! [C_291] :
      ( r2_hidden(C_291,'#skF_6')
      | ~ l1_waybel_0('#skF_1'('#skF_5','#skF_6',C_291),'#skF_5')
      | ~ v3_yellow_6('#skF_1'('#skF_5','#skF_6',C_291),'#skF_5')
      | ~ v7_waybel_0('#skF_1'('#skF_5','#skF_6',C_291))
      | ~ v4_orders_2('#skF_1'('#skF_5','#skF_6',C_291))
      | v2_struct_0('#skF_1'('#skF_5','#skF_6',C_291))
      | ~ v4_pre_topc('#skF_6','#skF_5')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r2_hidden(C_291,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_291,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_589,c_842])).

tff(c_850,plain,(
    ! [C_291] :
      ( r2_hidden(C_291,'#skF_6')
      | ~ l1_waybel_0('#skF_1'('#skF_5','#skF_6',C_291),'#skF_5')
      | ~ v3_yellow_6('#skF_1'('#skF_5','#skF_6',C_291),'#skF_5')
      | ~ v7_waybel_0('#skF_1'('#skF_5','#skF_6',C_291))
      | ~ v4_orders_2('#skF_1'('#skF_5','#skF_6',C_291))
      | v2_struct_0('#skF_1'('#skF_5','#skF_6',C_291))
      | v2_struct_0('#skF_5')
      | ~ r2_hidden(C_291,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_291,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_464,c_846])).

tff(c_852,plain,(
    ! [C_400] :
      ( r2_hidden(C_400,'#skF_6')
      | ~ l1_waybel_0('#skF_1'('#skF_5','#skF_6',C_400),'#skF_5')
      | ~ v3_yellow_6('#skF_1'('#skF_5','#skF_6',C_400),'#skF_5')
      | ~ v7_waybel_0('#skF_1'('#skF_5','#skF_6',C_400))
      | ~ v4_orders_2('#skF_1'('#skF_5','#skF_6',C_400))
      | v2_struct_0('#skF_1'('#skF_5','#skF_6',C_400))
      | ~ r2_hidden(C_400,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_400,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_850])).

tff(c_857,plain,(
    ! [C_401] :
      ( r2_hidden(C_401,'#skF_6')
      | ~ l1_waybel_0('#skF_1'('#skF_5','#skF_6',C_401),'#skF_5')
      | ~ v7_waybel_0('#skF_1'('#skF_5','#skF_6',C_401))
      | ~ v4_orders_2('#skF_1'('#skF_5','#skF_6',C_401))
      | v2_struct_0('#skF_1'('#skF_5','#skF_6',C_401))
      | ~ r2_hidden(C_401,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_401,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_565,c_852])).

tff(c_864,plain,
    ( r2_hidden('#skF_8','#skF_6')
    | ~ l1_waybel_0('#skF_1'('#skF_5','#skF_6','#skF_8'),'#skF_5')
    | ~ v7_waybel_0('#skF_1'('#skF_5','#skF_6','#skF_8'))
    | ~ v4_orders_2('#skF_1'('#skF_5','#skF_6','#skF_8'))
    | v2_struct_0('#skF_1'('#skF_5','#skF_6','#skF_8'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_668,c_857])).

tff(c_871,plain,
    ( r2_hidden('#skF_8','#skF_6')
    | v2_struct_0('#skF_1'('#skF_5','#skF_6','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_472,c_696,c_692,c_688,c_864])).

tff(c_873,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_704,c_466,c_871])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:55:31 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.19/1.74  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.19/1.75  
% 4.19/1.75  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.19/1.76  %$ r1_waybel_7 > r1_waybel_0 > v4_pre_topc > v3_yellow_6 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k2_pre_topc > k10_yellow_6 > #nlpp > u1_struct_0 > k3_yellow_1 > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2
% 4.19/1.76  
% 4.19/1.76  %Foreground sorts:
% 4.19/1.76  
% 4.19/1.76  
% 4.19/1.76  %Background operators:
% 4.19/1.76  
% 4.19/1.76  
% 4.19/1.76  %Foreground operators:
% 4.19/1.76  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.19/1.76  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.19/1.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.19/1.76  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.19/1.76  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 4.19/1.76  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 4.19/1.76  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 4.19/1.76  tff(k10_yellow_6, type, k10_yellow_6: ($i * $i) > $i).
% 4.19/1.76  tff(v3_yellow_6, type, v3_yellow_6: ($i * $i) > $o).
% 4.19/1.76  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.19/1.76  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 4.19/1.76  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 4.19/1.76  tff('#skF_7', type, '#skF_7': $i).
% 4.19/1.76  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.19/1.76  tff('#skF_5', type, '#skF_5': $i).
% 4.19/1.76  tff(r1_waybel_0, type, r1_waybel_0: ($i * $i * $i) > $o).
% 4.19/1.76  tff('#skF_6', type, '#skF_6': $i).
% 4.19/1.76  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 4.19/1.76  tff(r1_waybel_7, type, r1_waybel_7: ($i * $i * $i) > $o).
% 4.19/1.76  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.19/1.76  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 4.19/1.76  tff('#skF_8', type, '#skF_8': $i).
% 4.19/1.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.19/1.76  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 4.19/1.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.19/1.76  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.19/1.76  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 4.19/1.76  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.19/1.76  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.19/1.76  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.19/1.76  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.19/1.76  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.19/1.76  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.19/1.76  
% 4.69/1.80  tff(f_154, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (![C]: (((((~v1_xboole_0(C) & v1_subset_1(C, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(C, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(C, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (r2_hidden(B, C) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r1_waybel_7(A, C, D) => r2_hidden(D, B)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_yellow19)).
% 4.69/1.80  tff(f_89, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (![C]: (((((~v2_struct_0(C) & v4_orders_2(C)) & v7_waybel_0(C)) & v3_yellow_6(C, A)) & l1_waybel_0(C, A)) => (r1_waybel_0(A, C, B) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, k10_yellow_6(A, C)) => r2_hidden(D, B)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_yellow19)).
% 4.69/1.80  tff(f_56, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, k2_pre_topc(A, B)) <=> (?[D]: ((((((~v2_struct_0(D) & v4_orders_2(D)) & v7_waybel_0(D)) & v3_yellow_6(D, A)) & l1_waybel_0(D, A)) & r1_waybel_0(A, D, B)) & r2_hidden(C, k10_yellow_6(A, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_yellow19)).
% 4.69/1.80  tff(f_120, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, k2_pre_topc(A, B)) <=> (?[D]: ((((((~v1_xboole_0(D) & v1_subset_1(D, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(D, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(D, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(D, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) & r2_hidden(B, D)) & r1_waybel_7(A, D, C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_yellow19)).
% 4.69/1.80  tff(c_60, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_154])).
% 4.69/1.80  tff(c_58, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_154])).
% 4.69/1.80  tff(c_56, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_154])).
% 4.69/1.80  tff(c_54, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_154])).
% 4.69/1.80  tff(c_78, plain, (~v1_xboole_0('#skF_7') | ~v4_pre_topc('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_154])).
% 4.69/1.80  tff(c_101, plain, (~v4_pre_topc('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_78])).
% 4.69/1.80  tff(c_24, plain, (![A_23, B_37]: (m1_subset_1('#skF_3'(A_23, B_37), u1_struct_0(A_23)) | v4_pre_topc(B_37, A_23) | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0(A_23))) | ~l1_pre_topc(A_23) | ~v2_pre_topc(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.69/1.80  tff(c_102, plain, (![A_93, B_94]: (~v2_struct_0('#skF_2'(A_93, B_94)) | v4_pre_topc(B_94, A_93) | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0(A_93))) | ~l1_pre_topc(A_93) | ~v2_pre_topc(A_93) | v2_struct_0(A_93))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.69/1.80  tff(c_105, plain, (~v2_struct_0('#skF_2'('#skF_5', '#skF_6')) | v4_pre_topc('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_54, c_102])).
% 4.69/1.80  tff(c_108, plain, (~v2_struct_0('#skF_2'('#skF_5', '#skF_6')) | v4_pre_topc('#skF_6', '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_105])).
% 4.69/1.80  tff(c_109, plain, (~v2_struct_0('#skF_2'('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_60, c_101, c_108])).
% 4.69/1.80  tff(c_110, plain, (![A_95, B_96]: (v4_orders_2('#skF_2'(A_95, B_96)) | v4_pre_topc(B_96, A_95) | ~m1_subset_1(B_96, k1_zfmisc_1(u1_struct_0(A_95))) | ~l1_pre_topc(A_95) | ~v2_pre_topc(A_95) | v2_struct_0(A_95))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.69/1.80  tff(c_113, plain, (v4_orders_2('#skF_2'('#skF_5', '#skF_6')) | v4_pre_topc('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_54, c_110])).
% 4.69/1.80  tff(c_116, plain, (v4_orders_2('#skF_2'('#skF_5', '#skF_6')) | v4_pre_topc('#skF_6', '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_113])).
% 4.69/1.80  tff(c_117, plain, (v4_orders_2('#skF_2'('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_60, c_101, c_116])).
% 4.69/1.80  tff(c_118, plain, (![A_97, B_98]: (v7_waybel_0('#skF_2'(A_97, B_98)) | v4_pre_topc(B_98, A_97) | ~m1_subset_1(B_98, k1_zfmisc_1(u1_struct_0(A_97))) | ~l1_pre_topc(A_97) | ~v2_pre_topc(A_97) | v2_struct_0(A_97))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.69/1.80  tff(c_121, plain, (v7_waybel_0('#skF_2'('#skF_5', '#skF_6')) | v4_pre_topc('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_54, c_118])).
% 4.69/1.80  tff(c_124, plain, (v7_waybel_0('#skF_2'('#skF_5', '#skF_6')) | v4_pre_topc('#skF_6', '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_121])).
% 4.69/1.80  tff(c_125, plain, (v7_waybel_0('#skF_2'('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_60, c_101, c_124])).
% 4.69/1.80  tff(c_134, plain, (![A_101, B_102]: (v3_yellow_6('#skF_2'(A_101, B_102), A_101) | v4_pre_topc(B_102, A_101) | ~m1_subset_1(B_102, k1_zfmisc_1(u1_struct_0(A_101))) | ~l1_pre_topc(A_101) | ~v2_pre_topc(A_101) | v2_struct_0(A_101))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.69/1.80  tff(c_136, plain, (v3_yellow_6('#skF_2'('#skF_5', '#skF_6'), '#skF_5') | v4_pre_topc('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_54, c_134])).
% 4.69/1.80  tff(c_139, plain, (v3_yellow_6('#skF_2'('#skF_5', '#skF_6'), '#skF_5') | v4_pre_topc('#skF_6', '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_136])).
% 4.69/1.80  tff(c_140, plain, (v3_yellow_6('#skF_2'('#skF_5', '#skF_6'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_60, c_101, c_139])).
% 4.69/1.80  tff(c_127, plain, (![A_99, B_100]: (l1_waybel_0('#skF_2'(A_99, B_100), A_99) | v4_pre_topc(B_100, A_99) | ~m1_subset_1(B_100, k1_zfmisc_1(u1_struct_0(A_99))) | ~l1_pre_topc(A_99) | ~v2_pre_topc(A_99) | v2_struct_0(A_99))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.69/1.80  tff(c_129, plain, (l1_waybel_0('#skF_2'('#skF_5', '#skF_6'), '#skF_5') | v4_pre_topc('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_54, c_127])).
% 4.69/1.80  tff(c_132, plain, (l1_waybel_0('#skF_2'('#skF_5', '#skF_6'), '#skF_5') | v4_pre_topc('#skF_6', '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_129])).
% 4.69/1.80  tff(c_133, plain, (l1_waybel_0('#skF_2'('#skF_5', '#skF_6'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_60, c_101, c_132])).
% 4.69/1.80  tff(c_143, plain, (![A_107, B_108]: (r1_waybel_0(A_107, '#skF_2'(A_107, B_108), B_108) | v4_pre_topc(B_108, A_107) | ~m1_subset_1(B_108, k1_zfmisc_1(u1_struct_0(A_107))) | ~l1_pre_topc(A_107) | ~v2_pre_topc(A_107) | v2_struct_0(A_107))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.69/1.80  tff(c_145, plain, (r1_waybel_0('#skF_5', '#skF_2'('#skF_5', '#skF_6'), '#skF_6') | v4_pre_topc('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_54, c_143])).
% 4.69/1.80  tff(c_148, plain, (r1_waybel_0('#skF_5', '#skF_2'('#skF_5', '#skF_6'), '#skF_6') | v4_pre_topc('#skF_6', '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_145])).
% 4.69/1.80  tff(c_149, plain, (r1_waybel_0('#skF_5', '#skF_2'('#skF_5', '#skF_6'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_60, c_101, c_148])).
% 4.69/1.80  tff(c_22, plain, (![A_23, B_37]: (r2_hidden('#skF_3'(A_23, B_37), k10_yellow_6(A_23, '#skF_2'(A_23, B_37))) | v4_pre_topc(B_37, A_23) | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0(A_23))) | ~l1_pre_topc(A_23) | ~v2_pre_topc(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.69/1.80  tff(c_223, plain, (![C_158, A_159, B_160, D_161]: (r2_hidden(C_158, k2_pre_topc(A_159, B_160)) | ~r2_hidden(C_158, k10_yellow_6(A_159, D_161)) | ~r1_waybel_0(A_159, D_161, B_160) | ~l1_waybel_0(D_161, A_159) | ~v3_yellow_6(D_161, A_159) | ~v7_waybel_0(D_161) | ~v4_orders_2(D_161) | v2_struct_0(D_161) | ~m1_subset_1(C_158, u1_struct_0(A_159)) | ~m1_subset_1(B_160, k1_zfmisc_1(u1_struct_0(A_159))) | ~l1_pre_topc(A_159) | ~v2_pre_topc(A_159) | v2_struct_0(A_159))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.69/1.80  tff(c_229, plain, (![A_23, B_37, B_160]: (r2_hidden('#skF_3'(A_23, B_37), k2_pre_topc(A_23, B_160)) | ~r1_waybel_0(A_23, '#skF_2'(A_23, B_37), B_160) | ~l1_waybel_0('#skF_2'(A_23, B_37), A_23) | ~v3_yellow_6('#skF_2'(A_23, B_37), A_23) | ~v7_waybel_0('#skF_2'(A_23, B_37)) | ~v4_orders_2('#skF_2'(A_23, B_37)) | v2_struct_0('#skF_2'(A_23, B_37)) | ~m1_subset_1('#skF_3'(A_23, B_37), u1_struct_0(A_23)) | ~m1_subset_1(B_160, k1_zfmisc_1(u1_struct_0(A_23))) | v4_pre_topc(B_37, A_23) | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0(A_23))) | ~l1_pre_topc(A_23) | ~v2_pre_topc(A_23) | v2_struct_0(A_23))), inference(resolution, [status(thm)], [c_22, c_223])).
% 4.69/1.80  tff(c_287, plain, (![A_193, B_194, B_195]: (r2_hidden('#skF_3'(A_193, B_194), k2_pre_topc(A_193, B_195)) | ~r1_waybel_0(A_193, '#skF_2'(A_193, B_194), B_195) | ~l1_waybel_0('#skF_2'(A_193, B_194), A_193) | ~v3_yellow_6('#skF_2'(A_193, B_194), A_193) | ~v7_waybel_0('#skF_2'(A_193, B_194)) | ~v4_orders_2('#skF_2'(A_193, B_194)) | v2_struct_0('#skF_2'(A_193, B_194)) | ~m1_subset_1('#skF_3'(A_193, B_194), u1_struct_0(A_193)) | ~m1_subset_1(B_195, k1_zfmisc_1(u1_struct_0(A_193))) | v4_pre_topc(B_194, A_193) | ~m1_subset_1(B_194, k1_zfmisc_1(u1_struct_0(A_193))) | ~l1_pre_topc(A_193) | ~v2_pre_topc(A_193) | v2_struct_0(A_193))), inference(resolution, [status(thm)], [c_22, c_223])).
% 4.69/1.80  tff(c_42, plain, (![B_60, A_48, C_66]: (r2_hidden(B_60, '#skF_4'(A_48, B_60, C_66)) | ~r2_hidden(C_66, k2_pre_topc(A_48, B_60)) | ~m1_subset_1(C_66, u1_struct_0(A_48)) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_48))) | ~l1_pre_topc(A_48) | ~v2_pre_topc(A_48) | v2_struct_0(A_48))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.69/1.80  tff(c_394, plain, (![B_235, A_236, B_237]: (r2_hidden(B_235, '#skF_4'(A_236, B_235, '#skF_3'(A_236, B_237))) | ~r1_waybel_0(A_236, '#skF_2'(A_236, B_237), B_235) | ~l1_waybel_0('#skF_2'(A_236, B_237), A_236) | ~v3_yellow_6('#skF_2'(A_236, B_237), A_236) | ~v7_waybel_0('#skF_2'(A_236, B_237)) | ~v4_orders_2('#skF_2'(A_236, B_237)) | v2_struct_0('#skF_2'(A_236, B_237)) | ~m1_subset_1('#skF_3'(A_236, B_237), u1_struct_0(A_236)) | ~m1_subset_1(B_235, k1_zfmisc_1(u1_struct_0(A_236))) | v4_pre_topc(B_237, A_236) | ~m1_subset_1(B_237, k1_zfmisc_1(u1_struct_0(A_236))) | ~l1_pre_topc(A_236) | ~v2_pre_topc(A_236) | v2_struct_0(A_236))), inference(resolution, [status(thm)], [c_287, c_42])).
% 4.69/1.80  tff(c_46, plain, (![A_48, B_60, C_66]: (v13_waybel_0('#skF_4'(A_48, B_60, C_66), k3_yellow_1(k2_struct_0(A_48))) | ~r2_hidden(C_66, k2_pre_topc(A_48, B_60)) | ~m1_subset_1(C_66, u1_struct_0(A_48)) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_48))) | ~l1_pre_topc(A_48) | ~v2_pre_topc(A_48) | v2_struct_0(A_48))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.69/1.80  tff(c_48, plain, (![A_48, B_60, C_66]: (v2_waybel_0('#skF_4'(A_48, B_60, C_66), k3_yellow_1(k2_struct_0(A_48))) | ~r2_hidden(C_66, k2_pre_topc(A_48, B_60)) | ~m1_subset_1(C_66, u1_struct_0(A_48)) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_48))) | ~l1_pre_topc(A_48) | ~v2_pre_topc(A_48) | v2_struct_0(A_48))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.69/1.80  tff(c_50, plain, (![A_48, B_60, C_66]: (v1_subset_1('#skF_4'(A_48, B_60, C_66), u1_struct_0(k3_yellow_1(k2_struct_0(A_48)))) | ~r2_hidden(C_66, k2_pre_topc(A_48, B_60)) | ~m1_subset_1(C_66, u1_struct_0(A_48)) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_48))) | ~l1_pre_topc(A_48) | ~v2_pre_topc(A_48) | v2_struct_0(A_48))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.69/1.80  tff(c_44, plain, (![A_48, B_60, C_66]: (m1_subset_1('#skF_4'(A_48, B_60, C_66), k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_48))))) | ~r2_hidden(C_66, k2_pre_topc(A_48, B_60)) | ~m1_subset_1(C_66, u1_struct_0(A_48)) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_48))) | ~l1_pre_topc(A_48) | ~v2_pre_topc(A_48) | v2_struct_0(A_48))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.69/1.80  tff(c_175, plain, (![A_137, B_138, C_139]: (r1_waybel_7(A_137, '#skF_4'(A_137, B_138, C_139), C_139) | ~r2_hidden(C_139, k2_pre_topc(A_137, B_138)) | ~m1_subset_1(C_139, u1_struct_0(A_137)) | ~m1_subset_1(B_138, k1_zfmisc_1(u1_struct_0(A_137))) | ~l1_pre_topc(A_137) | ~v2_pre_topc(A_137) | v2_struct_0(A_137))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.69/1.80  tff(c_177, plain, (![C_139]: (r1_waybel_7('#skF_5', '#skF_4'('#skF_5', '#skF_6', C_139), C_139) | ~r2_hidden(C_139, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_139, u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_54, c_175])).
% 4.69/1.80  tff(c_180, plain, (![C_139]: (r1_waybel_7('#skF_5', '#skF_4'('#skF_5', '#skF_6', C_139), C_139) | ~r2_hidden(C_139, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_139, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_177])).
% 4.69/1.80  tff(c_181, plain, (![C_139]: (r1_waybel_7('#skF_5', '#skF_4'('#skF_5', '#skF_6', C_139), C_139) | ~r2_hidden(C_139, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_139, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_60, c_180])).
% 4.69/1.80  tff(c_100, plain, (![D_92, C_90]: (v4_pre_topc('#skF_6', '#skF_5') | r2_hidden(D_92, '#skF_6') | ~r1_waybel_7('#skF_5', C_90, D_92) | ~m1_subset_1(D_92, u1_struct_0('#skF_5')) | ~r2_hidden('#skF_6', C_90) | ~m1_subset_1(C_90, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))) | ~v13_waybel_0(C_90, k3_yellow_1(k2_struct_0('#skF_5'))) | ~v2_waybel_0(C_90, k3_yellow_1(k2_struct_0('#skF_5'))) | ~v1_subset_1(C_90, u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))) | v1_xboole_0(C_90))), inference(cnfTransformation, [status(thm)], [f_154])).
% 4.69/1.80  tff(c_186, plain, (![D_147, C_148]: (r2_hidden(D_147, '#skF_6') | ~r1_waybel_7('#skF_5', C_148, D_147) | ~m1_subset_1(D_147, u1_struct_0('#skF_5')) | ~r2_hidden('#skF_6', C_148) | ~m1_subset_1(C_148, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))) | ~v13_waybel_0(C_148, k3_yellow_1(k2_struct_0('#skF_5'))) | ~v2_waybel_0(C_148, k3_yellow_1(k2_struct_0('#skF_5'))) | ~v1_subset_1(C_148, u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))) | v1_xboole_0(C_148))), inference(negUnitSimplification, [status(thm)], [c_101, c_100])).
% 4.69/1.80  tff(c_250, plain, (![C_188]: (r2_hidden(C_188, '#skF_6') | ~r2_hidden('#skF_6', '#skF_4'('#skF_5', '#skF_6', C_188)) | ~m1_subset_1('#skF_4'('#skF_5', '#skF_6', C_188), k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))) | ~v13_waybel_0('#skF_4'('#skF_5', '#skF_6', C_188), k3_yellow_1(k2_struct_0('#skF_5'))) | ~v2_waybel_0('#skF_4'('#skF_5', '#skF_6', C_188), k3_yellow_1(k2_struct_0('#skF_5'))) | ~v1_subset_1('#skF_4'('#skF_5', '#skF_6', C_188), u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))) | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', C_188)) | ~r2_hidden(C_188, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_188, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_181, c_186])).
% 4.69/1.80  tff(c_254, plain, (![C_66]: (r2_hidden(C_66, '#skF_6') | ~r2_hidden('#skF_6', '#skF_4'('#skF_5', '#skF_6', C_66)) | ~v13_waybel_0('#skF_4'('#skF_5', '#skF_6', C_66), k3_yellow_1(k2_struct_0('#skF_5'))) | ~v2_waybel_0('#skF_4'('#skF_5', '#skF_6', C_66), k3_yellow_1(k2_struct_0('#skF_5'))) | ~v1_subset_1('#skF_4'('#skF_5', '#skF_6', C_66), u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))) | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', C_66)) | ~r2_hidden(C_66, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_66, u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_44, c_250])).
% 4.69/1.80  tff(c_257, plain, (![C_66]: (r2_hidden(C_66, '#skF_6') | ~r2_hidden('#skF_6', '#skF_4'('#skF_5', '#skF_6', C_66)) | ~v13_waybel_0('#skF_4'('#skF_5', '#skF_6', C_66), k3_yellow_1(k2_struct_0('#skF_5'))) | ~v2_waybel_0('#skF_4'('#skF_5', '#skF_6', C_66), k3_yellow_1(k2_struct_0('#skF_5'))) | ~v1_subset_1('#skF_4'('#skF_5', '#skF_6', C_66), u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))) | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', C_66)) | ~r2_hidden(C_66, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_66, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_254])).
% 4.69/1.80  tff(c_259, plain, (![C_189]: (r2_hidden(C_189, '#skF_6') | ~r2_hidden('#skF_6', '#skF_4'('#skF_5', '#skF_6', C_189)) | ~v13_waybel_0('#skF_4'('#skF_5', '#skF_6', C_189), k3_yellow_1(k2_struct_0('#skF_5'))) | ~v2_waybel_0('#skF_4'('#skF_5', '#skF_6', C_189), k3_yellow_1(k2_struct_0('#skF_5'))) | ~v1_subset_1('#skF_4'('#skF_5', '#skF_6', C_189), u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))) | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', C_189)) | ~r2_hidden(C_189, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_189, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_60, c_257])).
% 4.69/1.80  tff(c_263, plain, (![C_66]: (r2_hidden(C_66, '#skF_6') | ~r2_hidden('#skF_6', '#skF_4'('#skF_5', '#skF_6', C_66)) | ~v13_waybel_0('#skF_4'('#skF_5', '#skF_6', C_66), k3_yellow_1(k2_struct_0('#skF_5'))) | ~v2_waybel_0('#skF_4'('#skF_5', '#skF_6', C_66), k3_yellow_1(k2_struct_0('#skF_5'))) | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', C_66)) | ~r2_hidden(C_66, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_66, u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_50, c_259])).
% 4.69/1.80  tff(c_266, plain, (![C_66]: (r2_hidden(C_66, '#skF_6') | ~r2_hidden('#skF_6', '#skF_4'('#skF_5', '#skF_6', C_66)) | ~v13_waybel_0('#skF_4'('#skF_5', '#skF_6', C_66), k3_yellow_1(k2_struct_0('#skF_5'))) | ~v2_waybel_0('#skF_4'('#skF_5', '#skF_6', C_66), k3_yellow_1(k2_struct_0('#skF_5'))) | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', C_66)) | ~r2_hidden(C_66, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_66, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_263])).
% 4.69/1.80  tff(c_268, plain, (![C_190]: (r2_hidden(C_190, '#skF_6') | ~r2_hidden('#skF_6', '#skF_4'('#skF_5', '#skF_6', C_190)) | ~v13_waybel_0('#skF_4'('#skF_5', '#skF_6', C_190), k3_yellow_1(k2_struct_0('#skF_5'))) | ~v2_waybel_0('#skF_4'('#skF_5', '#skF_6', C_190), k3_yellow_1(k2_struct_0('#skF_5'))) | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', C_190)) | ~r2_hidden(C_190, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_190, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_60, c_266])).
% 4.69/1.80  tff(c_272, plain, (![C_66]: (r2_hidden(C_66, '#skF_6') | ~r2_hidden('#skF_6', '#skF_4'('#skF_5', '#skF_6', C_66)) | ~v13_waybel_0('#skF_4'('#skF_5', '#skF_6', C_66), k3_yellow_1(k2_struct_0('#skF_5'))) | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', C_66)) | ~r2_hidden(C_66, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_66, u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_48, c_268])).
% 4.69/1.80  tff(c_275, plain, (![C_66]: (r2_hidden(C_66, '#skF_6') | ~r2_hidden('#skF_6', '#skF_4'('#skF_5', '#skF_6', C_66)) | ~v13_waybel_0('#skF_4'('#skF_5', '#skF_6', C_66), k3_yellow_1(k2_struct_0('#skF_5'))) | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', C_66)) | ~r2_hidden(C_66, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_66, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_272])).
% 4.69/1.80  tff(c_277, plain, (![C_191]: (r2_hidden(C_191, '#skF_6') | ~r2_hidden('#skF_6', '#skF_4'('#skF_5', '#skF_6', C_191)) | ~v13_waybel_0('#skF_4'('#skF_5', '#skF_6', C_191), k3_yellow_1(k2_struct_0('#skF_5'))) | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', C_191)) | ~r2_hidden(C_191, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_191, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_60, c_275])).
% 4.69/1.80  tff(c_281, plain, (![C_66]: (r2_hidden(C_66, '#skF_6') | ~r2_hidden('#skF_6', '#skF_4'('#skF_5', '#skF_6', C_66)) | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', C_66)) | ~r2_hidden(C_66, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_66, u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_46, c_277])).
% 4.69/1.80  tff(c_284, plain, (![C_66]: (r2_hidden(C_66, '#skF_6') | ~r2_hidden('#skF_6', '#skF_4'('#skF_5', '#skF_6', C_66)) | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', C_66)) | ~r2_hidden(C_66, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_66, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_281])).
% 4.69/1.80  tff(c_285, plain, (![C_66]: (r2_hidden(C_66, '#skF_6') | ~r2_hidden('#skF_6', '#skF_4'('#skF_5', '#skF_6', C_66)) | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', C_66)) | ~r2_hidden(C_66, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_66, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_60, c_284])).
% 4.69/1.80  tff(c_400, plain, (![B_237]: (r2_hidden('#skF_3'('#skF_5', B_237), '#skF_6') | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_237))) | ~r2_hidden('#skF_3'('#skF_5', B_237), k2_pre_topc('#skF_5', '#skF_6')) | ~r1_waybel_0('#skF_5', '#skF_2'('#skF_5', B_237), '#skF_6') | ~l1_waybel_0('#skF_2'('#skF_5', B_237), '#skF_5') | ~v3_yellow_6('#skF_2'('#skF_5', B_237), '#skF_5') | ~v7_waybel_0('#skF_2'('#skF_5', B_237)) | ~v4_orders_2('#skF_2'('#skF_5', B_237)) | v2_struct_0('#skF_2'('#skF_5', B_237)) | ~m1_subset_1('#skF_3'('#skF_5', B_237), u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | v4_pre_topc(B_237, '#skF_5') | ~m1_subset_1(B_237, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_394, c_285])).
% 4.69/1.80  tff(c_407, plain, (![B_237]: (r2_hidden('#skF_3'('#skF_5', B_237), '#skF_6') | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_237))) | ~r2_hidden('#skF_3'('#skF_5', B_237), k2_pre_topc('#skF_5', '#skF_6')) | ~r1_waybel_0('#skF_5', '#skF_2'('#skF_5', B_237), '#skF_6') | ~l1_waybel_0('#skF_2'('#skF_5', B_237), '#skF_5') | ~v3_yellow_6('#skF_2'('#skF_5', B_237), '#skF_5') | ~v7_waybel_0('#skF_2'('#skF_5', B_237)) | ~v4_orders_2('#skF_2'('#skF_5', B_237)) | v2_struct_0('#skF_2'('#skF_5', B_237)) | ~m1_subset_1('#skF_3'('#skF_5', B_237), u1_struct_0('#skF_5')) | v4_pre_topc(B_237, '#skF_5') | ~m1_subset_1(B_237, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_400])).
% 4.69/1.80  tff(c_409, plain, (![B_238]: (r2_hidden('#skF_3'('#skF_5', B_238), '#skF_6') | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_238))) | ~r2_hidden('#skF_3'('#skF_5', B_238), k2_pre_topc('#skF_5', '#skF_6')) | ~r1_waybel_0('#skF_5', '#skF_2'('#skF_5', B_238), '#skF_6') | ~l1_waybel_0('#skF_2'('#skF_5', B_238), '#skF_5') | ~v3_yellow_6('#skF_2'('#skF_5', B_238), '#skF_5') | ~v7_waybel_0('#skF_2'('#skF_5', B_238)) | ~v4_orders_2('#skF_2'('#skF_5', B_238)) | v2_struct_0('#skF_2'('#skF_5', B_238)) | ~m1_subset_1('#skF_3'('#skF_5', B_238), u1_struct_0('#skF_5')) | v4_pre_topc(B_238, '#skF_5') | ~m1_subset_1(B_238, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_60, c_407])).
% 4.69/1.80  tff(c_413, plain, (![B_37]: (r2_hidden('#skF_3'('#skF_5', B_37), '#skF_6') | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_37))) | ~r1_waybel_0('#skF_5', '#skF_2'('#skF_5', B_37), '#skF_6') | ~l1_waybel_0('#skF_2'('#skF_5', B_37), '#skF_5') | ~v3_yellow_6('#skF_2'('#skF_5', B_37), '#skF_5') | ~v7_waybel_0('#skF_2'('#skF_5', B_37)) | ~v4_orders_2('#skF_2'('#skF_5', B_37)) | v2_struct_0('#skF_2'('#skF_5', B_37)) | ~m1_subset_1('#skF_3'('#skF_5', B_37), u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | v4_pre_topc(B_37, '#skF_5') | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_229, c_409])).
% 4.69/1.80  tff(c_416, plain, (![B_37]: (r2_hidden('#skF_3'('#skF_5', B_37), '#skF_6') | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_37))) | ~r1_waybel_0('#skF_5', '#skF_2'('#skF_5', B_37), '#skF_6') | ~l1_waybel_0('#skF_2'('#skF_5', B_37), '#skF_5') | ~v3_yellow_6('#skF_2'('#skF_5', B_37), '#skF_5') | ~v7_waybel_0('#skF_2'('#skF_5', B_37)) | ~v4_orders_2('#skF_2'('#skF_5', B_37)) | v2_struct_0('#skF_2'('#skF_5', B_37)) | ~m1_subset_1('#skF_3'('#skF_5', B_37), u1_struct_0('#skF_5')) | v4_pre_topc(B_37, '#skF_5') | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_413])).
% 4.69/1.80  tff(c_418, plain, (![B_239]: (r2_hidden('#skF_3'('#skF_5', B_239), '#skF_6') | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_239))) | ~r1_waybel_0('#skF_5', '#skF_2'('#skF_5', B_239), '#skF_6') | ~l1_waybel_0('#skF_2'('#skF_5', B_239), '#skF_5') | ~v3_yellow_6('#skF_2'('#skF_5', B_239), '#skF_5') | ~v7_waybel_0('#skF_2'('#skF_5', B_239)) | ~v4_orders_2('#skF_2'('#skF_5', B_239)) | v2_struct_0('#skF_2'('#skF_5', B_239)) | ~m1_subset_1('#skF_3'('#skF_5', B_239), u1_struct_0('#skF_5')) | v4_pre_topc(B_239, '#skF_5') | ~m1_subset_1(B_239, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_60, c_416])).
% 4.69/1.80  tff(c_422, plain, (![B_37]: (r2_hidden('#skF_3'('#skF_5', B_37), '#skF_6') | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_37))) | ~r1_waybel_0('#skF_5', '#skF_2'('#skF_5', B_37), '#skF_6') | ~l1_waybel_0('#skF_2'('#skF_5', B_37), '#skF_5') | ~v3_yellow_6('#skF_2'('#skF_5', B_37), '#skF_5') | ~v7_waybel_0('#skF_2'('#skF_5', B_37)) | ~v4_orders_2('#skF_2'('#skF_5', B_37)) | v2_struct_0('#skF_2'('#skF_5', B_37)) | v4_pre_topc(B_37, '#skF_5') | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_24, c_418])).
% 4.69/1.80  tff(c_425, plain, (![B_37]: (r2_hidden('#skF_3'('#skF_5', B_37), '#skF_6') | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_37))) | ~r1_waybel_0('#skF_5', '#skF_2'('#skF_5', B_37), '#skF_6') | ~l1_waybel_0('#skF_2'('#skF_5', B_37), '#skF_5') | ~v3_yellow_6('#skF_2'('#skF_5', B_37), '#skF_5') | ~v7_waybel_0('#skF_2'('#skF_5', B_37)) | ~v4_orders_2('#skF_2'('#skF_5', B_37)) | v2_struct_0('#skF_2'('#skF_5', B_37)) | v4_pre_topc(B_37, '#skF_5') | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_422])).
% 4.69/1.80  tff(c_431, plain, (![B_244]: (r2_hidden('#skF_3'('#skF_5', B_244), '#skF_6') | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_244))) | ~r1_waybel_0('#skF_5', '#skF_2'('#skF_5', B_244), '#skF_6') | ~l1_waybel_0('#skF_2'('#skF_5', B_244), '#skF_5') | ~v3_yellow_6('#skF_2'('#skF_5', B_244), '#skF_5') | ~v7_waybel_0('#skF_2'('#skF_5', B_244)) | ~v4_orders_2('#skF_2'('#skF_5', B_244)) | v2_struct_0('#skF_2'('#skF_5', B_244)) | v4_pre_topc(B_244, '#skF_5') | ~m1_subset_1(B_244, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_60, c_425])).
% 4.69/1.80  tff(c_434, plain, (r2_hidden('#skF_3'('#skF_5', '#skF_6'), '#skF_6') | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', '#skF_3'('#skF_5', '#skF_6'))) | ~r1_waybel_0('#skF_5', '#skF_2'('#skF_5', '#skF_6'), '#skF_6') | ~l1_waybel_0('#skF_2'('#skF_5', '#skF_6'), '#skF_5') | ~v3_yellow_6('#skF_2'('#skF_5', '#skF_6'), '#skF_5') | ~v7_waybel_0('#skF_2'('#skF_5', '#skF_6')) | ~v4_orders_2('#skF_2'('#skF_5', '#skF_6')) | v2_struct_0('#skF_2'('#skF_5', '#skF_6')) | v4_pre_topc('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_54, c_431])).
% 4.69/1.80  tff(c_437, plain, (r2_hidden('#skF_3'('#skF_5', '#skF_6'), '#skF_6') | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', '#skF_3'('#skF_5', '#skF_6'))) | v2_struct_0('#skF_2'('#skF_5', '#skF_6')) | v4_pre_topc('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_117, c_125, c_140, c_133, c_149, c_434])).
% 4.69/1.80  tff(c_438, plain, (r2_hidden('#skF_3'('#skF_5', '#skF_6'), '#skF_6') | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', '#skF_3'('#skF_5', '#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_101, c_109, c_437])).
% 4.69/1.80  tff(c_439, plain, (v1_xboole_0('#skF_4'('#skF_5', '#skF_6', '#skF_3'('#skF_5', '#skF_6')))), inference(splitLeft, [status(thm)], [c_438])).
% 4.69/1.80  tff(c_52, plain, (![A_48, B_60, C_66]: (~v1_xboole_0('#skF_4'(A_48, B_60, C_66)) | ~r2_hidden(C_66, k2_pre_topc(A_48, B_60)) | ~m1_subset_1(C_66, u1_struct_0(A_48)) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_48))) | ~l1_pre_topc(A_48) | ~v2_pre_topc(A_48) | v2_struct_0(A_48))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.69/1.80  tff(c_308, plain, (![A_193, B_195, B_194]: (~v1_xboole_0('#skF_4'(A_193, B_195, '#skF_3'(A_193, B_194))) | ~r1_waybel_0(A_193, '#skF_2'(A_193, B_194), B_195) | ~l1_waybel_0('#skF_2'(A_193, B_194), A_193) | ~v3_yellow_6('#skF_2'(A_193, B_194), A_193) | ~v7_waybel_0('#skF_2'(A_193, B_194)) | ~v4_orders_2('#skF_2'(A_193, B_194)) | v2_struct_0('#skF_2'(A_193, B_194)) | ~m1_subset_1('#skF_3'(A_193, B_194), u1_struct_0(A_193)) | ~m1_subset_1(B_195, k1_zfmisc_1(u1_struct_0(A_193))) | v4_pre_topc(B_194, A_193) | ~m1_subset_1(B_194, k1_zfmisc_1(u1_struct_0(A_193))) | ~l1_pre_topc(A_193) | ~v2_pre_topc(A_193) | v2_struct_0(A_193))), inference(resolution, [status(thm)], [c_287, c_52])).
% 4.69/1.80  tff(c_441, plain, (~r1_waybel_0('#skF_5', '#skF_2'('#skF_5', '#skF_6'), '#skF_6') | ~l1_waybel_0('#skF_2'('#skF_5', '#skF_6'), '#skF_5') | ~v3_yellow_6('#skF_2'('#skF_5', '#skF_6'), '#skF_5') | ~v7_waybel_0('#skF_2'('#skF_5', '#skF_6')) | ~v4_orders_2('#skF_2'('#skF_5', '#skF_6')) | v2_struct_0('#skF_2'('#skF_5', '#skF_6')) | ~m1_subset_1('#skF_3'('#skF_5', '#skF_6'), u1_struct_0('#skF_5')) | v4_pre_topc('#skF_6', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_439, c_308])).
% 4.69/1.80  tff(c_444, plain, (v2_struct_0('#skF_2'('#skF_5', '#skF_6')) | ~m1_subset_1('#skF_3'('#skF_5', '#skF_6'), u1_struct_0('#skF_5')) | v4_pre_topc('#skF_6', '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_117, c_125, c_140, c_133, c_149, c_441])).
% 4.69/1.80  tff(c_445, plain, (~m1_subset_1('#skF_3'('#skF_5', '#skF_6'), u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_60, c_101, c_109, c_444])).
% 4.69/1.80  tff(c_448, plain, (v4_pre_topc('#skF_6', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_24, c_445])).
% 4.69/1.80  tff(c_451, plain, (v4_pre_topc('#skF_6', '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_448])).
% 4.69/1.80  tff(c_453, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_101, c_451])).
% 4.69/1.80  tff(c_454, plain, (r2_hidden('#skF_3'('#skF_5', '#skF_6'), '#skF_6')), inference(splitRight, [status(thm)], [c_438])).
% 4.69/1.80  tff(c_20, plain, (![A_23, B_37]: (~r2_hidden('#skF_3'(A_23, B_37), B_37) | v4_pre_topc(B_37, A_23) | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0(A_23))) | ~l1_pre_topc(A_23) | ~v2_pre_topc(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.69/1.80  tff(c_457, plain, (v4_pre_topc('#skF_6', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_454, c_20])).
% 4.69/1.80  tff(c_460, plain, (v4_pre_topc('#skF_6', '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_457])).
% 4.69/1.80  tff(c_462, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_101, c_460])).
% 4.69/1.80  tff(c_464, plain, (v4_pre_topc('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_78])).
% 4.69/1.80  tff(c_66, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~v4_pre_topc('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_154])).
% 4.69/1.80  tff(c_472, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_464, c_66])).
% 4.69/1.80  tff(c_68, plain, (r2_hidden('#skF_6', '#skF_7') | ~v4_pre_topc('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_154])).
% 4.69/1.80  tff(c_468, plain, (r2_hidden('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_464, c_68])).
% 4.69/1.80  tff(c_463, plain, (~v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_78])).
% 4.69/1.80  tff(c_76, plain, (v1_subset_1('#skF_7', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))) | ~v4_pre_topc('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_154])).
% 4.69/1.80  tff(c_478, plain, (v1_subset_1('#skF_7', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_464, c_76])).
% 4.69/1.80  tff(c_74, plain, (v2_waybel_0('#skF_7', k3_yellow_1(k2_struct_0('#skF_5'))) | ~v4_pre_topc('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_154])).
% 4.69/1.80  tff(c_476, plain, (v2_waybel_0('#skF_7', k3_yellow_1(k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_464, c_74])).
% 4.69/1.80  tff(c_72, plain, (v13_waybel_0('#skF_7', k3_yellow_1(k2_struct_0('#skF_5'))) | ~v4_pre_topc('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_154])).
% 4.69/1.80  tff(c_474, plain, (v13_waybel_0('#skF_7', k3_yellow_1(k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_464, c_72])).
% 4.69/1.80  tff(c_70, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))) | ~v4_pre_topc('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_154])).
% 4.69/1.80  tff(c_480, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))))), inference(demodulation, [status(thm), theory('equality')], [c_464, c_70])).
% 4.69/1.80  tff(c_64, plain, (r1_waybel_7('#skF_5', '#skF_7', '#skF_8') | ~v4_pre_topc('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_154])).
% 4.69/1.80  tff(c_470, plain, (r1_waybel_7('#skF_5', '#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_464, c_64])).
% 4.69/1.80  tff(c_649, plain, (![C_322, A_323, B_324, D_325]: (r2_hidden(C_322, k2_pre_topc(A_323, B_324)) | ~r1_waybel_7(A_323, D_325, C_322) | ~r2_hidden(B_324, D_325) | ~m1_subset_1(D_325, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_323))))) | ~v13_waybel_0(D_325, k3_yellow_1(k2_struct_0(A_323))) | ~v2_waybel_0(D_325, k3_yellow_1(k2_struct_0(A_323))) | ~v1_subset_1(D_325, u1_struct_0(k3_yellow_1(k2_struct_0(A_323)))) | v1_xboole_0(D_325) | ~m1_subset_1(C_322, u1_struct_0(A_323)) | ~m1_subset_1(B_324, k1_zfmisc_1(u1_struct_0(A_323))) | ~l1_pre_topc(A_323) | ~v2_pre_topc(A_323) | v2_struct_0(A_323))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.69/1.80  tff(c_653, plain, (![B_324]: (r2_hidden('#skF_8', k2_pre_topc('#skF_5', B_324)) | ~r2_hidden(B_324, '#skF_7') | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))) | ~v13_waybel_0('#skF_7', k3_yellow_1(k2_struct_0('#skF_5'))) | ~v2_waybel_0('#skF_7', k3_yellow_1(k2_struct_0('#skF_5'))) | ~v1_subset_1('#skF_7', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))) | v1_xboole_0('#skF_7') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1(B_324, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_470, c_649])).
% 4.69/1.80  tff(c_660, plain, (![B_324]: (r2_hidden('#skF_8', k2_pre_topc('#skF_5', B_324)) | ~r2_hidden(B_324, '#skF_7') | v1_xboole_0('#skF_7') | ~m1_subset_1(B_324, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_472, c_478, c_476, c_474, c_480, c_653])).
% 4.69/1.80  tff(c_662, plain, (![B_326]: (r2_hidden('#skF_8', k2_pre_topc('#skF_5', B_326)) | ~r2_hidden(B_326, '#skF_7') | ~m1_subset_1(B_326, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_60, c_463, c_660])).
% 4.69/1.80  tff(c_665, plain, (r2_hidden('#skF_8', k2_pre_topc('#skF_5', '#skF_6')) | ~r2_hidden('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_54, c_662])).
% 4.69/1.80  tff(c_668, plain, (r2_hidden('#skF_8', k2_pre_topc('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_468, c_665])).
% 4.69/1.80  tff(c_16, plain, (![A_1, B_13, C_19]: (~v2_struct_0('#skF_1'(A_1, B_13, C_19)) | ~r2_hidden(C_19, k2_pre_topc(A_1, B_13)) | ~m1_subset_1(C_19, u1_struct_0(A_1)) | ~m1_subset_1(B_13, k1_zfmisc_1(u1_struct_0(A_1))) | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.69/1.80  tff(c_680, plain, (~v2_struct_0('#skF_1'('#skF_5', '#skF_6', '#skF_8')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_668, c_16])).
% 4.69/1.80  tff(c_703, plain, (~v2_struct_0('#skF_1'('#skF_5', '#skF_6', '#skF_8')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_472, c_680])).
% 4.69/1.80  tff(c_704, plain, (~v2_struct_0('#skF_1'('#skF_5', '#skF_6', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_60, c_703])).
% 4.69/1.80  tff(c_62, plain, (~r2_hidden('#skF_8', '#skF_6') | ~v4_pre_topc('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_154])).
% 4.69/1.80  tff(c_466, plain, (~r2_hidden('#skF_8', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_464, c_62])).
% 4.69/1.80  tff(c_14, plain, (![A_1, B_13, C_19]: (v4_orders_2('#skF_1'(A_1, B_13, C_19)) | ~r2_hidden(C_19, k2_pre_topc(A_1, B_13)) | ~m1_subset_1(C_19, u1_struct_0(A_1)) | ~m1_subset_1(B_13, k1_zfmisc_1(u1_struct_0(A_1))) | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.69/1.80  tff(c_676, plain, (v4_orders_2('#skF_1'('#skF_5', '#skF_6', '#skF_8')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_668, c_14])).
% 4.69/1.80  tff(c_695, plain, (v4_orders_2('#skF_1'('#skF_5', '#skF_6', '#skF_8')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_472, c_676])).
% 4.69/1.80  tff(c_696, plain, (v4_orders_2('#skF_1'('#skF_5', '#skF_6', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_60, c_695])).
% 4.69/1.80  tff(c_12, plain, (![A_1, B_13, C_19]: (v7_waybel_0('#skF_1'(A_1, B_13, C_19)) | ~r2_hidden(C_19, k2_pre_topc(A_1, B_13)) | ~m1_subset_1(C_19, u1_struct_0(A_1)) | ~m1_subset_1(B_13, k1_zfmisc_1(u1_struct_0(A_1))) | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.69/1.80  tff(c_674, plain, (v7_waybel_0('#skF_1'('#skF_5', '#skF_6', '#skF_8')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_668, c_12])).
% 4.69/1.80  tff(c_691, plain, (v7_waybel_0('#skF_1'('#skF_5', '#skF_6', '#skF_8')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_472, c_674])).
% 4.69/1.80  tff(c_692, plain, (v7_waybel_0('#skF_1'('#skF_5', '#skF_6', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_60, c_691])).
% 4.69/1.80  tff(c_8, plain, (![A_1, B_13, C_19]: (l1_waybel_0('#skF_1'(A_1, B_13, C_19), A_1) | ~r2_hidden(C_19, k2_pre_topc(A_1, B_13)) | ~m1_subset_1(C_19, u1_struct_0(A_1)) | ~m1_subset_1(B_13, k1_zfmisc_1(u1_struct_0(A_1))) | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.69/1.80  tff(c_672, plain, (l1_waybel_0('#skF_1'('#skF_5', '#skF_6', '#skF_8'), '#skF_5') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_668, c_8])).
% 4.69/1.80  tff(c_687, plain, (l1_waybel_0('#skF_1'('#skF_5', '#skF_6', '#skF_8'), '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_472, c_672])).
% 4.69/1.80  tff(c_688, plain, (l1_waybel_0('#skF_1'('#skF_5', '#skF_6', '#skF_8'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_60, c_687])).
% 4.69/1.80  tff(c_556, plain, (![A_275, B_276, C_277]: (v3_yellow_6('#skF_1'(A_275, B_276, C_277), A_275) | ~r2_hidden(C_277, k2_pre_topc(A_275, B_276)) | ~m1_subset_1(C_277, u1_struct_0(A_275)) | ~m1_subset_1(B_276, k1_zfmisc_1(u1_struct_0(A_275))) | ~l1_pre_topc(A_275) | ~v2_pre_topc(A_275) | v2_struct_0(A_275))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.69/1.80  tff(c_560, plain, (![C_277]: (v3_yellow_6('#skF_1'('#skF_5', '#skF_6', C_277), '#skF_5') | ~r2_hidden(C_277, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_277, u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_54, c_556])).
% 4.69/1.80  tff(c_564, plain, (![C_277]: (v3_yellow_6('#skF_1'('#skF_5', '#skF_6', C_277), '#skF_5') | ~r2_hidden(C_277, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_277, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_560])).
% 4.69/1.80  tff(c_565, plain, (![C_277]: (v3_yellow_6('#skF_1'('#skF_5', '#skF_6', C_277), '#skF_5') | ~r2_hidden(C_277, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_277, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_60, c_564])).
% 4.69/1.80  tff(c_580, plain, (![A_289, B_290, C_291]: (r1_waybel_0(A_289, '#skF_1'(A_289, B_290, C_291), B_290) | ~r2_hidden(C_291, k2_pre_topc(A_289, B_290)) | ~m1_subset_1(C_291, u1_struct_0(A_289)) | ~m1_subset_1(B_290, k1_zfmisc_1(u1_struct_0(A_289))) | ~l1_pre_topc(A_289) | ~v2_pre_topc(A_289) | v2_struct_0(A_289))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.69/1.80  tff(c_584, plain, (![C_291]: (r1_waybel_0('#skF_5', '#skF_1'('#skF_5', '#skF_6', C_291), '#skF_6') | ~r2_hidden(C_291, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_291, u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_54, c_580])).
% 4.69/1.80  tff(c_588, plain, (![C_291]: (r1_waybel_0('#skF_5', '#skF_1'('#skF_5', '#skF_6', C_291), '#skF_6') | ~r2_hidden(C_291, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_291, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_584])).
% 4.69/1.80  tff(c_589, plain, (![C_291]: (r1_waybel_0('#skF_5', '#skF_1'('#skF_5', '#skF_6', C_291), '#skF_6') | ~r2_hidden(C_291, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_291, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_60, c_588])).
% 4.69/1.80  tff(c_4, plain, (![C_19, A_1, B_13]: (r2_hidden(C_19, k10_yellow_6(A_1, '#skF_1'(A_1, B_13, C_19))) | ~r2_hidden(C_19, k2_pre_topc(A_1, B_13)) | ~m1_subset_1(C_19, u1_struct_0(A_1)) | ~m1_subset_1(B_13, k1_zfmisc_1(u1_struct_0(A_1))) | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.69/1.80  tff(c_634, plain, (![D_312, B_313, A_314, C_315]: (r2_hidden(D_312, B_313) | ~r2_hidden(D_312, k10_yellow_6(A_314, C_315)) | ~m1_subset_1(D_312, u1_struct_0(A_314)) | ~r1_waybel_0(A_314, C_315, B_313) | ~l1_waybel_0(C_315, A_314) | ~v3_yellow_6(C_315, A_314) | ~v7_waybel_0(C_315) | ~v4_orders_2(C_315) | v2_struct_0(C_315) | ~v4_pre_topc(B_313, A_314) | ~m1_subset_1(B_313, k1_zfmisc_1(u1_struct_0(A_314))) | ~l1_pre_topc(A_314) | ~v2_pre_topc(A_314) | v2_struct_0(A_314))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.69/1.80  tff(c_842, plain, (![C_396, B_397, A_398, B_399]: (r2_hidden(C_396, B_397) | ~r1_waybel_0(A_398, '#skF_1'(A_398, B_399, C_396), B_397) | ~l1_waybel_0('#skF_1'(A_398, B_399, C_396), A_398) | ~v3_yellow_6('#skF_1'(A_398, B_399, C_396), A_398) | ~v7_waybel_0('#skF_1'(A_398, B_399, C_396)) | ~v4_orders_2('#skF_1'(A_398, B_399, C_396)) | v2_struct_0('#skF_1'(A_398, B_399, C_396)) | ~v4_pre_topc(B_397, A_398) | ~m1_subset_1(B_397, k1_zfmisc_1(u1_struct_0(A_398))) | ~r2_hidden(C_396, k2_pre_topc(A_398, B_399)) | ~m1_subset_1(C_396, u1_struct_0(A_398)) | ~m1_subset_1(B_399, k1_zfmisc_1(u1_struct_0(A_398))) | ~l1_pre_topc(A_398) | ~v2_pre_topc(A_398) | v2_struct_0(A_398))), inference(resolution, [status(thm)], [c_4, c_634])).
% 4.69/1.80  tff(c_846, plain, (![C_291]: (r2_hidden(C_291, '#skF_6') | ~l1_waybel_0('#skF_1'('#skF_5', '#skF_6', C_291), '#skF_5') | ~v3_yellow_6('#skF_1'('#skF_5', '#skF_6', C_291), '#skF_5') | ~v7_waybel_0('#skF_1'('#skF_5', '#skF_6', C_291)) | ~v4_orders_2('#skF_1'('#skF_5', '#skF_6', C_291)) | v2_struct_0('#skF_1'('#skF_5', '#skF_6', C_291)) | ~v4_pre_topc('#skF_6', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~r2_hidden(C_291, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_291, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_589, c_842])).
% 4.69/1.80  tff(c_850, plain, (![C_291]: (r2_hidden(C_291, '#skF_6') | ~l1_waybel_0('#skF_1'('#skF_5', '#skF_6', C_291), '#skF_5') | ~v3_yellow_6('#skF_1'('#skF_5', '#skF_6', C_291), '#skF_5') | ~v7_waybel_0('#skF_1'('#skF_5', '#skF_6', C_291)) | ~v4_orders_2('#skF_1'('#skF_5', '#skF_6', C_291)) | v2_struct_0('#skF_1'('#skF_5', '#skF_6', C_291)) | v2_struct_0('#skF_5') | ~r2_hidden(C_291, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_291, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_464, c_846])).
% 4.69/1.80  tff(c_852, plain, (![C_400]: (r2_hidden(C_400, '#skF_6') | ~l1_waybel_0('#skF_1'('#skF_5', '#skF_6', C_400), '#skF_5') | ~v3_yellow_6('#skF_1'('#skF_5', '#skF_6', C_400), '#skF_5') | ~v7_waybel_0('#skF_1'('#skF_5', '#skF_6', C_400)) | ~v4_orders_2('#skF_1'('#skF_5', '#skF_6', C_400)) | v2_struct_0('#skF_1'('#skF_5', '#skF_6', C_400)) | ~r2_hidden(C_400, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_400, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_60, c_850])).
% 4.69/1.80  tff(c_857, plain, (![C_401]: (r2_hidden(C_401, '#skF_6') | ~l1_waybel_0('#skF_1'('#skF_5', '#skF_6', C_401), '#skF_5') | ~v7_waybel_0('#skF_1'('#skF_5', '#skF_6', C_401)) | ~v4_orders_2('#skF_1'('#skF_5', '#skF_6', C_401)) | v2_struct_0('#skF_1'('#skF_5', '#skF_6', C_401)) | ~r2_hidden(C_401, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_401, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_565, c_852])).
% 4.69/1.80  tff(c_864, plain, (r2_hidden('#skF_8', '#skF_6') | ~l1_waybel_0('#skF_1'('#skF_5', '#skF_6', '#skF_8'), '#skF_5') | ~v7_waybel_0('#skF_1'('#skF_5', '#skF_6', '#skF_8')) | ~v4_orders_2('#skF_1'('#skF_5', '#skF_6', '#skF_8')) | v2_struct_0('#skF_1'('#skF_5', '#skF_6', '#skF_8')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_668, c_857])).
% 4.69/1.80  tff(c_871, plain, (r2_hidden('#skF_8', '#skF_6') | v2_struct_0('#skF_1'('#skF_5', '#skF_6', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_472, c_696, c_692, c_688, c_864])).
% 4.69/1.80  tff(c_873, plain, $false, inference(negUnitSimplification, [status(thm)], [c_704, c_466, c_871])).
% 4.69/1.80  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.69/1.80  
% 4.69/1.80  Inference rules
% 4.69/1.80  ----------------------
% 4.69/1.80  #Ref     : 0
% 4.69/1.80  #Sup     : 133
% 4.69/1.80  #Fact    : 0
% 4.69/1.80  #Define  : 0
% 4.69/1.80  #Split   : 6
% 4.69/1.80  #Chain   : 0
% 4.69/1.80  #Close   : 0
% 4.69/1.80  
% 4.69/1.80  Ordering : KBO
% 4.69/1.80  
% 4.69/1.80  Simplification rules
% 4.69/1.80  ----------------------
% 4.69/1.80  #Subsume      : 43
% 4.69/1.80  #Demod        : 194
% 4.69/1.80  #Tautology    : 25
% 4.69/1.80  #SimpNegUnit  : 56
% 4.69/1.80  #BackRed      : 0
% 4.69/1.80  
% 4.69/1.80  #Partial instantiations: 0
% 4.69/1.80  #Strategies tried      : 1
% 4.69/1.80  
% 4.69/1.80  Timing (in seconds)
% 4.69/1.80  ----------------------
% 4.69/1.80  Preprocessing        : 0.37
% 4.69/1.80  Parsing              : 0.19
% 4.69/1.80  CNF conversion       : 0.04
% 4.69/1.80  Main loop            : 0.63
% 4.69/1.80  Inferencing          : 0.25
% 4.69/1.80  Reduction            : 0.17
% 4.69/1.80  Demodulation         : 0.12
% 4.69/1.80  BG Simplification    : 0.04
% 4.69/1.80  Subsumption          : 0.13
% 4.69/1.80  Abstraction          : 0.04
% 4.69/1.80  MUC search           : 0.00
% 4.69/1.80  Cooper               : 0.00
% 4.69/1.80  Total                : 1.07
% 4.69/1.80  Index Insertion      : 0.00
% 4.69/1.80  Index Deletion       : 0.00
% 4.69/1.80  Index Matching       : 0.00
% 4.69/1.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
