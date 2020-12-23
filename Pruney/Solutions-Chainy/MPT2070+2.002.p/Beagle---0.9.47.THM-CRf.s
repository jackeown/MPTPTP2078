%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:39 EST 2020

% Result     : Theorem 4.21s
% Output     : CNFRefutation 4.56s
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
%$ r2_waybel_7 > r1_waybel_0 > v4_pre_topc > v3_yellow_6 > v3_waybel_7 > v2_waybel_0 > v13_waybel_0 > r2_hidden > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k2_pre_topc > k10_yellow_6 > #nlpp > u1_struct_0 > k3_yellow_1 > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2

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

tff(r2_waybel_7,type,(
    r2_waybel_7: ( $i * $i * $i ) > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v13_waybel_0,type,(
    v13_waybel_0: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(v3_waybel_7,type,(
    v3_waybel_7: ( $i * $i ) > $o )).

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
                    & v2_waybel_0(C,k3_yellow_1(k2_struct_0(A)))
                    & v13_waybel_0(C,k3_yellow_1(k2_struct_0(A)))
                    & v3_waybel_7(C,k3_yellow_1(k2_struct_0(A)))
                    & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))))) )
                 => ( r2_hidden(B,C)
                   => ! [D] :
                        ( m1_subset_1(D,u1_struct_0(A))
                       => ( r2_waybel_7(A,C,D)
                         => r2_hidden(D,B) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_yellow19)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_yellow19)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_yellow19)).

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
                    & v2_waybel_0(D,k3_yellow_1(k2_struct_0(A)))
                    & v13_waybel_0(D,k3_yellow_1(k2_struct_0(A)))
                    & v3_waybel_7(D,k3_yellow_1(k2_struct_0(A)))
                    & m1_subset_1(D,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))
                    & r2_hidden(B,D)
                    & r2_waybel_7(A,D,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_yellow19)).

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

tff(c_222,plain,(
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

tff(c_228,plain,(
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
    inference(resolution,[status(thm)],[c_22,c_222])).

tff(c_286,plain,(
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
    inference(resolution,[status(thm)],[c_22,c_222])).

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

tff(c_393,plain,(
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
    inference(resolution,[status(thm)],[c_286,c_42])).

tff(c_48,plain,(
    ! [A_48,B_60,C_66] :
      ( v13_waybel_0('#skF_4'(A_48,B_60,C_66),k3_yellow_1(k2_struct_0(A_48)))
      | ~ r2_hidden(C_66,k2_pre_topc(A_48,B_60))
      | ~ m1_subset_1(C_66,u1_struct_0(A_48))
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ l1_pre_topc(A_48)
      | ~ v2_pre_topc(A_48)
      | v2_struct_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_50,plain,(
    ! [A_48,B_60,C_66] :
      ( v2_waybel_0('#skF_4'(A_48,B_60,C_66),k3_yellow_1(k2_struct_0(A_48)))
      | ~ r2_hidden(C_66,k2_pre_topc(A_48,B_60))
      | ~ m1_subset_1(C_66,u1_struct_0(A_48))
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ l1_pre_topc(A_48)
      | ~ v2_pre_topc(A_48)
      | v2_struct_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_46,plain,(
    ! [A_48,B_60,C_66] :
      ( v3_waybel_7('#skF_4'(A_48,B_60,C_66),k3_yellow_1(k2_struct_0(A_48)))
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

tff(c_176,plain,(
    ! [A_139,B_140,C_141] :
      ( r2_waybel_7(A_139,'#skF_4'(A_139,B_140,C_141),C_141)
      | ~ r2_hidden(C_141,k2_pre_topc(A_139,B_140))
      | ~ m1_subset_1(C_141,u1_struct_0(A_139))
      | ~ m1_subset_1(B_140,k1_zfmisc_1(u1_struct_0(A_139)))
      | ~ l1_pre_topc(A_139)
      | ~ v2_pre_topc(A_139)
      | v2_struct_0(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_178,plain,(
    ! [C_141] :
      ( r2_waybel_7('#skF_5','#skF_4'('#skF_5','#skF_6',C_141),C_141)
      | ~ r2_hidden(C_141,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_141,u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_54,c_176])).

tff(c_181,plain,(
    ! [C_141] :
      ( r2_waybel_7('#skF_5','#skF_4'('#skF_5','#skF_6',C_141),C_141)
      | ~ r2_hidden(C_141,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_141,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_178])).

tff(c_184,plain,(
    ! [C_145] :
      ( r2_waybel_7('#skF_5','#skF_4'('#skF_5','#skF_6',C_145),C_145)
      | ~ r2_hidden(C_145,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_145,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_181])).

tff(c_100,plain,(
    ! [D_92,C_90] :
      ( v4_pre_topc('#skF_6','#skF_5')
      | r2_hidden(D_92,'#skF_6')
      | ~ r2_waybel_7('#skF_5',C_90,D_92)
      | ~ m1_subset_1(D_92,u1_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_6',C_90)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))))
      | ~ v3_waybel_7(C_90,k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v13_waybel_0(C_90,k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v2_waybel_0(C_90,k3_yellow_1(k2_struct_0('#skF_5')))
      | v1_xboole_0(C_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_164,plain,(
    ! [D_92,C_90] :
      ( r2_hidden(D_92,'#skF_6')
      | ~ r2_waybel_7('#skF_5',C_90,D_92)
      | ~ m1_subset_1(D_92,u1_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_6',C_90)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))))
      | ~ v3_waybel_7(C_90,k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v13_waybel_0(C_90,k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v2_waybel_0(C_90,k3_yellow_1(k2_struct_0('#skF_5')))
      | v1_xboole_0(C_90) ) ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_100])).

tff(c_249,plain,(
    ! [C_188] :
      ( r2_hidden(C_188,'#skF_6')
      | ~ r2_hidden('#skF_6','#skF_4'('#skF_5','#skF_6',C_188))
      | ~ m1_subset_1('#skF_4'('#skF_5','#skF_6',C_188),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))))
      | ~ v3_waybel_7('#skF_4'('#skF_5','#skF_6',C_188),k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v13_waybel_0('#skF_4'('#skF_5','#skF_6',C_188),k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v2_waybel_0('#skF_4'('#skF_5','#skF_6',C_188),k3_yellow_1(k2_struct_0('#skF_5')))
      | v1_xboole_0('#skF_4'('#skF_5','#skF_6',C_188))
      | ~ r2_hidden(C_188,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_188,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_184,c_164])).

tff(c_253,plain,(
    ! [C_66] :
      ( r2_hidden(C_66,'#skF_6')
      | ~ r2_hidden('#skF_6','#skF_4'('#skF_5','#skF_6',C_66))
      | ~ v3_waybel_7('#skF_4'('#skF_5','#skF_6',C_66),k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v13_waybel_0('#skF_4'('#skF_5','#skF_6',C_66),k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v2_waybel_0('#skF_4'('#skF_5','#skF_6',C_66),k3_yellow_1(k2_struct_0('#skF_5')))
      | v1_xboole_0('#skF_4'('#skF_5','#skF_6',C_66))
      | ~ r2_hidden(C_66,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_66,u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_44,c_249])).

tff(c_256,plain,(
    ! [C_66] :
      ( r2_hidden(C_66,'#skF_6')
      | ~ r2_hidden('#skF_6','#skF_4'('#skF_5','#skF_6',C_66))
      | ~ v3_waybel_7('#skF_4'('#skF_5','#skF_6',C_66),k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v13_waybel_0('#skF_4'('#skF_5','#skF_6',C_66),k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v2_waybel_0('#skF_4'('#skF_5','#skF_6',C_66),k3_yellow_1(k2_struct_0('#skF_5')))
      | v1_xboole_0('#skF_4'('#skF_5','#skF_6',C_66))
      | ~ r2_hidden(C_66,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_66,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_253])).

tff(c_258,plain,(
    ! [C_189] :
      ( r2_hidden(C_189,'#skF_6')
      | ~ r2_hidden('#skF_6','#skF_4'('#skF_5','#skF_6',C_189))
      | ~ v3_waybel_7('#skF_4'('#skF_5','#skF_6',C_189),k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v13_waybel_0('#skF_4'('#skF_5','#skF_6',C_189),k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v2_waybel_0('#skF_4'('#skF_5','#skF_6',C_189),k3_yellow_1(k2_struct_0('#skF_5')))
      | v1_xboole_0('#skF_4'('#skF_5','#skF_6',C_189))
      | ~ r2_hidden(C_189,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_189,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_256])).

tff(c_262,plain,(
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
    inference(resolution,[status(thm)],[c_46,c_258])).

tff(c_265,plain,(
    ! [C_66] :
      ( r2_hidden(C_66,'#skF_6')
      | ~ r2_hidden('#skF_6','#skF_4'('#skF_5','#skF_6',C_66))
      | ~ v13_waybel_0('#skF_4'('#skF_5','#skF_6',C_66),k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v2_waybel_0('#skF_4'('#skF_5','#skF_6',C_66),k3_yellow_1(k2_struct_0('#skF_5')))
      | v1_xboole_0('#skF_4'('#skF_5','#skF_6',C_66))
      | ~ r2_hidden(C_66,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_66,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_262])).

tff(c_267,plain,(
    ! [C_190] :
      ( r2_hidden(C_190,'#skF_6')
      | ~ r2_hidden('#skF_6','#skF_4'('#skF_5','#skF_6',C_190))
      | ~ v13_waybel_0('#skF_4'('#skF_5','#skF_6',C_190),k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v2_waybel_0('#skF_4'('#skF_5','#skF_6',C_190),k3_yellow_1(k2_struct_0('#skF_5')))
      | v1_xboole_0('#skF_4'('#skF_5','#skF_6',C_190))
      | ~ r2_hidden(C_190,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_190,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_265])).

tff(c_271,plain,(
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
    inference(resolution,[status(thm)],[c_50,c_267])).

tff(c_274,plain,(
    ! [C_66] :
      ( r2_hidden(C_66,'#skF_6')
      | ~ r2_hidden('#skF_6','#skF_4'('#skF_5','#skF_6',C_66))
      | ~ v13_waybel_0('#skF_4'('#skF_5','#skF_6',C_66),k3_yellow_1(k2_struct_0('#skF_5')))
      | v1_xboole_0('#skF_4'('#skF_5','#skF_6',C_66))
      | ~ r2_hidden(C_66,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_66,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_271])).

tff(c_276,plain,(
    ! [C_191] :
      ( r2_hidden(C_191,'#skF_6')
      | ~ r2_hidden('#skF_6','#skF_4'('#skF_5','#skF_6',C_191))
      | ~ v13_waybel_0('#skF_4'('#skF_5','#skF_6',C_191),k3_yellow_1(k2_struct_0('#skF_5')))
      | v1_xboole_0('#skF_4'('#skF_5','#skF_6',C_191))
      | ~ r2_hidden(C_191,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_191,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_274])).

tff(c_280,plain,(
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
    inference(resolution,[status(thm)],[c_48,c_276])).

tff(c_283,plain,(
    ! [C_66] :
      ( r2_hidden(C_66,'#skF_6')
      | ~ r2_hidden('#skF_6','#skF_4'('#skF_5','#skF_6',C_66))
      | v1_xboole_0('#skF_4'('#skF_5','#skF_6',C_66))
      | ~ r2_hidden(C_66,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_66,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_280])).

tff(c_284,plain,(
    ! [C_66] :
      ( r2_hidden(C_66,'#skF_6')
      | ~ r2_hidden('#skF_6','#skF_4'('#skF_5','#skF_6',C_66))
      | v1_xboole_0('#skF_4'('#skF_5','#skF_6',C_66))
      | ~ r2_hidden(C_66,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_66,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_283])).

tff(c_399,plain,(
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
    inference(resolution,[status(thm)],[c_393,c_284])).

tff(c_406,plain,(
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
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_399])).

tff(c_408,plain,(
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
    inference(negUnitSimplification,[status(thm)],[c_60,c_406])).

tff(c_412,plain,(
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
    inference(resolution,[status(thm)],[c_228,c_408])).

tff(c_415,plain,(
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
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_412])).

tff(c_417,plain,(
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
    inference(negUnitSimplification,[status(thm)],[c_60,c_415])).

tff(c_421,plain,(
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
    inference(resolution,[status(thm)],[c_24,c_417])).

tff(c_424,plain,(
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
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_421])).

tff(c_426,plain,(
    ! [B_240] :
      ( r2_hidden('#skF_3'('#skF_5',B_240),'#skF_6')
      | v1_xboole_0('#skF_4'('#skF_5','#skF_6','#skF_3'('#skF_5',B_240)))
      | ~ r1_waybel_0('#skF_5','#skF_2'('#skF_5',B_240),'#skF_6')
      | ~ l1_waybel_0('#skF_2'('#skF_5',B_240),'#skF_5')
      | ~ v3_yellow_6('#skF_2'('#skF_5',B_240),'#skF_5')
      | ~ v7_waybel_0('#skF_2'('#skF_5',B_240))
      | ~ v4_orders_2('#skF_2'('#skF_5',B_240))
      | v2_struct_0('#skF_2'('#skF_5',B_240))
      | v4_pre_topc(B_240,'#skF_5')
      | ~ m1_subset_1(B_240,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_424])).

tff(c_429,plain,
    ( r2_hidden('#skF_3'('#skF_5','#skF_6'),'#skF_6')
    | v1_xboole_0('#skF_4'('#skF_5','#skF_6','#skF_3'('#skF_5','#skF_6')))
    | ~ r1_waybel_0('#skF_5','#skF_2'('#skF_5','#skF_6'),'#skF_6')
    | ~ l1_waybel_0('#skF_2'('#skF_5','#skF_6'),'#skF_5')
    | ~ v3_yellow_6('#skF_2'('#skF_5','#skF_6'),'#skF_5')
    | ~ v7_waybel_0('#skF_2'('#skF_5','#skF_6'))
    | ~ v4_orders_2('#skF_2'('#skF_5','#skF_6'))
    | v2_struct_0('#skF_2'('#skF_5','#skF_6'))
    | v4_pre_topc('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_426])).

tff(c_432,plain,
    ( r2_hidden('#skF_3'('#skF_5','#skF_6'),'#skF_6')
    | v1_xboole_0('#skF_4'('#skF_5','#skF_6','#skF_3'('#skF_5','#skF_6')))
    | v2_struct_0('#skF_2'('#skF_5','#skF_6'))
    | v4_pre_topc('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_125,c_140,c_133,c_149,c_429])).

tff(c_433,plain,
    ( r2_hidden('#skF_3'('#skF_5','#skF_6'),'#skF_6')
    | v1_xboole_0('#skF_4'('#skF_5','#skF_6','#skF_3'('#skF_5','#skF_6'))) ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_109,c_432])).

tff(c_438,plain,(
    v1_xboole_0('#skF_4'('#skF_5','#skF_6','#skF_3'('#skF_5','#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_433])).

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

tff(c_307,plain,(
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
    inference(resolution,[status(thm)],[c_286,c_52])).

tff(c_440,plain,
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
    inference(resolution,[status(thm)],[c_438,c_307])).

tff(c_443,plain,
    ( v2_struct_0('#skF_2'('#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_3'('#skF_5','#skF_6'),u1_struct_0('#skF_5'))
    | v4_pre_topc('#skF_6','#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_117,c_125,c_140,c_133,c_149,c_440])).

tff(c_444,plain,(
    ~ m1_subset_1('#skF_3'('#skF_5','#skF_6'),u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_101,c_109,c_443])).

tff(c_447,plain,
    ( v4_pre_topc('#skF_6','#skF_5')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_24,c_444])).

tff(c_450,plain,
    ( v4_pre_topc('#skF_6','#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_447])).

tff(c_452,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_101,c_450])).

tff(c_453,plain,(
    r2_hidden('#skF_3'('#skF_5','#skF_6'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_433])).

tff(c_20,plain,(
    ! [A_23,B_37] :
      ( ~ r2_hidden('#skF_3'(A_23,B_37),B_37)
      | v4_pre_topc(B_37,A_23)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_456,plain,
    ( v4_pre_topc('#skF_6','#skF_5')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_453,c_20])).

tff(c_459,plain,
    ( v4_pre_topc('#skF_6','#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_456])).

tff(c_461,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_101,c_459])).

tff(c_463,plain,(
    v4_pre_topc('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_66,plain,
    ( m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ v4_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_469,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_463,c_66])).

tff(c_68,plain,
    ( r2_hidden('#skF_6','#skF_7')
    | ~ v4_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_467,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_463,c_68])).

tff(c_462,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_76,plain,
    ( v2_waybel_0('#skF_7',k3_yellow_1(k2_struct_0('#skF_5')))
    | ~ v4_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_477,plain,(
    v2_waybel_0('#skF_7',k3_yellow_1(k2_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_463,c_76])).

tff(c_74,plain,
    ( v13_waybel_0('#skF_7',k3_yellow_1(k2_struct_0('#skF_5')))
    | ~ v4_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_475,plain,(
    v13_waybel_0('#skF_7',k3_yellow_1(k2_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_463,c_74])).

tff(c_72,plain,
    ( v3_waybel_7('#skF_7',k3_yellow_1(k2_struct_0('#skF_5')))
    | ~ v4_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_473,plain,(
    v3_waybel_7('#skF_7',k3_yellow_1(k2_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_463,c_72])).

tff(c_70,plain,
    ( m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))))
    | ~ v4_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_479,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_463,c_70])).

tff(c_64,plain,
    ( r2_waybel_7('#skF_5','#skF_7','#skF_8')
    | ~ v4_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_471,plain,(
    r2_waybel_7('#skF_5','#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_463,c_64])).

tff(c_649,plain,(
    ! [C_325,A_326,B_327,D_328] :
      ( r2_hidden(C_325,k2_pre_topc(A_326,B_327))
      | ~ r2_waybel_7(A_326,D_328,C_325)
      | ~ r2_hidden(B_327,D_328)
      | ~ m1_subset_1(D_328,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_326)))))
      | ~ v3_waybel_7(D_328,k3_yellow_1(k2_struct_0(A_326)))
      | ~ v13_waybel_0(D_328,k3_yellow_1(k2_struct_0(A_326)))
      | ~ v2_waybel_0(D_328,k3_yellow_1(k2_struct_0(A_326)))
      | v1_xboole_0(D_328)
      | ~ m1_subset_1(C_325,u1_struct_0(A_326))
      | ~ m1_subset_1(B_327,k1_zfmisc_1(u1_struct_0(A_326)))
      | ~ l1_pre_topc(A_326)
      | ~ v2_pre_topc(A_326)
      | v2_struct_0(A_326) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_653,plain,(
    ! [B_327] :
      ( r2_hidden('#skF_8',k2_pre_topc('#skF_5',B_327))
      | ~ r2_hidden(B_327,'#skF_7')
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))))
      | ~ v3_waybel_7('#skF_7',k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v13_waybel_0('#skF_7',k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v2_waybel_0('#skF_7',k3_yellow_1(k2_struct_0('#skF_5')))
      | v1_xboole_0('#skF_7')
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_327,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_471,c_649])).

tff(c_660,plain,(
    ! [B_327] :
      ( r2_hidden('#skF_8',k2_pre_topc('#skF_5',B_327))
      | ~ r2_hidden(B_327,'#skF_7')
      | v1_xboole_0('#skF_7')
      | ~ m1_subset_1(B_327,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_469,c_477,c_475,c_473,c_479,c_653])).

tff(c_662,plain,(
    ! [B_329] :
      ( r2_hidden('#skF_8',k2_pre_topc('#skF_5',B_329))
      | ~ r2_hidden(B_329,'#skF_7')
      | ~ m1_subset_1(B_329,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_462,c_660])).

tff(c_665,plain,
    ( r2_hidden('#skF_8',k2_pre_topc('#skF_5','#skF_6'))
    | ~ r2_hidden('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_54,c_662])).

tff(c_668,plain,(
    r2_hidden('#skF_8',k2_pre_topc('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_467,c_665])).

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

tff(c_678,plain,
    ( ~ v2_struct_0('#skF_1'('#skF_5','#skF_6','#skF_8'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_668,c_16])).

tff(c_699,plain,
    ( ~ v2_struct_0('#skF_1'('#skF_5','#skF_6','#skF_8'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_469,c_678])).

tff(c_700,plain,(
    ~ v2_struct_0('#skF_1'('#skF_5','#skF_6','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_699])).

tff(c_62,plain,
    ( ~ r2_hidden('#skF_8','#skF_6')
    | ~ v4_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_465,plain,(
    ~ r2_hidden('#skF_8','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_463,c_62])).

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
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_469,c_676])).

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

tff(c_680,plain,
    ( v7_waybel_0('#skF_1'('#skF_5','#skF_6','#skF_8'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_668,c_12])).

tff(c_703,plain,
    ( v7_waybel_0('#skF_1'('#skF_5','#skF_6','#skF_8'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_469,c_680])).

tff(c_704,plain,(
    v7_waybel_0('#skF_1'('#skF_5','#skF_6','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_703])).

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
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_469,c_672])).

tff(c_688,plain,(
    l1_waybel_0('#skF_1'('#skF_5','#skF_6','#skF_8'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_687])).

tff(c_556,plain,(
    ! [A_278,B_279,C_280] :
      ( v3_yellow_6('#skF_1'(A_278,B_279,C_280),A_278)
      | ~ r2_hidden(C_280,k2_pre_topc(A_278,B_279))
      | ~ m1_subset_1(C_280,u1_struct_0(A_278))
      | ~ m1_subset_1(B_279,k1_zfmisc_1(u1_struct_0(A_278)))
      | ~ l1_pre_topc(A_278)
      | ~ v2_pre_topc(A_278)
      | v2_struct_0(A_278) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_560,plain,(
    ! [C_280] :
      ( v3_yellow_6('#skF_1'('#skF_5','#skF_6',C_280),'#skF_5')
      | ~ r2_hidden(C_280,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_280,u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_54,c_556])).

tff(c_564,plain,(
    ! [C_280] :
      ( v3_yellow_6('#skF_1'('#skF_5','#skF_6',C_280),'#skF_5')
      | ~ r2_hidden(C_280,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_280,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_560])).

tff(c_565,plain,(
    ! [C_280] :
      ( v3_yellow_6('#skF_1'('#skF_5','#skF_6',C_280),'#skF_5')
      | ~ r2_hidden(C_280,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_280,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_564])).

tff(c_579,plain,(
    ! [A_289,B_290,C_291] :
      ( r1_waybel_0(A_289,'#skF_1'(A_289,B_290,C_291),B_290)
      | ~ r2_hidden(C_291,k2_pre_topc(A_289,B_290))
      | ~ m1_subset_1(C_291,u1_struct_0(A_289))
      | ~ m1_subset_1(B_290,k1_zfmisc_1(u1_struct_0(A_289)))
      | ~ l1_pre_topc(A_289)
      | ~ v2_pre_topc(A_289)
      | v2_struct_0(A_289) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_583,plain,(
    ! [C_291] :
      ( r1_waybel_0('#skF_5','#skF_1'('#skF_5','#skF_6',C_291),'#skF_6')
      | ~ r2_hidden(C_291,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_291,u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_54,c_579])).

tff(c_587,plain,(
    ! [C_291] :
      ( r1_waybel_0('#skF_5','#skF_1'('#skF_5','#skF_6',C_291),'#skF_6')
      | ~ r2_hidden(C_291,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_291,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_583])).

tff(c_588,plain,(
    ! [C_291] :
      ( r1_waybel_0('#skF_5','#skF_1'('#skF_5','#skF_6',C_291),'#skF_6')
      | ~ r2_hidden(C_291,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_291,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_587])).

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

tff(c_837,plain,(
    ! [C_392,B_393,A_394,B_395] :
      ( r2_hidden(C_392,B_393)
      | ~ r1_waybel_0(A_394,'#skF_1'(A_394,B_395,C_392),B_393)
      | ~ l1_waybel_0('#skF_1'(A_394,B_395,C_392),A_394)
      | ~ v3_yellow_6('#skF_1'(A_394,B_395,C_392),A_394)
      | ~ v7_waybel_0('#skF_1'(A_394,B_395,C_392))
      | ~ v4_orders_2('#skF_1'(A_394,B_395,C_392))
      | v2_struct_0('#skF_1'(A_394,B_395,C_392))
      | ~ v4_pre_topc(B_393,A_394)
      | ~ m1_subset_1(B_393,k1_zfmisc_1(u1_struct_0(A_394)))
      | ~ r2_hidden(C_392,k2_pre_topc(A_394,B_395))
      | ~ m1_subset_1(C_392,u1_struct_0(A_394))
      | ~ m1_subset_1(B_395,k1_zfmisc_1(u1_struct_0(A_394)))
      | ~ l1_pre_topc(A_394)
      | ~ v2_pre_topc(A_394)
      | v2_struct_0(A_394) ) ),
    inference(resolution,[status(thm)],[c_4,c_634])).

tff(c_839,plain,(
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
    inference(resolution,[status(thm)],[c_588,c_837])).

tff(c_842,plain,(
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
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_463,c_839])).

tff(c_844,plain,(
    ! [C_396] :
      ( r2_hidden(C_396,'#skF_6')
      | ~ l1_waybel_0('#skF_1'('#skF_5','#skF_6',C_396),'#skF_5')
      | ~ v3_yellow_6('#skF_1'('#skF_5','#skF_6',C_396),'#skF_5')
      | ~ v7_waybel_0('#skF_1'('#skF_5','#skF_6',C_396))
      | ~ v4_orders_2('#skF_1'('#skF_5','#skF_6',C_396))
      | v2_struct_0('#skF_1'('#skF_5','#skF_6',C_396))
      | ~ r2_hidden(C_396,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_396,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_842])).

tff(c_849,plain,(
    ! [C_397] :
      ( r2_hidden(C_397,'#skF_6')
      | ~ l1_waybel_0('#skF_1'('#skF_5','#skF_6',C_397),'#skF_5')
      | ~ v7_waybel_0('#skF_1'('#skF_5','#skF_6',C_397))
      | ~ v4_orders_2('#skF_1'('#skF_5','#skF_6',C_397))
      | v2_struct_0('#skF_1'('#skF_5','#skF_6',C_397))
      | ~ r2_hidden(C_397,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_397,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_565,c_844])).

tff(c_856,plain,
    ( r2_hidden('#skF_8','#skF_6')
    | ~ l1_waybel_0('#skF_1'('#skF_5','#skF_6','#skF_8'),'#skF_5')
    | ~ v7_waybel_0('#skF_1'('#skF_5','#skF_6','#skF_8'))
    | ~ v4_orders_2('#skF_1'('#skF_5','#skF_6','#skF_8'))
    | v2_struct_0('#skF_1'('#skF_5','#skF_6','#skF_8'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_668,c_849])).

tff(c_863,plain,
    ( r2_hidden('#skF_8','#skF_6')
    | v2_struct_0('#skF_1'('#skF_5','#skF_6','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_469,c_696,c_704,c_688,c_856])).

tff(c_865,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_700,c_465,c_863])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:26:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.21/1.81  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.44/1.83  
% 4.44/1.83  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.44/1.83  %$ r2_waybel_7 > r1_waybel_0 > v4_pre_topc > v3_yellow_6 > v3_waybel_7 > v2_waybel_0 > v13_waybel_0 > r2_hidden > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k2_pre_topc > k10_yellow_6 > #nlpp > u1_struct_0 > k3_yellow_1 > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2
% 4.44/1.83  
% 4.44/1.83  %Foreground sorts:
% 4.44/1.83  
% 4.44/1.83  
% 4.44/1.83  %Background operators:
% 4.44/1.83  
% 4.44/1.83  
% 4.44/1.83  %Foreground operators:
% 4.44/1.83  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.44/1.83  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.44/1.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.44/1.83  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.44/1.83  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 4.44/1.83  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 4.44/1.83  tff(k10_yellow_6, type, k10_yellow_6: ($i * $i) > $i).
% 4.44/1.83  tff(v3_yellow_6, type, v3_yellow_6: ($i * $i) > $o).
% 4.44/1.83  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.44/1.83  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 4.44/1.83  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 4.44/1.83  tff('#skF_7', type, '#skF_7': $i).
% 4.44/1.83  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.44/1.83  tff('#skF_5', type, '#skF_5': $i).
% 4.44/1.83  tff(r1_waybel_0, type, r1_waybel_0: ($i * $i * $i) > $o).
% 4.44/1.83  tff('#skF_6', type, '#skF_6': $i).
% 4.44/1.83  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 4.44/1.83  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.44/1.83  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 4.44/1.83  tff('#skF_8', type, '#skF_8': $i).
% 4.44/1.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.44/1.83  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 4.44/1.83  tff(r2_waybel_7, type, r2_waybel_7: ($i * $i * $i) > $o).
% 4.44/1.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.44/1.83  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.44/1.83  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 4.44/1.83  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.44/1.83  tff(v3_waybel_7, type, v3_waybel_7: ($i * $i) > $o).
% 4.44/1.83  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.44/1.83  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.44/1.83  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.44/1.83  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.44/1.83  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.44/1.83  
% 4.56/1.87  tff(f_154, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (![C]: (((((~v1_xboole_0(C) & v2_waybel_0(C, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(C, k3_yellow_1(k2_struct_0(A)))) & v3_waybel_7(C, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (r2_hidden(B, C) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_waybel_7(A, C, D) => r2_hidden(D, B)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_yellow19)).
% 4.56/1.87  tff(f_89, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (![C]: (((((~v2_struct_0(C) & v4_orders_2(C)) & v7_waybel_0(C)) & v3_yellow_6(C, A)) & l1_waybel_0(C, A)) => (r1_waybel_0(A, C, B) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, k10_yellow_6(A, C)) => r2_hidden(D, B)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_yellow19)).
% 4.56/1.87  tff(f_56, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, k2_pre_topc(A, B)) <=> (?[D]: ((((((~v2_struct_0(D) & v4_orders_2(D)) & v7_waybel_0(D)) & v3_yellow_6(D, A)) & l1_waybel_0(D, A)) & r1_waybel_0(A, D, B)) & r2_hidden(C, k10_yellow_6(A, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_yellow19)).
% 4.56/1.87  tff(f_120, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, k2_pre_topc(A, B)) <=> (?[D]: ((((((~v1_xboole_0(D) & v2_waybel_0(D, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(D, k3_yellow_1(k2_struct_0(A)))) & v3_waybel_7(D, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(D, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) & r2_hidden(B, D)) & r2_waybel_7(A, D, C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_yellow19)).
% 4.56/1.87  tff(c_60, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_154])).
% 4.56/1.87  tff(c_58, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_154])).
% 4.56/1.87  tff(c_56, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_154])).
% 4.56/1.87  tff(c_54, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_154])).
% 4.56/1.87  tff(c_78, plain, (~v1_xboole_0('#skF_7') | ~v4_pre_topc('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_154])).
% 4.56/1.87  tff(c_101, plain, (~v4_pre_topc('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_78])).
% 4.56/1.87  tff(c_24, plain, (![A_23, B_37]: (m1_subset_1('#skF_3'(A_23, B_37), u1_struct_0(A_23)) | v4_pre_topc(B_37, A_23) | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0(A_23))) | ~l1_pre_topc(A_23) | ~v2_pre_topc(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.56/1.87  tff(c_102, plain, (![A_93, B_94]: (~v2_struct_0('#skF_2'(A_93, B_94)) | v4_pre_topc(B_94, A_93) | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0(A_93))) | ~l1_pre_topc(A_93) | ~v2_pre_topc(A_93) | v2_struct_0(A_93))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.56/1.87  tff(c_105, plain, (~v2_struct_0('#skF_2'('#skF_5', '#skF_6')) | v4_pre_topc('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_54, c_102])).
% 4.56/1.87  tff(c_108, plain, (~v2_struct_0('#skF_2'('#skF_5', '#skF_6')) | v4_pre_topc('#skF_6', '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_105])).
% 4.56/1.87  tff(c_109, plain, (~v2_struct_0('#skF_2'('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_60, c_101, c_108])).
% 4.56/1.87  tff(c_110, plain, (![A_95, B_96]: (v4_orders_2('#skF_2'(A_95, B_96)) | v4_pre_topc(B_96, A_95) | ~m1_subset_1(B_96, k1_zfmisc_1(u1_struct_0(A_95))) | ~l1_pre_topc(A_95) | ~v2_pre_topc(A_95) | v2_struct_0(A_95))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.56/1.87  tff(c_113, plain, (v4_orders_2('#skF_2'('#skF_5', '#skF_6')) | v4_pre_topc('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_54, c_110])).
% 4.56/1.87  tff(c_116, plain, (v4_orders_2('#skF_2'('#skF_5', '#skF_6')) | v4_pre_topc('#skF_6', '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_113])).
% 4.56/1.87  tff(c_117, plain, (v4_orders_2('#skF_2'('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_60, c_101, c_116])).
% 4.56/1.87  tff(c_118, plain, (![A_97, B_98]: (v7_waybel_0('#skF_2'(A_97, B_98)) | v4_pre_topc(B_98, A_97) | ~m1_subset_1(B_98, k1_zfmisc_1(u1_struct_0(A_97))) | ~l1_pre_topc(A_97) | ~v2_pre_topc(A_97) | v2_struct_0(A_97))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.56/1.87  tff(c_121, plain, (v7_waybel_0('#skF_2'('#skF_5', '#skF_6')) | v4_pre_topc('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_54, c_118])).
% 4.56/1.87  tff(c_124, plain, (v7_waybel_0('#skF_2'('#skF_5', '#skF_6')) | v4_pre_topc('#skF_6', '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_121])).
% 4.56/1.87  tff(c_125, plain, (v7_waybel_0('#skF_2'('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_60, c_101, c_124])).
% 4.56/1.87  tff(c_134, plain, (![A_101, B_102]: (v3_yellow_6('#skF_2'(A_101, B_102), A_101) | v4_pre_topc(B_102, A_101) | ~m1_subset_1(B_102, k1_zfmisc_1(u1_struct_0(A_101))) | ~l1_pre_topc(A_101) | ~v2_pre_topc(A_101) | v2_struct_0(A_101))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.56/1.87  tff(c_136, plain, (v3_yellow_6('#skF_2'('#skF_5', '#skF_6'), '#skF_5') | v4_pre_topc('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_54, c_134])).
% 4.56/1.87  tff(c_139, plain, (v3_yellow_6('#skF_2'('#skF_5', '#skF_6'), '#skF_5') | v4_pre_topc('#skF_6', '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_136])).
% 4.56/1.87  tff(c_140, plain, (v3_yellow_6('#skF_2'('#skF_5', '#skF_6'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_60, c_101, c_139])).
% 4.56/1.87  tff(c_127, plain, (![A_99, B_100]: (l1_waybel_0('#skF_2'(A_99, B_100), A_99) | v4_pre_topc(B_100, A_99) | ~m1_subset_1(B_100, k1_zfmisc_1(u1_struct_0(A_99))) | ~l1_pre_topc(A_99) | ~v2_pre_topc(A_99) | v2_struct_0(A_99))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.56/1.87  tff(c_129, plain, (l1_waybel_0('#skF_2'('#skF_5', '#skF_6'), '#skF_5') | v4_pre_topc('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_54, c_127])).
% 4.56/1.87  tff(c_132, plain, (l1_waybel_0('#skF_2'('#skF_5', '#skF_6'), '#skF_5') | v4_pre_topc('#skF_6', '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_129])).
% 4.56/1.87  tff(c_133, plain, (l1_waybel_0('#skF_2'('#skF_5', '#skF_6'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_60, c_101, c_132])).
% 4.56/1.87  tff(c_143, plain, (![A_107, B_108]: (r1_waybel_0(A_107, '#skF_2'(A_107, B_108), B_108) | v4_pre_topc(B_108, A_107) | ~m1_subset_1(B_108, k1_zfmisc_1(u1_struct_0(A_107))) | ~l1_pre_topc(A_107) | ~v2_pre_topc(A_107) | v2_struct_0(A_107))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.56/1.87  tff(c_145, plain, (r1_waybel_0('#skF_5', '#skF_2'('#skF_5', '#skF_6'), '#skF_6') | v4_pre_topc('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_54, c_143])).
% 4.56/1.87  tff(c_148, plain, (r1_waybel_0('#skF_5', '#skF_2'('#skF_5', '#skF_6'), '#skF_6') | v4_pre_topc('#skF_6', '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_145])).
% 4.56/1.87  tff(c_149, plain, (r1_waybel_0('#skF_5', '#skF_2'('#skF_5', '#skF_6'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_60, c_101, c_148])).
% 4.56/1.87  tff(c_22, plain, (![A_23, B_37]: (r2_hidden('#skF_3'(A_23, B_37), k10_yellow_6(A_23, '#skF_2'(A_23, B_37))) | v4_pre_topc(B_37, A_23) | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0(A_23))) | ~l1_pre_topc(A_23) | ~v2_pre_topc(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.56/1.87  tff(c_222, plain, (![C_158, A_159, B_160, D_161]: (r2_hidden(C_158, k2_pre_topc(A_159, B_160)) | ~r2_hidden(C_158, k10_yellow_6(A_159, D_161)) | ~r1_waybel_0(A_159, D_161, B_160) | ~l1_waybel_0(D_161, A_159) | ~v3_yellow_6(D_161, A_159) | ~v7_waybel_0(D_161) | ~v4_orders_2(D_161) | v2_struct_0(D_161) | ~m1_subset_1(C_158, u1_struct_0(A_159)) | ~m1_subset_1(B_160, k1_zfmisc_1(u1_struct_0(A_159))) | ~l1_pre_topc(A_159) | ~v2_pre_topc(A_159) | v2_struct_0(A_159))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.56/1.87  tff(c_228, plain, (![A_23, B_37, B_160]: (r2_hidden('#skF_3'(A_23, B_37), k2_pre_topc(A_23, B_160)) | ~r1_waybel_0(A_23, '#skF_2'(A_23, B_37), B_160) | ~l1_waybel_0('#skF_2'(A_23, B_37), A_23) | ~v3_yellow_6('#skF_2'(A_23, B_37), A_23) | ~v7_waybel_0('#skF_2'(A_23, B_37)) | ~v4_orders_2('#skF_2'(A_23, B_37)) | v2_struct_0('#skF_2'(A_23, B_37)) | ~m1_subset_1('#skF_3'(A_23, B_37), u1_struct_0(A_23)) | ~m1_subset_1(B_160, k1_zfmisc_1(u1_struct_0(A_23))) | v4_pre_topc(B_37, A_23) | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0(A_23))) | ~l1_pre_topc(A_23) | ~v2_pre_topc(A_23) | v2_struct_0(A_23))), inference(resolution, [status(thm)], [c_22, c_222])).
% 4.56/1.87  tff(c_286, plain, (![A_193, B_194, B_195]: (r2_hidden('#skF_3'(A_193, B_194), k2_pre_topc(A_193, B_195)) | ~r1_waybel_0(A_193, '#skF_2'(A_193, B_194), B_195) | ~l1_waybel_0('#skF_2'(A_193, B_194), A_193) | ~v3_yellow_6('#skF_2'(A_193, B_194), A_193) | ~v7_waybel_0('#skF_2'(A_193, B_194)) | ~v4_orders_2('#skF_2'(A_193, B_194)) | v2_struct_0('#skF_2'(A_193, B_194)) | ~m1_subset_1('#skF_3'(A_193, B_194), u1_struct_0(A_193)) | ~m1_subset_1(B_195, k1_zfmisc_1(u1_struct_0(A_193))) | v4_pre_topc(B_194, A_193) | ~m1_subset_1(B_194, k1_zfmisc_1(u1_struct_0(A_193))) | ~l1_pre_topc(A_193) | ~v2_pre_topc(A_193) | v2_struct_0(A_193))), inference(resolution, [status(thm)], [c_22, c_222])).
% 4.56/1.87  tff(c_42, plain, (![B_60, A_48, C_66]: (r2_hidden(B_60, '#skF_4'(A_48, B_60, C_66)) | ~r2_hidden(C_66, k2_pre_topc(A_48, B_60)) | ~m1_subset_1(C_66, u1_struct_0(A_48)) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_48))) | ~l1_pre_topc(A_48) | ~v2_pre_topc(A_48) | v2_struct_0(A_48))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.56/1.87  tff(c_393, plain, (![B_235, A_236, B_237]: (r2_hidden(B_235, '#skF_4'(A_236, B_235, '#skF_3'(A_236, B_237))) | ~r1_waybel_0(A_236, '#skF_2'(A_236, B_237), B_235) | ~l1_waybel_0('#skF_2'(A_236, B_237), A_236) | ~v3_yellow_6('#skF_2'(A_236, B_237), A_236) | ~v7_waybel_0('#skF_2'(A_236, B_237)) | ~v4_orders_2('#skF_2'(A_236, B_237)) | v2_struct_0('#skF_2'(A_236, B_237)) | ~m1_subset_1('#skF_3'(A_236, B_237), u1_struct_0(A_236)) | ~m1_subset_1(B_235, k1_zfmisc_1(u1_struct_0(A_236))) | v4_pre_topc(B_237, A_236) | ~m1_subset_1(B_237, k1_zfmisc_1(u1_struct_0(A_236))) | ~l1_pre_topc(A_236) | ~v2_pre_topc(A_236) | v2_struct_0(A_236))), inference(resolution, [status(thm)], [c_286, c_42])).
% 4.56/1.87  tff(c_48, plain, (![A_48, B_60, C_66]: (v13_waybel_0('#skF_4'(A_48, B_60, C_66), k3_yellow_1(k2_struct_0(A_48))) | ~r2_hidden(C_66, k2_pre_topc(A_48, B_60)) | ~m1_subset_1(C_66, u1_struct_0(A_48)) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_48))) | ~l1_pre_topc(A_48) | ~v2_pre_topc(A_48) | v2_struct_0(A_48))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.56/1.87  tff(c_50, plain, (![A_48, B_60, C_66]: (v2_waybel_0('#skF_4'(A_48, B_60, C_66), k3_yellow_1(k2_struct_0(A_48))) | ~r2_hidden(C_66, k2_pre_topc(A_48, B_60)) | ~m1_subset_1(C_66, u1_struct_0(A_48)) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_48))) | ~l1_pre_topc(A_48) | ~v2_pre_topc(A_48) | v2_struct_0(A_48))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.56/1.87  tff(c_46, plain, (![A_48, B_60, C_66]: (v3_waybel_7('#skF_4'(A_48, B_60, C_66), k3_yellow_1(k2_struct_0(A_48))) | ~r2_hidden(C_66, k2_pre_topc(A_48, B_60)) | ~m1_subset_1(C_66, u1_struct_0(A_48)) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_48))) | ~l1_pre_topc(A_48) | ~v2_pre_topc(A_48) | v2_struct_0(A_48))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.56/1.87  tff(c_44, plain, (![A_48, B_60, C_66]: (m1_subset_1('#skF_4'(A_48, B_60, C_66), k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_48))))) | ~r2_hidden(C_66, k2_pre_topc(A_48, B_60)) | ~m1_subset_1(C_66, u1_struct_0(A_48)) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_48))) | ~l1_pre_topc(A_48) | ~v2_pre_topc(A_48) | v2_struct_0(A_48))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.56/1.87  tff(c_176, plain, (![A_139, B_140, C_141]: (r2_waybel_7(A_139, '#skF_4'(A_139, B_140, C_141), C_141) | ~r2_hidden(C_141, k2_pre_topc(A_139, B_140)) | ~m1_subset_1(C_141, u1_struct_0(A_139)) | ~m1_subset_1(B_140, k1_zfmisc_1(u1_struct_0(A_139))) | ~l1_pre_topc(A_139) | ~v2_pre_topc(A_139) | v2_struct_0(A_139))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.56/1.87  tff(c_178, plain, (![C_141]: (r2_waybel_7('#skF_5', '#skF_4'('#skF_5', '#skF_6', C_141), C_141) | ~r2_hidden(C_141, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_141, u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_54, c_176])).
% 4.56/1.87  tff(c_181, plain, (![C_141]: (r2_waybel_7('#skF_5', '#skF_4'('#skF_5', '#skF_6', C_141), C_141) | ~r2_hidden(C_141, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_141, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_178])).
% 4.56/1.87  tff(c_184, plain, (![C_145]: (r2_waybel_7('#skF_5', '#skF_4'('#skF_5', '#skF_6', C_145), C_145) | ~r2_hidden(C_145, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_145, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_60, c_181])).
% 4.56/1.87  tff(c_100, plain, (![D_92, C_90]: (v4_pre_topc('#skF_6', '#skF_5') | r2_hidden(D_92, '#skF_6') | ~r2_waybel_7('#skF_5', C_90, D_92) | ~m1_subset_1(D_92, u1_struct_0('#skF_5')) | ~r2_hidden('#skF_6', C_90) | ~m1_subset_1(C_90, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))) | ~v3_waybel_7(C_90, k3_yellow_1(k2_struct_0('#skF_5'))) | ~v13_waybel_0(C_90, k3_yellow_1(k2_struct_0('#skF_5'))) | ~v2_waybel_0(C_90, k3_yellow_1(k2_struct_0('#skF_5'))) | v1_xboole_0(C_90))), inference(cnfTransformation, [status(thm)], [f_154])).
% 4.56/1.87  tff(c_164, plain, (![D_92, C_90]: (r2_hidden(D_92, '#skF_6') | ~r2_waybel_7('#skF_5', C_90, D_92) | ~m1_subset_1(D_92, u1_struct_0('#skF_5')) | ~r2_hidden('#skF_6', C_90) | ~m1_subset_1(C_90, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))) | ~v3_waybel_7(C_90, k3_yellow_1(k2_struct_0('#skF_5'))) | ~v13_waybel_0(C_90, k3_yellow_1(k2_struct_0('#skF_5'))) | ~v2_waybel_0(C_90, k3_yellow_1(k2_struct_0('#skF_5'))) | v1_xboole_0(C_90))), inference(negUnitSimplification, [status(thm)], [c_101, c_100])).
% 4.56/1.87  tff(c_249, plain, (![C_188]: (r2_hidden(C_188, '#skF_6') | ~r2_hidden('#skF_6', '#skF_4'('#skF_5', '#skF_6', C_188)) | ~m1_subset_1('#skF_4'('#skF_5', '#skF_6', C_188), k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))) | ~v3_waybel_7('#skF_4'('#skF_5', '#skF_6', C_188), k3_yellow_1(k2_struct_0('#skF_5'))) | ~v13_waybel_0('#skF_4'('#skF_5', '#skF_6', C_188), k3_yellow_1(k2_struct_0('#skF_5'))) | ~v2_waybel_0('#skF_4'('#skF_5', '#skF_6', C_188), k3_yellow_1(k2_struct_0('#skF_5'))) | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', C_188)) | ~r2_hidden(C_188, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_188, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_184, c_164])).
% 4.56/1.87  tff(c_253, plain, (![C_66]: (r2_hidden(C_66, '#skF_6') | ~r2_hidden('#skF_6', '#skF_4'('#skF_5', '#skF_6', C_66)) | ~v3_waybel_7('#skF_4'('#skF_5', '#skF_6', C_66), k3_yellow_1(k2_struct_0('#skF_5'))) | ~v13_waybel_0('#skF_4'('#skF_5', '#skF_6', C_66), k3_yellow_1(k2_struct_0('#skF_5'))) | ~v2_waybel_0('#skF_4'('#skF_5', '#skF_6', C_66), k3_yellow_1(k2_struct_0('#skF_5'))) | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', C_66)) | ~r2_hidden(C_66, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_66, u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_44, c_249])).
% 4.56/1.87  tff(c_256, plain, (![C_66]: (r2_hidden(C_66, '#skF_6') | ~r2_hidden('#skF_6', '#skF_4'('#skF_5', '#skF_6', C_66)) | ~v3_waybel_7('#skF_4'('#skF_5', '#skF_6', C_66), k3_yellow_1(k2_struct_0('#skF_5'))) | ~v13_waybel_0('#skF_4'('#skF_5', '#skF_6', C_66), k3_yellow_1(k2_struct_0('#skF_5'))) | ~v2_waybel_0('#skF_4'('#skF_5', '#skF_6', C_66), k3_yellow_1(k2_struct_0('#skF_5'))) | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', C_66)) | ~r2_hidden(C_66, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_66, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_253])).
% 4.56/1.87  tff(c_258, plain, (![C_189]: (r2_hidden(C_189, '#skF_6') | ~r2_hidden('#skF_6', '#skF_4'('#skF_5', '#skF_6', C_189)) | ~v3_waybel_7('#skF_4'('#skF_5', '#skF_6', C_189), k3_yellow_1(k2_struct_0('#skF_5'))) | ~v13_waybel_0('#skF_4'('#skF_5', '#skF_6', C_189), k3_yellow_1(k2_struct_0('#skF_5'))) | ~v2_waybel_0('#skF_4'('#skF_5', '#skF_6', C_189), k3_yellow_1(k2_struct_0('#skF_5'))) | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', C_189)) | ~r2_hidden(C_189, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_189, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_60, c_256])).
% 4.56/1.87  tff(c_262, plain, (![C_66]: (r2_hidden(C_66, '#skF_6') | ~r2_hidden('#skF_6', '#skF_4'('#skF_5', '#skF_6', C_66)) | ~v13_waybel_0('#skF_4'('#skF_5', '#skF_6', C_66), k3_yellow_1(k2_struct_0('#skF_5'))) | ~v2_waybel_0('#skF_4'('#skF_5', '#skF_6', C_66), k3_yellow_1(k2_struct_0('#skF_5'))) | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', C_66)) | ~r2_hidden(C_66, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_66, u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_46, c_258])).
% 4.56/1.87  tff(c_265, plain, (![C_66]: (r2_hidden(C_66, '#skF_6') | ~r2_hidden('#skF_6', '#skF_4'('#skF_5', '#skF_6', C_66)) | ~v13_waybel_0('#skF_4'('#skF_5', '#skF_6', C_66), k3_yellow_1(k2_struct_0('#skF_5'))) | ~v2_waybel_0('#skF_4'('#skF_5', '#skF_6', C_66), k3_yellow_1(k2_struct_0('#skF_5'))) | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', C_66)) | ~r2_hidden(C_66, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_66, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_262])).
% 4.56/1.87  tff(c_267, plain, (![C_190]: (r2_hidden(C_190, '#skF_6') | ~r2_hidden('#skF_6', '#skF_4'('#skF_5', '#skF_6', C_190)) | ~v13_waybel_0('#skF_4'('#skF_5', '#skF_6', C_190), k3_yellow_1(k2_struct_0('#skF_5'))) | ~v2_waybel_0('#skF_4'('#skF_5', '#skF_6', C_190), k3_yellow_1(k2_struct_0('#skF_5'))) | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', C_190)) | ~r2_hidden(C_190, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_190, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_60, c_265])).
% 4.56/1.87  tff(c_271, plain, (![C_66]: (r2_hidden(C_66, '#skF_6') | ~r2_hidden('#skF_6', '#skF_4'('#skF_5', '#skF_6', C_66)) | ~v13_waybel_0('#skF_4'('#skF_5', '#skF_6', C_66), k3_yellow_1(k2_struct_0('#skF_5'))) | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', C_66)) | ~r2_hidden(C_66, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_66, u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_50, c_267])).
% 4.56/1.87  tff(c_274, plain, (![C_66]: (r2_hidden(C_66, '#skF_6') | ~r2_hidden('#skF_6', '#skF_4'('#skF_5', '#skF_6', C_66)) | ~v13_waybel_0('#skF_4'('#skF_5', '#skF_6', C_66), k3_yellow_1(k2_struct_0('#skF_5'))) | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', C_66)) | ~r2_hidden(C_66, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_66, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_271])).
% 4.56/1.87  tff(c_276, plain, (![C_191]: (r2_hidden(C_191, '#skF_6') | ~r2_hidden('#skF_6', '#skF_4'('#skF_5', '#skF_6', C_191)) | ~v13_waybel_0('#skF_4'('#skF_5', '#skF_6', C_191), k3_yellow_1(k2_struct_0('#skF_5'))) | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', C_191)) | ~r2_hidden(C_191, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_191, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_60, c_274])).
% 4.56/1.87  tff(c_280, plain, (![C_66]: (r2_hidden(C_66, '#skF_6') | ~r2_hidden('#skF_6', '#skF_4'('#skF_5', '#skF_6', C_66)) | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', C_66)) | ~r2_hidden(C_66, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_66, u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_48, c_276])).
% 4.56/1.87  tff(c_283, plain, (![C_66]: (r2_hidden(C_66, '#skF_6') | ~r2_hidden('#skF_6', '#skF_4'('#skF_5', '#skF_6', C_66)) | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', C_66)) | ~r2_hidden(C_66, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_66, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_280])).
% 4.56/1.87  tff(c_284, plain, (![C_66]: (r2_hidden(C_66, '#skF_6') | ~r2_hidden('#skF_6', '#skF_4'('#skF_5', '#skF_6', C_66)) | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', C_66)) | ~r2_hidden(C_66, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_66, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_60, c_283])).
% 4.56/1.87  tff(c_399, plain, (![B_237]: (r2_hidden('#skF_3'('#skF_5', B_237), '#skF_6') | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_237))) | ~r2_hidden('#skF_3'('#skF_5', B_237), k2_pre_topc('#skF_5', '#skF_6')) | ~r1_waybel_0('#skF_5', '#skF_2'('#skF_5', B_237), '#skF_6') | ~l1_waybel_0('#skF_2'('#skF_5', B_237), '#skF_5') | ~v3_yellow_6('#skF_2'('#skF_5', B_237), '#skF_5') | ~v7_waybel_0('#skF_2'('#skF_5', B_237)) | ~v4_orders_2('#skF_2'('#skF_5', B_237)) | v2_struct_0('#skF_2'('#skF_5', B_237)) | ~m1_subset_1('#skF_3'('#skF_5', B_237), u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | v4_pre_topc(B_237, '#skF_5') | ~m1_subset_1(B_237, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_393, c_284])).
% 4.56/1.87  tff(c_406, plain, (![B_237]: (r2_hidden('#skF_3'('#skF_5', B_237), '#skF_6') | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_237))) | ~r2_hidden('#skF_3'('#skF_5', B_237), k2_pre_topc('#skF_5', '#skF_6')) | ~r1_waybel_0('#skF_5', '#skF_2'('#skF_5', B_237), '#skF_6') | ~l1_waybel_0('#skF_2'('#skF_5', B_237), '#skF_5') | ~v3_yellow_6('#skF_2'('#skF_5', B_237), '#skF_5') | ~v7_waybel_0('#skF_2'('#skF_5', B_237)) | ~v4_orders_2('#skF_2'('#skF_5', B_237)) | v2_struct_0('#skF_2'('#skF_5', B_237)) | ~m1_subset_1('#skF_3'('#skF_5', B_237), u1_struct_0('#skF_5')) | v4_pre_topc(B_237, '#skF_5') | ~m1_subset_1(B_237, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_399])).
% 4.56/1.87  tff(c_408, plain, (![B_238]: (r2_hidden('#skF_3'('#skF_5', B_238), '#skF_6') | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_238))) | ~r2_hidden('#skF_3'('#skF_5', B_238), k2_pre_topc('#skF_5', '#skF_6')) | ~r1_waybel_0('#skF_5', '#skF_2'('#skF_5', B_238), '#skF_6') | ~l1_waybel_0('#skF_2'('#skF_5', B_238), '#skF_5') | ~v3_yellow_6('#skF_2'('#skF_5', B_238), '#skF_5') | ~v7_waybel_0('#skF_2'('#skF_5', B_238)) | ~v4_orders_2('#skF_2'('#skF_5', B_238)) | v2_struct_0('#skF_2'('#skF_5', B_238)) | ~m1_subset_1('#skF_3'('#skF_5', B_238), u1_struct_0('#skF_5')) | v4_pre_topc(B_238, '#skF_5') | ~m1_subset_1(B_238, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_60, c_406])).
% 4.56/1.87  tff(c_412, plain, (![B_37]: (r2_hidden('#skF_3'('#skF_5', B_37), '#skF_6') | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_37))) | ~r1_waybel_0('#skF_5', '#skF_2'('#skF_5', B_37), '#skF_6') | ~l1_waybel_0('#skF_2'('#skF_5', B_37), '#skF_5') | ~v3_yellow_6('#skF_2'('#skF_5', B_37), '#skF_5') | ~v7_waybel_0('#skF_2'('#skF_5', B_37)) | ~v4_orders_2('#skF_2'('#skF_5', B_37)) | v2_struct_0('#skF_2'('#skF_5', B_37)) | ~m1_subset_1('#skF_3'('#skF_5', B_37), u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | v4_pre_topc(B_37, '#skF_5') | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_228, c_408])).
% 4.56/1.87  tff(c_415, plain, (![B_37]: (r2_hidden('#skF_3'('#skF_5', B_37), '#skF_6') | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_37))) | ~r1_waybel_0('#skF_5', '#skF_2'('#skF_5', B_37), '#skF_6') | ~l1_waybel_0('#skF_2'('#skF_5', B_37), '#skF_5') | ~v3_yellow_6('#skF_2'('#skF_5', B_37), '#skF_5') | ~v7_waybel_0('#skF_2'('#skF_5', B_37)) | ~v4_orders_2('#skF_2'('#skF_5', B_37)) | v2_struct_0('#skF_2'('#skF_5', B_37)) | ~m1_subset_1('#skF_3'('#skF_5', B_37), u1_struct_0('#skF_5')) | v4_pre_topc(B_37, '#skF_5') | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_412])).
% 4.56/1.87  tff(c_417, plain, (![B_239]: (r2_hidden('#skF_3'('#skF_5', B_239), '#skF_6') | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_239))) | ~r1_waybel_0('#skF_5', '#skF_2'('#skF_5', B_239), '#skF_6') | ~l1_waybel_0('#skF_2'('#skF_5', B_239), '#skF_5') | ~v3_yellow_6('#skF_2'('#skF_5', B_239), '#skF_5') | ~v7_waybel_0('#skF_2'('#skF_5', B_239)) | ~v4_orders_2('#skF_2'('#skF_5', B_239)) | v2_struct_0('#skF_2'('#skF_5', B_239)) | ~m1_subset_1('#skF_3'('#skF_5', B_239), u1_struct_0('#skF_5')) | v4_pre_topc(B_239, '#skF_5') | ~m1_subset_1(B_239, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_60, c_415])).
% 4.56/1.87  tff(c_421, plain, (![B_37]: (r2_hidden('#skF_3'('#skF_5', B_37), '#skF_6') | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_37))) | ~r1_waybel_0('#skF_5', '#skF_2'('#skF_5', B_37), '#skF_6') | ~l1_waybel_0('#skF_2'('#skF_5', B_37), '#skF_5') | ~v3_yellow_6('#skF_2'('#skF_5', B_37), '#skF_5') | ~v7_waybel_0('#skF_2'('#skF_5', B_37)) | ~v4_orders_2('#skF_2'('#skF_5', B_37)) | v2_struct_0('#skF_2'('#skF_5', B_37)) | v4_pre_topc(B_37, '#skF_5') | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_24, c_417])).
% 4.56/1.87  tff(c_424, plain, (![B_37]: (r2_hidden('#skF_3'('#skF_5', B_37), '#skF_6') | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_37))) | ~r1_waybel_0('#skF_5', '#skF_2'('#skF_5', B_37), '#skF_6') | ~l1_waybel_0('#skF_2'('#skF_5', B_37), '#skF_5') | ~v3_yellow_6('#skF_2'('#skF_5', B_37), '#skF_5') | ~v7_waybel_0('#skF_2'('#skF_5', B_37)) | ~v4_orders_2('#skF_2'('#skF_5', B_37)) | v2_struct_0('#skF_2'('#skF_5', B_37)) | v4_pre_topc(B_37, '#skF_5') | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_421])).
% 4.56/1.87  tff(c_426, plain, (![B_240]: (r2_hidden('#skF_3'('#skF_5', B_240), '#skF_6') | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_240))) | ~r1_waybel_0('#skF_5', '#skF_2'('#skF_5', B_240), '#skF_6') | ~l1_waybel_0('#skF_2'('#skF_5', B_240), '#skF_5') | ~v3_yellow_6('#skF_2'('#skF_5', B_240), '#skF_5') | ~v7_waybel_0('#skF_2'('#skF_5', B_240)) | ~v4_orders_2('#skF_2'('#skF_5', B_240)) | v2_struct_0('#skF_2'('#skF_5', B_240)) | v4_pre_topc(B_240, '#skF_5') | ~m1_subset_1(B_240, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_60, c_424])).
% 4.56/1.87  tff(c_429, plain, (r2_hidden('#skF_3'('#skF_5', '#skF_6'), '#skF_6') | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', '#skF_3'('#skF_5', '#skF_6'))) | ~r1_waybel_0('#skF_5', '#skF_2'('#skF_5', '#skF_6'), '#skF_6') | ~l1_waybel_0('#skF_2'('#skF_5', '#skF_6'), '#skF_5') | ~v3_yellow_6('#skF_2'('#skF_5', '#skF_6'), '#skF_5') | ~v7_waybel_0('#skF_2'('#skF_5', '#skF_6')) | ~v4_orders_2('#skF_2'('#skF_5', '#skF_6')) | v2_struct_0('#skF_2'('#skF_5', '#skF_6')) | v4_pre_topc('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_54, c_426])).
% 4.56/1.87  tff(c_432, plain, (r2_hidden('#skF_3'('#skF_5', '#skF_6'), '#skF_6') | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', '#skF_3'('#skF_5', '#skF_6'))) | v2_struct_0('#skF_2'('#skF_5', '#skF_6')) | v4_pre_topc('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_117, c_125, c_140, c_133, c_149, c_429])).
% 4.56/1.87  tff(c_433, plain, (r2_hidden('#skF_3'('#skF_5', '#skF_6'), '#skF_6') | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', '#skF_3'('#skF_5', '#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_101, c_109, c_432])).
% 4.56/1.87  tff(c_438, plain, (v1_xboole_0('#skF_4'('#skF_5', '#skF_6', '#skF_3'('#skF_5', '#skF_6')))), inference(splitLeft, [status(thm)], [c_433])).
% 4.56/1.87  tff(c_52, plain, (![A_48, B_60, C_66]: (~v1_xboole_0('#skF_4'(A_48, B_60, C_66)) | ~r2_hidden(C_66, k2_pre_topc(A_48, B_60)) | ~m1_subset_1(C_66, u1_struct_0(A_48)) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_48))) | ~l1_pre_topc(A_48) | ~v2_pre_topc(A_48) | v2_struct_0(A_48))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.56/1.87  tff(c_307, plain, (![A_193, B_195, B_194]: (~v1_xboole_0('#skF_4'(A_193, B_195, '#skF_3'(A_193, B_194))) | ~r1_waybel_0(A_193, '#skF_2'(A_193, B_194), B_195) | ~l1_waybel_0('#skF_2'(A_193, B_194), A_193) | ~v3_yellow_6('#skF_2'(A_193, B_194), A_193) | ~v7_waybel_0('#skF_2'(A_193, B_194)) | ~v4_orders_2('#skF_2'(A_193, B_194)) | v2_struct_0('#skF_2'(A_193, B_194)) | ~m1_subset_1('#skF_3'(A_193, B_194), u1_struct_0(A_193)) | ~m1_subset_1(B_195, k1_zfmisc_1(u1_struct_0(A_193))) | v4_pre_topc(B_194, A_193) | ~m1_subset_1(B_194, k1_zfmisc_1(u1_struct_0(A_193))) | ~l1_pre_topc(A_193) | ~v2_pre_topc(A_193) | v2_struct_0(A_193))), inference(resolution, [status(thm)], [c_286, c_52])).
% 4.56/1.87  tff(c_440, plain, (~r1_waybel_0('#skF_5', '#skF_2'('#skF_5', '#skF_6'), '#skF_6') | ~l1_waybel_0('#skF_2'('#skF_5', '#skF_6'), '#skF_5') | ~v3_yellow_6('#skF_2'('#skF_5', '#skF_6'), '#skF_5') | ~v7_waybel_0('#skF_2'('#skF_5', '#skF_6')) | ~v4_orders_2('#skF_2'('#skF_5', '#skF_6')) | v2_struct_0('#skF_2'('#skF_5', '#skF_6')) | ~m1_subset_1('#skF_3'('#skF_5', '#skF_6'), u1_struct_0('#skF_5')) | v4_pre_topc('#skF_6', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_438, c_307])).
% 4.56/1.87  tff(c_443, plain, (v2_struct_0('#skF_2'('#skF_5', '#skF_6')) | ~m1_subset_1('#skF_3'('#skF_5', '#skF_6'), u1_struct_0('#skF_5')) | v4_pre_topc('#skF_6', '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_117, c_125, c_140, c_133, c_149, c_440])).
% 4.56/1.87  tff(c_444, plain, (~m1_subset_1('#skF_3'('#skF_5', '#skF_6'), u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_60, c_101, c_109, c_443])).
% 4.56/1.87  tff(c_447, plain, (v4_pre_topc('#skF_6', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_24, c_444])).
% 4.56/1.87  tff(c_450, plain, (v4_pre_topc('#skF_6', '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_447])).
% 4.56/1.87  tff(c_452, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_101, c_450])).
% 4.56/1.87  tff(c_453, plain, (r2_hidden('#skF_3'('#skF_5', '#skF_6'), '#skF_6')), inference(splitRight, [status(thm)], [c_433])).
% 4.56/1.87  tff(c_20, plain, (![A_23, B_37]: (~r2_hidden('#skF_3'(A_23, B_37), B_37) | v4_pre_topc(B_37, A_23) | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0(A_23))) | ~l1_pre_topc(A_23) | ~v2_pre_topc(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.56/1.87  tff(c_456, plain, (v4_pre_topc('#skF_6', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_453, c_20])).
% 4.56/1.87  tff(c_459, plain, (v4_pre_topc('#skF_6', '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_456])).
% 4.56/1.87  tff(c_461, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_101, c_459])).
% 4.56/1.87  tff(c_463, plain, (v4_pre_topc('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_78])).
% 4.56/1.87  tff(c_66, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~v4_pre_topc('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_154])).
% 4.56/1.87  tff(c_469, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_463, c_66])).
% 4.56/1.87  tff(c_68, plain, (r2_hidden('#skF_6', '#skF_7') | ~v4_pre_topc('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_154])).
% 4.56/1.87  tff(c_467, plain, (r2_hidden('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_463, c_68])).
% 4.56/1.87  tff(c_462, plain, (~v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_78])).
% 4.56/1.87  tff(c_76, plain, (v2_waybel_0('#skF_7', k3_yellow_1(k2_struct_0('#skF_5'))) | ~v4_pre_topc('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_154])).
% 4.56/1.87  tff(c_477, plain, (v2_waybel_0('#skF_7', k3_yellow_1(k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_463, c_76])).
% 4.56/1.87  tff(c_74, plain, (v13_waybel_0('#skF_7', k3_yellow_1(k2_struct_0('#skF_5'))) | ~v4_pre_topc('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_154])).
% 4.56/1.87  tff(c_475, plain, (v13_waybel_0('#skF_7', k3_yellow_1(k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_463, c_74])).
% 4.56/1.87  tff(c_72, plain, (v3_waybel_7('#skF_7', k3_yellow_1(k2_struct_0('#skF_5'))) | ~v4_pre_topc('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_154])).
% 4.56/1.87  tff(c_473, plain, (v3_waybel_7('#skF_7', k3_yellow_1(k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_463, c_72])).
% 4.56/1.87  tff(c_70, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))) | ~v4_pre_topc('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_154])).
% 4.56/1.87  tff(c_479, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))))), inference(demodulation, [status(thm), theory('equality')], [c_463, c_70])).
% 4.56/1.87  tff(c_64, plain, (r2_waybel_7('#skF_5', '#skF_7', '#skF_8') | ~v4_pre_topc('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_154])).
% 4.56/1.87  tff(c_471, plain, (r2_waybel_7('#skF_5', '#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_463, c_64])).
% 4.56/1.87  tff(c_649, plain, (![C_325, A_326, B_327, D_328]: (r2_hidden(C_325, k2_pre_topc(A_326, B_327)) | ~r2_waybel_7(A_326, D_328, C_325) | ~r2_hidden(B_327, D_328) | ~m1_subset_1(D_328, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_326))))) | ~v3_waybel_7(D_328, k3_yellow_1(k2_struct_0(A_326))) | ~v13_waybel_0(D_328, k3_yellow_1(k2_struct_0(A_326))) | ~v2_waybel_0(D_328, k3_yellow_1(k2_struct_0(A_326))) | v1_xboole_0(D_328) | ~m1_subset_1(C_325, u1_struct_0(A_326)) | ~m1_subset_1(B_327, k1_zfmisc_1(u1_struct_0(A_326))) | ~l1_pre_topc(A_326) | ~v2_pre_topc(A_326) | v2_struct_0(A_326))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.56/1.87  tff(c_653, plain, (![B_327]: (r2_hidden('#skF_8', k2_pre_topc('#skF_5', B_327)) | ~r2_hidden(B_327, '#skF_7') | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))) | ~v3_waybel_7('#skF_7', k3_yellow_1(k2_struct_0('#skF_5'))) | ~v13_waybel_0('#skF_7', k3_yellow_1(k2_struct_0('#skF_5'))) | ~v2_waybel_0('#skF_7', k3_yellow_1(k2_struct_0('#skF_5'))) | v1_xboole_0('#skF_7') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1(B_327, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_471, c_649])).
% 4.56/1.87  tff(c_660, plain, (![B_327]: (r2_hidden('#skF_8', k2_pre_topc('#skF_5', B_327)) | ~r2_hidden(B_327, '#skF_7') | v1_xboole_0('#skF_7') | ~m1_subset_1(B_327, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_469, c_477, c_475, c_473, c_479, c_653])).
% 4.56/1.87  tff(c_662, plain, (![B_329]: (r2_hidden('#skF_8', k2_pre_topc('#skF_5', B_329)) | ~r2_hidden(B_329, '#skF_7') | ~m1_subset_1(B_329, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_60, c_462, c_660])).
% 4.56/1.87  tff(c_665, plain, (r2_hidden('#skF_8', k2_pre_topc('#skF_5', '#skF_6')) | ~r2_hidden('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_54, c_662])).
% 4.56/1.87  tff(c_668, plain, (r2_hidden('#skF_8', k2_pre_topc('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_467, c_665])).
% 4.56/1.87  tff(c_16, plain, (![A_1, B_13, C_19]: (~v2_struct_0('#skF_1'(A_1, B_13, C_19)) | ~r2_hidden(C_19, k2_pre_topc(A_1, B_13)) | ~m1_subset_1(C_19, u1_struct_0(A_1)) | ~m1_subset_1(B_13, k1_zfmisc_1(u1_struct_0(A_1))) | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.56/1.87  tff(c_678, plain, (~v2_struct_0('#skF_1'('#skF_5', '#skF_6', '#skF_8')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_668, c_16])).
% 4.56/1.87  tff(c_699, plain, (~v2_struct_0('#skF_1'('#skF_5', '#skF_6', '#skF_8')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_469, c_678])).
% 4.56/1.87  tff(c_700, plain, (~v2_struct_0('#skF_1'('#skF_5', '#skF_6', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_60, c_699])).
% 4.56/1.87  tff(c_62, plain, (~r2_hidden('#skF_8', '#skF_6') | ~v4_pre_topc('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_154])).
% 4.56/1.87  tff(c_465, plain, (~r2_hidden('#skF_8', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_463, c_62])).
% 4.56/1.87  tff(c_14, plain, (![A_1, B_13, C_19]: (v4_orders_2('#skF_1'(A_1, B_13, C_19)) | ~r2_hidden(C_19, k2_pre_topc(A_1, B_13)) | ~m1_subset_1(C_19, u1_struct_0(A_1)) | ~m1_subset_1(B_13, k1_zfmisc_1(u1_struct_0(A_1))) | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.56/1.87  tff(c_676, plain, (v4_orders_2('#skF_1'('#skF_5', '#skF_6', '#skF_8')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_668, c_14])).
% 4.56/1.87  tff(c_695, plain, (v4_orders_2('#skF_1'('#skF_5', '#skF_6', '#skF_8')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_469, c_676])).
% 4.56/1.87  tff(c_696, plain, (v4_orders_2('#skF_1'('#skF_5', '#skF_6', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_60, c_695])).
% 4.56/1.87  tff(c_12, plain, (![A_1, B_13, C_19]: (v7_waybel_0('#skF_1'(A_1, B_13, C_19)) | ~r2_hidden(C_19, k2_pre_topc(A_1, B_13)) | ~m1_subset_1(C_19, u1_struct_0(A_1)) | ~m1_subset_1(B_13, k1_zfmisc_1(u1_struct_0(A_1))) | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.56/1.87  tff(c_680, plain, (v7_waybel_0('#skF_1'('#skF_5', '#skF_6', '#skF_8')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_668, c_12])).
% 4.56/1.87  tff(c_703, plain, (v7_waybel_0('#skF_1'('#skF_5', '#skF_6', '#skF_8')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_469, c_680])).
% 4.56/1.87  tff(c_704, plain, (v7_waybel_0('#skF_1'('#skF_5', '#skF_6', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_60, c_703])).
% 4.56/1.87  tff(c_8, plain, (![A_1, B_13, C_19]: (l1_waybel_0('#skF_1'(A_1, B_13, C_19), A_1) | ~r2_hidden(C_19, k2_pre_topc(A_1, B_13)) | ~m1_subset_1(C_19, u1_struct_0(A_1)) | ~m1_subset_1(B_13, k1_zfmisc_1(u1_struct_0(A_1))) | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.56/1.87  tff(c_672, plain, (l1_waybel_0('#skF_1'('#skF_5', '#skF_6', '#skF_8'), '#skF_5') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_668, c_8])).
% 4.56/1.87  tff(c_687, plain, (l1_waybel_0('#skF_1'('#skF_5', '#skF_6', '#skF_8'), '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_469, c_672])).
% 4.56/1.87  tff(c_688, plain, (l1_waybel_0('#skF_1'('#skF_5', '#skF_6', '#skF_8'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_60, c_687])).
% 4.56/1.87  tff(c_556, plain, (![A_278, B_279, C_280]: (v3_yellow_6('#skF_1'(A_278, B_279, C_280), A_278) | ~r2_hidden(C_280, k2_pre_topc(A_278, B_279)) | ~m1_subset_1(C_280, u1_struct_0(A_278)) | ~m1_subset_1(B_279, k1_zfmisc_1(u1_struct_0(A_278))) | ~l1_pre_topc(A_278) | ~v2_pre_topc(A_278) | v2_struct_0(A_278))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.56/1.87  tff(c_560, plain, (![C_280]: (v3_yellow_6('#skF_1'('#skF_5', '#skF_6', C_280), '#skF_5') | ~r2_hidden(C_280, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_280, u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_54, c_556])).
% 4.56/1.87  tff(c_564, plain, (![C_280]: (v3_yellow_6('#skF_1'('#skF_5', '#skF_6', C_280), '#skF_5') | ~r2_hidden(C_280, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_280, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_560])).
% 4.56/1.87  tff(c_565, plain, (![C_280]: (v3_yellow_6('#skF_1'('#skF_5', '#skF_6', C_280), '#skF_5') | ~r2_hidden(C_280, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_280, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_60, c_564])).
% 4.56/1.87  tff(c_579, plain, (![A_289, B_290, C_291]: (r1_waybel_0(A_289, '#skF_1'(A_289, B_290, C_291), B_290) | ~r2_hidden(C_291, k2_pre_topc(A_289, B_290)) | ~m1_subset_1(C_291, u1_struct_0(A_289)) | ~m1_subset_1(B_290, k1_zfmisc_1(u1_struct_0(A_289))) | ~l1_pre_topc(A_289) | ~v2_pre_topc(A_289) | v2_struct_0(A_289))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.56/1.87  tff(c_583, plain, (![C_291]: (r1_waybel_0('#skF_5', '#skF_1'('#skF_5', '#skF_6', C_291), '#skF_6') | ~r2_hidden(C_291, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_291, u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_54, c_579])).
% 4.56/1.87  tff(c_587, plain, (![C_291]: (r1_waybel_0('#skF_5', '#skF_1'('#skF_5', '#skF_6', C_291), '#skF_6') | ~r2_hidden(C_291, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_291, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_583])).
% 4.56/1.87  tff(c_588, plain, (![C_291]: (r1_waybel_0('#skF_5', '#skF_1'('#skF_5', '#skF_6', C_291), '#skF_6') | ~r2_hidden(C_291, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_291, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_60, c_587])).
% 4.56/1.87  tff(c_4, plain, (![C_19, A_1, B_13]: (r2_hidden(C_19, k10_yellow_6(A_1, '#skF_1'(A_1, B_13, C_19))) | ~r2_hidden(C_19, k2_pre_topc(A_1, B_13)) | ~m1_subset_1(C_19, u1_struct_0(A_1)) | ~m1_subset_1(B_13, k1_zfmisc_1(u1_struct_0(A_1))) | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.56/1.87  tff(c_634, plain, (![D_312, B_313, A_314, C_315]: (r2_hidden(D_312, B_313) | ~r2_hidden(D_312, k10_yellow_6(A_314, C_315)) | ~m1_subset_1(D_312, u1_struct_0(A_314)) | ~r1_waybel_0(A_314, C_315, B_313) | ~l1_waybel_0(C_315, A_314) | ~v3_yellow_6(C_315, A_314) | ~v7_waybel_0(C_315) | ~v4_orders_2(C_315) | v2_struct_0(C_315) | ~v4_pre_topc(B_313, A_314) | ~m1_subset_1(B_313, k1_zfmisc_1(u1_struct_0(A_314))) | ~l1_pre_topc(A_314) | ~v2_pre_topc(A_314) | v2_struct_0(A_314))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.56/1.87  tff(c_837, plain, (![C_392, B_393, A_394, B_395]: (r2_hidden(C_392, B_393) | ~r1_waybel_0(A_394, '#skF_1'(A_394, B_395, C_392), B_393) | ~l1_waybel_0('#skF_1'(A_394, B_395, C_392), A_394) | ~v3_yellow_6('#skF_1'(A_394, B_395, C_392), A_394) | ~v7_waybel_0('#skF_1'(A_394, B_395, C_392)) | ~v4_orders_2('#skF_1'(A_394, B_395, C_392)) | v2_struct_0('#skF_1'(A_394, B_395, C_392)) | ~v4_pre_topc(B_393, A_394) | ~m1_subset_1(B_393, k1_zfmisc_1(u1_struct_0(A_394))) | ~r2_hidden(C_392, k2_pre_topc(A_394, B_395)) | ~m1_subset_1(C_392, u1_struct_0(A_394)) | ~m1_subset_1(B_395, k1_zfmisc_1(u1_struct_0(A_394))) | ~l1_pre_topc(A_394) | ~v2_pre_topc(A_394) | v2_struct_0(A_394))), inference(resolution, [status(thm)], [c_4, c_634])).
% 4.56/1.87  tff(c_839, plain, (![C_291]: (r2_hidden(C_291, '#skF_6') | ~l1_waybel_0('#skF_1'('#skF_5', '#skF_6', C_291), '#skF_5') | ~v3_yellow_6('#skF_1'('#skF_5', '#skF_6', C_291), '#skF_5') | ~v7_waybel_0('#skF_1'('#skF_5', '#skF_6', C_291)) | ~v4_orders_2('#skF_1'('#skF_5', '#skF_6', C_291)) | v2_struct_0('#skF_1'('#skF_5', '#skF_6', C_291)) | ~v4_pre_topc('#skF_6', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~r2_hidden(C_291, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_291, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_588, c_837])).
% 4.56/1.87  tff(c_842, plain, (![C_291]: (r2_hidden(C_291, '#skF_6') | ~l1_waybel_0('#skF_1'('#skF_5', '#skF_6', C_291), '#skF_5') | ~v3_yellow_6('#skF_1'('#skF_5', '#skF_6', C_291), '#skF_5') | ~v7_waybel_0('#skF_1'('#skF_5', '#skF_6', C_291)) | ~v4_orders_2('#skF_1'('#skF_5', '#skF_6', C_291)) | v2_struct_0('#skF_1'('#skF_5', '#skF_6', C_291)) | v2_struct_0('#skF_5') | ~r2_hidden(C_291, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_291, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_463, c_839])).
% 4.56/1.87  tff(c_844, plain, (![C_396]: (r2_hidden(C_396, '#skF_6') | ~l1_waybel_0('#skF_1'('#skF_5', '#skF_6', C_396), '#skF_5') | ~v3_yellow_6('#skF_1'('#skF_5', '#skF_6', C_396), '#skF_5') | ~v7_waybel_0('#skF_1'('#skF_5', '#skF_6', C_396)) | ~v4_orders_2('#skF_1'('#skF_5', '#skF_6', C_396)) | v2_struct_0('#skF_1'('#skF_5', '#skF_6', C_396)) | ~r2_hidden(C_396, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_396, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_60, c_842])).
% 4.56/1.87  tff(c_849, plain, (![C_397]: (r2_hidden(C_397, '#skF_6') | ~l1_waybel_0('#skF_1'('#skF_5', '#skF_6', C_397), '#skF_5') | ~v7_waybel_0('#skF_1'('#skF_5', '#skF_6', C_397)) | ~v4_orders_2('#skF_1'('#skF_5', '#skF_6', C_397)) | v2_struct_0('#skF_1'('#skF_5', '#skF_6', C_397)) | ~r2_hidden(C_397, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_397, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_565, c_844])).
% 4.56/1.87  tff(c_856, plain, (r2_hidden('#skF_8', '#skF_6') | ~l1_waybel_0('#skF_1'('#skF_5', '#skF_6', '#skF_8'), '#skF_5') | ~v7_waybel_0('#skF_1'('#skF_5', '#skF_6', '#skF_8')) | ~v4_orders_2('#skF_1'('#skF_5', '#skF_6', '#skF_8')) | v2_struct_0('#skF_1'('#skF_5', '#skF_6', '#skF_8')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_668, c_849])).
% 4.56/1.87  tff(c_863, plain, (r2_hidden('#skF_8', '#skF_6') | v2_struct_0('#skF_1'('#skF_5', '#skF_6', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_469, c_696, c_704, c_688, c_856])).
% 4.56/1.87  tff(c_865, plain, $false, inference(negUnitSimplification, [status(thm)], [c_700, c_465, c_863])).
% 4.56/1.87  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.56/1.87  
% 4.56/1.87  Inference rules
% 4.56/1.87  ----------------------
% 4.56/1.87  #Ref     : 0
% 4.56/1.87  #Sup     : 131
% 4.56/1.87  #Fact    : 0
% 4.56/1.87  #Define  : 0
% 4.56/1.87  #Split   : 5
% 4.56/1.87  #Chain   : 0
% 4.56/1.87  #Close   : 0
% 4.56/1.87  
% 4.56/1.87  Ordering : KBO
% 4.56/1.87  
% 4.56/1.87  Simplification rules
% 4.56/1.87  ----------------------
% 4.56/1.87  #Subsume      : 44
% 4.56/1.87  #Demod        : 194
% 4.56/1.87  #Tautology    : 24
% 4.56/1.87  #SimpNegUnit  : 56
% 4.56/1.87  #BackRed      : 0
% 4.56/1.87  
% 4.56/1.87  #Partial instantiations: 0
% 4.56/1.87  #Strategies tried      : 1
% 4.56/1.87  
% 4.56/1.87  Timing (in seconds)
% 4.56/1.87  ----------------------
% 4.56/1.87  Preprocessing        : 0.37
% 4.56/1.87  Parsing              : 0.17
% 4.56/1.87  CNF conversion       : 0.05
% 4.56/1.87  Main loop            : 0.62
% 4.56/1.87  Inferencing          : 0.24
% 4.56/1.87  Reduction            : 0.18
% 4.56/1.87  Demodulation         : 0.12
% 4.56/1.87  BG Simplification    : 0.04
% 4.56/1.87  Subsumption          : 0.13
% 4.56/1.87  Abstraction          : 0.02
% 4.56/1.87  MUC search           : 0.00
% 4.56/1.87  Cooper               : 0.00
% 4.56/1.87  Total                : 1.06
% 4.56/1.87  Index Insertion      : 0.00
% 4.56/1.87  Index Deletion       : 0.00
% 4.56/1.87  Index Matching       : 0.00
% 4.56/1.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
