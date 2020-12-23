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
% DateTime   : Thu Dec  3 10:31:39 EST 2020

% Result     : Theorem 3.67s
% Output     : CNFRefutation 4.08s
% Verified   : 
% Statistics : Number of formulae       :  177 (1017 expanded)
%              Number of leaves         :   36 ( 382 expanded)
%              Depth                    :   36
%              Number of atoms          :  802 (6795 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_waybel_9 > r2_waybel_7 > r1_waybel_0 > v4_pre_topc > v3_waybel_7 > v2_waybel_0 > v13_waybel_0 > r2_hidden > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k2_pre_topc > #nlpp > u1_struct_0 > k3_yellow_1 > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2

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

tff(r3_waybel_9,type,(
    r3_waybel_9: ( $i * $i * $i ) > $o )).

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

tff(f_150,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_yellow19)).

tff(f_85,axiom,(
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
                  & l1_waybel_0(C,A) )
               => ( r1_waybel_0(A,C,B)
                 => ! [D] :
                      ( m1_subset_1(D,u1_struct_0(A))
                     => ( r3_waybel_9(A,C,D)
                       => r2_hidden(D,B) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_yellow19)).

tff(f_54,axiom,(
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
                    & l1_waybel_0(D,A)
                    & r1_waybel_0(A,D,B)
                    & r3_waybel_9(A,D,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_yellow19)).

tff(f_116,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_yellow19)).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_54,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_52,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_50,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_74,plain,
    ( ~ v1_xboole_0('#skF_7')
    | ~ v4_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_97,plain,(
    ~ v4_pre_topc('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_22,plain,(
    ! [A_23,B_37] :
      ( m1_subset_1('#skF_3'(A_23,B_37),u1_struct_0(A_23))
      | v4_pre_topc(B_37,A_23)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_98,plain,(
    ! [A_93,B_94] :
      ( ~ v2_struct_0('#skF_2'(A_93,B_94))
      | v4_pre_topc(B_94,A_93)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ l1_pre_topc(A_93)
      | ~ v2_pre_topc(A_93)
      | v2_struct_0(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_101,plain,
    ( ~ v2_struct_0('#skF_2'('#skF_5','#skF_6'))
    | v4_pre_topc('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_98])).

tff(c_104,plain,
    ( ~ v2_struct_0('#skF_2'('#skF_5','#skF_6'))
    | v4_pre_topc('#skF_6','#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_101])).

tff(c_105,plain,(
    ~ v2_struct_0('#skF_2'('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_97,c_104])).

tff(c_106,plain,(
    ! [A_95,B_96] :
      ( v4_orders_2('#skF_2'(A_95,B_96))
      | v4_pre_topc(B_96,A_95)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ l1_pre_topc(A_95)
      | ~ v2_pre_topc(A_95)
      | v2_struct_0(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_109,plain,
    ( v4_orders_2('#skF_2'('#skF_5','#skF_6'))
    | v4_pre_topc('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_106])).

tff(c_112,plain,
    ( v4_orders_2('#skF_2'('#skF_5','#skF_6'))
    | v4_pre_topc('#skF_6','#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_109])).

tff(c_113,plain,(
    v4_orders_2('#skF_2'('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_97,c_112])).

tff(c_114,plain,(
    ! [A_97,B_98] :
      ( v7_waybel_0('#skF_2'(A_97,B_98))
      | v4_pre_topc(B_98,A_97)
      | ~ m1_subset_1(B_98,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ l1_pre_topc(A_97)
      | ~ v2_pre_topc(A_97)
      | v2_struct_0(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_117,plain,
    ( v7_waybel_0('#skF_2'('#skF_5','#skF_6'))
    | v4_pre_topc('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_114])).

tff(c_120,plain,
    ( v7_waybel_0('#skF_2'('#skF_5','#skF_6'))
    | v4_pre_topc('#skF_6','#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_117])).

tff(c_121,plain,(
    v7_waybel_0('#skF_2'('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_97,c_120])).

tff(c_123,plain,(
    ! [A_99,B_100] :
      ( l1_waybel_0('#skF_2'(A_99,B_100),A_99)
      | v4_pre_topc(B_100,A_99)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ l1_pre_topc(A_99)
      | ~ v2_pre_topc(A_99)
      | v2_struct_0(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_125,plain,
    ( l1_waybel_0('#skF_2'('#skF_5','#skF_6'),'#skF_5')
    | v4_pre_topc('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_123])).

tff(c_128,plain,
    ( l1_waybel_0('#skF_2'('#skF_5','#skF_6'),'#skF_5')
    | v4_pre_topc('#skF_6','#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_125])).

tff(c_129,plain,(
    l1_waybel_0('#skF_2'('#skF_5','#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_97,c_128])).

tff(c_132,plain,(
    ! [A_105,B_106] :
      ( r1_waybel_0(A_105,'#skF_2'(A_105,B_106),B_106)
      | v4_pre_topc(B_106,A_105)
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ l1_pre_topc(A_105)
      | ~ v2_pre_topc(A_105)
      | v2_struct_0(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_134,plain,
    ( r1_waybel_0('#skF_5','#skF_2'('#skF_5','#skF_6'),'#skF_6')
    | v4_pre_topc('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_132])).

tff(c_137,plain,
    ( r1_waybel_0('#skF_5','#skF_2'('#skF_5','#skF_6'),'#skF_6')
    | v4_pre_topc('#skF_6','#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_134])).

tff(c_138,plain,(
    r1_waybel_0('#skF_5','#skF_2'('#skF_5','#skF_6'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_97,c_137])).

tff(c_20,plain,(
    ! [A_23,B_37] :
      ( r3_waybel_9(A_23,'#skF_2'(A_23,B_37),'#skF_3'(A_23,B_37))
      | v4_pre_topc(B_37,A_23)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_207,plain,(
    ! [C_153,A_154,B_155,D_156] :
      ( r2_hidden(C_153,k2_pre_topc(A_154,B_155))
      | ~ r3_waybel_9(A_154,D_156,C_153)
      | ~ r1_waybel_0(A_154,D_156,B_155)
      | ~ l1_waybel_0(D_156,A_154)
      | ~ v7_waybel_0(D_156)
      | ~ v4_orders_2(D_156)
      | v2_struct_0(D_156)
      | ~ m1_subset_1(C_153,u1_struct_0(A_154))
      | ~ m1_subset_1(B_155,k1_zfmisc_1(u1_struct_0(A_154)))
      | ~ l1_pre_topc(A_154)
      | ~ v2_pre_topc(A_154)
      | v2_struct_0(A_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_216,plain,(
    ! [A_23,B_37,B_155] :
      ( r2_hidden('#skF_3'(A_23,B_37),k2_pre_topc(A_23,B_155))
      | ~ r1_waybel_0(A_23,'#skF_2'(A_23,B_37),B_155)
      | ~ l1_waybel_0('#skF_2'(A_23,B_37),A_23)
      | ~ v7_waybel_0('#skF_2'(A_23,B_37))
      | ~ v4_orders_2('#skF_2'(A_23,B_37))
      | v2_struct_0('#skF_2'(A_23,B_37))
      | ~ m1_subset_1('#skF_3'(A_23,B_37),u1_struct_0(A_23))
      | ~ m1_subset_1(B_155,k1_zfmisc_1(u1_struct_0(A_23)))
      | v4_pre_topc(B_37,A_23)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23)
      | v2_struct_0(A_23) ) ),
    inference(resolution,[status(thm)],[c_20,c_207])).

tff(c_288,plain,(
    ! [A_188,B_189,B_190] :
      ( r2_hidden('#skF_3'(A_188,B_189),k2_pre_topc(A_188,B_190))
      | ~ r1_waybel_0(A_188,'#skF_2'(A_188,B_189),B_190)
      | ~ l1_waybel_0('#skF_2'(A_188,B_189),A_188)
      | ~ v7_waybel_0('#skF_2'(A_188,B_189))
      | ~ v4_orders_2('#skF_2'(A_188,B_189))
      | v2_struct_0('#skF_2'(A_188,B_189))
      | ~ m1_subset_1('#skF_3'(A_188,B_189),u1_struct_0(A_188))
      | ~ m1_subset_1(B_190,k1_zfmisc_1(u1_struct_0(A_188)))
      | v4_pre_topc(B_189,A_188)
      | ~ m1_subset_1(B_189,k1_zfmisc_1(u1_struct_0(A_188)))
      | ~ l1_pre_topc(A_188)
      | ~ v2_pre_topc(A_188)
      | v2_struct_0(A_188) ) ),
    inference(resolution,[status(thm)],[c_20,c_207])).

tff(c_38,plain,(
    ! [B_60,A_48,C_66] :
      ( r2_hidden(B_60,'#skF_4'(A_48,B_60,C_66))
      | ~ r2_hidden(C_66,k2_pre_topc(A_48,B_60))
      | ~ m1_subset_1(C_66,u1_struct_0(A_48))
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ l1_pre_topc(A_48)
      | ~ v2_pre_topc(A_48)
      | v2_struct_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_372,plain,(
    ! [B_220,A_221,B_222] :
      ( r2_hidden(B_220,'#skF_4'(A_221,B_220,'#skF_3'(A_221,B_222)))
      | ~ r1_waybel_0(A_221,'#skF_2'(A_221,B_222),B_220)
      | ~ l1_waybel_0('#skF_2'(A_221,B_222),A_221)
      | ~ v7_waybel_0('#skF_2'(A_221,B_222))
      | ~ v4_orders_2('#skF_2'(A_221,B_222))
      | v2_struct_0('#skF_2'(A_221,B_222))
      | ~ m1_subset_1('#skF_3'(A_221,B_222),u1_struct_0(A_221))
      | ~ m1_subset_1(B_220,k1_zfmisc_1(u1_struct_0(A_221)))
      | v4_pre_topc(B_222,A_221)
      | ~ m1_subset_1(B_222,k1_zfmisc_1(u1_struct_0(A_221)))
      | ~ l1_pre_topc(A_221)
      | ~ v2_pre_topc(A_221)
      | v2_struct_0(A_221) ) ),
    inference(resolution,[status(thm)],[c_288,c_38])).

tff(c_44,plain,(
    ! [A_48,B_60,C_66] :
      ( v13_waybel_0('#skF_4'(A_48,B_60,C_66),k3_yellow_1(k2_struct_0(A_48)))
      | ~ r2_hidden(C_66,k2_pre_topc(A_48,B_60))
      | ~ m1_subset_1(C_66,u1_struct_0(A_48))
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ l1_pre_topc(A_48)
      | ~ v2_pre_topc(A_48)
      | v2_struct_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_46,plain,(
    ! [A_48,B_60,C_66] :
      ( v2_waybel_0('#skF_4'(A_48,B_60,C_66),k3_yellow_1(k2_struct_0(A_48)))
      | ~ r2_hidden(C_66,k2_pre_topc(A_48,B_60))
      | ~ m1_subset_1(C_66,u1_struct_0(A_48))
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ l1_pre_topc(A_48)
      | ~ v2_pre_topc(A_48)
      | v2_struct_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_42,plain,(
    ! [A_48,B_60,C_66] :
      ( v3_waybel_7('#skF_4'(A_48,B_60,C_66),k3_yellow_1(k2_struct_0(A_48)))
      | ~ r2_hidden(C_66,k2_pre_topc(A_48,B_60))
      | ~ m1_subset_1(C_66,u1_struct_0(A_48))
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ l1_pre_topc(A_48)
      | ~ v2_pre_topc(A_48)
      | v2_struct_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_40,plain,(
    ! [A_48,B_60,C_66] :
      ( m1_subset_1('#skF_4'(A_48,B_60,C_66),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_48)))))
      | ~ r2_hidden(C_66,k2_pre_topc(A_48,B_60))
      | ~ m1_subset_1(C_66,u1_struct_0(A_48))
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ l1_pre_topc(A_48)
      | ~ v2_pre_topc(A_48)
      | v2_struct_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_147,plain,(
    ! [A_127,B_128,C_129] :
      ( r2_waybel_7(A_127,'#skF_4'(A_127,B_128,C_129),C_129)
      | ~ r2_hidden(C_129,k2_pre_topc(A_127,B_128))
      | ~ m1_subset_1(C_129,u1_struct_0(A_127))
      | ~ m1_subset_1(B_128,k1_zfmisc_1(u1_struct_0(A_127)))
      | ~ l1_pre_topc(A_127)
      | ~ v2_pre_topc(A_127)
      | v2_struct_0(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_149,plain,(
    ! [C_129] :
      ( r2_waybel_7('#skF_5','#skF_4'('#skF_5','#skF_6',C_129),C_129)
      | ~ r2_hidden(C_129,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_129,u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_50,c_147])).

tff(c_152,plain,(
    ! [C_129] :
      ( r2_waybel_7('#skF_5','#skF_4'('#skF_5','#skF_6',C_129),C_129)
      | ~ r2_hidden(C_129,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_129,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_149])).

tff(c_153,plain,(
    ! [C_129] :
      ( r2_waybel_7('#skF_5','#skF_4'('#skF_5','#skF_6',C_129),C_129)
      | ~ r2_hidden(C_129,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_129,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_152])).

tff(c_96,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_156,plain,(
    ! [D_131,C_132] :
      ( r2_hidden(D_131,'#skF_6')
      | ~ r2_waybel_7('#skF_5',C_132,D_131)
      | ~ m1_subset_1(D_131,u1_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_6',C_132)
      | ~ m1_subset_1(C_132,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))))
      | ~ v3_waybel_7(C_132,k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v13_waybel_0(C_132,k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v2_waybel_0(C_132,k3_yellow_1(k2_struct_0('#skF_5')))
      | v1_xboole_0(C_132) ) ),
    inference(negUnitSimplification,[status(thm)],[c_97,c_96])).

tff(c_239,plain,(
    ! [C_165] :
      ( r2_hidden(C_165,'#skF_6')
      | ~ r2_hidden('#skF_6','#skF_4'('#skF_5','#skF_6',C_165))
      | ~ m1_subset_1('#skF_4'('#skF_5','#skF_6',C_165),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))))
      | ~ v3_waybel_7('#skF_4'('#skF_5','#skF_6',C_165),k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v13_waybel_0('#skF_4'('#skF_5','#skF_6',C_165),k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v2_waybel_0('#skF_4'('#skF_5','#skF_6',C_165),k3_yellow_1(k2_struct_0('#skF_5')))
      | v1_xboole_0('#skF_4'('#skF_5','#skF_6',C_165))
      | ~ r2_hidden(C_165,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_165,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_153,c_156])).

tff(c_243,plain,(
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
    inference(resolution,[status(thm)],[c_40,c_239])).

tff(c_246,plain,(
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
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_243])).

tff(c_248,plain,(
    ! [C_166] :
      ( r2_hidden(C_166,'#skF_6')
      | ~ r2_hidden('#skF_6','#skF_4'('#skF_5','#skF_6',C_166))
      | ~ v3_waybel_7('#skF_4'('#skF_5','#skF_6',C_166),k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v13_waybel_0('#skF_4'('#skF_5','#skF_6',C_166),k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v2_waybel_0('#skF_4'('#skF_5','#skF_6',C_166),k3_yellow_1(k2_struct_0('#skF_5')))
      | v1_xboole_0('#skF_4'('#skF_5','#skF_6',C_166))
      | ~ r2_hidden(C_166,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_166,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_246])).

tff(c_252,plain,(
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
    inference(resolution,[status(thm)],[c_42,c_248])).

tff(c_255,plain,(
    ! [C_66] :
      ( r2_hidden(C_66,'#skF_6')
      | ~ r2_hidden('#skF_6','#skF_4'('#skF_5','#skF_6',C_66))
      | ~ v13_waybel_0('#skF_4'('#skF_5','#skF_6',C_66),k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v2_waybel_0('#skF_4'('#skF_5','#skF_6',C_66),k3_yellow_1(k2_struct_0('#skF_5')))
      | v1_xboole_0('#skF_4'('#skF_5','#skF_6',C_66))
      | ~ r2_hidden(C_66,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_66,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_252])).

tff(c_257,plain,(
    ! [C_167] :
      ( r2_hidden(C_167,'#skF_6')
      | ~ r2_hidden('#skF_6','#skF_4'('#skF_5','#skF_6',C_167))
      | ~ v13_waybel_0('#skF_4'('#skF_5','#skF_6',C_167),k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v2_waybel_0('#skF_4'('#skF_5','#skF_6',C_167),k3_yellow_1(k2_struct_0('#skF_5')))
      | v1_xboole_0('#skF_4'('#skF_5','#skF_6',C_167))
      | ~ r2_hidden(C_167,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_167,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_255])).

tff(c_261,plain,(
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
    inference(resolution,[status(thm)],[c_46,c_257])).

tff(c_264,plain,(
    ! [C_66] :
      ( r2_hidden(C_66,'#skF_6')
      | ~ r2_hidden('#skF_6','#skF_4'('#skF_5','#skF_6',C_66))
      | ~ v13_waybel_0('#skF_4'('#skF_5','#skF_6',C_66),k3_yellow_1(k2_struct_0('#skF_5')))
      | v1_xboole_0('#skF_4'('#skF_5','#skF_6',C_66))
      | ~ r2_hidden(C_66,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_66,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_261])).

tff(c_266,plain,(
    ! [C_168] :
      ( r2_hidden(C_168,'#skF_6')
      | ~ r2_hidden('#skF_6','#skF_4'('#skF_5','#skF_6',C_168))
      | ~ v13_waybel_0('#skF_4'('#skF_5','#skF_6',C_168),k3_yellow_1(k2_struct_0('#skF_5')))
      | v1_xboole_0('#skF_4'('#skF_5','#skF_6',C_168))
      | ~ r2_hidden(C_168,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_168,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_264])).

tff(c_270,plain,(
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
    inference(resolution,[status(thm)],[c_44,c_266])).

tff(c_273,plain,(
    ! [C_66] :
      ( r2_hidden(C_66,'#skF_6')
      | ~ r2_hidden('#skF_6','#skF_4'('#skF_5','#skF_6',C_66))
      | v1_xboole_0('#skF_4'('#skF_5','#skF_6',C_66))
      | ~ r2_hidden(C_66,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_66,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_270])).

tff(c_274,plain,(
    ! [C_66] :
      ( r2_hidden(C_66,'#skF_6')
      | ~ r2_hidden('#skF_6','#skF_4'('#skF_5','#skF_6',C_66))
      | v1_xboole_0('#skF_4'('#skF_5','#skF_6',C_66))
      | ~ r2_hidden(C_66,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_66,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_273])).

tff(c_378,plain,(
    ! [B_222] :
      ( r2_hidden('#skF_3'('#skF_5',B_222),'#skF_6')
      | v1_xboole_0('#skF_4'('#skF_5','#skF_6','#skF_3'('#skF_5',B_222)))
      | ~ r2_hidden('#skF_3'('#skF_5',B_222),k2_pre_topc('#skF_5','#skF_6'))
      | ~ r1_waybel_0('#skF_5','#skF_2'('#skF_5',B_222),'#skF_6')
      | ~ l1_waybel_0('#skF_2'('#skF_5',B_222),'#skF_5')
      | ~ v7_waybel_0('#skF_2'('#skF_5',B_222))
      | ~ v4_orders_2('#skF_2'('#skF_5',B_222))
      | v2_struct_0('#skF_2'('#skF_5',B_222))
      | ~ m1_subset_1('#skF_3'('#skF_5',B_222),u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v4_pre_topc(B_222,'#skF_5')
      | ~ m1_subset_1(B_222,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_372,c_274])).

tff(c_385,plain,(
    ! [B_222] :
      ( r2_hidden('#skF_3'('#skF_5',B_222),'#skF_6')
      | v1_xboole_0('#skF_4'('#skF_5','#skF_6','#skF_3'('#skF_5',B_222)))
      | ~ r2_hidden('#skF_3'('#skF_5',B_222),k2_pre_topc('#skF_5','#skF_6'))
      | ~ r1_waybel_0('#skF_5','#skF_2'('#skF_5',B_222),'#skF_6')
      | ~ l1_waybel_0('#skF_2'('#skF_5',B_222),'#skF_5')
      | ~ v7_waybel_0('#skF_2'('#skF_5',B_222))
      | ~ v4_orders_2('#skF_2'('#skF_5',B_222))
      | v2_struct_0('#skF_2'('#skF_5',B_222))
      | ~ m1_subset_1('#skF_3'('#skF_5',B_222),u1_struct_0('#skF_5'))
      | v4_pre_topc(B_222,'#skF_5')
      | ~ m1_subset_1(B_222,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_378])).

tff(c_413,plain,(
    ! [B_234] :
      ( r2_hidden('#skF_3'('#skF_5',B_234),'#skF_6')
      | v1_xboole_0('#skF_4'('#skF_5','#skF_6','#skF_3'('#skF_5',B_234)))
      | ~ r2_hidden('#skF_3'('#skF_5',B_234),k2_pre_topc('#skF_5','#skF_6'))
      | ~ r1_waybel_0('#skF_5','#skF_2'('#skF_5',B_234),'#skF_6')
      | ~ l1_waybel_0('#skF_2'('#skF_5',B_234),'#skF_5')
      | ~ v7_waybel_0('#skF_2'('#skF_5',B_234))
      | ~ v4_orders_2('#skF_2'('#skF_5',B_234))
      | v2_struct_0('#skF_2'('#skF_5',B_234))
      | ~ m1_subset_1('#skF_3'('#skF_5',B_234),u1_struct_0('#skF_5'))
      | v4_pre_topc(B_234,'#skF_5')
      | ~ m1_subset_1(B_234,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_385])).

tff(c_417,plain,(
    ! [B_37] :
      ( r2_hidden('#skF_3'('#skF_5',B_37),'#skF_6')
      | v1_xboole_0('#skF_4'('#skF_5','#skF_6','#skF_3'('#skF_5',B_37)))
      | ~ r1_waybel_0('#skF_5','#skF_2'('#skF_5',B_37),'#skF_6')
      | ~ l1_waybel_0('#skF_2'('#skF_5',B_37),'#skF_5')
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
    inference(resolution,[status(thm)],[c_216,c_413])).

tff(c_420,plain,(
    ! [B_37] :
      ( r2_hidden('#skF_3'('#skF_5',B_37),'#skF_6')
      | v1_xboole_0('#skF_4'('#skF_5','#skF_6','#skF_3'('#skF_5',B_37)))
      | ~ r1_waybel_0('#skF_5','#skF_2'('#skF_5',B_37),'#skF_6')
      | ~ l1_waybel_0('#skF_2'('#skF_5',B_37),'#skF_5')
      | ~ v7_waybel_0('#skF_2'('#skF_5',B_37))
      | ~ v4_orders_2('#skF_2'('#skF_5',B_37))
      | v2_struct_0('#skF_2'('#skF_5',B_37))
      | ~ m1_subset_1('#skF_3'('#skF_5',B_37),u1_struct_0('#skF_5'))
      | v4_pre_topc(B_37,'#skF_5')
      | ~ m1_subset_1(B_37,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_417])).

tff(c_422,plain,(
    ! [B_235] :
      ( r2_hidden('#skF_3'('#skF_5',B_235),'#skF_6')
      | v1_xboole_0('#skF_4'('#skF_5','#skF_6','#skF_3'('#skF_5',B_235)))
      | ~ r1_waybel_0('#skF_5','#skF_2'('#skF_5',B_235),'#skF_6')
      | ~ l1_waybel_0('#skF_2'('#skF_5',B_235),'#skF_5')
      | ~ v7_waybel_0('#skF_2'('#skF_5',B_235))
      | ~ v4_orders_2('#skF_2'('#skF_5',B_235))
      | v2_struct_0('#skF_2'('#skF_5',B_235))
      | ~ m1_subset_1('#skF_3'('#skF_5',B_235),u1_struct_0('#skF_5'))
      | v4_pre_topc(B_235,'#skF_5')
      | ~ m1_subset_1(B_235,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_420])).

tff(c_426,plain,(
    ! [B_37] :
      ( r2_hidden('#skF_3'('#skF_5',B_37),'#skF_6')
      | v1_xboole_0('#skF_4'('#skF_5','#skF_6','#skF_3'('#skF_5',B_37)))
      | ~ r1_waybel_0('#skF_5','#skF_2'('#skF_5',B_37),'#skF_6')
      | ~ l1_waybel_0('#skF_2'('#skF_5',B_37),'#skF_5')
      | ~ v7_waybel_0('#skF_2'('#skF_5',B_37))
      | ~ v4_orders_2('#skF_2'('#skF_5',B_37))
      | v2_struct_0('#skF_2'('#skF_5',B_37))
      | v4_pre_topc(B_37,'#skF_5')
      | ~ m1_subset_1(B_37,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_22,c_422])).

tff(c_429,plain,(
    ! [B_37] :
      ( r2_hidden('#skF_3'('#skF_5',B_37),'#skF_6')
      | v1_xboole_0('#skF_4'('#skF_5','#skF_6','#skF_3'('#skF_5',B_37)))
      | ~ r1_waybel_0('#skF_5','#skF_2'('#skF_5',B_37),'#skF_6')
      | ~ l1_waybel_0('#skF_2'('#skF_5',B_37),'#skF_5')
      | ~ v7_waybel_0('#skF_2'('#skF_5',B_37))
      | ~ v4_orders_2('#skF_2'('#skF_5',B_37))
      | v2_struct_0('#skF_2'('#skF_5',B_37))
      | v4_pre_topc(B_37,'#skF_5')
      | ~ m1_subset_1(B_37,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_426])).

tff(c_431,plain,(
    ! [B_236] :
      ( r2_hidden('#skF_3'('#skF_5',B_236),'#skF_6')
      | v1_xboole_0('#skF_4'('#skF_5','#skF_6','#skF_3'('#skF_5',B_236)))
      | ~ r1_waybel_0('#skF_5','#skF_2'('#skF_5',B_236),'#skF_6')
      | ~ l1_waybel_0('#skF_2'('#skF_5',B_236),'#skF_5')
      | ~ v7_waybel_0('#skF_2'('#skF_5',B_236))
      | ~ v4_orders_2('#skF_2'('#skF_5',B_236))
      | v2_struct_0('#skF_2'('#skF_5',B_236))
      | v4_pre_topc(B_236,'#skF_5')
      | ~ m1_subset_1(B_236,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_429])).

tff(c_434,plain,
    ( r2_hidden('#skF_3'('#skF_5','#skF_6'),'#skF_6')
    | v1_xboole_0('#skF_4'('#skF_5','#skF_6','#skF_3'('#skF_5','#skF_6')))
    | ~ r1_waybel_0('#skF_5','#skF_2'('#skF_5','#skF_6'),'#skF_6')
    | ~ l1_waybel_0('#skF_2'('#skF_5','#skF_6'),'#skF_5')
    | ~ v7_waybel_0('#skF_2'('#skF_5','#skF_6'))
    | ~ v4_orders_2('#skF_2'('#skF_5','#skF_6'))
    | v2_struct_0('#skF_2'('#skF_5','#skF_6'))
    | v4_pre_topc('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_431])).

tff(c_437,plain,
    ( r2_hidden('#skF_3'('#skF_5','#skF_6'),'#skF_6')
    | v1_xboole_0('#skF_4'('#skF_5','#skF_6','#skF_3'('#skF_5','#skF_6')))
    | v2_struct_0('#skF_2'('#skF_5','#skF_6'))
    | v4_pre_topc('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_121,c_129,c_138,c_434])).

tff(c_438,plain,
    ( r2_hidden('#skF_3'('#skF_5','#skF_6'),'#skF_6')
    | v1_xboole_0('#skF_4'('#skF_5','#skF_6','#skF_3'('#skF_5','#skF_6'))) ),
    inference(negUnitSimplification,[status(thm)],[c_97,c_105,c_437])).

tff(c_439,plain,(
    v1_xboole_0('#skF_4'('#skF_5','#skF_6','#skF_3'('#skF_5','#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_438])).

tff(c_48,plain,(
    ! [A_48,B_60,C_66] :
      ( ~ v1_xboole_0('#skF_4'(A_48,B_60,C_66))
      | ~ r2_hidden(C_66,k2_pre_topc(A_48,B_60))
      | ~ m1_subset_1(C_66,u1_struct_0(A_48))
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ l1_pre_topc(A_48)
      | ~ v2_pre_topc(A_48)
      | v2_struct_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_308,plain,(
    ! [A_188,B_190,B_189] :
      ( ~ v1_xboole_0('#skF_4'(A_188,B_190,'#skF_3'(A_188,B_189)))
      | ~ r1_waybel_0(A_188,'#skF_2'(A_188,B_189),B_190)
      | ~ l1_waybel_0('#skF_2'(A_188,B_189),A_188)
      | ~ v7_waybel_0('#skF_2'(A_188,B_189))
      | ~ v4_orders_2('#skF_2'(A_188,B_189))
      | v2_struct_0('#skF_2'(A_188,B_189))
      | ~ m1_subset_1('#skF_3'(A_188,B_189),u1_struct_0(A_188))
      | ~ m1_subset_1(B_190,k1_zfmisc_1(u1_struct_0(A_188)))
      | v4_pre_topc(B_189,A_188)
      | ~ m1_subset_1(B_189,k1_zfmisc_1(u1_struct_0(A_188)))
      | ~ l1_pre_topc(A_188)
      | ~ v2_pre_topc(A_188)
      | v2_struct_0(A_188) ) ),
    inference(resolution,[status(thm)],[c_288,c_48])).

tff(c_441,plain,
    ( ~ r1_waybel_0('#skF_5','#skF_2'('#skF_5','#skF_6'),'#skF_6')
    | ~ l1_waybel_0('#skF_2'('#skF_5','#skF_6'),'#skF_5')
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
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_113,c_121,c_129,c_138,c_441])).

tff(c_445,plain,(
    ~ m1_subset_1('#skF_3'('#skF_5','#skF_6'),u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_97,c_105,c_444])).

tff(c_455,plain,
    ( v4_pre_topc('#skF_6','#skF_5')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_22,c_445])).

tff(c_458,plain,
    ( v4_pre_topc('#skF_6','#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_455])).

tff(c_460,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_97,c_458])).

tff(c_461,plain,(
    r2_hidden('#skF_3'('#skF_5','#skF_6'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_438])).

tff(c_18,plain,(
    ! [A_23,B_37] :
      ( ~ r2_hidden('#skF_3'(A_23,B_37),B_37)
      | v4_pre_topc(B_37,A_23)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_464,plain,
    ( v4_pre_topc('#skF_6','#skF_5')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_461,c_18])).

tff(c_467,plain,
    ( v4_pre_topc('#skF_6','#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_464])).

tff(c_469,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_97,c_467])).

tff(c_471,plain,(
    v4_pre_topc('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_62,plain,
    ( m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ v4_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_479,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_471,c_62])).

tff(c_64,plain,
    ( r2_hidden('#skF_6','#skF_7')
    | ~ v4_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_473,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_471,c_64])).

tff(c_470,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_72,plain,
    ( v2_waybel_0('#skF_7',k3_yellow_1(k2_struct_0('#skF_5')))
    | ~ v4_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_485,plain,(
    v2_waybel_0('#skF_7',k3_yellow_1(k2_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_471,c_72])).

tff(c_70,plain,
    ( v13_waybel_0('#skF_7',k3_yellow_1(k2_struct_0('#skF_5')))
    | ~ v4_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_481,plain,(
    v13_waybel_0('#skF_7',k3_yellow_1(k2_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_471,c_70])).

tff(c_68,plain,
    ( v3_waybel_7('#skF_7',k3_yellow_1(k2_struct_0('#skF_5')))
    | ~ v4_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_483,plain,(
    v3_waybel_7('#skF_7',k3_yellow_1(k2_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_471,c_68])).

tff(c_66,plain,
    ( m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))))
    | ~ v4_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_487,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_471,c_66])).

tff(c_60,plain,
    ( r2_waybel_7('#skF_5','#skF_7','#skF_8')
    | ~ v4_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_477,plain,(
    r2_waybel_7('#skF_5','#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_471,c_60])).

tff(c_660,plain,(
    ! [C_315,A_316,B_317,D_318] :
      ( r2_hidden(C_315,k2_pre_topc(A_316,B_317))
      | ~ r2_waybel_7(A_316,D_318,C_315)
      | ~ r2_hidden(B_317,D_318)
      | ~ m1_subset_1(D_318,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_316)))))
      | ~ v3_waybel_7(D_318,k3_yellow_1(k2_struct_0(A_316)))
      | ~ v13_waybel_0(D_318,k3_yellow_1(k2_struct_0(A_316)))
      | ~ v2_waybel_0(D_318,k3_yellow_1(k2_struct_0(A_316)))
      | v1_xboole_0(D_318)
      | ~ m1_subset_1(C_315,u1_struct_0(A_316))
      | ~ m1_subset_1(B_317,k1_zfmisc_1(u1_struct_0(A_316)))
      | ~ l1_pre_topc(A_316)
      | ~ v2_pre_topc(A_316)
      | v2_struct_0(A_316) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_664,plain,(
    ! [B_317] :
      ( r2_hidden('#skF_8',k2_pre_topc('#skF_5',B_317))
      | ~ r2_hidden(B_317,'#skF_7')
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))))
      | ~ v3_waybel_7('#skF_7',k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v13_waybel_0('#skF_7',k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v2_waybel_0('#skF_7',k3_yellow_1(k2_struct_0('#skF_5')))
      | v1_xboole_0('#skF_7')
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_317,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_477,c_660])).

tff(c_671,plain,(
    ! [B_317] :
      ( r2_hidden('#skF_8',k2_pre_topc('#skF_5',B_317))
      | ~ r2_hidden(B_317,'#skF_7')
      | v1_xboole_0('#skF_7')
      | ~ m1_subset_1(B_317,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_479,c_485,c_481,c_483,c_487,c_664])).

tff(c_673,plain,(
    ! [B_319] :
      ( r2_hidden('#skF_8',k2_pre_topc('#skF_5',B_319))
      | ~ r2_hidden(B_319,'#skF_7')
      | ~ m1_subset_1(B_319,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_470,c_671])).

tff(c_676,plain,
    ( r2_hidden('#skF_8',k2_pre_topc('#skF_5','#skF_6'))
    | ~ r2_hidden('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_50,c_673])).

tff(c_679,plain,(
    r2_hidden('#skF_8',k2_pre_topc('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_473,c_676])).

tff(c_14,plain,(
    ! [A_1,B_13,C_19] :
      ( ~ v2_struct_0('#skF_1'(A_1,B_13,C_19))
      | ~ r2_hidden(C_19,k2_pre_topc(A_1,B_13))
      | ~ m1_subset_1(C_19,u1_struct_0(A_1))
      | ~ m1_subset_1(B_13,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_690,plain,
    ( ~ v2_struct_0('#skF_1'('#skF_5','#skF_6','#skF_8'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_679,c_14])).

tff(c_713,plain,
    ( ~ v2_struct_0('#skF_1'('#skF_5','#skF_6','#skF_8'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_479,c_690])).

tff(c_714,plain,(
    ~ v2_struct_0('#skF_1'('#skF_5','#skF_6','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_713])).

tff(c_12,plain,(
    ! [A_1,B_13,C_19] :
      ( v4_orders_2('#skF_1'(A_1,B_13,C_19))
      | ~ r2_hidden(C_19,k2_pre_topc(A_1,B_13))
      | ~ m1_subset_1(C_19,u1_struct_0(A_1))
      | ~ m1_subset_1(B_13,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_692,plain,
    ( v4_orders_2('#skF_1'('#skF_5','#skF_6','#skF_8'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_679,c_12])).

tff(c_717,plain,
    ( v4_orders_2('#skF_1'('#skF_5','#skF_6','#skF_8'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_479,c_692])).

tff(c_718,plain,(
    v4_orders_2('#skF_1'('#skF_5','#skF_6','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_717])).

tff(c_10,plain,(
    ! [A_1,B_13,C_19] :
      ( v7_waybel_0('#skF_1'(A_1,B_13,C_19))
      | ~ r2_hidden(C_19,k2_pre_topc(A_1,B_13))
      | ~ m1_subset_1(C_19,u1_struct_0(A_1))
      | ~ m1_subset_1(B_13,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_688,plain,
    ( v7_waybel_0('#skF_1'('#skF_5','#skF_6','#skF_8'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_679,c_10])).

tff(c_709,plain,
    ( v7_waybel_0('#skF_1'('#skF_5','#skF_6','#skF_8'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_479,c_688])).

tff(c_710,plain,(
    v7_waybel_0('#skF_1'('#skF_5','#skF_6','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_709])).

tff(c_8,plain,(
    ! [A_1,B_13,C_19] :
      ( l1_waybel_0('#skF_1'(A_1,B_13,C_19),A_1)
      | ~ r2_hidden(C_19,k2_pre_topc(A_1,B_13))
      | ~ m1_subset_1(C_19,u1_struct_0(A_1))
      | ~ m1_subset_1(B_13,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_686,plain,
    ( l1_waybel_0('#skF_1'('#skF_5','#skF_6','#skF_8'),'#skF_5')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_679,c_8])).

tff(c_705,plain,
    ( l1_waybel_0('#skF_1'('#skF_5','#skF_6','#skF_8'),'#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_479,c_686])).

tff(c_706,plain,(
    l1_waybel_0('#skF_1'('#skF_5','#skF_6','#skF_8'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_705])).

tff(c_58,plain,
    ( ~ r2_hidden('#skF_8','#skF_6')
    | ~ v4_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_475,plain,(
    ~ r2_hidden('#skF_8','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_471,c_58])).

tff(c_566,plain,(
    ! [A_279,B_280,C_281] :
      ( r1_waybel_0(A_279,'#skF_1'(A_279,B_280,C_281),B_280)
      | ~ r2_hidden(C_281,k2_pre_topc(A_279,B_280))
      | ~ m1_subset_1(C_281,u1_struct_0(A_279))
      | ~ m1_subset_1(B_280,k1_zfmisc_1(u1_struct_0(A_279)))
      | ~ l1_pre_topc(A_279)
      | ~ v2_pre_topc(A_279)
      | v2_struct_0(A_279) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_570,plain,(
    ! [C_281] :
      ( r1_waybel_0('#skF_5','#skF_1'('#skF_5','#skF_6',C_281),'#skF_6')
      | ~ r2_hidden(C_281,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_281,u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_50,c_566])).

tff(c_574,plain,(
    ! [C_281] :
      ( r1_waybel_0('#skF_5','#skF_1'('#skF_5','#skF_6',C_281),'#skF_6')
      | ~ r2_hidden(C_281,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_281,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_570])).

tff(c_575,plain,(
    ! [C_281] :
      ( r1_waybel_0('#skF_5','#skF_1'('#skF_5','#skF_6',C_281),'#skF_6')
      | ~ r2_hidden(C_281,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_281,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_574])).

tff(c_555,plain,(
    ! [A_275,B_276,C_277] :
      ( r3_waybel_9(A_275,'#skF_1'(A_275,B_276,C_277),C_277)
      | ~ r2_hidden(C_277,k2_pre_topc(A_275,B_276))
      | ~ m1_subset_1(C_277,u1_struct_0(A_275))
      | ~ m1_subset_1(B_276,k1_zfmisc_1(u1_struct_0(A_275)))
      | ~ l1_pre_topc(A_275)
      | ~ v2_pre_topc(A_275)
      | v2_struct_0(A_275) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_559,plain,(
    ! [C_277] :
      ( r3_waybel_9('#skF_5','#skF_1'('#skF_5','#skF_6',C_277),C_277)
      | ~ r2_hidden(C_277,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_277,u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_50,c_555])).

tff(c_563,plain,(
    ! [C_277] :
      ( r3_waybel_9('#skF_5','#skF_1'('#skF_5','#skF_6',C_277),C_277)
      | ~ r2_hidden(C_277,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_277,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_559])).

tff(c_564,plain,(
    ! [C_277] :
      ( r3_waybel_9('#skF_5','#skF_1'('#skF_5','#skF_6',C_277),C_277)
      | ~ r2_hidden(C_277,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_277,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_563])).

tff(c_630,plain,(
    ! [D_303,B_304,A_305,C_306] :
      ( r2_hidden(D_303,B_304)
      | ~ r3_waybel_9(A_305,C_306,D_303)
      | ~ m1_subset_1(D_303,u1_struct_0(A_305))
      | ~ r1_waybel_0(A_305,C_306,B_304)
      | ~ l1_waybel_0(C_306,A_305)
      | ~ v7_waybel_0(C_306)
      | ~ v4_orders_2(C_306)
      | v2_struct_0(C_306)
      | ~ v4_pre_topc(B_304,A_305)
      | ~ m1_subset_1(B_304,k1_zfmisc_1(u1_struct_0(A_305)))
      | ~ l1_pre_topc(A_305)
      | ~ v2_pre_topc(A_305)
      | v2_struct_0(A_305) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_632,plain,(
    ! [C_277,B_304] :
      ( r2_hidden(C_277,B_304)
      | ~ r1_waybel_0('#skF_5','#skF_1'('#skF_5','#skF_6',C_277),B_304)
      | ~ l1_waybel_0('#skF_1'('#skF_5','#skF_6',C_277),'#skF_5')
      | ~ v7_waybel_0('#skF_1'('#skF_5','#skF_6',C_277))
      | ~ v4_orders_2('#skF_1'('#skF_5','#skF_6',C_277))
      | v2_struct_0('#skF_1'('#skF_5','#skF_6',C_277))
      | ~ v4_pre_topc(B_304,'#skF_5')
      | ~ m1_subset_1(B_304,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r2_hidden(C_277,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_277,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_564,c_630])).

tff(c_637,plain,(
    ! [C_277,B_304] :
      ( r2_hidden(C_277,B_304)
      | ~ r1_waybel_0('#skF_5','#skF_1'('#skF_5','#skF_6',C_277),B_304)
      | ~ l1_waybel_0('#skF_1'('#skF_5','#skF_6',C_277),'#skF_5')
      | ~ v7_waybel_0('#skF_1'('#skF_5','#skF_6',C_277))
      | ~ v4_orders_2('#skF_1'('#skF_5','#skF_6',C_277))
      | v2_struct_0('#skF_1'('#skF_5','#skF_6',C_277))
      | ~ v4_pre_topc(B_304,'#skF_5')
      | ~ m1_subset_1(B_304,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v2_struct_0('#skF_5')
      | ~ r2_hidden(C_277,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_277,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_632])).

tff(c_652,plain,(
    ! [C_309,B_310] :
      ( r2_hidden(C_309,B_310)
      | ~ r1_waybel_0('#skF_5','#skF_1'('#skF_5','#skF_6',C_309),B_310)
      | ~ l1_waybel_0('#skF_1'('#skF_5','#skF_6',C_309),'#skF_5')
      | ~ v7_waybel_0('#skF_1'('#skF_5','#skF_6',C_309))
      | ~ v4_orders_2('#skF_1'('#skF_5','#skF_6',C_309))
      | v2_struct_0('#skF_1'('#skF_5','#skF_6',C_309))
      | ~ v4_pre_topc(B_310,'#skF_5')
      | ~ m1_subset_1(B_310,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r2_hidden(C_309,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_309,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_637])).

tff(c_654,plain,(
    ! [C_281] :
      ( r2_hidden(C_281,'#skF_6')
      | ~ l1_waybel_0('#skF_1'('#skF_5','#skF_6',C_281),'#skF_5')
      | ~ v7_waybel_0('#skF_1'('#skF_5','#skF_6',C_281))
      | ~ v4_orders_2('#skF_1'('#skF_5','#skF_6',C_281))
      | v2_struct_0('#skF_1'('#skF_5','#skF_6',C_281))
      | ~ v4_pre_topc('#skF_6','#skF_5')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r2_hidden(C_281,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_281,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_575,c_652])).

tff(c_657,plain,(
    ! [C_281] :
      ( r2_hidden(C_281,'#skF_6')
      | ~ l1_waybel_0('#skF_1'('#skF_5','#skF_6',C_281),'#skF_5')
      | ~ v7_waybel_0('#skF_1'('#skF_5','#skF_6',C_281))
      | ~ v4_orders_2('#skF_1'('#skF_5','#skF_6',C_281))
      | v2_struct_0('#skF_1'('#skF_5','#skF_6',C_281))
      | ~ r2_hidden(C_281,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_281,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_471,c_654])).

tff(c_682,plain,
    ( r2_hidden('#skF_8','#skF_6')
    | ~ l1_waybel_0('#skF_1'('#skF_5','#skF_6','#skF_8'),'#skF_5')
    | ~ v7_waybel_0('#skF_1'('#skF_5','#skF_6','#skF_8'))
    | ~ v4_orders_2('#skF_1'('#skF_5','#skF_6','#skF_8'))
    | v2_struct_0('#skF_1'('#skF_5','#skF_6','#skF_8'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_679,c_657])).

tff(c_697,plain,
    ( r2_hidden('#skF_8','#skF_6')
    | ~ l1_waybel_0('#skF_1'('#skF_5','#skF_6','#skF_8'),'#skF_5')
    | ~ v7_waybel_0('#skF_1'('#skF_5','#skF_6','#skF_8'))
    | ~ v4_orders_2('#skF_1'('#skF_5','#skF_6','#skF_8'))
    | v2_struct_0('#skF_1'('#skF_5','#skF_6','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_479,c_682])).

tff(c_698,plain,
    ( ~ l1_waybel_0('#skF_1'('#skF_5','#skF_6','#skF_8'),'#skF_5')
    | ~ v7_waybel_0('#skF_1'('#skF_5','#skF_6','#skF_8'))
    | ~ v4_orders_2('#skF_1'('#skF_5','#skF_6','#skF_8'))
    | v2_struct_0('#skF_1'('#skF_5','#skF_6','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_475,c_697])).

tff(c_724,plain,(
    v2_struct_0('#skF_1'('#skF_5','#skF_6','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_718,c_710,c_706,c_698])).

tff(c_725,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_714,c_724])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:17:57 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.67/1.88  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.67/1.90  
% 3.67/1.90  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.67/1.90  %$ r3_waybel_9 > r2_waybel_7 > r1_waybel_0 > v4_pre_topc > v3_waybel_7 > v2_waybel_0 > v13_waybel_0 > r2_hidden > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k2_pre_topc > #nlpp > u1_struct_0 > k3_yellow_1 > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2
% 3.67/1.90  
% 3.67/1.90  %Foreground sorts:
% 3.67/1.90  
% 3.67/1.90  
% 3.67/1.90  %Background operators:
% 3.67/1.90  
% 3.67/1.90  
% 3.67/1.90  %Foreground operators:
% 3.67/1.90  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.67/1.90  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.67/1.90  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.67/1.90  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.67/1.90  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 3.67/1.90  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 3.67/1.90  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.67/1.90  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 3.67/1.90  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.67/1.90  tff('#skF_7', type, '#skF_7': $i).
% 3.67/1.90  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.67/1.90  tff('#skF_5', type, '#skF_5': $i).
% 3.67/1.90  tff(r3_waybel_9, type, r3_waybel_9: ($i * $i * $i) > $o).
% 3.67/1.90  tff(r1_waybel_0, type, r1_waybel_0: ($i * $i * $i) > $o).
% 3.67/1.90  tff('#skF_6', type, '#skF_6': $i).
% 3.67/1.90  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.67/1.90  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.67/1.90  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.67/1.90  tff('#skF_8', type, '#skF_8': $i).
% 3.67/1.90  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.67/1.90  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 3.67/1.90  tff(r2_waybel_7, type, r2_waybel_7: ($i * $i * $i) > $o).
% 3.67/1.90  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.67/1.90  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.67/1.90  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 3.67/1.90  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.67/1.90  tff(v3_waybel_7, type, v3_waybel_7: ($i * $i) > $o).
% 3.67/1.90  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.67/1.90  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.67/1.90  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.67/1.90  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.67/1.90  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.67/1.90  
% 4.08/1.93  tff(f_150, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (![C]: (((((~v1_xboole_0(C) & v2_waybel_0(C, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(C, k3_yellow_1(k2_struct_0(A)))) & v3_waybel_7(C, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (r2_hidden(B, C) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_waybel_7(A, C, D) => r2_hidden(D, B)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_yellow19)).
% 4.08/1.93  tff(f_85, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (![C]: ((((~v2_struct_0(C) & v4_orders_2(C)) & v7_waybel_0(C)) & l1_waybel_0(C, A)) => (r1_waybel_0(A, C, B) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r3_waybel_9(A, C, D) => r2_hidden(D, B)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_yellow19)).
% 4.08/1.93  tff(f_54, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, k2_pre_topc(A, B)) <=> (?[D]: (((((~v2_struct_0(D) & v4_orders_2(D)) & v7_waybel_0(D)) & l1_waybel_0(D, A)) & r1_waybel_0(A, D, B)) & r3_waybel_9(A, D, C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_yellow19)).
% 4.08/1.93  tff(f_116, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, k2_pre_topc(A, B)) <=> (?[D]: ((((((~v1_xboole_0(D) & v2_waybel_0(D, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(D, k3_yellow_1(k2_struct_0(A)))) & v3_waybel_7(D, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(D, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) & r2_hidden(B, D)) & r2_waybel_7(A, D, C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_yellow19)).
% 4.08/1.93  tff(c_56, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_150])).
% 4.08/1.93  tff(c_54, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_150])).
% 4.08/1.93  tff(c_52, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_150])).
% 4.08/1.93  tff(c_50, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_150])).
% 4.08/1.93  tff(c_74, plain, (~v1_xboole_0('#skF_7') | ~v4_pre_topc('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_150])).
% 4.08/1.93  tff(c_97, plain, (~v4_pre_topc('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_74])).
% 4.08/1.93  tff(c_22, plain, (![A_23, B_37]: (m1_subset_1('#skF_3'(A_23, B_37), u1_struct_0(A_23)) | v4_pre_topc(B_37, A_23) | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0(A_23))) | ~l1_pre_topc(A_23) | ~v2_pre_topc(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.08/1.93  tff(c_98, plain, (![A_93, B_94]: (~v2_struct_0('#skF_2'(A_93, B_94)) | v4_pre_topc(B_94, A_93) | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0(A_93))) | ~l1_pre_topc(A_93) | ~v2_pre_topc(A_93) | v2_struct_0(A_93))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.08/1.93  tff(c_101, plain, (~v2_struct_0('#skF_2'('#skF_5', '#skF_6')) | v4_pre_topc('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_50, c_98])).
% 4.08/1.93  tff(c_104, plain, (~v2_struct_0('#skF_2'('#skF_5', '#skF_6')) | v4_pre_topc('#skF_6', '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_101])).
% 4.08/1.93  tff(c_105, plain, (~v2_struct_0('#skF_2'('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_56, c_97, c_104])).
% 4.08/1.93  tff(c_106, plain, (![A_95, B_96]: (v4_orders_2('#skF_2'(A_95, B_96)) | v4_pre_topc(B_96, A_95) | ~m1_subset_1(B_96, k1_zfmisc_1(u1_struct_0(A_95))) | ~l1_pre_topc(A_95) | ~v2_pre_topc(A_95) | v2_struct_0(A_95))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.08/1.93  tff(c_109, plain, (v4_orders_2('#skF_2'('#skF_5', '#skF_6')) | v4_pre_topc('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_50, c_106])).
% 4.08/1.93  tff(c_112, plain, (v4_orders_2('#skF_2'('#skF_5', '#skF_6')) | v4_pre_topc('#skF_6', '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_109])).
% 4.08/1.93  tff(c_113, plain, (v4_orders_2('#skF_2'('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_56, c_97, c_112])).
% 4.08/1.93  tff(c_114, plain, (![A_97, B_98]: (v7_waybel_0('#skF_2'(A_97, B_98)) | v4_pre_topc(B_98, A_97) | ~m1_subset_1(B_98, k1_zfmisc_1(u1_struct_0(A_97))) | ~l1_pre_topc(A_97) | ~v2_pre_topc(A_97) | v2_struct_0(A_97))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.08/1.93  tff(c_117, plain, (v7_waybel_0('#skF_2'('#skF_5', '#skF_6')) | v4_pre_topc('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_50, c_114])).
% 4.08/1.93  tff(c_120, plain, (v7_waybel_0('#skF_2'('#skF_5', '#skF_6')) | v4_pre_topc('#skF_6', '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_117])).
% 4.08/1.93  tff(c_121, plain, (v7_waybel_0('#skF_2'('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_56, c_97, c_120])).
% 4.08/1.93  tff(c_123, plain, (![A_99, B_100]: (l1_waybel_0('#skF_2'(A_99, B_100), A_99) | v4_pre_topc(B_100, A_99) | ~m1_subset_1(B_100, k1_zfmisc_1(u1_struct_0(A_99))) | ~l1_pre_topc(A_99) | ~v2_pre_topc(A_99) | v2_struct_0(A_99))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.08/1.93  tff(c_125, plain, (l1_waybel_0('#skF_2'('#skF_5', '#skF_6'), '#skF_5') | v4_pre_topc('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_50, c_123])).
% 4.08/1.93  tff(c_128, plain, (l1_waybel_0('#skF_2'('#skF_5', '#skF_6'), '#skF_5') | v4_pre_topc('#skF_6', '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_125])).
% 4.08/1.93  tff(c_129, plain, (l1_waybel_0('#skF_2'('#skF_5', '#skF_6'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_56, c_97, c_128])).
% 4.08/1.93  tff(c_132, plain, (![A_105, B_106]: (r1_waybel_0(A_105, '#skF_2'(A_105, B_106), B_106) | v4_pre_topc(B_106, A_105) | ~m1_subset_1(B_106, k1_zfmisc_1(u1_struct_0(A_105))) | ~l1_pre_topc(A_105) | ~v2_pre_topc(A_105) | v2_struct_0(A_105))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.08/1.93  tff(c_134, plain, (r1_waybel_0('#skF_5', '#skF_2'('#skF_5', '#skF_6'), '#skF_6') | v4_pre_topc('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_50, c_132])).
% 4.08/1.93  tff(c_137, plain, (r1_waybel_0('#skF_5', '#skF_2'('#skF_5', '#skF_6'), '#skF_6') | v4_pre_topc('#skF_6', '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_134])).
% 4.08/1.93  tff(c_138, plain, (r1_waybel_0('#skF_5', '#skF_2'('#skF_5', '#skF_6'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_56, c_97, c_137])).
% 4.08/1.93  tff(c_20, plain, (![A_23, B_37]: (r3_waybel_9(A_23, '#skF_2'(A_23, B_37), '#skF_3'(A_23, B_37)) | v4_pre_topc(B_37, A_23) | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0(A_23))) | ~l1_pre_topc(A_23) | ~v2_pre_topc(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.08/1.93  tff(c_207, plain, (![C_153, A_154, B_155, D_156]: (r2_hidden(C_153, k2_pre_topc(A_154, B_155)) | ~r3_waybel_9(A_154, D_156, C_153) | ~r1_waybel_0(A_154, D_156, B_155) | ~l1_waybel_0(D_156, A_154) | ~v7_waybel_0(D_156) | ~v4_orders_2(D_156) | v2_struct_0(D_156) | ~m1_subset_1(C_153, u1_struct_0(A_154)) | ~m1_subset_1(B_155, k1_zfmisc_1(u1_struct_0(A_154))) | ~l1_pre_topc(A_154) | ~v2_pre_topc(A_154) | v2_struct_0(A_154))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.08/1.93  tff(c_216, plain, (![A_23, B_37, B_155]: (r2_hidden('#skF_3'(A_23, B_37), k2_pre_topc(A_23, B_155)) | ~r1_waybel_0(A_23, '#skF_2'(A_23, B_37), B_155) | ~l1_waybel_0('#skF_2'(A_23, B_37), A_23) | ~v7_waybel_0('#skF_2'(A_23, B_37)) | ~v4_orders_2('#skF_2'(A_23, B_37)) | v2_struct_0('#skF_2'(A_23, B_37)) | ~m1_subset_1('#skF_3'(A_23, B_37), u1_struct_0(A_23)) | ~m1_subset_1(B_155, k1_zfmisc_1(u1_struct_0(A_23))) | v4_pre_topc(B_37, A_23) | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0(A_23))) | ~l1_pre_topc(A_23) | ~v2_pre_topc(A_23) | v2_struct_0(A_23))), inference(resolution, [status(thm)], [c_20, c_207])).
% 4.08/1.93  tff(c_288, plain, (![A_188, B_189, B_190]: (r2_hidden('#skF_3'(A_188, B_189), k2_pre_topc(A_188, B_190)) | ~r1_waybel_0(A_188, '#skF_2'(A_188, B_189), B_190) | ~l1_waybel_0('#skF_2'(A_188, B_189), A_188) | ~v7_waybel_0('#skF_2'(A_188, B_189)) | ~v4_orders_2('#skF_2'(A_188, B_189)) | v2_struct_0('#skF_2'(A_188, B_189)) | ~m1_subset_1('#skF_3'(A_188, B_189), u1_struct_0(A_188)) | ~m1_subset_1(B_190, k1_zfmisc_1(u1_struct_0(A_188))) | v4_pre_topc(B_189, A_188) | ~m1_subset_1(B_189, k1_zfmisc_1(u1_struct_0(A_188))) | ~l1_pre_topc(A_188) | ~v2_pre_topc(A_188) | v2_struct_0(A_188))), inference(resolution, [status(thm)], [c_20, c_207])).
% 4.08/1.93  tff(c_38, plain, (![B_60, A_48, C_66]: (r2_hidden(B_60, '#skF_4'(A_48, B_60, C_66)) | ~r2_hidden(C_66, k2_pre_topc(A_48, B_60)) | ~m1_subset_1(C_66, u1_struct_0(A_48)) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_48))) | ~l1_pre_topc(A_48) | ~v2_pre_topc(A_48) | v2_struct_0(A_48))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.08/1.93  tff(c_372, plain, (![B_220, A_221, B_222]: (r2_hidden(B_220, '#skF_4'(A_221, B_220, '#skF_3'(A_221, B_222))) | ~r1_waybel_0(A_221, '#skF_2'(A_221, B_222), B_220) | ~l1_waybel_0('#skF_2'(A_221, B_222), A_221) | ~v7_waybel_0('#skF_2'(A_221, B_222)) | ~v4_orders_2('#skF_2'(A_221, B_222)) | v2_struct_0('#skF_2'(A_221, B_222)) | ~m1_subset_1('#skF_3'(A_221, B_222), u1_struct_0(A_221)) | ~m1_subset_1(B_220, k1_zfmisc_1(u1_struct_0(A_221))) | v4_pre_topc(B_222, A_221) | ~m1_subset_1(B_222, k1_zfmisc_1(u1_struct_0(A_221))) | ~l1_pre_topc(A_221) | ~v2_pre_topc(A_221) | v2_struct_0(A_221))), inference(resolution, [status(thm)], [c_288, c_38])).
% 4.08/1.93  tff(c_44, plain, (![A_48, B_60, C_66]: (v13_waybel_0('#skF_4'(A_48, B_60, C_66), k3_yellow_1(k2_struct_0(A_48))) | ~r2_hidden(C_66, k2_pre_topc(A_48, B_60)) | ~m1_subset_1(C_66, u1_struct_0(A_48)) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_48))) | ~l1_pre_topc(A_48) | ~v2_pre_topc(A_48) | v2_struct_0(A_48))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.08/1.93  tff(c_46, plain, (![A_48, B_60, C_66]: (v2_waybel_0('#skF_4'(A_48, B_60, C_66), k3_yellow_1(k2_struct_0(A_48))) | ~r2_hidden(C_66, k2_pre_topc(A_48, B_60)) | ~m1_subset_1(C_66, u1_struct_0(A_48)) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_48))) | ~l1_pre_topc(A_48) | ~v2_pre_topc(A_48) | v2_struct_0(A_48))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.08/1.93  tff(c_42, plain, (![A_48, B_60, C_66]: (v3_waybel_7('#skF_4'(A_48, B_60, C_66), k3_yellow_1(k2_struct_0(A_48))) | ~r2_hidden(C_66, k2_pre_topc(A_48, B_60)) | ~m1_subset_1(C_66, u1_struct_0(A_48)) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_48))) | ~l1_pre_topc(A_48) | ~v2_pre_topc(A_48) | v2_struct_0(A_48))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.08/1.93  tff(c_40, plain, (![A_48, B_60, C_66]: (m1_subset_1('#skF_4'(A_48, B_60, C_66), k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_48))))) | ~r2_hidden(C_66, k2_pre_topc(A_48, B_60)) | ~m1_subset_1(C_66, u1_struct_0(A_48)) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_48))) | ~l1_pre_topc(A_48) | ~v2_pre_topc(A_48) | v2_struct_0(A_48))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.08/1.93  tff(c_147, plain, (![A_127, B_128, C_129]: (r2_waybel_7(A_127, '#skF_4'(A_127, B_128, C_129), C_129) | ~r2_hidden(C_129, k2_pre_topc(A_127, B_128)) | ~m1_subset_1(C_129, u1_struct_0(A_127)) | ~m1_subset_1(B_128, k1_zfmisc_1(u1_struct_0(A_127))) | ~l1_pre_topc(A_127) | ~v2_pre_topc(A_127) | v2_struct_0(A_127))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.08/1.93  tff(c_149, plain, (![C_129]: (r2_waybel_7('#skF_5', '#skF_4'('#skF_5', '#skF_6', C_129), C_129) | ~r2_hidden(C_129, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_129, u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_50, c_147])).
% 4.08/1.93  tff(c_152, plain, (![C_129]: (r2_waybel_7('#skF_5', '#skF_4'('#skF_5', '#skF_6', C_129), C_129) | ~r2_hidden(C_129, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_129, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_149])).
% 4.08/1.93  tff(c_153, plain, (![C_129]: (r2_waybel_7('#skF_5', '#skF_4'('#skF_5', '#skF_6', C_129), C_129) | ~r2_hidden(C_129, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_129, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_56, c_152])).
% 4.08/1.93  tff(c_96, plain, (![D_92, C_90]: (v4_pre_topc('#skF_6', '#skF_5') | r2_hidden(D_92, '#skF_6') | ~r2_waybel_7('#skF_5', C_90, D_92) | ~m1_subset_1(D_92, u1_struct_0('#skF_5')) | ~r2_hidden('#skF_6', C_90) | ~m1_subset_1(C_90, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))) | ~v3_waybel_7(C_90, k3_yellow_1(k2_struct_0('#skF_5'))) | ~v13_waybel_0(C_90, k3_yellow_1(k2_struct_0('#skF_5'))) | ~v2_waybel_0(C_90, k3_yellow_1(k2_struct_0('#skF_5'))) | v1_xboole_0(C_90))), inference(cnfTransformation, [status(thm)], [f_150])).
% 4.08/1.93  tff(c_156, plain, (![D_131, C_132]: (r2_hidden(D_131, '#skF_6') | ~r2_waybel_7('#skF_5', C_132, D_131) | ~m1_subset_1(D_131, u1_struct_0('#skF_5')) | ~r2_hidden('#skF_6', C_132) | ~m1_subset_1(C_132, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))) | ~v3_waybel_7(C_132, k3_yellow_1(k2_struct_0('#skF_5'))) | ~v13_waybel_0(C_132, k3_yellow_1(k2_struct_0('#skF_5'))) | ~v2_waybel_0(C_132, k3_yellow_1(k2_struct_0('#skF_5'))) | v1_xboole_0(C_132))), inference(negUnitSimplification, [status(thm)], [c_97, c_96])).
% 4.08/1.93  tff(c_239, plain, (![C_165]: (r2_hidden(C_165, '#skF_6') | ~r2_hidden('#skF_6', '#skF_4'('#skF_5', '#skF_6', C_165)) | ~m1_subset_1('#skF_4'('#skF_5', '#skF_6', C_165), k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))) | ~v3_waybel_7('#skF_4'('#skF_5', '#skF_6', C_165), k3_yellow_1(k2_struct_0('#skF_5'))) | ~v13_waybel_0('#skF_4'('#skF_5', '#skF_6', C_165), k3_yellow_1(k2_struct_0('#skF_5'))) | ~v2_waybel_0('#skF_4'('#skF_5', '#skF_6', C_165), k3_yellow_1(k2_struct_0('#skF_5'))) | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', C_165)) | ~r2_hidden(C_165, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_165, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_153, c_156])).
% 4.08/1.93  tff(c_243, plain, (![C_66]: (r2_hidden(C_66, '#skF_6') | ~r2_hidden('#skF_6', '#skF_4'('#skF_5', '#skF_6', C_66)) | ~v3_waybel_7('#skF_4'('#skF_5', '#skF_6', C_66), k3_yellow_1(k2_struct_0('#skF_5'))) | ~v13_waybel_0('#skF_4'('#skF_5', '#skF_6', C_66), k3_yellow_1(k2_struct_0('#skF_5'))) | ~v2_waybel_0('#skF_4'('#skF_5', '#skF_6', C_66), k3_yellow_1(k2_struct_0('#skF_5'))) | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', C_66)) | ~r2_hidden(C_66, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_66, u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_40, c_239])).
% 4.08/1.93  tff(c_246, plain, (![C_66]: (r2_hidden(C_66, '#skF_6') | ~r2_hidden('#skF_6', '#skF_4'('#skF_5', '#skF_6', C_66)) | ~v3_waybel_7('#skF_4'('#skF_5', '#skF_6', C_66), k3_yellow_1(k2_struct_0('#skF_5'))) | ~v13_waybel_0('#skF_4'('#skF_5', '#skF_6', C_66), k3_yellow_1(k2_struct_0('#skF_5'))) | ~v2_waybel_0('#skF_4'('#skF_5', '#skF_6', C_66), k3_yellow_1(k2_struct_0('#skF_5'))) | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', C_66)) | ~r2_hidden(C_66, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_66, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_243])).
% 4.08/1.93  tff(c_248, plain, (![C_166]: (r2_hidden(C_166, '#skF_6') | ~r2_hidden('#skF_6', '#skF_4'('#skF_5', '#skF_6', C_166)) | ~v3_waybel_7('#skF_4'('#skF_5', '#skF_6', C_166), k3_yellow_1(k2_struct_0('#skF_5'))) | ~v13_waybel_0('#skF_4'('#skF_5', '#skF_6', C_166), k3_yellow_1(k2_struct_0('#skF_5'))) | ~v2_waybel_0('#skF_4'('#skF_5', '#skF_6', C_166), k3_yellow_1(k2_struct_0('#skF_5'))) | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', C_166)) | ~r2_hidden(C_166, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_166, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_56, c_246])).
% 4.08/1.93  tff(c_252, plain, (![C_66]: (r2_hidden(C_66, '#skF_6') | ~r2_hidden('#skF_6', '#skF_4'('#skF_5', '#skF_6', C_66)) | ~v13_waybel_0('#skF_4'('#skF_5', '#skF_6', C_66), k3_yellow_1(k2_struct_0('#skF_5'))) | ~v2_waybel_0('#skF_4'('#skF_5', '#skF_6', C_66), k3_yellow_1(k2_struct_0('#skF_5'))) | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', C_66)) | ~r2_hidden(C_66, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_66, u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_42, c_248])).
% 4.08/1.93  tff(c_255, plain, (![C_66]: (r2_hidden(C_66, '#skF_6') | ~r2_hidden('#skF_6', '#skF_4'('#skF_5', '#skF_6', C_66)) | ~v13_waybel_0('#skF_4'('#skF_5', '#skF_6', C_66), k3_yellow_1(k2_struct_0('#skF_5'))) | ~v2_waybel_0('#skF_4'('#skF_5', '#skF_6', C_66), k3_yellow_1(k2_struct_0('#skF_5'))) | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', C_66)) | ~r2_hidden(C_66, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_66, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_252])).
% 4.08/1.93  tff(c_257, plain, (![C_167]: (r2_hidden(C_167, '#skF_6') | ~r2_hidden('#skF_6', '#skF_4'('#skF_5', '#skF_6', C_167)) | ~v13_waybel_0('#skF_4'('#skF_5', '#skF_6', C_167), k3_yellow_1(k2_struct_0('#skF_5'))) | ~v2_waybel_0('#skF_4'('#skF_5', '#skF_6', C_167), k3_yellow_1(k2_struct_0('#skF_5'))) | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', C_167)) | ~r2_hidden(C_167, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_167, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_56, c_255])).
% 4.08/1.93  tff(c_261, plain, (![C_66]: (r2_hidden(C_66, '#skF_6') | ~r2_hidden('#skF_6', '#skF_4'('#skF_5', '#skF_6', C_66)) | ~v13_waybel_0('#skF_4'('#skF_5', '#skF_6', C_66), k3_yellow_1(k2_struct_0('#skF_5'))) | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', C_66)) | ~r2_hidden(C_66, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_66, u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_46, c_257])).
% 4.08/1.93  tff(c_264, plain, (![C_66]: (r2_hidden(C_66, '#skF_6') | ~r2_hidden('#skF_6', '#skF_4'('#skF_5', '#skF_6', C_66)) | ~v13_waybel_0('#skF_4'('#skF_5', '#skF_6', C_66), k3_yellow_1(k2_struct_0('#skF_5'))) | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', C_66)) | ~r2_hidden(C_66, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_66, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_261])).
% 4.08/1.93  tff(c_266, plain, (![C_168]: (r2_hidden(C_168, '#skF_6') | ~r2_hidden('#skF_6', '#skF_4'('#skF_5', '#skF_6', C_168)) | ~v13_waybel_0('#skF_4'('#skF_5', '#skF_6', C_168), k3_yellow_1(k2_struct_0('#skF_5'))) | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', C_168)) | ~r2_hidden(C_168, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_168, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_56, c_264])).
% 4.08/1.93  tff(c_270, plain, (![C_66]: (r2_hidden(C_66, '#skF_6') | ~r2_hidden('#skF_6', '#skF_4'('#skF_5', '#skF_6', C_66)) | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', C_66)) | ~r2_hidden(C_66, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_66, u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_44, c_266])).
% 4.08/1.93  tff(c_273, plain, (![C_66]: (r2_hidden(C_66, '#skF_6') | ~r2_hidden('#skF_6', '#skF_4'('#skF_5', '#skF_6', C_66)) | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', C_66)) | ~r2_hidden(C_66, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_66, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_270])).
% 4.08/1.93  tff(c_274, plain, (![C_66]: (r2_hidden(C_66, '#skF_6') | ~r2_hidden('#skF_6', '#skF_4'('#skF_5', '#skF_6', C_66)) | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', C_66)) | ~r2_hidden(C_66, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_66, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_56, c_273])).
% 4.08/1.93  tff(c_378, plain, (![B_222]: (r2_hidden('#skF_3'('#skF_5', B_222), '#skF_6') | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_222))) | ~r2_hidden('#skF_3'('#skF_5', B_222), k2_pre_topc('#skF_5', '#skF_6')) | ~r1_waybel_0('#skF_5', '#skF_2'('#skF_5', B_222), '#skF_6') | ~l1_waybel_0('#skF_2'('#skF_5', B_222), '#skF_5') | ~v7_waybel_0('#skF_2'('#skF_5', B_222)) | ~v4_orders_2('#skF_2'('#skF_5', B_222)) | v2_struct_0('#skF_2'('#skF_5', B_222)) | ~m1_subset_1('#skF_3'('#skF_5', B_222), u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | v4_pre_topc(B_222, '#skF_5') | ~m1_subset_1(B_222, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_372, c_274])).
% 4.08/1.93  tff(c_385, plain, (![B_222]: (r2_hidden('#skF_3'('#skF_5', B_222), '#skF_6') | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_222))) | ~r2_hidden('#skF_3'('#skF_5', B_222), k2_pre_topc('#skF_5', '#skF_6')) | ~r1_waybel_0('#skF_5', '#skF_2'('#skF_5', B_222), '#skF_6') | ~l1_waybel_0('#skF_2'('#skF_5', B_222), '#skF_5') | ~v7_waybel_0('#skF_2'('#skF_5', B_222)) | ~v4_orders_2('#skF_2'('#skF_5', B_222)) | v2_struct_0('#skF_2'('#skF_5', B_222)) | ~m1_subset_1('#skF_3'('#skF_5', B_222), u1_struct_0('#skF_5')) | v4_pre_topc(B_222, '#skF_5') | ~m1_subset_1(B_222, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_378])).
% 4.08/1.93  tff(c_413, plain, (![B_234]: (r2_hidden('#skF_3'('#skF_5', B_234), '#skF_6') | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_234))) | ~r2_hidden('#skF_3'('#skF_5', B_234), k2_pre_topc('#skF_5', '#skF_6')) | ~r1_waybel_0('#skF_5', '#skF_2'('#skF_5', B_234), '#skF_6') | ~l1_waybel_0('#skF_2'('#skF_5', B_234), '#skF_5') | ~v7_waybel_0('#skF_2'('#skF_5', B_234)) | ~v4_orders_2('#skF_2'('#skF_5', B_234)) | v2_struct_0('#skF_2'('#skF_5', B_234)) | ~m1_subset_1('#skF_3'('#skF_5', B_234), u1_struct_0('#skF_5')) | v4_pre_topc(B_234, '#skF_5') | ~m1_subset_1(B_234, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_56, c_385])).
% 4.08/1.93  tff(c_417, plain, (![B_37]: (r2_hidden('#skF_3'('#skF_5', B_37), '#skF_6') | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_37))) | ~r1_waybel_0('#skF_5', '#skF_2'('#skF_5', B_37), '#skF_6') | ~l1_waybel_0('#skF_2'('#skF_5', B_37), '#skF_5') | ~v7_waybel_0('#skF_2'('#skF_5', B_37)) | ~v4_orders_2('#skF_2'('#skF_5', B_37)) | v2_struct_0('#skF_2'('#skF_5', B_37)) | ~m1_subset_1('#skF_3'('#skF_5', B_37), u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | v4_pre_topc(B_37, '#skF_5') | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_216, c_413])).
% 4.08/1.93  tff(c_420, plain, (![B_37]: (r2_hidden('#skF_3'('#skF_5', B_37), '#skF_6') | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_37))) | ~r1_waybel_0('#skF_5', '#skF_2'('#skF_5', B_37), '#skF_6') | ~l1_waybel_0('#skF_2'('#skF_5', B_37), '#skF_5') | ~v7_waybel_0('#skF_2'('#skF_5', B_37)) | ~v4_orders_2('#skF_2'('#skF_5', B_37)) | v2_struct_0('#skF_2'('#skF_5', B_37)) | ~m1_subset_1('#skF_3'('#skF_5', B_37), u1_struct_0('#skF_5')) | v4_pre_topc(B_37, '#skF_5') | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_417])).
% 4.08/1.93  tff(c_422, plain, (![B_235]: (r2_hidden('#skF_3'('#skF_5', B_235), '#skF_6') | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_235))) | ~r1_waybel_0('#skF_5', '#skF_2'('#skF_5', B_235), '#skF_6') | ~l1_waybel_0('#skF_2'('#skF_5', B_235), '#skF_5') | ~v7_waybel_0('#skF_2'('#skF_5', B_235)) | ~v4_orders_2('#skF_2'('#skF_5', B_235)) | v2_struct_0('#skF_2'('#skF_5', B_235)) | ~m1_subset_1('#skF_3'('#skF_5', B_235), u1_struct_0('#skF_5')) | v4_pre_topc(B_235, '#skF_5') | ~m1_subset_1(B_235, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_56, c_420])).
% 4.08/1.93  tff(c_426, plain, (![B_37]: (r2_hidden('#skF_3'('#skF_5', B_37), '#skF_6') | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_37))) | ~r1_waybel_0('#skF_5', '#skF_2'('#skF_5', B_37), '#skF_6') | ~l1_waybel_0('#skF_2'('#skF_5', B_37), '#skF_5') | ~v7_waybel_0('#skF_2'('#skF_5', B_37)) | ~v4_orders_2('#skF_2'('#skF_5', B_37)) | v2_struct_0('#skF_2'('#skF_5', B_37)) | v4_pre_topc(B_37, '#skF_5') | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_22, c_422])).
% 4.08/1.93  tff(c_429, plain, (![B_37]: (r2_hidden('#skF_3'('#skF_5', B_37), '#skF_6') | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_37))) | ~r1_waybel_0('#skF_5', '#skF_2'('#skF_5', B_37), '#skF_6') | ~l1_waybel_0('#skF_2'('#skF_5', B_37), '#skF_5') | ~v7_waybel_0('#skF_2'('#skF_5', B_37)) | ~v4_orders_2('#skF_2'('#skF_5', B_37)) | v2_struct_0('#skF_2'('#skF_5', B_37)) | v4_pre_topc(B_37, '#skF_5') | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_426])).
% 4.08/1.93  tff(c_431, plain, (![B_236]: (r2_hidden('#skF_3'('#skF_5', B_236), '#skF_6') | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_236))) | ~r1_waybel_0('#skF_5', '#skF_2'('#skF_5', B_236), '#skF_6') | ~l1_waybel_0('#skF_2'('#skF_5', B_236), '#skF_5') | ~v7_waybel_0('#skF_2'('#skF_5', B_236)) | ~v4_orders_2('#skF_2'('#skF_5', B_236)) | v2_struct_0('#skF_2'('#skF_5', B_236)) | v4_pre_topc(B_236, '#skF_5') | ~m1_subset_1(B_236, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_56, c_429])).
% 4.08/1.93  tff(c_434, plain, (r2_hidden('#skF_3'('#skF_5', '#skF_6'), '#skF_6') | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', '#skF_3'('#skF_5', '#skF_6'))) | ~r1_waybel_0('#skF_5', '#skF_2'('#skF_5', '#skF_6'), '#skF_6') | ~l1_waybel_0('#skF_2'('#skF_5', '#skF_6'), '#skF_5') | ~v7_waybel_0('#skF_2'('#skF_5', '#skF_6')) | ~v4_orders_2('#skF_2'('#skF_5', '#skF_6')) | v2_struct_0('#skF_2'('#skF_5', '#skF_6')) | v4_pre_topc('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_50, c_431])).
% 4.08/1.93  tff(c_437, plain, (r2_hidden('#skF_3'('#skF_5', '#skF_6'), '#skF_6') | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', '#skF_3'('#skF_5', '#skF_6'))) | v2_struct_0('#skF_2'('#skF_5', '#skF_6')) | v4_pre_topc('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_113, c_121, c_129, c_138, c_434])).
% 4.08/1.93  tff(c_438, plain, (r2_hidden('#skF_3'('#skF_5', '#skF_6'), '#skF_6') | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', '#skF_3'('#skF_5', '#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_97, c_105, c_437])).
% 4.08/1.93  tff(c_439, plain, (v1_xboole_0('#skF_4'('#skF_5', '#skF_6', '#skF_3'('#skF_5', '#skF_6')))), inference(splitLeft, [status(thm)], [c_438])).
% 4.08/1.93  tff(c_48, plain, (![A_48, B_60, C_66]: (~v1_xboole_0('#skF_4'(A_48, B_60, C_66)) | ~r2_hidden(C_66, k2_pre_topc(A_48, B_60)) | ~m1_subset_1(C_66, u1_struct_0(A_48)) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_48))) | ~l1_pre_topc(A_48) | ~v2_pre_topc(A_48) | v2_struct_0(A_48))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.08/1.93  tff(c_308, plain, (![A_188, B_190, B_189]: (~v1_xboole_0('#skF_4'(A_188, B_190, '#skF_3'(A_188, B_189))) | ~r1_waybel_0(A_188, '#skF_2'(A_188, B_189), B_190) | ~l1_waybel_0('#skF_2'(A_188, B_189), A_188) | ~v7_waybel_0('#skF_2'(A_188, B_189)) | ~v4_orders_2('#skF_2'(A_188, B_189)) | v2_struct_0('#skF_2'(A_188, B_189)) | ~m1_subset_1('#skF_3'(A_188, B_189), u1_struct_0(A_188)) | ~m1_subset_1(B_190, k1_zfmisc_1(u1_struct_0(A_188))) | v4_pre_topc(B_189, A_188) | ~m1_subset_1(B_189, k1_zfmisc_1(u1_struct_0(A_188))) | ~l1_pre_topc(A_188) | ~v2_pre_topc(A_188) | v2_struct_0(A_188))), inference(resolution, [status(thm)], [c_288, c_48])).
% 4.08/1.93  tff(c_441, plain, (~r1_waybel_0('#skF_5', '#skF_2'('#skF_5', '#skF_6'), '#skF_6') | ~l1_waybel_0('#skF_2'('#skF_5', '#skF_6'), '#skF_5') | ~v7_waybel_0('#skF_2'('#skF_5', '#skF_6')) | ~v4_orders_2('#skF_2'('#skF_5', '#skF_6')) | v2_struct_0('#skF_2'('#skF_5', '#skF_6')) | ~m1_subset_1('#skF_3'('#skF_5', '#skF_6'), u1_struct_0('#skF_5')) | v4_pre_topc('#skF_6', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_439, c_308])).
% 4.08/1.93  tff(c_444, plain, (v2_struct_0('#skF_2'('#skF_5', '#skF_6')) | ~m1_subset_1('#skF_3'('#skF_5', '#skF_6'), u1_struct_0('#skF_5')) | v4_pre_topc('#skF_6', '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_113, c_121, c_129, c_138, c_441])).
% 4.08/1.93  tff(c_445, plain, (~m1_subset_1('#skF_3'('#skF_5', '#skF_6'), u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_56, c_97, c_105, c_444])).
% 4.08/1.93  tff(c_455, plain, (v4_pre_topc('#skF_6', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_22, c_445])).
% 4.08/1.93  tff(c_458, plain, (v4_pre_topc('#skF_6', '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_455])).
% 4.08/1.93  tff(c_460, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_97, c_458])).
% 4.08/1.93  tff(c_461, plain, (r2_hidden('#skF_3'('#skF_5', '#skF_6'), '#skF_6')), inference(splitRight, [status(thm)], [c_438])).
% 4.08/1.93  tff(c_18, plain, (![A_23, B_37]: (~r2_hidden('#skF_3'(A_23, B_37), B_37) | v4_pre_topc(B_37, A_23) | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0(A_23))) | ~l1_pre_topc(A_23) | ~v2_pre_topc(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.08/1.93  tff(c_464, plain, (v4_pre_topc('#skF_6', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_461, c_18])).
% 4.08/1.93  tff(c_467, plain, (v4_pre_topc('#skF_6', '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_464])).
% 4.08/1.93  tff(c_469, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_97, c_467])).
% 4.08/1.93  tff(c_471, plain, (v4_pre_topc('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_74])).
% 4.08/1.93  tff(c_62, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~v4_pre_topc('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_150])).
% 4.08/1.93  tff(c_479, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_471, c_62])).
% 4.08/1.93  tff(c_64, plain, (r2_hidden('#skF_6', '#skF_7') | ~v4_pre_topc('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_150])).
% 4.08/1.93  tff(c_473, plain, (r2_hidden('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_471, c_64])).
% 4.08/1.93  tff(c_470, plain, (~v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_74])).
% 4.08/1.93  tff(c_72, plain, (v2_waybel_0('#skF_7', k3_yellow_1(k2_struct_0('#skF_5'))) | ~v4_pre_topc('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_150])).
% 4.08/1.93  tff(c_485, plain, (v2_waybel_0('#skF_7', k3_yellow_1(k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_471, c_72])).
% 4.08/1.93  tff(c_70, plain, (v13_waybel_0('#skF_7', k3_yellow_1(k2_struct_0('#skF_5'))) | ~v4_pre_topc('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_150])).
% 4.08/1.93  tff(c_481, plain, (v13_waybel_0('#skF_7', k3_yellow_1(k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_471, c_70])).
% 4.08/1.93  tff(c_68, plain, (v3_waybel_7('#skF_7', k3_yellow_1(k2_struct_0('#skF_5'))) | ~v4_pre_topc('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_150])).
% 4.08/1.93  tff(c_483, plain, (v3_waybel_7('#skF_7', k3_yellow_1(k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_471, c_68])).
% 4.08/1.93  tff(c_66, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))) | ~v4_pre_topc('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_150])).
% 4.08/1.93  tff(c_487, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))))), inference(demodulation, [status(thm), theory('equality')], [c_471, c_66])).
% 4.08/1.93  tff(c_60, plain, (r2_waybel_7('#skF_5', '#skF_7', '#skF_8') | ~v4_pre_topc('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_150])).
% 4.08/1.93  tff(c_477, plain, (r2_waybel_7('#skF_5', '#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_471, c_60])).
% 4.08/1.93  tff(c_660, plain, (![C_315, A_316, B_317, D_318]: (r2_hidden(C_315, k2_pre_topc(A_316, B_317)) | ~r2_waybel_7(A_316, D_318, C_315) | ~r2_hidden(B_317, D_318) | ~m1_subset_1(D_318, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_316))))) | ~v3_waybel_7(D_318, k3_yellow_1(k2_struct_0(A_316))) | ~v13_waybel_0(D_318, k3_yellow_1(k2_struct_0(A_316))) | ~v2_waybel_0(D_318, k3_yellow_1(k2_struct_0(A_316))) | v1_xboole_0(D_318) | ~m1_subset_1(C_315, u1_struct_0(A_316)) | ~m1_subset_1(B_317, k1_zfmisc_1(u1_struct_0(A_316))) | ~l1_pre_topc(A_316) | ~v2_pre_topc(A_316) | v2_struct_0(A_316))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.08/1.93  tff(c_664, plain, (![B_317]: (r2_hidden('#skF_8', k2_pre_topc('#skF_5', B_317)) | ~r2_hidden(B_317, '#skF_7') | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))) | ~v3_waybel_7('#skF_7', k3_yellow_1(k2_struct_0('#skF_5'))) | ~v13_waybel_0('#skF_7', k3_yellow_1(k2_struct_0('#skF_5'))) | ~v2_waybel_0('#skF_7', k3_yellow_1(k2_struct_0('#skF_5'))) | v1_xboole_0('#skF_7') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1(B_317, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_477, c_660])).
% 4.08/1.93  tff(c_671, plain, (![B_317]: (r2_hidden('#skF_8', k2_pre_topc('#skF_5', B_317)) | ~r2_hidden(B_317, '#skF_7') | v1_xboole_0('#skF_7') | ~m1_subset_1(B_317, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_479, c_485, c_481, c_483, c_487, c_664])).
% 4.08/1.93  tff(c_673, plain, (![B_319]: (r2_hidden('#skF_8', k2_pre_topc('#skF_5', B_319)) | ~r2_hidden(B_319, '#skF_7') | ~m1_subset_1(B_319, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_56, c_470, c_671])).
% 4.08/1.93  tff(c_676, plain, (r2_hidden('#skF_8', k2_pre_topc('#skF_5', '#skF_6')) | ~r2_hidden('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_50, c_673])).
% 4.08/1.93  tff(c_679, plain, (r2_hidden('#skF_8', k2_pre_topc('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_473, c_676])).
% 4.08/1.93  tff(c_14, plain, (![A_1, B_13, C_19]: (~v2_struct_0('#skF_1'(A_1, B_13, C_19)) | ~r2_hidden(C_19, k2_pre_topc(A_1, B_13)) | ~m1_subset_1(C_19, u1_struct_0(A_1)) | ~m1_subset_1(B_13, k1_zfmisc_1(u1_struct_0(A_1))) | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.08/1.93  tff(c_690, plain, (~v2_struct_0('#skF_1'('#skF_5', '#skF_6', '#skF_8')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_679, c_14])).
% 4.08/1.93  tff(c_713, plain, (~v2_struct_0('#skF_1'('#skF_5', '#skF_6', '#skF_8')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_479, c_690])).
% 4.08/1.93  tff(c_714, plain, (~v2_struct_0('#skF_1'('#skF_5', '#skF_6', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_56, c_713])).
% 4.08/1.93  tff(c_12, plain, (![A_1, B_13, C_19]: (v4_orders_2('#skF_1'(A_1, B_13, C_19)) | ~r2_hidden(C_19, k2_pre_topc(A_1, B_13)) | ~m1_subset_1(C_19, u1_struct_0(A_1)) | ~m1_subset_1(B_13, k1_zfmisc_1(u1_struct_0(A_1))) | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.08/1.93  tff(c_692, plain, (v4_orders_2('#skF_1'('#skF_5', '#skF_6', '#skF_8')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_679, c_12])).
% 4.08/1.93  tff(c_717, plain, (v4_orders_2('#skF_1'('#skF_5', '#skF_6', '#skF_8')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_479, c_692])).
% 4.08/1.93  tff(c_718, plain, (v4_orders_2('#skF_1'('#skF_5', '#skF_6', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_56, c_717])).
% 4.08/1.93  tff(c_10, plain, (![A_1, B_13, C_19]: (v7_waybel_0('#skF_1'(A_1, B_13, C_19)) | ~r2_hidden(C_19, k2_pre_topc(A_1, B_13)) | ~m1_subset_1(C_19, u1_struct_0(A_1)) | ~m1_subset_1(B_13, k1_zfmisc_1(u1_struct_0(A_1))) | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.08/1.93  tff(c_688, plain, (v7_waybel_0('#skF_1'('#skF_5', '#skF_6', '#skF_8')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_679, c_10])).
% 4.08/1.93  tff(c_709, plain, (v7_waybel_0('#skF_1'('#skF_5', '#skF_6', '#skF_8')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_479, c_688])).
% 4.08/1.93  tff(c_710, plain, (v7_waybel_0('#skF_1'('#skF_5', '#skF_6', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_56, c_709])).
% 4.08/1.93  tff(c_8, plain, (![A_1, B_13, C_19]: (l1_waybel_0('#skF_1'(A_1, B_13, C_19), A_1) | ~r2_hidden(C_19, k2_pre_topc(A_1, B_13)) | ~m1_subset_1(C_19, u1_struct_0(A_1)) | ~m1_subset_1(B_13, k1_zfmisc_1(u1_struct_0(A_1))) | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.08/1.93  tff(c_686, plain, (l1_waybel_0('#skF_1'('#skF_5', '#skF_6', '#skF_8'), '#skF_5') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_679, c_8])).
% 4.08/1.93  tff(c_705, plain, (l1_waybel_0('#skF_1'('#skF_5', '#skF_6', '#skF_8'), '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_479, c_686])).
% 4.08/1.93  tff(c_706, plain, (l1_waybel_0('#skF_1'('#skF_5', '#skF_6', '#skF_8'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_56, c_705])).
% 4.08/1.93  tff(c_58, plain, (~r2_hidden('#skF_8', '#skF_6') | ~v4_pre_topc('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_150])).
% 4.08/1.93  tff(c_475, plain, (~r2_hidden('#skF_8', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_471, c_58])).
% 4.08/1.93  tff(c_566, plain, (![A_279, B_280, C_281]: (r1_waybel_0(A_279, '#skF_1'(A_279, B_280, C_281), B_280) | ~r2_hidden(C_281, k2_pre_topc(A_279, B_280)) | ~m1_subset_1(C_281, u1_struct_0(A_279)) | ~m1_subset_1(B_280, k1_zfmisc_1(u1_struct_0(A_279))) | ~l1_pre_topc(A_279) | ~v2_pre_topc(A_279) | v2_struct_0(A_279))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.08/1.93  tff(c_570, plain, (![C_281]: (r1_waybel_0('#skF_5', '#skF_1'('#skF_5', '#skF_6', C_281), '#skF_6') | ~r2_hidden(C_281, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_281, u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_50, c_566])).
% 4.08/1.93  tff(c_574, plain, (![C_281]: (r1_waybel_0('#skF_5', '#skF_1'('#skF_5', '#skF_6', C_281), '#skF_6') | ~r2_hidden(C_281, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_281, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_570])).
% 4.08/1.93  tff(c_575, plain, (![C_281]: (r1_waybel_0('#skF_5', '#skF_1'('#skF_5', '#skF_6', C_281), '#skF_6') | ~r2_hidden(C_281, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_281, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_56, c_574])).
% 4.08/1.93  tff(c_555, plain, (![A_275, B_276, C_277]: (r3_waybel_9(A_275, '#skF_1'(A_275, B_276, C_277), C_277) | ~r2_hidden(C_277, k2_pre_topc(A_275, B_276)) | ~m1_subset_1(C_277, u1_struct_0(A_275)) | ~m1_subset_1(B_276, k1_zfmisc_1(u1_struct_0(A_275))) | ~l1_pre_topc(A_275) | ~v2_pre_topc(A_275) | v2_struct_0(A_275))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.08/1.93  tff(c_559, plain, (![C_277]: (r3_waybel_9('#skF_5', '#skF_1'('#skF_5', '#skF_6', C_277), C_277) | ~r2_hidden(C_277, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_277, u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_50, c_555])).
% 4.08/1.93  tff(c_563, plain, (![C_277]: (r3_waybel_9('#skF_5', '#skF_1'('#skF_5', '#skF_6', C_277), C_277) | ~r2_hidden(C_277, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_277, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_559])).
% 4.08/1.93  tff(c_564, plain, (![C_277]: (r3_waybel_9('#skF_5', '#skF_1'('#skF_5', '#skF_6', C_277), C_277) | ~r2_hidden(C_277, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_277, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_56, c_563])).
% 4.08/1.93  tff(c_630, plain, (![D_303, B_304, A_305, C_306]: (r2_hidden(D_303, B_304) | ~r3_waybel_9(A_305, C_306, D_303) | ~m1_subset_1(D_303, u1_struct_0(A_305)) | ~r1_waybel_0(A_305, C_306, B_304) | ~l1_waybel_0(C_306, A_305) | ~v7_waybel_0(C_306) | ~v4_orders_2(C_306) | v2_struct_0(C_306) | ~v4_pre_topc(B_304, A_305) | ~m1_subset_1(B_304, k1_zfmisc_1(u1_struct_0(A_305))) | ~l1_pre_topc(A_305) | ~v2_pre_topc(A_305) | v2_struct_0(A_305))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.08/1.93  tff(c_632, plain, (![C_277, B_304]: (r2_hidden(C_277, B_304) | ~r1_waybel_0('#skF_5', '#skF_1'('#skF_5', '#skF_6', C_277), B_304) | ~l1_waybel_0('#skF_1'('#skF_5', '#skF_6', C_277), '#skF_5') | ~v7_waybel_0('#skF_1'('#skF_5', '#skF_6', C_277)) | ~v4_orders_2('#skF_1'('#skF_5', '#skF_6', C_277)) | v2_struct_0('#skF_1'('#skF_5', '#skF_6', C_277)) | ~v4_pre_topc(B_304, '#skF_5') | ~m1_subset_1(B_304, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~r2_hidden(C_277, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_277, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_564, c_630])).
% 4.08/1.93  tff(c_637, plain, (![C_277, B_304]: (r2_hidden(C_277, B_304) | ~r1_waybel_0('#skF_5', '#skF_1'('#skF_5', '#skF_6', C_277), B_304) | ~l1_waybel_0('#skF_1'('#skF_5', '#skF_6', C_277), '#skF_5') | ~v7_waybel_0('#skF_1'('#skF_5', '#skF_6', C_277)) | ~v4_orders_2('#skF_1'('#skF_5', '#skF_6', C_277)) | v2_struct_0('#skF_1'('#skF_5', '#skF_6', C_277)) | ~v4_pre_topc(B_304, '#skF_5') | ~m1_subset_1(B_304, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5') | ~r2_hidden(C_277, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_277, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_632])).
% 4.08/1.93  tff(c_652, plain, (![C_309, B_310]: (r2_hidden(C_309, B_310) | ~r1_waybel_0('#skF_5', '#skF_1'('#skF_5', '#skF_6', C_309), B_310) | ~l1_waybel_0('#skF_1'('#skF_5', '#skF_6', C_309), '#skF_5') | ~v7_waybel_0('#skF_1'('#skF_5', '#skF_6', C_309)) | ~v4_orders_2('#skF_1'('#skF_5', '#skF_6', C_309)) | v2_struct_0('#skF_1'('#skF_5', '#skF_6', C_309)) | ~v4_pre_topc(B_310, '#skF_5') | ~m1_subset_1(B_310, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r2_hidden(C_309, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_309, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_56, c_637])).
% 4.08/1.93  tff(c_654, plain, (![C_281]: (r2_hidden(C_281, '#skF_6') | ~l1_waybel_0('#skF_1'('#skF_5', '#skF_6', C_281), '#skF_5') | ~v7_waybel_0('#skF_1'('#skF_5', '#skF_6', C_281)) | ~v4_orders_2('#skF_1'('#skF_5', '#skF_6', C_281)) | v2_struct_0('#skF_1'('#skF_5', '#skF_6', C_281)) | ~v4_pre_topc('#skF_6', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r2_hidden(C_281, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_281, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_575, c_652])).
% 4.08/1.93  tff(c_657, plain, (![C_281]: (r2_hidden(C_281, '#skF_6') | ~l1_waybel_0('#skF_1'('#skF_5', '#skF_6', C_281), '#skF_5') | ~v7_waybel_0('#skF_1'('#skF_5', '#skF_6', C_281)) | ~v4_orders_2('#skF_1'('#skF_5', '#skF_6', C_281)) | v2_struct_0('#skF_1'('#skF_5', '#skF_6', C_281)) | ~r2_hidden(C_281, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_281, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_471, c_654])).
% 4.08/1.93  tff(c_682, plain, (r2_hidden('#skF_8', '#skF_6') | ~l1_waybel_0('#skF_1'('#skF_5', '#skF_6', '#skF_8'), '#skF_5') | ~v7_waybel_0('#skF_1'('#skF_5', '#skF_6', '#skF_8')) | ~v4_orders_2('#skF_1'('#skF_5', '#skF_6', '#skF_8')) | v2_struct_0('#skF_1'('#skF_5', '#skF_6', '#skF_8')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_679, c_657])).
% 4.08/1.93  tff(c_697, plain, (r2_hidden('#skF_8', '#skF_6') | ~l1_waybel_0('#skF_1'('#skF_5', '#skF_6', '#skF_8'), '#skF_5') | ~v7_waybel_0('#skF_1'('#skF_5', '#skF_6', '#skF_8')) | ~v4_orders_2('#skF_1'('#skF_5', '#skF_6', '#skF_8')) | v2_struct_0('#skF_1'('#skF_5', '#skF_6', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_479, c_682])).
% 4.08/1.93  tff(c_698, plain, (~l1_waybel_0('#skF_1'('#skF_5', '#skF_6', '#skF_8'), '#skF_5') | ~v7_waybel_0('#skF_1'('#skF_5', '#skF_6', '#skF_8')) | ~v4_orders_2('#skF_1'('#skF_5', '#skF_6', '#skF_8')) | v2_struct_0('#skF_1'('#skF_5', '#skF_6', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_475, c_697])).
% 4.08/1.93  tff(c_724, plain, (v2_struct_0('#skF_1'('#skF_5', '#skF_6', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_718, c_710, c_706, c_698])).
% 4.08/1.93  tff(c_725, plain, $false, inference(negUnitSimplification, [status(thm)], [c_714, c_724])).
% 4.08/1.93  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.08/1.93  
% 4.08/1.93  Inference rules
% 4.08/1.93  ----------------------
% 4.08/1.93  #Ref     : 0
% 4.08/1.93  #Sup     : 101
% 4.08/1.93  #Fact    : 0
% 4.08/1.93  #Define  : 0
% 4.08/1.93  #Split   : 5
% 4.08/1.93  #Chain   : 0
% 4.08/1.93  #Close   : 0
% 4.08/1.93  
% 4.08/1.93  Ordering : KBO
% 4.08/1.93  
% 4.08/1.93  Simplification rules
% 4.08/1.93  ----------------------
% 4.08/1.93  #Subsume      : 36
% 4.08/1.93  #Demod        : 170
% 4.08/1.93  #Tautology    : 18
% 4.08/1.93  #SimpNegUnit  : 51
% 4.08/1.93  #BackRed      : 0
% 4.08/1.93  
% 4.08/1.93  #Partial instantiations: 0
% 4.08/1.93  #Strategies tried      : 1
% 4.08/1.93  
% 4.08/1.93  Timing (in seconds)
% 4.08/1.93  ----------------------
% 4.08/1.94  Preprocessing        : 0.55
% 4.08/1.94  Parsing              : 0.28
% 4.08/1.94  CNF conversion       : 0.06
% 4.08/1.94  Main loop            : 0.48
% 4.08/1.94  Inferencing          : 0.19
% 4.08/1.94  Reduction            : 0.14
% 4.08/1.94  Demodulation         : 0.09
% 4.08/1.94  BG Simplification    : 0.05
% 4.08/1.94  Subsumption          : 0.10
% 4.08/1.94  Abstraction          : 0.02
% 4.08/1.94  MUC search           : 0.00
% 4.08/1.94  Cooper               : 0.00
% 4.08/1.94  Total                : 1.09
% 4.08/1.94  Index Insertion      : 0.00
% 4.08/1.94  Index Deletion       : 0.00
% 4.08/1.94  Index Matching       : 0.00
% 4.08/1.94  BG Taut test         : 0.00
%------------------------------------------------------------------------------
