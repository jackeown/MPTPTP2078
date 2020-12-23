%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:38 EST 2020

% Result     : Theorem 3.53s
% Output     : CNFRefutation 3.89s
% Verified   : 
% Statistics : Number of formulae       :  185 (1584 expanded)
%              Number of leaves         :   31 ( 583 expanded)
%              Depth                    :   25
%              Number of atoms          :  907 (10719 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   19 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_waybel_9 > r1_waybel_0 > v4_pre_topc > v3_yellow_6 > r2_hidden > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k2_pre_topc > k10_yellow_6 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_4

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

tff(k10_yellow_6,type,(
    k10_yellow_6: ( $i * $i ) > $i )).

tff(v3_yellow_6,type,(
    v3_yellow_6: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v7_waybel_0,type,(
    v7_waybel_0: $i > $o )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

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

tff(f_116,axiom,(
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

tff(f_85,axiom,(
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
    ( ~ v2_struct_0('#skF_7')
    | ~ v4_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_97,plain,(
    ~ v4_pre_topc('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_38,plain,(
    ! [A_45,B_59] :
      ( m1_subset_1('#skF_4'(A_45,B_59),u1_struct_0(A_45))
      | v4_pre_topc(B_59,A_45)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ l1_pre_topc(A_45)
      | ~ v2_pre_topc(A_45)
      | v2_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_98,plain,(
    ! [A_93,B_94] :
      ( ~ v2_struct_0('#skF_3'(A_93,B_94))
      | v4_pre_topc(B_94,A_93)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ l1_pre_topc(A_93)
      | ~ v2_pre_topc(A_93)
      | v2_struct_0(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_101,plain,
    ( ~ v2_struct_0('#skF_3'('#skF_5','#skF_6'))
    | v4_pre_topc('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_98])).

tff(c_104,plain,
    ( ~ v2_struct_0('#skF_3'('#skF_5','#skF_6'))
    | v4_pre_topc('#skF_6','#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_101])).

tff(c_105,plain,(
    ~ v2_struct_0('#skF_3'('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_97,c_104])).

tff(c_106,plain,(
    ! [A_95,B_96] :
      ( v4_orders_2('#skF_3'(A_95,B_96))
      | v4_pre_topc(B_96,A_95)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ l1_pre_topc(A_95)
      | ~ v2_pre_topc(A_95)
      | v2_struct_0(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_109,plain,
    ( v4_orders_2('#skF_3'('#skF_5','#skF_6'))
    | v4_pre_topc('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_106])).

tff(c_112,plain,
    ( v4_orders_2('#skF_3'('#skF_5','#skF_6'))
    | v4_pre_topc('#skF_6','#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_109])).

tff(c_113,plain,(
    v4_orders_2('#skF_3'('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_97,c_112])).

tff(c_114,plain,(
    ! [A_97,B_98] :
      ( v7_waybel_0('#skF_3'(A_97,B_98))
      | v4_pre_topc(B_98,A_97)
      | ~ m1_subset_1(B_98,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ l1_pre_topc(A_97)
      | ~ v2_pre_topc(A_97)
      | v2_struct_0(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_117,plain,
    ( v7_waybel_0('#skF_3'('#skF_5','#skF_6'))
    | v4_pre_topc('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_114])).

tff(c_120,plain,
    ( v7_waybel_0('#skF_3'('#skF_5','#skF_6'))
    | v4_pre_topc('#skF_6','#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_117])).

tff(c_121,plain,(
    v7_waybel_0('#skF_3'('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_97,c_120])).

tff(c_123,plain,(
    ! [A_99,B_100] :
      ( l1_waybel_0('#skF_3'(A_99,B_100),A_99)
      | v4_pre_topc(B_100,A_99)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ l1_pre_topc(A_99)
      | ~ v2_pre_topc(A_99)
      | v2_struct_0(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_125,plain,
    ( l1_waybel_0('#skF_3'('#skF_5','#skF_6'),'#skF_5')
    | v4_pre_topc('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_123])).

tff(c_128,plain,
    ( l1_waybel_0('#skF_3'('#skF_5','#skF_6'),'#skF_5')
    | v4_pre_topc('#skF_6','#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_125])).

tff(c_129,plain,(
    l1_waybel_0('#skF_3'('#skF_5','#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_97,c_128])).

tff(c_132,plain,(
    ! [A_105,B_106] :
      ( r1_waybel_0(A_105,'#skF_3'(A_105,B_106),B_106)
      | v4_pre_topc(B_106,A_105)
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ l1_pre_topc(A_105)
      | ~ v2_pre_topc(A_105)
      | v2_struct_0(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_134,plain,
    ( r1_waybel_0('#skF_5','#skF_3'('#skF_5','#skF_6'),'#skF_6')
    | v4_pre_topc('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_132])).

tff(c_137,plain,
    ( r1_waybel_0('#skF_5','#skF_3'('#skF_5','#skF_6'),'#skF_6')
    | v4_pre_topc('#skF_6','#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_134])).

tff(c_138,plain,(
    r1_waybel_0('#skF_5','#skF_3'('#skF_5','#skF_6'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_97,c_137])).

tff(c_36,plain,(
    ! [A_45,B_59] :
      ( r3_waybel_9(A_45,'#skF_3'(A_45,B_59),'#skF_4'(A_45,B_59))
      | v4_pre_topc(B_59,A_45)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ l1_pre_topc(A_45)
      | ~ v2_pre_topc(A_45)
      | v2_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_196,plain,(
    ! [C_154,A_155,B_156,D_157] :
      ( r2_hidden(C_154,k2_pre_topc(A_155,B_156))
      | ~ r3_waybel_9(A_155,D_157,C_154)
      | ~ r1_waybel_0(A_155,D_157,B_156)
      | ~ l1_waybel_0(D_157,A_155)
      | ~ v7_waybel_0(D_157)
      | ~ v4_orders_2(D_157)
      | v2_struct_0(D_157)
      | ~ m1_subset_1(C_154,u1_struct_0(A_155))
      | ~ m1_subset_1(B_156,k1_zfmisc_1(u1_struct_0(A_155)))
      | ~ l1_pre_topc(A_155)
      | ~ v2_pre_topc(A_155)
      | v2_struct_0(A_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_244,plain,(
    ! [A_174,B_175,B_176] :
      ( r2_hidden('#skF_4'(A_174,B_175),k2_pre_topc(A_174,B_176))
      | ~ r1_waybel_0(A_174,'#skF_3'(A_174,B_175),B_176)
      | ~ l1_waybel_0('#skF_3'(A_174,B_175),A_174)
      | ~ v7_waybel_0('#skF_3'(A_174,B_175))
      | ~ v4_orders_2('#skF_3'(A_174,B_175))
      | v2_struct_0('#skF_3'(A_174,B_175))
      | ~ m1_subset_1('#skF_4'(A_174,B_175),u1_struct_0(A_174))
      | ~ m1_subset_1(B_176,k1_zfmisc_1(u1_struct_0(A_174)))
      | v4_pre_topc(B_175,A_174)
      | ~ m1_subset_1(B_175,k1_zfmisc_1(u1_struct_0(A_174)))
      | ~ l1_pre_topc(A_174)
      | ~ v2_pre_topc(A_174)
      | v2_struct_0(A_174) ) ),
    inference(resolution,[status(thm)],[c_36,c_196])).

tff(c_28,plain,(
    ! [A_23,B_35,C_41] :
      ( v4_orders_2('#skF_2'(A_23,B_35,C_41))
      | ~ r2_hidden(C_41,k2_pre_topc(A_23,B_35))
      | ~ m1_subset_1(C_41,u1_struct_0(A_23))
      | ~ m1_subset_1(B_35,k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_341,plain,(
    ! [A_204,B_205,B_206] :
      ( v4_orders_2('#skF_2'(A_204,B_205,'#skF_4'(A_204,B_206)))
      | ~ r1_waybel_0(A_204,'#skF_3'(A_204,B_206),B_205)
      | ~ l1_waybel_0('#skF_3'(A_204,B_206),A_204)
      | ~ v7_waybel_0('#skF_3'(A_204,B_206))
      | ~ v4_orders_2('#skF_3'(A_204,B_206))
      | v2_struct_0('#skF_3'(A_204,B_206))
      | ~ m1_subset_1('#skF_4'(A_204,B_206),u1_struct_0(A_204))
      | ~ m1_subset_1(B_205,k1_zfmisc_1(u1_struct_0(A_204)))
      | v4_pre_topc(B_206,A_204)
      | ~ m1_subset_1(B_206,k1_zfmisc_1(u1_struct_0(A_204)))
      | ~ l1_pre_topc(A_204)
      | ~ v2_pre_topc(A_204)
      | v2_struct_0(A_204) ) ),
    inference(resolution,[status(thm)],[c_244,c_28])).

tff(c_345,plain,(
    ! [A_207,B_208,B_209] :
      ( v4_orders_2('#skF_2'(A_207,B_208,'#skF_4'(A_207,B_209)))
      | ~ r1_waybel_0(A_207,'#skF_3'(A_207,B_209),B_208)
      | ~ l1_waybel_0('#skF_3'(A_207,B_209),A_207)
      | ~ v7_waybel_0('#skF_3'(A_207,B_209))
      | ~ v4_orders_2('#skF_3'(A_207,B_209))
      | v2_struct_0('#skF_3'(A_207,B_209))
      | ~ m1_subset_1(B_208,k1_zfmisc_1(u1_struct_0(A_207)))
      | v4_pre_topc(B_209,A_207)
      | ~ m1_subset_1(B_209,k1_zfmisc_1(u1_struct_0(A_207)))
      | ~ l1_pre_topc(A_207)
      | ~ v2_pre_topc(A_207)
      | v2_struct_0(A_207) ) ),
    inference(resolution,[status(thm)],[c_38,c_341])).

tff(c_347,plain,(
    ! [B_209] :
      ( v4_orders_2('#skF_2'('#skF_5','#skF_6','#skF_4'('#skF_5',B_209)))
      | ~ r1_waybel_0('#skF_5','#skF_3'('#skF_5',B_209),'#skF_6')
      | ~ l1_waybel_0('#skF_3'('#skF_5',B_209),'#skF_5')
      | ~ v7_waybel_0('#skF_3'('#skF_5',B_209))
      | ~ v4_orders_2('#skF_3'('#skF_5',B_209))
      | v2_struct_0('#skF_3'('#skF_5',B_209))
      | v4_pre_topc(B_209,'#skF_5')
      | ~ m1_subset_1(B_209,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_50,c_345])).

tff(c_350,plain,(
    ! [B_209] :
      ( v4_orders_2('#skF_2'('#skF_5','#skF_6','#skF_4'('#skF_5',B_209)))
      | ~ r1_waybel_0('#skF_5','#skF_3'('#skF_5',B_209),'#skF_6')
      | ~ l1_waybel_0('#skF_3'('#skF_5',B_209),'#skF_5')
      | ~ v7_waybel_0('#skF_3'('#skF_5',B_209))
      | ~ v4_orders_2('#skF_3'('#skF_5',B_209))
      | v2_struct_0('#skF_3'('#skF_5',B_209))
      | v4_pre_topc(B_209,'#skF_5')
      | ~ m1_subset_1(B_209,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_347])).

tff(c_352,plain,(
    ! [B_210] :
      ( v4_orders_2('#skF_2'('#skF_5','#skF_6','#skF_4'('#skF_5',B_210)))
      | ~ r1_waybel_0('#skF_5','#skF_3'('#skF_5',B_210),'#skF_6')
      | ~ l1_waybel_0('#skF_3'('#skF_5',B_210),'#skF_5')
      | ~ v7_waybel_0('#skF_3'('#skF_5',B_210))
      | ~ v4_orders_2('#skF_3'('#skF_5',B_210))
      | v2_struct_0('#skF_3'('#skF_5',B_210))
      | v4_pre_topc(B_210,'#skF_5')
      | ~ m1_subset_1(B_210,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_350])).

tff(c_355,plain,
    ( v4_orders_2('#skF_2'('#skF_5','#skF_6','#skF_4'('#skF_5','#skF_6')))
    | ~ r1_waybel_0('#skF_5','#skF_3'('#skF_5','#skF_6'),'#skF_6')
    | ~ l1_waybel_0('#skF_3'('#skF_5','#skF_6'),'#skF_5')
    | ~ v7_waybel_0('#skF_3'('#skF_5','#skF_6'))
    | ~ v4_orders_2('#skF_3'('#skF_5','#skF_6'))
    | v2_struct_0('#skF_3'('#skF_5','#skF_6'))
    | v4_pre_topc('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_352])).

tff(c_358,plain,
    ( v4_orders_2('#skF_2'('#skF_5','#skF_6','#skF_4'('#skF_5','#skF_6')))
    | v2_struct_0('#skF_3'('#skF_5','#skF_6'))
    | v4_pre_topc('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_121,c_129,c_138,c_355])).

tff(c_359,plain,(
    v4_orders_2('#skF_2'('#skF_5','#skF_6','#skF_4'('#skF_5','#skF_6'))) ),
    inference(negUnitSimplification,[status(thm)],[c_97,c_105,c_358])).

tff(c_26,plain,(
    ! [A_23,B_35,C_41] :
      ( v7_waybel_0('#skF_2'(A_23,B_35,C_41))
      | ~ r2_hidden(C_41,k2_pre_topc(A_23,B_35))
      | ~ m1_subset_1(C_41,u1_struct_0(A_23))
      | ~ m1_subset_1(B_35,k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_367,plain,(
    ! [A_215,B_216,B_217] :
      ( v7_waybel_0('#skF_2'(A_215,B_216,'#skF_4'(A_215,B_217)))
      | ~ r1_waybel_0(A_215,'#skF_3'(A_215,B_217),B_216)
      | ~ l1_waybel_0('#skF_3'(A_215,B_217),A_215)
      | ~ v7_waybel_0('#skF_3'(A_215,B_217))
      | ~ v4_orders_2('#skF_3'(A_215,B_217))
      | v2_struct_0('#skF_3'(A_215,B_217))
      | ~ m1_subset_1('#skF_4'(A_215,B_217),u1_struct_0(A_215))
      | ~ m1_subset_1(B_216,k1_zfmisc_1(u1_struct_0(A_215)))
      | v4_pre_topc(B_217,A_215)
      | ~ m1_subset_1(B_217,k1_zfmisc_1(u1_struct_0(A_215)))
      | ~ l1_pre_topc(A_215)
      | ~ v2_pre_topc(A_215)
      | v2_struct_0(A_215) ) ),
    inference(resolution,[status(thm)],[c_244,c_26])).

tff(c_371,plain,(
    ! [A_218,B_219,B_220] :
      ( v7_waybel_0('#skF_2'(A_218,B_219,'#skF_4'(A_218,B_220)))
      | ~ r1_waybel_0(A_218,'#skF_3'(A_218,B_220),B_219)
      | ~ l1_waybel_0('#skF_3'(A_218,B_220),A_218)
      | ~ v7_waybel_0('#skF_3'(A_218,B_220))
      | ~ v4_orders_2('#skF_3'(A_218,B_220))
      | v2_struct_0('#skF_3'(A_218,B_220))
      | ~ m1_subset_1(B_219,k1_zfmisc_1(u1_struct_0(A_218)))
      | v4_pre_topc(B_220,A_218)
      | ~ m1_subset_1(B_220,k1_zfmisc_1(u1_struct_0(A_218)))
      | ~ l1_pre_topc(A_218)
      | ~ v2_pre_topc(A_218)
      | v2_struct_0(A_218) ) ),
    inference(resolution,[status(thm)],[c_38,c_367])).

tff(c_373,plain,(
    ! [B_220] :
      ( v7_waybel_0('#skF_2'('#skF_5','#skF_6','#skF_4'('#skF_5',B_220)))
      | ~ r1_waybel_0('#skF_5','#skF_3'('#skF_5',B_220),'#skF_6')
      | ~ l1_waybel_0('#skF_3'('#skF_5',B_220),'#skF_5')
      | ~ v7_waybel_0('#skF_3'('#skF_5',B_220))
      | ~ v4_orders_2('#skF_3'('#skF_5',B_220))
      | v2_struct_0('#skF_3'('#skF_5',B_220))
      | v4_pre_topc(B_220,'#skF_5')
      | ~ m1_subset_1(B_220,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_50,c_371])).

tff(c_376,plain,(
    ! [B_220] :
      ( v7_waybel_0('#skF_2'('#skF_5','#skF_6','#skF_4'('#skF_5',B_220)))
      | ~ r1_waybel_0('#skF_5','#skF_3'('#skF_5',B_220),'#skF_6')
      | ~ l1_waybel_0('#skF_3'('#skF_5',B_220),'#skF_5')
      | ~ v7_waybel_0('#skF_3'('#skF_5',B_220))
      | ~ v4_orders_2('#skF_3'('#skF_5',B_220))
      | v2_struct_0('#skF_3'('#skF_5',B_220))
      | v4_pre_topc(B_220,'#skF_5')
      | ~ m1_subset_1(B_220,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_373])).

tff(c_378,plain,(
    ! [B_221] :
      ( v7_waybel_0('#skF_2'('#skF_5','#skF_6','#skF_4'('#skF_5',B_221)))
      | ~ r1_waybel_0('#skF_5','#skF_3'('#skF_5',B_221),'#skF_6')
      | ~ l1_waybel_0('#skF_3'('#skF_5',B_221),'#skF_5')
      | ~ v7_waybel_0('#skF_3'('#skF_5',B_221))
      | ~ v4_orders_2('#skF_3'('#skF_5',B_221))
      | v2_struct_0('#skF_3'('#skF_5',B_221))
      | v4_pre_topc(B_221,'#skF_5')
      | ~ m1_subset_1(B_221,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_376])).

tff(c_381,plain,
    ( v7_waybel_0('#skF_2'('#skF_5','#skF_6','#skF_4'('#skF_5','#skF_6')))
    | ~ r1_waybel_0('#skF_5','#skF_3'('#skF_5','#skF_6'),'#skF_6')
    | ~ l1_waybel_0('#skF_3'('#skF_5','#skF_6'),'#skF_5')
    | ~ v7_waybel_0('#skF_3'('#skF_5','#skF_6'))
    | ~ v4_orders_2('#skF_3'('#skF_5','#skF_6'))
    | v2_struct_0('#skF_3'('#skF_5','#skF_6'))
    | v4_pre_topc('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_378])).

tff(c_384,plain,
    ( v7_waybel_0('#skF_2'('#skF_5','#skF_6','#skF_4'('#skF_5','#skF_6')))
    | v2_struct_0('#skF_3'('#skF_5','#skF_6'))
    | v4_pre_topc('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_121,c_129,c_138,c_381])).

tff(c_385,plain,(
    v7_waybel_0('#skF_2'('#skF_5','#skF_6','#skF_4'('#skF_5','#skF_6'))) ),
    inference(negUnitSimplification,[status(thm)],[c_97,c_105,c_384])).

tff(c_22,plain,(
    ! [A_23,B_35,C_41] :
      ( l1_waybel_0('#skF_2'(A_23,B_35,C_41),A_23)
      | ~ r2_hidden(C_41,k2_pre_topc(A_23,B_35))
      | ~ m1_subset_1(C_41,u1_struct_0(A_23))
      | ~ m1_subset_1(B_35,k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_386,plain,(
    ! [A_222,B_223,B_224] :
      ( l1_waybel_0('#skF_2'(A_222,B_223,'#skF_4'(A_222,B_224)),A_222)
      | ~ r1_waybel_0(A_222,'#skF_3'(A_222,B_224),B_223)
      | ~ l1_waybel_0('#skF_3'(A_222,B_224),A_222)
      | ~ v7_waybel_0('#skF_3'(A_222,B_224))
      | ~ v4_orders_2('#skF_3'(A_222,B_224))
      | v2_struct_0('#skF_3'(A_222,B_224))
      | ~ m1_subset_1('#skF_4'(A_222,B_224),u1_struct_0(A_222))
      | ~ m1_subset_1(B_223,k1_zfmisc_1(u1_struct_0(A_222)))
      | v4_pre_topc(B_224,A_222)
      | ~ m1_subset_1(B_224,k1_zfmisc_1(u1_struct_0(A_222)))
      | ~ l1_pre_topc(A_222)
      | ~ v2_pre_topc(A_222)
      | v2_struct_0(A_222) ) ),
    inference(resolution,[status(thm)],[c_244,c_22])).

tff(c_390,plain,(
    ! [A_225,B_226,B_227] :
      ( l1_waybel_0('#skF_2'(A_225,B_226,'#skF_4'(A_225,B_227)),A_225)
      | ~ r1_waybel_0(A_225,'#skF_3'(A_225,B_227),B_226)
      | ~ l1_waybel_0('#skF_3'(A_225,B_227),A_225)
      | ~ v7_waybel_0('#skF_3'(A_225,B_227))
      | ~ v4_orders_2('#skF_3'(A_225,B_227))
      | v2_struct_0('#skF_3'(A_225,B_227))
      | ~ m1_subset_1(B_226,k1_zfmisc_1(u1_struct_0(A_225)))
      | v4_pre_topc(B_227,A_225)
      | ~ m1_subset_1(B_227,k1_zfmisc_1(u1_struct_0(A_225)))
      | ~ l1_pre_topc(A_225)
      | ~ v2_pre_topc(A_225)
      | v2_struct_0(A_225) ) ),
    inference(resolution,[status(thm)],[c_38,c_386])).

tff(c_392,plain,(
    ! [B_227] :
      ( l1_waybel_0('#skF_2'('#skF_5','#skF_6','#skF_4'('#skF_5',B_227)),'#skF_5')
      | ~ r1_waybel_0('#skF_5','#skF_3'('#skF_5',B_227),'#skF_6')
      | ~ l1_waybel_0('#skF_3'('#skF_5',B_227),'#skF_5')
      | ~ v7_waybel_0('#skF_3'('#skF_5',B_227))
      | ~ v4_orders_2('#skF_3'('#skF_5',B_227))
      | v2_struct_0('#skF_3'('#skF_5',B_227))
      | v4_pre_topc(B_227,'#skF_5')
      | ~ m1_subset_1(B_227,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_50,c_390])).

tff(c_395,plain,(
    ! [B_227] :
      ( l1_waybel_0('#skF_2'('#skF_5','#skF_6','#skF_4'('#skF_5',B_227)),'#skF_5')
      | ~ r1_waybel_0('#skF_5','#skF_3'('#skF_5',B_227),'#skF_6')
      | ~ l1_waybel_0('#skF_3'('#skF_5',B_227),'#skF_5')
      | ~ v7_waybel_0('#skF_3'('#skF_5',B_227))
      | ~ v4_orders_2('#skF_3'('#skF_5',B_227))
      | v2_struct_0('#skF_3'('#skF_5',B_227))
      | v4_pre_topc(B_227,'#skF_5')
      | ~ m1_subset_1(B_227,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_392])).

tff(c_397,plain,(
    ! [B_228] :
      ( l1_waybel_0('#skF_2'('#skF_5','#skF_6','#skF_4'('#skF_5',B_228)),'#skF_5')
      | ~ r1_waybel_0('#skF_5','#skF_3'('#skF_5',B_228),'#skF_6')
      | ~ l1_waybel_0('#skF_3'('#skF_5',B_228),'#skF_5')
      | ~ v7_waybel_0('#skF_3'('#skF_5',B_228))
      | ~ v4_orders_2('#skF_3'('#skF_5',B_228))
      | v2_struct_0('#skF_3'('#skF_5',B_228))
      | v4_pre_topc(B_228,'#skF_5')
      | ~ m1_subset_1(B_228,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_395])).

tff(c_400,plain,
    ( l1_waybel_0('#skF_2'('#skF_5','#skF_6','#skF_4'('#skF_5','#skF_6')),'#skF_5')
    | ~ r1_waybel_0('#skF_5','#skF_3'('#skF_5','#skF_6'),'#skF_6')
    | ~ l1_waybel_0('#skF_3'('#skF_5','#skF_6'),'#skF_5')
    | ~ v7_waybel_0('#skF_3'('#skF_5','#skF_6'))
    | ~ v4_orders_2('#skF_3'('#skF_5','#skF_6'))
    | v2_struct_0('#skF_3'('#skF_5','#skF_6'))
    | v4_pre_topc('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_397])).

tff(c_403,plain,
    ( l1_waybel_0('#skF_2'('#skF_5','#skF_6','#skF_4'('#skF_5','#skF_6')),'#skF_5')
    | v2_struct_0('#skF_3'('#skF_5','#skF_6'))
    | v4_pre_topc('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_121,c_129,c_138,c_400])).

tff(c_404,plain,(
    l1_waybel_0('#skF_2'('#skF_5','#skF_6','#skF_4'('#skF_5','#skF_6')),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_97,c_105,c_403])).

tff(c_150,plain,(
    ! [A_133,B_134,C_135] :
      ( v3_yellow_6('#skF_2'(A_133,B_134,C_135),A_133)
      | ~ r2_hidden(C_135,k2_pre_topc(A_133,B_134))
      | ~ m1_subset_1(C_135,u1_struct_0(A_133))
      | ~ m1_subset_1(B_134,k1_zfmisc_1(u1_struct_0(A_133)))
      | ~ l1_pre_topc(A_133)
      | ~ v2_pre_topc(A_133)
      | v2_struct_0(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_152,plain,(
    ! [C_135] :
      ( v3_yellow_6('#skF_2'('#skF_5','#skF_6',C_135),'#skF_5')
      | ~ r2_hidden(C_135,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_135,u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_50,c_150])).

tff(c_155,plain,(
    ! [C_135] :
      ( v3_yellow_6('#skF_2'('#skF_5','#skF_6',C_135),'#skF_5')
      | ~ r2_hidden(C_135,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_135,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_152])).

tff(c_156,plain,(
    ! [C_135] :
      ( v3_yellow_6('#skF_2'('#skF_5','#skF_6',C_135),'#skF_5')
      | ~ r2_hidden(C_135,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_135,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_155])).

tff(c_158,plain,(
    ! [A_137,B_138,C_139] :
      ( r1_waybel_0(A_137,'#skF_2'(A_137,B_138,C_139),B_138)
      | ~ r2_hidden(C_139,k2_pre_topc(A_137,B_138))
      | ~ m1_subset_1(C_139,u1_struct_0(A_137))
      | ~ m1_subset_1(B_138,k1_zfmisc_1(u1_struct_0(A_137)))
      | ~ l1_pre_topc(A_137)
      | ~ v2_pre_topc(A_137)
      | v2_struct_0(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_160,plain,(
    ! [C_139] :
      ( r1_waybel_0('#skF_5','#skF_2'('#skF_5','#skF_6',C_139),'#skF_6')
      | ~ r2_hidden(C_139,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_139,u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_50,c_158])).

tff(c_163,plain,(
    ! [C_139] :
      ( r1_waybel_0('#skF_5','#skF_2'('#skF_5','#skF_6',C_139),'#skF_6')
      | ~ r2_hidden(C_139,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_139,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_160])).

tff(c_164,plain,(
    ! [C_139] :
      ( r1_waybel_0('#skF_5','#skF_2'('#skF_5','#skF_6',C_139),'#skF_6')
      | ~ r2_hidden(C_139,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_139,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_163])).

tff(c_18,plain,(
    ! [C_41,A_23,B_35] :
      ( r2_hidden(C_41,k10_yellow_6(A_23,'#skF_2'(A_23,B_35,C_41)))
      | ~ r2_hidden(C_41,k2_pre_topc(A_23,B_35))
      | ~ m1_subset_1(C_41,u1_struct_0(A_23))
      | ~ m1_subset_1(B_35,k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_96,plain,(
    ! [D_92,C_90] :
      ( v4_pre_topc('#skF_6','#skF_5')
      | r2_hidden(D_92,'#skF_6')
      | ~ r2_hidden(D_92,k10_yellow_6('#skF_5',C_90))
      | ~ m1_subset_1(D_92,u1_struct_0('#skF_5'))
      | ~ r1_waybel_0('#skF_5',C_90,'#skF_6')
      | ~ l1_waybel_0(C_90,'#skF_5')
      | ~ v3_yellow_6(C_90,'#skF_5')
      | ~ v7_waybel_0(C_90)
      | ~ v4_orders_2(C_90)
      | v2_struct_0(C_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_187,plain,(
    ! [D_152,C_153] :
      ( r2_hidden(D_152,'#skF_6')
      | ~ r2_hidden(D_152,k10_yellow_6('#skF_5',C_153))
      | ~ m1_subset_1(D_152,u1_struct_0('#skF_5'))
      | ~ r1_waybel_0('#skF_5',C_153,'#skF_6')
      | ~ l1_waybel_0(C_153,'#skF_5')
      | ~ v3_yellow_6(C_153,'#skF_5')
      | ~ v7_waybel_0(C_153)
      | ~ v4_orders_2(C_153)
      | v2_struct_0(C_153) ) ),
    inference(negUnitSimplification,[status(thm)],[c_97,c_96])).

tff(c_191,plain,(
    ! [C_41,B_35] :
      ( r2_hidden(C_41,'#skF_6')
      | ~ r1_waybel_0('#skF_5','#skF_2'('#skF_5',B_35,C_41),'#skF_6')
      | ~ l1_waybel_0('#skF_2'('#skF_5',B_35,C_41),'#skF_5')
      | ~ v3_yellow_6('#skF_2'('#skF_5',B_35,C_41),'#skF_5')
      | ~ v7_waybel_0('#skF_2'('#skF_5',B_35,C_41))
      | ~ v4_orders_2('#skF_2'('#skF_5',B_35,C_41))
      | v2_struct_0('#skF_2'('#skF_5',B_35,C_41))
      | ~ r2_hidden(C_41,k2_pre_topc('#skF_5',B_35))
      | ~ m1_subset_1(C_41,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_35,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_18,c_187])).

tff(c_194,plain,(
    ! [C_41,B_35] :
      ( r2_hidden(C_41,'#skF_6')
      | ~ r1_waybel_0('#skF_5','#skF_2'('#skF_5',B_35,C_41),'#skF_6')
      | ~ l1_waybel_0('#skF_2'('#skF_5',B_35,C_41),'#skF_5')
      | ~ v3_yellow_6('#skF_2'('#skF_5',B_35,C_41),'#skF_5')
      | ~ v7_waybel_0('#skF_2'('#skF_5',B_35,C_41))
      | ~ v4_orders_2('#skF_2'('#skF_5',B_35,C_41))
      | v2_struct_0('#skF_2'('#skF_5',B_35,C_41))
      | ~ r2_hidden(C_41,k2_pre_topc('#skF_5',B_35))
      | ~ m1_subset_1(C_41,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_35,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_191])).

tff(c_232,plain,(
    ! [C_170,B_171] :
      ( r2_hidden(C_170,'#skF_6')
      | ~ r1_waybel_0('#skF_5','#skF_2'('#skF_5',B_171,C_170),'#skF_6')
      | ~ l1_waybel_0('#skF_2'('#skF_5',B_171,C_170),'#skF_5')
      | ~ v3_yellow_6('#skF_2'('#skF_5',B_171,C_170),'#skF_5')
      | ~ v7_waybel_0('#skF_2'('#skF_5',B_171,C_170))
      | ~ v4_orders_2('#skF_2'('#skF_5',B_171,C_170))
      | v2_struct_0('#skF_2'('#skF_5',B_171,C_170))
      | ~ r2_hidden(C_170,k2_pre_topc('#skF_5',B_171))
      | ~ m1_subset_1(C_170,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_171,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_194])).

tff(c_234,plain,(
    ! [C_139] :
      ( r2_hidden(C_139,'#skF_6')
      | ~ l1_waybel_0('#skF_2'('#skF_5','#skF_6',C_139),'#skF_5')
      | ~ v3_yellow_6('#skF_2'('#skF_5','#skF_6',C_139),'#skF_5')
      | ~ v7_waybel_0('#skF_2'('#skF_5','#skF_6',C_139))
      | ~ v4_orders_2('#skF_2'('#skF_5','#skF_6',C_139))
      | v2_struct_0('#skF_2'('#skF_5','#skF_6',C_139))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r2_hidden(C_139,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_139,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_164,c_232])).

tff(c_238,plain,(
    ! [C_172] :
      ( r2_hidden(C_172,'#skF_6')
      | ~ l1_waybel_0('#skF_2'('#skF_5','#skF_6',C_172),'#skF_5')
      | ~ v3_yellow_6('#skF_2'('#skF_5','#skF_6',C_172),'#skF_5')
      | ~ v7_waybel_0('#skF_2'('#skF_5','#skF_6',C_172))
      | ~ v4_orders_2('#skF_2'('#skF_5','#skF_6',C_172))
      | v2_struct_0('#skF_2'('#skF_5','#skF_6',C_172))
      | ~ r2_hidden(C_172,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_172,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_234])).

tff(c_242,plain,(
    ! [C_135] :
      ( r2_hidden(C_135,'#skF_6')
      | ~ l1_waybel_0('#skF_2'('#skF_5','#skF_6',C_135),'#skF_5')
      | ~ v7_waybel_0('#skF_2'('#skF_5','#skF_6',C_135))
      | ~ v4_orders_2('#skF_2'('#skF_5','#skF_6',C_135))
      | v2_struct_0('#skF_2'('#skF_5','#skF_6',C_135))
      | ~ r2_hidden(C_135,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_135,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_156,c_238])).

tff(c_248,plain,(
    ! [B_175] :
      ( r2_hidden('#skF_4'('#skF_5',B_175),'#skF_6')
      | ~ l1_waybel_0('#skF_2'('#skF_5','#skF_6','#skF_4'('#skF_5',B_175)),'#skF_5')
      | ~ v7_waybel_0('#skF_2'('#skF_5','#skF_6','#skF_4'('#skF_5',B_175)))
      | ~ v4_orders_2('#skF_2'('#skF_5','#skF_6','#skF_4'('#skF_5',B_175)))
      | v2_struct_0('#skF_2'('#skF_5','#skF_6','#skF_4'('#skF_5',B_175)))
      | ~ r1_waybel_0('#skF_5','#skF_3'('#skF_5',B_175),'#skF_6')
      | ~ l1_waybel_0('#skF_3'('#skF_5',B_175),'#skF_5')
      | ~ v7_waybel_0('#skF_3'('#skF_5',B_175))
      | ~ v4_orders_2('#skF_3'('#skF_5',B_175))
      | v2_struct_0('#skF_3'('#skF_5',B_175))
      | ~ m1_subset_1('#skF_4'('#skF_5',B_175),u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v4_pre_topc(B_175,'#skF_5')
      | ~ m1_subset_1(B_175,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_244,c_242])).

tff(c_270,plain,(
    ! [B_175] :
      ( r2_hidden('#skF_4'('#skF_5',B_175),'#skF_6')
      | ~ l1_waybel_0('#skF_2'('#skF_5','#skF_6','#skF_4'('#skF_5',B_175)),'#skF_5')
      | ~ v7_waybel_0('#skF_2'('#skF_5','#skF_6','#skF_4'('#skF_5',B_175)))
      | ~ v4_orders_2('#skF_2'('#skF_5','#skF_6','#skF_4'('#skF_5',B_175)))
      | v2_struct_0('#skF_2'('#skF_5','#skF_6','#skF_4'('#skF_5',B_175)))
      | ~ r1_waybel_0('#skF_5','#skF_3'('#skF_5',B_175),'#skF_6')
      | ~ l1_waybel_0('#skF_3'('#skF_5',B_175),'#skF_5')
      | ~ v7_waybel_0('#skF_3'('#skF_5',B_175))
      | ~ v4_orders_2('#skF_3'('#skF_5',B_175))
      | v2_struct_0('#skF_3'('#skF_5',B_175))
      | ~ m1_subset_1('#skF_4'('#skF_5',B_175),u1_struct_0('#skF_5'))
      | v4_pre_topc(B_175,'#skF_5')
      | ~ m1_subset_1(B_175,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_248])).

tff(c_281,plain,(
    ! [B_177] :
      ( r2_hidden('#skF_4'('#skF_5',B_177),'#skF_6')
      | ~ l1_waybel_0('#skF_2'('#skF_5','#skF_6','#skF_4'('#skF_5',B_177)),'#skF_5')
      | ~ v7_waybel_0('#skF_2'('#skF_5','#skF_6','#skF_4'('#skF_5',B_177)))
      | ~ v4_orders_2('#skF_2'('#skF_5','#skF_6','#skF_4'('#skF_5',B_177)))
      | v2_struct_0('#skF_2'('#skF_5','#skF_6','#skF_4'('#skF_5',B_177)))
      | ~ r1_waybel_0('#skF_5','#skF_3'('#skF_5',B_177),'#skF_6')
      | ~ l1_waybel_0('#skF_3'('#skF_5',B_177),'#skF_5')
      | ~ v7_waybel_0('#skF_3'('#skF_5',B_177))
      | ~ v4_orders_2('#skF_3'('#skF_5',B_177))
      | v2_struct_0('#skF_3'('#skF_5',B_177))
      | ~ m1_subset_1('#skF_4'('#skF_5',B_177),u1_struct_0('#skF_5'))
      | v4_pre_topc(B_177,'#skF_5')
      | ~ m1_subset_1(B_177,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_270])).

tff(c_285,plain,(
    ! [B_59] :
      ( r2_hidden('#skF_4'('#skF_5',B_59),'#skF_6')
      | ~ l1_waybel_0('#skF_2'('#skF_5','#skF_6','#skF_4'('#skF_5',B_59)),'#skF_5')
      | ~ v7_waybel_0('#skF_2'('#skF_5','#skF_6','#skF_4'('#skF_5',B_59)))
      | ~ v4_orders_2('#skF_2'('#skF_5','#skF_6','#skF_4'('#skF_5',B_59)))
      | v2_struct_0('#skF_2'('#skF_5','#skF_6','#skF_4'('#skF_5',B_59)))
      | ~ r1_waybel_0('#skF_5','#skF_3'('#skF_5',B_59),'#skF_6')
      | ~ l1_waybel_0('#skF_3'('#skF_5',B_59),'#skF_5')
      | ~ v7_waybel_0('#skF_3'('#skF_5',B_59))
      | ~ v4_orders_2('#skF_3'('#skF_5',B_59))
      | v2_struct_0('#skF_3'('#skF_5',B_59))
      | v4_pre_topc(B_59,'#skF_5')
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_38,c_281])).

tff(c_288,plain,(
    ! [B_59] :
      ( r2_hidden('#skF_4'('#skF_5',B_59),'#skF_6')
      | ~ l1_waybel_0('#skF_2'('#skF_5','#skF_6','#skF_4'('#skF_5',B_59)),'#skF_5')
      | ~ v7_waybel_0('#skF_2'('#skF_5','#skF_6','#skF_4'('#skF_5',B_59)))
      | ~ v4_orders_2('#skF_2'('#skF_5','#skF_6','#skF_4'('#skF_5',B_59)))
      | v2_struct_0('#skF_2'('#skF_5','#skF_6','#skF_4'('#skF_5',B_59)))
      | ~ r1_waybel_0('#skF_5','#skF_3'('#skF_5',B_59),'#skF_6')
      | ~ l1_waybel_0('#skF_3'('#skF_5',B_59),'#skF_5')
      | ~ v7_waybel_0('#skF_3'('#skF_5',B_59))
      | ~ v4_orders_2('#skF_3'('#skF_5',B_59))
      | v2_struct_0('#skF_3'('#skF_5',B_59))
      | v4_pre_topc(B_59,'#skF_5')
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_285])).

tff(c_424,plain,(
    ! [B_236] :
      ( r2_hidden('#skF_4'('#skF_5',B_236),'#skF_6')
      | ~ l1_waybel_0('#skF_2'('#skF_5','#skF_6','#skF_4'('#skF_5',B_236)),'#skF_5')
      | ~ v7_waybel_0('#skF_2'('#skF_5','#skF_6','#skF_4'('#skF_5',B_236)))
      | ~ v4_orders_2('#skF_2'('#skF_5','#skF_6','#skF_4'('#skF_5',B_236)))
      | v2_struct_0('#skF_2'('#skF_5','#skF_6','#skF_4'('#skF_5',B_236)))
      | ~ r1_waybel_0('#skF_5','#skF_3'('#skF_5',B_236),'#skF_6')
      | ~ l1_waybel_0('#skF_3'('#skF_5',B_236),'#skF_5')
      | ~ v7_waybel_0('#skF_3'('#skF_5',B_236))
      | ~ v4_orders_2('#skF_3'('#skF_5',B_236))
      | v2_struct_0('#skF_3'('#skF_5',B_236))
      | v4_pre_topc(B_236,'#skF_5')
      | ~ m1_subset_1(B_236,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_288])).

tff(c_427,plain,
    ( r2_hidden('#skF_4'('#skF_5','#skF_6'),'#skF_6')
    | ~ l1_waybel_0('#skF_2'('#skF_5','#skF_6','#skF_4'('#skF_5','#skF_6')),'#skF_5')
    | ~ v7_waybel_0('#skF_2'('#skF_5','#skF_6','#skF_4'('#skF_5','#skF_6')))
    | ~ v4_orders_2('#skF_2'('#skF_5','#skF_6','#skF_4'('#skF_5','#skF_6')))
    | v2_struct_0('#skF_2'('#skF_5','#skF_6','#skF_4'('#skF_5','#skF_6')))
    | ~ r1_waybel_0('#skF_5','#skF_3'('#skF_5','#skF_6'),'#skF_6')
    | ~ l1_waybel_0('#skF_3'('#skF_5','#skF_6'),'#skF_5')
    | ~ v7_waybel_0('#skF_3'('#skF_5','#skF_6'))
    | ~ v4_orders_2('#skF_3'('#skF_5','#skF_6'))
    | v2_struct_0('#skF_3'('#skF_5','#skF_6'))
    | v4_pre_topc('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_424])).

tff(c_430,plain,
    ( r2_hidden('#skF_4'('#skF_5','#skF_6'),'#skF_6')
    | v2_struct_0('#skF_2'('#skF_5','#skF_6','#skF_4'('#skF_5','#skF_6')))
    | v2_struct_0('#skF_3'('#skF_5','#skF_6'))
    | v4_pre_topc('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_121,c_129,c_138,c_359,c_385,c_404,c_427])).

tff(c_431,plain,
    ( r2_hidden('#skF_4'('#skF_5','#skF_6'),'#skF_6')
    | v2_struct_0('#skF_2'('#skF_5','#skF_6','#skF_4'('#skF_5','#skF_6'))) ),
    inference(negUnitSimplification,[status(thm)],[c_97,c_105,c_430])).

tff(c_432,plain,(
    v2_struct_0('#skF_2'('#skF_5','#skF_6','#skF_4'('#skF_5','#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_431])).

tff(c_30,plain,(
    ! [A_23,B_35,C_41] :
      ( ~ v2_struct_0('#skF_2'(A_23,B_35,C_41))
      | ~ r2_hidden(C_41,k2_pre_topc(A_23,B_35))
      | ~ m1_subset_1(C_41,u1_struct_0(A_23))
      | ~ m1_subset_1(B_35,k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_277,plain,(
    ! [A_174,B_176,B_175] :
      ( ~ v2_struct_0('#skF_2'(A_174,B_176,'#skF_4'(A_174,B_175)))
      | ~ r1_waybel_0(A_174,'#skF_3'(A_174,B_175),B_176)
      | ~ l1_waybel_0('#skF_3'(A_174,B_175),A_174)
      | ~ v7_waybel_0('#skF_3'(A_174,B_175))
      | ~ v4_orders_2('#skF_3'(A_174,B_175))
      | v2_struct_0('#skF_3'(A_174,B_175))
      | ~ m1_subset_1('#skF_4'(A_174,B_175),u1_struct_0(A_174))
      | ~ m1_subset_1(B_176,k1_zfmisc_1(u1_struct_0(A_174)))
      | v4_pre_topc(B_175,A_174)
      | ~ m1_subset_1(B_175,k1_zfmisc_1(u1_struct_0(A_174)))
      | ~ l1_pre_topc(A_174)
      | ~ v2_pre_topc(A_174)
      | v2_struct_0(A_174) ) ),
    inference(resolution,[status(thm)],[c_244,c_30])).

tff(c_434,plain,
    ( ~ r1_waybel_0('#skF_5','#skF_3'('#skF_5','#skF_6'),'#skF_6')
    | ~ l1_waybel_0('#skF_3'('#skF_5','#skF_6'),'#skF_5')
    | ~ v7_waybel_0('#skF_3'('#skF_5','#skF_6'))
    | ~ v4_orders_2('#skF_3'('#skF_5','#skF_6'))
    | v2_struct_0('#skF_3'('#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4'('#skF_5','#skF_6'),u1_struct_0('#skF_5'))
    | v4_pre_topc('#skF_6','#skF_5')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_432,c_277])).

tff(c_437,plain,
    ( v2_struct_0('#skF_3'('#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4'('#skF_5','#skF_6'),u1_struct_0('#skF_5'))
    | v4_pre_topc('#skF_6','#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_113,c_121,c_129,c_138,c_434])).

tff(c_438,plain,(
    ~ m1_subset_1('#skF_4'('#skF_5','#skF_6'),u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_97,c_105,c_437])).

tff(c_441,plain,
    ( v4_pre_topc('#skF_6','#skF_5')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_438])).

tff(c_444,plain,
    ( v4_pre_topc('#skF_6','#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_441])).

tff(c_446,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_97,c_444])).

tff(c_447,plain,(
    r2_hidden('#skF_4'('#skF_5','#skF_6'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_431])).

tff(c_34,plain,(
    ! [A_45,B_59] :
      ( ~ r2_hidden('#skF_4'(A_45,B_59),B_59)
      | v4_pre_topc(B_59,A_45)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ l1_pre_topc(A_45)
      | ~ v2_pre_topc(A_45)
      | v2_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_450,plain,
    ( v4_pre_topc('#skF_6','#skF_5')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_447,c_34])).

tff(c_453,plain,
    ( v4_pre_topc('#skF_6','#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_450])).

tff(c_455,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_97,c_453])).

tff(c_457,plain,(
    v4_pre_topc('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_62,plain,
    ( m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ v4_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_471,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_457,c_62])).

tff(c_64,plain,
    ( r1_waybel_0('#skF_5','#skF_7','#skF_6')
    | ~ v4_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_469,plain,(
    r1_waybel_0('#skF_5','#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_457,c_64])).

tff(c_456,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_72,plain,
    ( v4_orders_2('#skF_7')
    | ~ v4_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_461,plain,(
    v4_orders_2('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_457,c_72])).

tff(c_70,plain,
    ( v7_waybel_0('#skF_7')
    | ~ v4_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_459,plain,(
    v7_waybel_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_457,c_70])).

tff(c_68,plain,
    ( v3_yellow_6('#skF_7','#skF_5')
    | ~ v4_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_465,plain,(
    v3_yellow_6('#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_457,c_68])).

tff(c_66,plain,
    ( l1_waybel_0('#skF_7','#skF_5')
    | ~ v4_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_467,plain,(
    l1_waybel_0('#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_457,c_66])).

tff(c_60,plain,
    ( r2_hidden('#skF_8',k10_yellow_6('#skF_5','#skF_7'))
    | ~ v4_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_473,plain,(
    r2_hidden('#skF_8',k10_yellow_6('#skF_5','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_457,c_60])).

tff(c_584,plain,(
    ! [C_304,A_305,B_306,D_307] :
      ( r2_hidden(C_304,k2_pre_topc(A_305,B_306))
      | ~ r2_hidden(C_304,k10_yellow_6(A_305,D_307))
      | ~ r1_waybel_0(A_305,D_307,B_306)
      | ~ l1_waybel_0(D_307,A_305)
      | ~ v3_yellow_6(D_307,A_305)
      | ~ v7_waybel_0(D_307)
      | ~ v4_orders_2(D_307)
      | v2_struct_0(D_307)
      | ~ m1_subset_1(C_304,u1_struct_0(A_305))
      | ~ m1_subset_1(B_306,k1_zfmisc_1(u1_struct_0(A_305)))
      | ~ l1_pre_topc(A_305)
      | ~ v2_pre_topc(A_305)
      | v2_struct_0(A_305) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_588,plain,(
    ! [B_306] :
      ( r2_hidden('#skF_8',k2_pre_topc('#skF_5',B_306))
      | ~ r1_waybel_0('#skF_5','#skF_7',B_306)
      | ~ l1_waybel_0('#skF_7','#skF_5')
      | ~ v3_yellow_6('#skF_7','#skF_5')
      | ~ v7_waybel_0('#skF_7')
      | ~ v4_orders_2('#skF_7')
      | v2_struct_0('#skF_7')
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_306,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_473,c_584])).

tff(c_592,plain,(
    ! [B_306] :
      ( r2_hidden('#skF_8',k2_pre_topc('#skF_5',B_306))
      | ~ r1_waybel_0('#skF_5','#skF_7',B_306)
      | v2_struct_0('#skF_7')
      | ~ m1_subset_1(B_306,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_471,c_461,c_459,c_465,c_467,c_588])).

tff(c_594,plain,(
    ! [B_308] :
      ( r2_hidden('#skF_8',k2_pre_topc('#skF_5',B_308))
      | ~ r1_waybel_0('#skF_5','#skF_7',B_308)
      | ~ m1_subset_1(B_308,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_456,c_592])).

tff(c_597,plain,
    ( r2_hidden('#skF_8',k2_pre_topc('#skF_5','#skF_6'))
    | ~ r1_waybel_0('#skF_5','#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_594])).

tff(c_600,plain,(
    r2_hidden('#skF_8',k2_pre_topc('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_469,c_597])).

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

tff(c_616,plain,
    ( ~ v2_struct_0('#skF_1'('#skF_5','#skF_6','#skF_8'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_600,c_14])).

tff(c_647,plain,
    ( ~ v2_struct_0('#skF_1'('#skF_5','#skF_6','#skF_8'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_471,c_616])).

tff(c_648,plain,(
    ~ v2_struct_0('#skF_1'('#skF_5','#skF_6','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_647])).

tff(c_58,plain,
    ( ~ r2_hidden('#skF_8','#skF_6')
    | ~ v4_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_463,plain,(
    ~ r2_hidden('#skF_8','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_457,c_58])).

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

tff(c_612,plain,
    ( v4_orders_2('#skF_1'('#skF_5','#skF_6','#skF_8'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_600,c_12])).

tff(c_639,plain,
    ( v4_orders_2('#skF_1'('#skF_5','#skF_6','#skF_8'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_471,c_612])).

tff(c_640,plain,(
    v4_orders_2('#skF_1'('#skF_5','#skF_6','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_639])).

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

tff(c_608,plain,
    ( v7_waybel_0('#skF_1'('#skF_5','#skF_6','#skF_8'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_600,c_10])).

tff(c_631,plain,
    ( v7_waybel_0('#skF_1'('#skF_5','#skF_6','#skF_8'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_471,c_608])).

tff(c_632,plain,(
    v7_waybel_0('#skF_1'('#skF_5','#skF_6','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_631])).

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

tff(c_602,plain,
    ( l1_waybel_0('#skF_1'('#skF_5','#skF_6','#skF_8'),'#skF_5')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_600,c_8])).

tff(c_619,plain,
    ( l1_waybel_0('#skF_1'('#skF_5','#skF_6','#skF_8'),'#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_471,c_602])).

tff(c_620,plain,(
    l1_waybel_0('#skF_1'('#skF_5','#skF_6','#skF_8'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_619])).

tff(c_532,plain,(
    ! [A_281,B_282,C_283] :
      ( r1_waybel_0(A_281,'#skF_1'(A_281,B_282,C_283),B_282)
      | ~ r2_hidden(C_283,k2_pre_topc(A_281,B_282))
      | ~ m1_subset_1(C_283,u1_struct_0(A_281))
      | ~ m1_subset_1(B_282,k1_zfmisc_1(u1_struct_0(A_281)))
      | ~ l1_pre_topc(A_281)
      | ~ v2_pre_topc(A_281)
      | v2_struct_0(A_281) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_534,plain,(
    ! [C_283] :
      ( r1_waybel_0('#skF_5','#skF_1'('#skF_5','#skF_6',C_283),'#skF_6')
      | ~ r2_hidden(C_283,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_283,u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_50,c_532])).

tff(c_537,plain,(
    ! [C_283] :
      ( r1_waybel_0('#skF_5','#skF_1'('#skF_5','#skF_6',C_283),'#skF_6')
      | ~ r2_hidden(C_283,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_283,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_534])).

tff(c_538,plain,(
    ! [C_283] :
      ( r1_waybel_0('#skF_5','#skF_1'('#skF_5','#skF_6',C_283),'#skF_6')
      | ~ r2_hidden(C_283,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_283,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_537])).

tff(c_540,plain,(
    ! [A_285,B_286,C_287] :
      ( r3_waybel_9(A_285,'#skF_1'(A_285,B_286,C_287),C_287)
      | ~ r2_hidden(C_287,k2_pre_topc(A_285,B_286))
      | ~ m1_subset_1(C_287,u1_struct_0(A_285))
      | ~ m1_subset_1(B_286,k1_zfmisc_1(u1_struct_0(A_285)))
      | ~ l1_pre_topc(A_285)
      | ~ v2_pre_topc(A_285)
      | v2_struct_0(A_285) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_542,plain,(
    ! [C_287] :
      ( r3_waybel_9('#skF_5','#skF_1'('#skF_5','#skF_6',C_287),C_287)
      | ~ r2_hidden(C_287,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_287,u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_50,c_540])).

tff(c_545,plain,(
    ! [C_287] :
      ( r3_waybel_9('#skF_5','#skF_1'('#skF_5','#skF_6',C_287),C_287)
      | ~ r2_hidden(C_287,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_287,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_542])).

tff(c_546,plain,(
    ! [C_287] :
      ( r3_waybel_9('#skF_5','#skF_1'('#skF_5','#skF_6',C_287),C_287)
      | ~ r2_hidden(C_287,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_287,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_545])).

tff(c_574,plain,(
    ! [D_300,B_301,A_302,C_303] :
      ( r2_hidden(D_300,B_301)
      | ~ r3_waybel_9(A_302,C_303,D_300)
      | ~ m1_subset_1(D_300,u1_struct_0(A_302))
      | ~ r1_waybel_0(A_302,C_303,B_301)
      | ~ l1_waybel_0(C_303,A_302)
      | ~ v7_waybel_0(C_303)
      | ~ v4_orders_2(C_303)
      | v2_struct_0(C_303)
      | ~ v4_pre_topc(B_301,A_302)
      | ~ m1_subset_1(B_301,k1_zfmisc_1(u1_struct_0(A_302)))
      | ~ l1_pre_topc(A_302)
      | ~ v2_pre_topc(A_302)
      | v2_struct_0(A_302) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_576,plain,(
    ! [C_287,B_301] :
      ( r2_hidden(C_287,B_301)
      | ~ r1_waybel_0('#skF_5','#skF_1'('#skF_5','#skF_6',C_287),B_301)
      | ~ l1_waybel_0('#skF_1'('#skF_5','#skF_6',C_287),'#skF_5')
      | ~ v7_waybel_0('#skF_1'('#skF_5','#skF_6',C_287))
      | ~ v4_orders_2('#skF_1'('#skF_5','#skF_6',C_287))
      | v2_struct_0('#skF_1'('#skF_5','#skF_6',C_287))
      | ~ v4_pre_topc(B_301,'#skF_5')
      | ~ m1_subset_1(B_301,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r2_hidden(C_287,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_287,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_546,c_574])).

tff(c_581,plain,(
    ! [C_287,B_301] :
      ( r2_hidden(C_287,B_301)
      | ~ r1_waybel_0('#skF_5','#skF_1'('#skF_5','#skF_6',C_287),B_301)
      | ~ l1_waybel_0('#skF_1'('#skF_5','#skF_6',C_287),'#skF_5')
      | ~ v7_waybel_0('#skF_1'('#skF_5','#skF_6',C_287))
      | ~ v4_orders_2('#skF_1'('#skF_5','#skF_6',C_287))
      | v2_struct_0('#skF_1'('#skF_5','#skF_6',C_287))
      | ~ v4_pre_topc(B_301,'#skF_5')
      | ~ m1_subset_1(B_301,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v2_struct_0('#skF_5')
      | ~ r2_hidden(C_287,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_287,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_576])).

tff(c_688,plain,(
    ! [C_317,B_318] :
      ( r2_hidden(C_317,B_318)
      | ~ r1_waybel_0('#skF_5','#skF_1'('#skF_5','#skF_6',C_317),B_318)
      | ~ l1_waybel_0('#skF_1'('#skF_5','#skF_6',C_317),'#skF_5')
      | ~ v7_waybel_0('#skF_1'('#skF_5','#skF_6',C_317))
      | ~ v4_orders_2('#skF_1'('#skF_5','#skF_6',C_317))
      | v2_struct_0('#skF_1'('#skF_5','#skF_6',C_317))
      | ~ v4_pre_topc(B_318,'#skF_5')
      | ~ m1_subset_1(B_318,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r2_hidden(C_317,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_317,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_581])).

tff(c_690,plain,(
    ! [C_283] :
      ( r2_hidden(C_283,'#skF_6')
      | ~ l1_waybel_0('#skF_1'('#skF_5','#skF_6',C_283),'#skF_5')
      | ~ v7_waybel_0('#skF_1'('#skF_5','#skF_6',C_283))
      | ~ v4_orders_2('#skF_1'('#skF_5','#skF_6',C_283))
      | v2_struct_0('#skF_1'('#skF_5','#skF_6',C_283))
      | ~ v4_pre_topc('#skF_6','#skF_5')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r2_hidden(C_283,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_283,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_538,c_688])).

tff(c_694,plain,(
    ! [C_319] :
      ( r2_hidden(C_319,'#skF_6')
      | ~ l1_waybel_0('#skF_1'('#skF_5','#skF_6',C_319),'#skF_5')
      | ~ v7_waybel_0('#skF_1'('#skF_5','#skF_6',C_319))
      | ~ v4_orders_2('#skF_1'('#skF_5','#skF_6',C_319))
      | v2_struct_0('#skF_1'('#skF_5','#skF_6',C_319))
      | ~ r2_hidden(C_319,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_319,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_457,c_690])).

tff(c_701,plain,
    ( r2_hidden('#skF_8','#skF_6')
    | ~ l1_waybel_0('#skF_1'('#skF_5','#skF_6','#skF_8'),'#skF_5')
    | ~ v7_waybel_0('#skF_1'('#skF_5','#skF_6','#skF_8'))
    | ~ v4_orders_2('#skF_1'('#skF_5','#skF_6','#skF_8'))
    | v2_struct_0('#skF_1'('#skF_5','#skF_6','#skF_8'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_600,c_694])).

tff(c_708,plain,
    ( r2_hidden('#skF_8','#skF_6')
    | v2_struct_0('#skF_1'('#skF_5','#skF_6','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_471,c_640,c_632,c_620,c_701])).

tff(c_710,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_648,c_463,c_708])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:47:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.53/1.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.89/1.64  
% 3.89/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.89/1.64  %$ r3_waybel_9 > r1_waybel_0 > v4_pre_topc > v3_yellow_6 > r2_hidden > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k2_pre_topc > k10_yellow_6 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_4
% 3.89/1.64  
% 3.89/1.64  %Foreground sorts:
% 3.89/1.64  
% 3.89/1.64  
% 3.89/1.64  %Background operators:
% 3.89/1.64  
% 3.89/1.64  
% 3.89/1.64  %Foreground operators:
% 3.89/1.64  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.89/1.64  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.89/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.89/1.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.89/1.64  tff(k10_yellow_6, type, k10_yellow_6: ($i * $i) > $i).
% 3.89/1.64  tff(v3_yellow_6, type, v3_yellow_6: ($i * $i) > $o).
% 3.89/1.64  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.89/1.64  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 3.89/1.64  tff('#skF_7', type, '#skF_7': $i).
% 3.89/1.64  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.89/1.64  tff('#skF_5', type, '#skF_5': $i).
% 3.89/1.64  tff(r3_waybel_9, type, r3_waybel_9: ($i * $i * $i) > $o).
% 3.89/1.64  tff(r1_waybel_0, type, r1_waybel_0: ($i * $i * $i) > $o).
% 3.89/1.64  tff('#skF_6', type, '#skF_6': $i).
% 3.89/1.64  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.89/1.64  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.89/1.64  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.89/1.64  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.89/1.64  tff('#skF_8', type, '#skF_8': $i).
% 3.89/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.89/1.64  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 3.89/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.89/1.64  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.89/1.64  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.89/1.64  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.89/1.64  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.89/1.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.89/1.64  
% 3.89/1.68  tff(f_150, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (![C]: (((((~v2_struct_0(C) & v4_orders_2(C)) & v7_waybel_0(C)) & v3_yellow_6(C, A)) & l1_waybel_0(C, A)) => (r1_waybel_0(A, C, B) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, k10_yellow_6(A, C)) => r2_hidden(D, B)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_yellow19)).
% 3.89/1.68  tff(f_116, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (![C]: ((((~v2_struct_0(C) & v4_orders_2(C)) & v7_waybel_0(C)) & l1_waybel_0(C, A)) => (r1_waybel_0(A, C, B) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r3_waybel_9(A, C, D) => r2_hidden(D, B)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_yellow19)).
% 3.89/1.68  tff(f_54, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, k2_pre_topc(A, B)) <=> (?[D]: (((((~v2_struct_0(D) & v4_orders_2(D)) & v7_waybel_0(D)) & l1_waybel_0(D, A)) & r1_waybel_0(A, D, B)) & r3_waybel_9(A, D, C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_yellow19)).
% 3.89/1.68  tff(f_85, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, k2_pre_topc(A, B)) <=> (?[D]: ((((((~v2_struct_0(D) & v4_orders_2(D)) & v7_waybel_0(D)) & v3_yellow_6(D, A)) & l1_waybel_0(D, A)) & r1_waybel_0(A, D, B)) & r2_hidden(C, k10_yellow_6(A, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_yellow19)).
% 3.89/1.68  tff(c_56, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.89/1.68  tff(c_54, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.89/1.68  tff(c_52, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.89/1.68  tff(c_50, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.89/1.68  tff(c_74, plain, (~v2_struct_0('#skF_7') | ~v4_pre_topc('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.89/1.68  tff(c_97, plain, (~v4_pre_topc('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_74])).
% 3.89/1.68  tff(c_38, plain, (![A_45, B_59]: (m1_subset_1('#skF_4'(A_45, B_59), u1_struct_0(A_45)) | v4_pre_topc(B_59, A_45) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(A_45))) | ~l1_pre_topc(A_45) | ~v2_pre_topc(A_45) | v2_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.89/1.68  tff(c_98, plain, (![A_93, B_94]: (~v2_struct_0('#skF_3'(A_93, B_94)) | v4_pre_topc(B_94, A_93) | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0(A_93))) | ~l1_pre_topc(A_93) | ~v2_pre_topc(A_93) | v2_struct_0(A_93))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.89/1.68  tff(c_101, plain, (~v2_struct_0('#skF_3'('#skF_5', '#skF_6')) | v4_pre_topc('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_50, c_98])).
% 3.89/1.68  tff(c_104, plain, (~v2_struct_0('#skF_3'('#skF_5', '#skF_6')) | v4_pre_topc('#skF_6', '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_101])).
% 3.89/1.68  tff(c_105, plain, (~v2_struct_0('#skF_3'('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_56, c_97, c_104])).
% 3.89/1.68  tff(c_106, plain, (![A_95, B_96]: (v4_orders_2('#skF_3'(A_95, B_96)) | v4_pre_topc(B_96, A_95) | ~m1_subset_1(B_96, k1_zfmisc_1(u1_struct_0(A_95))) | ~l1_pre_topc(A_95) | ~v2_pre_topc(A_95) | v2_struct_0(A_95))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.89/1.68  tff(c_109, plain, (v4_orders_2('#skF_3'('#skF_5', '#skF_6')) | v4_pre_topc('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_50, c_106])).
% 3.89/1.68  tff(c_112, plain, (v4_orders_2('#skF_3'('#skF_5', '#skF_6')) | v4_pre_topc('#skF_6', '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_109])).
% 3.89/1.68  tff(c_113, plain, (v4_orders_2('#skF_3'('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_56, c_97, c_112])).
% 3.89/1.68  tff(c_114, plain, (![A_97, B_98]: (v7_waybel_0('#skF_3'(A_97, B_98)) | v4_pre_topc(B_98, A_97) | ~m1_subset_1(B_98, k1_zfmisc_1(u1_struct_0(A_97))) | ~l1_pre_topc(A_97) | ~v2_pre_topc(A_97) | v2_struct_0(A_97))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.89/1.68  tff(c_117, plain, (v7_waybel_0('#skF_3'('#skF_5', '#skF_6')) | v4_pre_topc('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_50, c_114])).
% 3.89/1.68  tff(c_120, plain, (v7_waybel_0('#skF_3'('#skF_5', '#skF_6')) | v4_pre_topc('#skF_6', '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_117])).
% 3.89/1.68  tff(c_121, plain, (v7_waybel_0('#skF_3'('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_56, c_97, c_120])).
% 3.89/1.68  tff(c_123, plain, (![A_99, B_100]: (l1_waybel_0('#skF_3'(A_99, B_100), A_99) | v4_pre_topc(B_100, A_99) | ~m1_subset_1(B_100, k1_zfmisc_1(u1_struct_0(A_99))) | ~l1_pre_topc(A_99) | ~v2_pre_topc(A_99) | v2_struct_0(A_99))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.89/1.68  tff(c_125, plain, (l1_waybel_0('#skF_3'('#skF_5', '#skF_6'), '#skF_5') | v4_pre_topc('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_50, c_123])).
% 3.89/1.68  tff(c_128, plain, (l1_waybel_0('#skF_3'('#skF_5', '#skF_6'), '#skF_5') | v4_pre_topc('#skF_6', '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_125])).
% 3.89/1.68  tff(c_129, plain, (l1_waybel_0('#skF_3'('#skF_5', '#skF_6'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_56, c_97, c_128])).
% 3.89/1.68  tff(c_132, plain, (![A_105, B_106]: (r1_waybel_0(A_105, '#skF_3'(A_105, B_106), B_106) | v4_pre_topc(B_106, A_105) | ~m1_subset_1(B_106, k1_zfmisc_1(u1_struct_0(A_105))) | ~l1_pre_topc(A_105) | ~v2_pre_topc(A_105) | v2_struct_0(A_105))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.89/1.68  tff(c_134, plain, (r1_waybel_0('#skF_5', '#skF_3'('#skF_5', '#skF_6'), '#skF_6') | v4_pre_topc('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_50, c_132])).
% 3.89/1.68  tff(c_137, plain, (r1_waybel_0('#skF_5', '#skF_3'('#skF_5', '#skF_6'), '#skF_6') | v4_pre_topc('#skF_6', '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_134])).
% 3.89/1.68  tff(c_138, plain, (r1_waybel_0('#skF_5', '#skF_3'('#skF_5', '#skF_6'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_56, c_97, c_137])).
% 3.89/1.68  tff(c_36, plain, (![A_45, B_59]: (r3_waybel_9(A_45, '#skF_3'(A_45, B_59), '#skF_4'(A_45, B_59)) | v4_pre_topc(B_59, A_45) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(A_45))) | ~l1_pre_topc(A_45) | ~v2_pre_topc(A_45) | v2_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.89/1.68  tff(c_196, plain, (![C_154, A_155, B_156, D_157]: (r2_hidden(C_154, k2_pre_topc(A_155, B_156)) | ~r3_waybel_9(A_155, D_157, C_154) | ~r1_waybel_0(A_155, D_157, B_156) | ~l1_waybel_0(D_157, A_155) | ~v7_waybel_0(D_157) | ~v4_orders_2(D_157) | v2_struct_0(D_157) | ~m1_subset_1(C_154, u1_struct_0(A_155)) | ~m1_subset_1(B_156, k1_zfmisc_1(u1_struct_0(A_155))) | ~l1_pre_topc(A_155) | ~v2_pre_topc(A_155) | v2_struct_0(A_155))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.89/1.68  tff(c_244, plain, (![A_174, B_175, B_176]: (r2_hidden('#skF_4'(A_174, B_175), k2_pre_topc(A_174, B_176)) | ~r1_waybel_0(A_174, '#skF_3'(A_174, B_175), B_176) | ~l1_waybel_0('#skF_3'(A_174, B_175), A_174) | ~v7_waybel_0('#skF_3'(A_174, B_175)) | ~v4_orders_2('#skF_3'(A_174, B_175)) | v2_struct_0('#skF_3'(A_174, B_175)) | ~m1_subset_1('#skF_4'(A_174, B_175), u1_struct_0(A_174)) | ~m1_subset_1(B_176, k1_zfmisc_1(u1_struct_0(A_174))) | v4_pre_topc(B_175, A_174) | ~m1_subset_1(B_175, k1_zfmisc_1(u1_struct_0(A_174))) | ~l1_pre_topc(A_174) | ~v2_pre_topc(A_174) | v2_struct_0(A_174))), inference(resolution, [status(thm)], [c_36, c_196])).
% 3.89/1.68  tff(c_28, plain, (![A_23, B_35, C_41]: (v4_orders_2('#skF_2'(A_23, B_35, C_41)) | ~r2_hidden(C_41, k2_pre_topc(A_23, B_35)) | ~m1_subset_1(C_41, u1_struct_0(A_23)) | ~m1_subset_1(B_35, k1_zfmisc_1(u1_struct_0(A_23))) | ~l1_pre_topc(A_23) | ~v2_pre_topc(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.89/1.68  tff(c_341, plain, (![A_204, B_205, B_206]: (v4_orders_2('#skF_2'(A_204, B_205, '#skF_4'(A_204, B_206))) | ~r1_waybel_0(A_204, '#skF_3'(A_204, B_206), B_205) | ~l1_waybel_0('#skF_3'(A_204, B_206), A_204) | ~v7_waybel_0('#skF_3'(A_204, B_206)) | ~v4_orders_2('#skF_3'(A_204, B_206)) | v2_struct_0('#skF_3'(A_204, B_206)) | ~m1_subset_1('#skF_4'(A_204, B_206), u1_struct_0(A_204)) | ~m1_subset_1(B_205, k1_zfmisc_1(u1_struct_0(A_204))) | v4_pre_topc(B_206, A_204) | ~m1_subset_1(B_206, k1_zfmisc_1(u1_struct_0(A_204))) | ~l1_pre_topc(A_204) | ~v2_pre_topc(A_204) | v2_struct_0(A_204))), inference(resolution, [status(thm)], [c_244, c_28])).
% 3.89/1.68  tff(c_345, plain, (![A_207, B_208, B_209]: (v4_orders_2('#skF_2'(A_207, B_208, '#skF_4'(A_207, B_209))) | ~r1_waybel_0(A_207, '#skF_3'(A_207, B_209), B_208) | ~l1_waybel_0('#skF_3'(A_207, B_209), A_207) | ~v7_waybel_0('#skF_3'(A_207, B_209)) | ~v4_orders_2('#skF_3'(A_207, B_209)) | v2_struct_0('#skF_3'(A_207, B_209)) | ~m1_subset_1(B_208, k1_zfmisc_1(u1_struct_0(A_207))) | v4_pre_topc(B_209, A_207) | ~m1_subset_1(B_209, k1_zfmisc_1(u1_struct_0(A_207))) | ~l1_pre_topc(A_207) | ~v2_pre_topc(A_207) | v2_struct_0(A_207))), inference(resolution, [status(thm)], [c_38, c_341])).
% 3.89/1.68  tff(c_347, plain, (![B_209]: (v4_orders_2('#skF_2'('#skF_5', '#skF_6', '#skF_4'('#skF_5', B_209))) | ~r1_waybel_0('#skF_5', '#skF_3'('#skF_5', B_209), '#skF_6') | ~l1_waybel_0('#skF_3'('#skF_5', B_209), '#skF_5') | ~v7_waybel_0('#skF_3'('#skF_5', B_209)) | ~v4_orders_2('#skF_3'('#skF_5', B_209)) | v2_struct_0('#skF_3'('#skF_5', B_209)) | v4_pre_topc(B_209, '#skF_5') | ~m1_subset_1(B_209, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_50, c_345])).
% 3.89/1.68  tff(c_350, plain, (![B_209]: (v4_orders_2('#skF_2'('#skF_5', '#skF_6', '#skF_4'('#skF_5', B_209))) | ~r1_waybel_0('#skF_5', '#skF_3'('#skF_5', B_209), '#skF_6') | ~l1_waybel_0('#skF_3'('#skF_5', B_209), '#skF_5') | ~v7_waybel_0('#skF_3'('#skF_5', B_209)) | ~v4_orders_2('#skF_3'('#skF_5', B_209)) | v2_struct_0('#skF_3'('#skF_5', B_209)) | v4_pre_topc(B_209, '#skF_5') | ~m1_subset_1(B_209, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_347])).
% 3.89/1.68  tff(c_352, plain, (![B_210]: (v4_orders_2('#skF_2'('#skF_5', '#skF_6', '#skF_4'('#skF_5', B_210))) | ~r1_waybel_0('#skF_5', '#skF_3'('#skF_5', B_210), '#skF_6') | ~l1_waybel_0('#skF_3'('#skF_5', B_210), '#skF_5') | ~v7_waybel_0('#skF_3'('#skF_5', B_210)) | ~v4_orders_2('#skF_3'('#skF_5', B_210)) | v2_struct_0('#skF_3'('#skF_5', B_210)) | v4_pre_topc(B_210, '#skF_5') | ~m1_subset_1(B_210, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_56, c_350])).
% 3.89/1.68  tff(c_355, plain, (v4_orders_2('#skF_2'('#skF_5', '#skF_6', '#skF_4'('#skF_5', '#skF_6'))) | ~r1_waybel_0('#skF_5', '#skF_3'('#skF_5', '#skF_6'), '#skF_6') | ~l1_waybel_0('#skF_3'('#skF_5', '#skF_6'), '#skF_5') | ~v7_waybel_0('#skF_3'('#skF_5', '#skF_6')) | ~v4_orders_2('#skF_3'('#skF_5', '#skF_6')) | v2_struct_0('#skF_3'('#skF_5', '#skF_6')) | v4_pre_topc('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_50, c_352])).
% 3.89/1.68  tff(c_358, plain, (v4_orders_2('#skF_2'('#skF_5', '#skF_6', '#skF_4'('#skF_5', '#skF_6'))) | v2_struct_0('#skF_3'('#skF_5', '#skF_6')) | v4_pre_topc('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_113, c_121, c_129, c_138, c_355])).
% 3.89/1.68  tff(c_359, plain, (v4_orders_2('#skF_2'('#skF_5', '#skF_6', '#skF_4'('#skF_5', '#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_97, c_105, c_358])).
% 3.89/1.68  tff(c_26, plain, (![A_23, B_35, C_41]: (v7_waybel_0('#skF_2'(A_23, B_35, C_41)) | ~r2_hidden(C_41, k2_pre_topc(A_23, B_35)) | ~m1_subset_1(C_41, u1_struct_0(A_23)) | ~m1_subset_1(B_35, k1_zfmisc_1(u1_struct_0(A_23))) | ~l1_pre_topc(A_23) | ~v2_pre_topc(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.89/1.68  tff(c_367, plain, (![A_215, B_216, B_217]: (v7_waybel_0('#skF_2'(A_215, B_216, '#skF_4'(A_215, B_217))) | ~r1_waybel_0(A_215, '#skF_3'(A_215, B_217), B_216) | ~l1_waybel_0('#skF_3'(A_215, B_217), A_215) | ~v7_waybel_0('#skF_3'(A_215, B_217)) | ~v4_orders_2('#skF_3'(A_215, B_217)) | v2_struct_0('#skF_3'(A_215, B_217)) | ~m1_subset_1('#skF_4'(A_215, B_217), u1_struct_0(A_215)) | ~m1_subset_1(B_216, k1_zfmisc_1(u1_struct_0(A_215))) | v4_pre_topc(B_217, A_215) | ~m1_subset_1(B_217, k1_zfmisc_1(u1_struct_0(A_215))) | ~l1_pre_topc(A_215) | ~v2_pre_topc(A_215) | v2_struct_0(A_215))), inference(resolution, [status(thm)], [c_244, c_26])).
% 3.89/1.68  tff(c_371, plain, (![A_218, B_219, B_220]: (v7_waybel_0('#skF_2'(A_218, B_219, '#skF_4'(A_218, B_220))) | ~r1_waybel_0(A_218, '#skF_3'(A_218, B_220), B_219) | ~l1_waybel_0('#skF_3'(A_218, B_220), A_218) | ~v7_waybel_0('#skF_3'(A_218, B_220)) | ~v4_orders_2('#skF_3'(A_218, B_220)) | v2_struct_0('#skF_3'(A_218, B_220)) | ~m1_subset_1(B_219, k1_zfmisc_1(u1_struct_0(A_218))) | v4_pre_topc(B_220, A_218) | ~m1_subset_1(B_220, k1_zfmisc_1(u1_struct_0(A_218))) | ~l1_pre_topc(A_218) | ~v2_pre_topc(A_218) | v2_struct_0(A_218))), inference(resolution, [status(thm)], [c_38, c_367])).
% 3.89/1.68  tff(c_373, plain, (![B_220]: (v7_waybel_0('#skF_2'('#skF_5', '#skF_6', '#skF_4'('#skF_5', B_220))) | ~r1_waybel_0('#skF_5', '#skF_3'('#skF_5', B_220), '#skF_6') | ~l1_waybel_0('#skF_3'('#skF_5', B_220), '#skF_5') | ~v7_waybel_0('#skF_3'('#skF_5', B_220)) | ~v4_orders_2('#skF_3'('#skF_5', B_220)) | v2_struct_0('#skF_3'('#skF_5', B_220)) | v4_pre_topc(B_220, '#skF_5') | ~m1_subset_1(B_220, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_50, c_371])).
% 3.89/1.68  tff(c_376, plain, (![B_220]: (v7_waybel_0('#skF_2'('#skF_5', '#skF_6', '#skF_4'('#skF_5', B_220))) | ~r1_waybel_0('#skF_5', '#skF_3'('#skF_5', B_220), '#skF_6') | ~l1_waybel_0('#skF_3'('#skF_5', B_220), '#skF_5') | ~v7_waybel_0('#skF_3'('#skF_5', B_220)) | ~v4_orders_2('#skF_3'('#skF_5', B_220)) | v2_struct_0('#skF_3'('#skF_5', B_220)) | v4_pre_topc(B_220, '#skF_5') | ~m1_subset_1(B_220, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_373])).
% 3.89/1.68  tff(c_378, plain, (![B_221]: (v7_waybel_0('#skF_2'('#skF_5', '#skF_6', '#skF_4'('#skF_5', B_221))) | ~r1_waybel_0('#skF_5', '#skF_3'('#skF_5', B_221), '#skF_6') | ~l1_waybel_0('#skF_3'('#skF_5', B_221), '#skF_5') | ~v7_waybel_0('#skF_3'('#skF_5', B_221)) | ~v4_orders_2('#skF_3'('#skF_5', B_221)) | v2_struct_0('#skF_3'('#skF_5', B_221)) | v4_pre_topc(B_221, '#skF_5') | ~m1_subset_1(B_221, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_56, c_376])).
% 3.89/1.68  tff(c_381, plain, (v7_waybel_0('#skF_2'('#skF_5', '#skF_6', '#skF_4'('#skF_5', '#skF_6'))) | ~r1_waybel_0('#skF_5', '#skF_3'('#skF_5', '#skF_6'), '#skF_6') | ~l1_waybel_0('#skF_3'('#skF_5', '#skF_6'), '#skF_5') | ~v7_waybel_0('#skF_3'('#skF_5', '#skF_6')) | ~v4_orders_2('#skF_3'('#skF_5', '#skF_6')) | v2_struct_0('#skF_3'('#skF_5', '#skF_6')) | v4_pre_topc('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_50, c_378])).
% 3.89/1.68  tff(c_384, plain, (v7_waybel_0('#skF_2'('#skF_5', '#skF_6', '#skF_4'('#skF_5', '#skF_6'))) | v2_struct_0('#skF_3'('#skF_5', '#skF_6')) | v4_pre_topc('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_113, c_121, c_129, c_138, c_381])).
% 3.89/1.68  tff(c_385, plain, (v7_waybel_0('#skF_2'('#skF_5', '#skF_6', '#skF_4'('#skF_5', '#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_97, c_105, c_384])).
% 3.89/1.68  tff(c_22, plain, (![A_23, B_35, C_41]: (l1_waybel_0('#skF_2'(A_23, B_35, C_41), A_23) | ~r2_hidden(C_41, k2_pre_topc(A_23, B_35)) | ~m1_subset_1(C_41, u1_struct_0(A_23)) | ~m1_subset_1(B_35, k1_zfmisc_1(u1_struct_0(A_23))) | ~l1_pre_topc(A_23) | ~v2_pre_topc(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.89/1.68  tff(c_386, plain, (![A_222, B_223, B_224]: (l1_waybel_0('#skF_2'(A_222, B_223, '#skF_4'(A_222, B_224)), A_222) | ~r1_waybel_0(A_222, '#skF_3'(A_222, B_224), B_223) | ~l1_waybel_0('#skF_3'(A_222, B_224), A_222) | ~v7_waybel_0('#skF_3'(A_222, B_224)) | ~v4_orders_2('#skF_3'(A_222, B_224)) | v2_struct_0('#skF_3'(A_222, B_224)) | ~m1_subset_1('#skF_4'(A_222, B_224), u1_struct_0(A_222)) | ~m1_subset_1(B_223, k1_zfmisc_1(u1_struct_0(A_222))) | v4_pre_topc(B_224, A_222) | ~m1_subset_1(B_224, k1_zfmisc_1(u1_struct_0(A_222))) | ~l1_pre_topc(A_222) | ~v2_pre_topc(A_222) | v2_struct_0(A_222))), inference(resolution, [status(thm)], [c_244, c_22])).
% 3.89/1.68  tff(c_390, plain, (![A_225, B_226, B_227]: (l1_waybel_0('#skF_2'(A_225, B_226, '#skF_4'(A_225, B_227)), A_225) | ~r1_waybel_0(A_225, '#skF_3'(A_225, B_227), B_226) | ~l1_waybel_0('#skF_3'(A_225, B_227), A_225) | ~v7_waybel_0('#skF_3'(A_225, B_227)) | ~v4_orders_2('#skF_3'(A_225, B_227)) | v2_struct_0('#skF_3'(A_225, B_227)) | ~m1_subset_1(B_226, k1_zfmisc_1(u1_struct_0(A_225))) | v4_pre_topc(B_227, A_225) | ~m1_subset_1(B_227, k1_zfmisc_1(u1_struct_0(A_225))) | ~l1_pre_topc(A_225) | ~v2_pre_topc(A_225) | v2_struct_0(A_225))), inference(resolution, [status(thm)], [c_38, c_386])).
% 3.89/1.68  tff(c_392, plain, (![B_227]: (l1_waybel_0('#skF_2'('#skF_5', '#skF_6', '#skF_4'('#skF_5', B_227)), '#skF_5') | ~r1_waybel_0('#skF_5', '#skF_3'('#skF_5', B_227), '#skF_6') | ~l1_waybel_0('#skF_3'('#skF_5', B_227), '#skF_5') | ~v7_waybel_0('#skF_3'('#skF_5', B_227)) | ~v4_orders_2('#skF_3'('#skF_5', B_227)) | v2_struct_0('#skF_3'('#skF_5', B_227)) | v4_pre_topc(B_227, '#skF_5') | ~m1_subset_1(B_227, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_50, c_390])).
% 3.89/1.68  tff(c_395, plain, (![B_227]: (l1_waybel_0('#skF_2'('#skF_5', '#skF_6', '#skF_4'('#skF_5', B_227)), '#skF_5') | ~r1_waybel_0('#skF_5', '#skF_3'('#skF_5', B_227), '#skF_6') | ~l1_waybel_0('#skF_3'('#skF_5', B_227), '#skF_5') | ~v7_waybel_0('#skF_3'('#skF_5', B_227)) | ~v4_orders_2('#skF_3'('#skF_5', B_227)) | v2_struct_0('#skF_3'('#skF_5', B_227)) | v4_pre_topc(B_227, '#skF_5') | ~m1_subset_1(B_227, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_392])).
% 3.89/1.68  tff(c_397, plain, (![B_228]: (l1_waybel_0('#skF_2'('#skF_5', '#skF_6', '#skF_4'('#skF_5', B_228)), '#skF_5') | ~r1_waybel_0('#skF_5', '#skF_3'('#skF_5', B_228), '#skF_6') | ~l1_waybel_0('#skF_3'('#skF_5', B_228), '#skF_5') | ~v7_waybel_0('#skF_3'('#skF_5', B_228)) | ~v4_orders_2('#skF_3'('#skF_5', B_228)) | v2_struct_0('#skF_3'('#skF_5', B_228)) | v4_pre_topc(B_228, '#skF_5') | ~m1_subset_1(B_228, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_56, c_395])).
% 3.89/1.68  tff(c_400, plain, (l1_waybel_0('#skF_2'('#skF_5', '#skF_6', '#skF_4'('#skF_5', '#skF_6')), '#skF_5') | ~r1_waybel_0('#skF_5', '#skF_3'('#skF_5', '#skF_6'), '#skF_6') | ~l1_waybel_0('#skF_3'('#skF_5', '#skF_6'), '#skF_5') | ~v7_waybel_0('#skF_3'('#skF_5', '#skF_6')) | ~v4_orders_2('#skF_3'('#skF_5', '#skF_6')) | v2_struct_0('#skF_3'('#skF_5', '#skF_6')) | v4_pre_topc('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_50, c_397])).
% 3.89/1.68  tff(c_403, plain, (l1_waybel_0('#skF_2'('#skF_5', '#skF_6', '#skF_4'('#skF_5', '#skF_6')), '#skF_5') | v2_struct_0('#skF_3'('#skF_5', '#skF_6')) | v4_pre_topc('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_113, c_121, c_129, c_138, c_400])).
% 3.89/1.68  tff(c_404, plain, (l1_waybel_0('#skF_2'('#skF_5', '#skF_6', '#skF_4'('#skF_5', '#skF_6')), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_97, c_105, c_403])).
% 3.89/1.68  tff(c_150, plain, (![A_133, B_134, C_135]: (v3_yellow_6('#skF_2'(A_133, B_134, C_135), A_133) | ~r2_hidden(C_135, k2_pre_topc(A_133, B_134)) | ~m1_subset_1(C_135, u1_struct_0(A_133)) | ~m1_subset_1(B_134, k1_zfmisc_1(u1_struct_0(A_133))) | ~l1_pre_topc(A_133) | ~v2_pre_topc(A_133) | v2_struct_0(A_133))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.89/1.68  tff(c_152, plain, (![C_135]: (v3_yellow_6('#skF_2'('#skF_5', '#skF_6', C_135), '#skF_5') | ~r2_hidden(C_135, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_135, u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_50, c_150])).
% 3.89/1.68  tff(c_155, plain, (![C_135]: (v3_yellow_6('#skF_2'('#skF_5', '#skF_6', C_135), '#skF_5') | ~r2_hidden(C_135, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_135, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_152])).
% 3.89/1.68  tff(c_156, plain, (![C_135]: (v3_yellow_6('#skF_2'('#skF_5', '#skF_6', C_135), '#skF_5') | ~r2_hidden(C_135, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_135, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_56, c_155])).
% 3.89/1.68  tff(c_158, plain, (![A_137, B_138, C_139]: (r1_waybel_0(A_137, '#skF_2'(A_137, B_138, C_139), B_138) | ~r2_hidden(C_139, k2_pre_topc(A_137, B_138)) | ~m1_subset_1(C_139, u1_struct_0(A_137)) | ~m1_subset_1(B_138, k1_zfmisc_1(u1_struct_0(A_137))) | ~l1_pre_topc(A_137) | ~v2_pre_topc(A_137) | v2_struct_0(A_137))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.89/1.68  tff(c_160, plain, (![C_139]: (r1_waybel_0('#skF_5', '#skF_2'('#skF_5', '#skF_6', C_139), '#skF_6') | ~r2_hidden(C_139, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_139, u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_50, c_158])).
% 3.89/1.68  tff(c_163, plain, (![C_139]: (r1_waybel_0('#skF_5', '#skF_2'('#skF_5', '#skF_6', C_139), '#skF_6') | ~r2_hidden(C_139, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_139, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_160])).
% 3.89/1.68  tff(c_164, plain, (![C_139]: (r1_waybel_0('#skF_5', '#skF_2'('#skF_5', '#skF_6', C_139), '#skF_6') | ~r2_hidden(C_139, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_139, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_56, c_163])).
% 3.89/1.68  tff(c_18, plain, (![C_41, A_23, B_35]: (r2_hidden(C_41, k10_yellow_6(A_23, '#skF_2'(A_23, B_35, C_41))) | ~r2_hidden(C_41, k2_pre_topc(A_23, B_35)) | ~m1_subset_1(C_41, u1_struct_0(A_23)) | ~m1_subset_1(B_35, k1_zfmisc_1(u1_struct_0(A_23))) | ~l1_pre_topc(A_23) | ~v2_pre_topc(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.89/1.68  tff(c_96, plain, (![D_92, C_90]: (v4_pre_topc('#skF_6', '#skF_5') | r2_hidden(D_92, '#skF_6') | ~r2_hidden(D_92, k10_yellow_6('#skF_5', C_90)) | ~m1_subset_1(D_92, u1_struct_0('#skF_5')) | ~r1_waybel_0('#skF_5', C_90, '#skF_6') | ~l1_waybel_0(C_90, '#skF_5') | ~v3_yellow_6(C_90, '#skF_5') | ~v7_waybel_0(C_90) | ~v4_orders_2(C_90) | v2_struct_0(C_90))), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.89/1.68  tff(c_187, plain, (![D_152, C_153]: (r2_hidden(D_152, '#skF_6') | ~r2_hidden(D_152, k10_yellow_6('#skF_5', C_153)) | ~m1_subset_1(D_152, u1_struct_0('#skF_5')) | ~r1_waybel_0('#skF_5', C_153, '#skF_6') | ~l1_waybel_0(C_153, '#skF_5') | ~v3_yellow_6(C_153, '#skF_5') | ~v7_waybel_0(C_153) | ~v4_orders_2(C_153) | v2_struct_0(C_153))), inference(negUnitSimplification, [status(thm)], [c_97, c_96])).
% 3.89/1.68  tff(c_191, plain, (![C_41, B_35]: (r2_hidden(C_41, '#skF_6') | ~r1_waybel_0('#skF_5', '#skF_2'('#skF_5', B_35, C_41), '#skF_6') | ~l1_waybel_0('#skF_2'('#skF_5', B_35, C_41), '#skF_5') | ~v3_yellow_6('#skF_2'('#skF_5', B_35, C_41), '#skF_5') | ~v7_waybel_0('#skF_2'('#skF_5', B_35, C_41)) | ~v4_orders_2('#skF_2'('#skF_5', B_35, C_41)) | v2_struct_0('#skF_2'('#skF_5', B_35, C_41)) | ~r2_hidden(C_41, k2_pre_topc('#skF_5', B_35)) | ~m1_subset_1(C_41, u1_struct_0('#skF_5')) | ~m1_subset_1(B_35, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_18, c_187])).
% 3.89/1.68  tff(c_194, plain, (![C_41, B_35]: (r2_hidden(C_41, '#skF_6') | ~r1_waybel_0('#skF_5', '#skF_2'('#skF_5', B_35, C_41), '#skF_6') | ~l1_waybel_0('#skF_2'('#skF_5', B_35, C_41), '#skF_5') | ~v3_yellow_6('#skF_2'('#skF_5', B_35, C_41), '#skF_5') | ~v7_waybel_0('#skF_2'('#skF_5', B_35, C_41)) | ~v4_orders_2('#skF_2'('#skF_5', B_35, C_41)) | v2_struct_0('#skF_2'('#skF_5', B_35, C_41)) | ~r2_hidden(C_41, k2_pre_topc('#skF_5', B_35)) | ~m1_subset_1(C_41, u1_struct_0('#skF_5')) | ~m1_subset_1(B_35, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_191])).
% 3.89/1.68  tff(c_232, plain, (![C_170, B_171]: (r2_hidden(C_170, '#skF_6') | ~r1_waybel_0('#skF_5', '#skF_2'('#skF_5', B_171, C_170), '#skF_6') | ~l1_waybel_0('#skF_2'('#skF_5', B_171, C_170), '#skF_5') | ~v3_yellow_6('#skF_2'('#skF_5', B_171, C_170), '#skF_5') | ~v7_waybel_0('#skF_2'('#skF_5', B_171, C_170)) | ~v4_orders_2('#skF_2'('#skF_5', B_171, C_170)) | v2_struct_0('#skF_2'('#skF_5', B_171, C_170)) | ~r2_hidden(C_170, k2_pre_topc('#skF_5', B_171)) | ~m1_subset_1(C_170, u1_struct_0('#skF_5')) | ~m1_subset_1(B_171, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_56, c_194])).
% 3.89/1.68  tff(c_234, plain, (![C_139]: (r2_hidden(C_139, '#skF_6') | ~l1_waybel_0('#skF_2'('#skF_5', '#skF_6', C_139), '#skF_5') | ~v3_yellow_6('#skF_2'('#skF_5', '#skF_6', C_139), '#skF_5') | ~v7_waybel_0('#skF_2'('#skF_5', '#skF_6', C_139)) | ~v4_orders_2('#skF_2'('#skF_5', '#skF_6', C_139)) | v2_struct_0('#skF_2'('#skF_5', '#skF_6', C_139)) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r2_hidden(C_139, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_139, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_164, c_232])).
% 3.89/1.68  tff(c_238, plain, (![C_172]: (r2_hidden(C_172, '#skF_6') | ~l1_waybel_0('#skF_2'('#skF_5', '#skF_6', C_172), '#skF_5') | ~v3_yellow_6('#skF_2'('#skF_5', '#skF_6', C_172), '#skF_5') | ~v7_waybel_0('#skF_2'('#skF_5', '#skF_6', C_172)) | ~v4_orders_2('#skF_2'('#skF_5', '#skF_6', C_172)) | v2_struct_0('#skF_2'('#skF_5', '#skF_6', C_172)) | ~r2_hidden(C_172, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_172, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_234])).
% 3.89/1.68  tff(c_242, plain, (![C_135]: (r2_hidden(C_135, '#skF_6') | ~l1_waybel_0('#skF_2'('#skF_5', '#skF_6', C_135), '#skF_5') | ~v7_waybel_0('#skF_2'('#skF_5', '#skF_6', C_135)) | ~v4_orders_2('#skF_2'('#skF_5', '#skF_6', C_135)) | v2_struct_0('#skF_2'('#skF_5', '#skF_6', C_135)) | ~r2_hidden(C_135, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_135, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_156, c_238])).
% 3.89/1.68  tff(c_248, plain, (![B_175]: (r2_hidden('#skF_4'('#skF_5', B_175), '#skF_6') | ~l1_waybel_0('#skF_2'('#skF_5', '#skF_6', '#skF_4'('#skF_5', B_175)), '#skF_5') | ~v7_waybel_0('#skF_2'('#skF_5', '#skF_6', '#skF_4'('#skF_5', B_175))) | ~v4_orders_2('#skF_2'('#skF_5', '#skF_6', '#skF_4'('#skF_5', B_175))) | v2_struct_0('#skF_2'('#skF_5', '#skF_6', '#skF_4'('#skF_5', B_175))) | ~r1_waybel_0('#skF_5', '#skF_3'('#skF_5', B_175), '#skF_6') | ~l1_waybel_0('#skF_3'('#skF_5', B_175), '#skF_5') | ~v7_waybel_0('#skF_3'('#skF_5', B_175)) | ~v4_orders_2('#skF_3'('#skF_5', B_175)) | v2_struct_0('#skF_3'('#skF_5', B_175)) | ~m1_subset_1('#skF_4'('#skF_5', B_175), u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | v4_pre_topc(B_175, '#skF_5') | ~m1_subset_1(B_175, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_244, c_242])).
% 3.89/1.68  tff(c_270, plain, (![B_175]: (r2_hidden('#skF_4'('#skF_5', B_175), '#skF_6') | ~l1_waybel_0('#skF_2'('#skF_5', '#skF_6', '#skF_4'('#skF_5', B_175)), '#skF_5') | ~v7_waybel_0('#skF_2'('#skF_5', '#skF_6', '#skF_4'('#skF_5', B_175))) | ~v4_orders_2('#skF_2'('#skF_5', '#skF_6', '#skF_4'('#skF_5', B_175))) | v2_struct_0('#skF_2'('#skF_5', '#skF_6', '#skF_4'('#skF_5', B_175))) | ~r1_waybel_0('#skF_5', '#skF_3'('#skF_5', B_175), '#skF_6') | ~l1_waybel_0('#skF_3'('#skF_5', B_175), '#skF_5') | ~v7_waybel_0('#skF_3'('#skF_5', B_175)) | ~v4_orders_2('#skF_3'('#skF_5', B_175)) | v2_struct_0('#skF_3'('#skF_5', B_175)) | ~m1_subset_1('#skF_4'('#skF_5', B_175), u1_struct_0('#skF_5')) | v4_pre_topc(B_175, '#skF_5') | ~m1_subset_1(B_175, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_248])).
% 3.89/1.68  tff(c_281, plain, (![B_177]: (r2_hidden('#skF_4'('#skF_5', B_177), '#skF_6') | ~l1_waybel_0('#skF_2'('#skF_5', '#skF_6', '#skF_4'('#skF_5', B_177)), '#skF_5') | ~v7_waybel_0('#skF_2'('#skF_5', '#skF_6', '#skF_4'('#skF_5', B_177))) | ~v4_orders_2('#skF_2'('#skF_5', '#skF_6', '#skF_4'('#skF_5', B_177))) | v2_struct_0('#skF_2'('#skF_5', '#skF_6', '#skF_4'('#skF_5', B_177))) | ~r1_waybel_0('#skF_5', '#skF_3'('#skF_5', B_177), '#skF_6') | ~l1_waybel_0('#skF_3'('#skF_5', B_177), '#skF_5') | ~v7_waybel_0('#skF_3'('#skF_5', B_177)) | ~v4_orders_2('#skF_3'('#skF_5', B_177)) | v2_struct_0('#skF_3'('#skF_5', B_177)) | ~m1_subset_1('#skF_4'('#skF_5', B_177), u1_struct_0('#skF_5')) | v4_pre_topc(B_177, '#skF_5') | ~m1_subset_1(B_177, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_56, c_270])).
% 3.89/1.68  tff(c_285, plain, (![B_59]: (r2_hidden('#skF_4'('#skF_5', B_59), '#skF_6') | ~l1_waybel_0('#skF_2'('#skF_5', '#skF_6', '#skF_4'('#skF_5', B_59)), '#skF_5') | ~v7_waybel_0('#skF_2'('#skF_5', '#skF_6', '#skF_4'('#skF_5', B_59))) | ~v4_orders_2('#skF_2'('#skF_5', '#skF_6', '#skF_4'('#skF_5', B_59))) | v2_struct_0('#skF_2'('#skF_5', '#skF_6', '#skF_4'('#skF_5', B_59))) | ~r1_waybel_0('#skF_5', '#skF_3'('#skF_5', B_59), '#skF_6') | ~l1_waybel_0('#skF_3'('#skF_5', B_59), '#skF_5') | ~v7_waybel_0('#skF_3'('#skF_5', B_59)) | ~v4_orders_2('#skF_3'('#skF_5', B_59)) | v2_struct_0('#skF_3'('#skF_5', B_59)) | v4_pre_topc(B_59, '#skF_5') | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_38, c_281])).
% 3.89/1.68  tff(c_288, plain, (![B_59]: (r2_hidden('#skF_4'('#skF_5', B_59), '#skF_6') | ~l1_waybel_0('#skF_2'('#skF_5', '#skF_6', '#skF_4'('#skF_5', B_59)), '#skF_5') | ~v7_waybel_0('#skF_2'('#skF_5', '#skF_6', '#skF_4'('#skF_5', B_59))) | ~v4_orders_2('#skF_2'('#skF_5', '#skF_6', '#skF_4'('#skF_5', B_59))) | v2_struct_0('#skF_2'('#skF_5', '#skF_6', '#skF_4'('#skF_5', B_59))) | ~r1_waybel_0('#skF_5', '#skF_3'('#skF_5', B_59), '#skF_6') | ~l1_waybel_0('#skF_3'('#skF_5', B_59), '#skF_5') | ~v7_waybel_0('#skF_3'('#skF_5', B_59)) | ~v4_orders_2('#skF_3'('#skF_5', B_59)) | v2_struct_0('#skF_3'('#skF_5', B_59)) | v4_pre_topc(B_59, '#skF_5') | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_285])).
% 3.89/1.68  tff(c_424, plain, (![B_236]: (r2_hidden('#skF_4'('#skF_5', B_236), '#skF_6') | ~l1_waybel_0('#skF_2'('#skF_5', '#skF_6', '#skF_4'('#skF_5', B_236)), '#skF_5') | ~v7_waybel_0('#skF_2'('#skF_5', '#skF_6', '#skF_4'('#skF_5', B_236))) | ~v4_orders_2('#skF_2'('#skF_5', '#skF_6', '#skF_4'('#skF_5', B_236))) | v2_struct_0('#skF_2'('#skF_5', '#skF_6', '#skF_4'('#skF_5', B_236))) | ~r1_waybel_0('#skF_5', '#skF_3'('#skF_5', B_236), '#skF_6') | ~l1_waybel_0('#skF_3'('#skF_5', B_236), '#skF_5') | ~v7_waybel_0('#skF_3'('#skF_5', B_236)) | ~v4_orders_2('#skF_3'('#skF_5', B_236)) | v2_struct_0('#skF_3'('#skF_5', B_236)) | v4_pre_topc(B_236, '#skF_5') | ~m1_subset_1(B_236, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_56, c_288])).
% 3.89/1.68  tff(c_427, plain, (r2_hidden('#skF_4'('#skF_5', '#skF_6'), '#skF_6') | ~l1_waybel_0('#skF_2'('#skF_5', '#skF_6', '#skF_4'('#skF_5', '#skF_6')), '#skF_5') | ~v7_waybel_0('#skF_2'('#skF_5', '#skF_6', '#skF_4'('#skF_5', '#skF_6'))) | ~v4_orders_2('#skF_2'('#skF_5', '#skF_6', '#skF_4'('#skF_5', '#skF_6'))) | v2_struct_0('#skF_2'('#skF_5', '#skF_6', '#skF_4'('#skF_5', '#skF_6'))) | ~r1_waybel_0('#skF_5', '#skF_3'('#skF_5', '#skF_6'), '#skF_6') | ~l1_waybel_0('#skF_3'('#skF_5', '#skF_6'), '#skF_5') | ~v7_waybel_0('#skF_3'('#skF_5', '#skF_6')) | ~v4_orders_2('#skF_3'('#skF_5', '#skF_6')) | v2_struct_0('#skF_3'('#skF_5', '#skF_6')) | v4_pre_topc('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_50, c_424])).
% 3.89/1.68  tff(c_430, plain, (r2_hidden('#skF_4'('#skF_5', '#skF_6'), '#skF_6') | v2_struct_0('#skF_2'('#skF_5', '#skF_6', '#skF_4'('#skF_5', '#skF_6'))) | v2_struct_0('#skF_3'('#skF_5', '#skF_6')) | v4_pre_topc('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_113, c_121, c_129, c_138, c_359, c_385, c_404, c_427])).
% 3.89/1.68  tff(c_431, plain, (r2_hidden('#skF_4'('#skF_5', '#skF_6'), '#skF_6') | v2_struct_0('#skF_2'('#skF_5', '#skF_6', '#skF_4'('#skF_5', '#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_97, c_105, c_430])).
% 3.89/1.68  tff(c_432, plain, (v2_struct_0('#skF_2'('#skF_5', '#skF_6', '#skF_4'('#skF_5', '#skF_6')))), inference(splitLeft, [status(thm)], [c_431])).
% 3.89/1.68  tff(c_30, plain, (![A_23, B_35, C_41]: (~v2_struct_0('#skF_2'(A_23, B_35, C_41)) | ~r2_hidden(C_41, k2_pre_topc(A_23, B_35)) | ~m1_subset_1(C_41, u1_struct_0(A_23)) | ~m1_subset_1(B_35, k1_zfmisc_1(u1_struct_0(A_23))) | ~l1_pre_topc(A_23) | ~v2_pre_topc(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.89/1.68  tff(c_277, plain, (![A_174, B_176, B_175]: (~v2_struct_0('#skF_2'(A_174, B_176, '#skF_4'(A_174, B_175))) | ~r1_waybel_0(A_174, '#skF_3'(A_174, B_175), B_176) | ~l1_waybel_0('#skF_3'(A_174, B_175), A_174) | ~v7_waybel_0('#skF_3'(A_174, B_175)) | ~v4_orders_2('#skF_3'(A_174, B_175)) | v2_struct_0('#skF_3'(A_174, B_175)) | ~m1_subset_1('#skF_4'(A_174, B_175), u1_struct_0(A_174)) | ~m1_subset_1(B_176, k1_zfmisc_1(u1_struct_0(A_174))) | v4_pre_topc(B_175, A_174) | ~m1_subset_1(B_175, k1_zfmisc_1(u1_struct_0(A_174))) | ~l1_pre_topc(A_174) | ~v2_pre_topc(A_174) | v2_struct_0(A_174))), inference(resolution, [status(thm)], [c_244, c_30])).
% 3.89/1.68  tff(c_434, plain, (~r1_waybel_0('#skF_5', '#skF_3'('#skF_5', '#skF_6'), '#skF_6') | ~l1_waybel_0('#skF_3'('#skF_5', '#skF_6'), '#skF_5') | ~v7_waybel_0('#skF_3'('#skF_5', '#skF_6')) | ~v4_orders_2('#skF_3'('#skF_5', '#skF_6')) | v2_struct_0('#skF_3'('#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4'('#skF_5', '#skF_6'), u1_struct_0('#skF_5')) | v4_pre_topc('#skF_6', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_432, c_277])).
% 3.89/1.68  tff(c_437, plain, (v2_struct_0('#skF_3'('#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4'('#skF_5', '#skF_6'), u1_struct_0('#skF_5')) | v4_pre_topc('#skF_6', '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_113, c_121, c_129, c_138, c_434])).
% 3.89/1.68  tff(c_438, plain, (~m1_subset_1('#skF_4'('#skF_5', '#skF_6'), u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_56, c_97, c_105, c_437])).
% 3.89/1.68  tff(c_441, plain, (v4_pre_topc('#skF_6', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_38, c_438])).
% 3.89/1.68  tff(c_444, plain, (v4_pre_topc('#skF_6', '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_441])).
% 3.89/1.68  tff(c_446, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_97, c_444])).
% 3.89/1.68  tff(c_447, plain, (r2_hidden('#skF_4'('#skF_5', '#skF_6'), '#skF_6')), inference(splitRight, [status(thm)], [c_431])).
% 3.89/1.68  tff(c_34, plain, (![A_45, B_59]: (~r2_hidden('#skF_4'(A_45, B_59), B_59) | v4_pre_topc(B_59, A_45) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(A_45))) | ~l1_pre_topc(A_45) | ~v2_pre_topc(A_45) | v2_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.89/1.68  tff(c_450, plain, (v4_pre_topc('#skF_6', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_447, c_34])).
% 3.89/1.68  tff(c_453, plain, (v4_pre_topc('#skF_6', '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_450])).
% 3.89/1.68  tff(c_455, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_97, c_453])).
% 3.89/1.68  tff(c_457, plain, (v4_pre_topc('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_74])).
% 3.89/1.68  tff(c_62, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~v4_pre_topc('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.89/1.68  tff(c_471, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_457, c_62])).
% 3.89/1.68  tff(c_64, plain, (r1_waybel_0('#skF_5', '#skF_7', '#skF_6') | ~v4_pre_topc('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.89/1.68  tff(c_469, plain, (r1_waybel_0('#skF_5', '#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_457, c_64])).
% 3.89/1.68  tff(c_456, plain, (~v2_struct_0('#skF_7')), inference(splitRight, [status(thm)], [c_74])).
% 3.89/1.68  tff(c_72, plain, (v4_orders_2('#skF_7') | ~v4_pre_topc('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.89/1.68  tff(c_461, plain, (v4_orders_2('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_457, c_72])).
% 3.89/1.68  tff(c_70, plain, (v7_waybel_0('#skF_7') | ~v4_pre_topc('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.89/1.68  tff(c_459, plain, (v7_waybel_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_457, c_70])).
% 3.89/1.68  tff(c_68, plain, (v3_yellow_6('#skF_7', '#skF_5') | ~v4_pre_topc('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.89/1.68  tff(c_465, plain, (v3_yellow_6('#skF_7', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_457, c_68])).
% 3.89/1.68  tff(c_66, plain, (l1_waybel_0('#skF_7', '#skF_5') | ~v4_pre_topc('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.89/1.68  tff(c_467, plain, (l1_waybel_0('#skF_7', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_457, c_66])).
% 3.89/1.68  tff(c_60, plain, (r2_hidden('#skF_8', k10_yellow_6('#skF_5', '#skF_7')) | ~v4_pre_topc('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.89/1.68  tff(c_473, plain, (r2_hidden('#skF_8', k10_yellow_6('#skF_5', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_457, c_60])).
% 3.89/1.68  tff(c_584, plain, (![C_304, A_305, B_306, D_307]: (r2_hidden(C_304, k2_pre_topc(A_305, B_306)) | ~r2_hidden(C_304, k10_yellow_6(A_305, D_307)) | ~r1_waybel_0(A_305, D_307, B_306) | ~l1_waybel_0(D_307, A_305) | ~v3_yellow_6(D_307, A_305) | ~v7_waybel_0(D_307) | ~v4_orders_2(D_307) | v2_struct_0(D_307) | ~m1_subset_1(C_304, u1_struct_0(A_305)) | ~m1_subset_1(B_306, k1_zfmisc_1(u1_struct_0(A_305))) | ~l1_pre_topc(A_305) | ~v2_pre_topc(A_305) | v2_struct_0(A_305))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.89/1.68  tff(c_588, plain, (![B_306]: (r2_hidden('#skF_8', k2_pre_topc('#skF_5', B_306)) | ~r1_waybel_0('#skF_5', '#skF_7', B_306) | ~l1_waybel_0('#skF_7', '#skF_5') | ~v3_yellow_6('#skF_7', '#skF_5') | ~v7_waybel_0('#skF_7') | ~v4_orders_2('#skF_7') | v2_struct_0('#skF_7') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1(B_306, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_473, c_584])).
% 3.89/1.68  tff(c_592, plain, (![B_306]: (r2_hidden('#skF_8', k2_pre_topc('#skF_5', B_306)) | ~r1_waybel_0('#skF_5', '#skF_7', B_306) | v2_struct_0('#skF_7') | ~m1_subset_1(B_306, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_471, c_461, c_459, c_465, c_467, c_588])).
% 3.89/1.68  tff(c_594, plain, (![B_308]: (r2_hidden('#skF_8', k2_pre_topc('#skF_5', B_308)) | ~r1_waybel_0('#skF_5', '#skF_7', B_308) | ~m1_subset_1(B_308, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_56, c_456, c_592])).
% 3.89/1.68  tff(c_597, plain, (r2_hidden('#skF_8', k2_pre_topc('#skF_5', '#skF_6')) | ~r1_waybel_0('#skF_5', '#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_50, c_594])).
% 3.89/1.68  tff(c_600, plain, (r2_hidden('#skF_8', k2_pre_topc('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_469, c_597])).
% 3.89/1.68  tff(c_14, plain, (![A_1, B_13, C_19]: (~v2_struct_0('#skF_1'(A_1, B_13, C_19)) | ~r2_hidden(C_19, k2_pre_topc(A_1, B_13)) | ~m1_subset_1(C_19, u1_struct_0(A_1)) | ~m1_subset_1(B_13, k1_zfmisc_1(u1_struct_0(A_1))) | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.89/1.68  tff(c_616, plain, (~v2_struct_0('#skF_1'('#skF_5', '#skF_6', '#skF_8')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_600, c_14])).
% 3.89/1.68  tff(c_647, plain, (~v2_struct_0('#skF_1'('#skF_5', '#skF_6', '#skF_8')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_471, c_616])).
% 3.89/1.68  tff(c_648, plain, (~v2_struct_0('#skF_1'('#skF_5', '#skF_6', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_56, c_647])).
% 3.89/1.68  tff(c_58, plain, (~r2_hidden('#skF_8', '#skF_6') | ~v4_pre_topc('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.89/1.68  tff(c_463, plain, (~r2_hidden('#skF_8', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_457, c_58])).
% 3.89/1.68  tff(c_12, plain, (![A_1, B_13, C_19]: (v4_orders_2('#skF_1'(A_1, B_13, C_19)) | ~r2_hidden(C_19, k2_pre_topc(A_1, B_13)) | ~m1_subset_1(C_19, u1_struct_0(A_1)) | ~m1_subset_1(B_13, k1_zfmisc_1(u1_struct_0(A_1))) | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.89/1.68  tff(c_612, plain, (v4_orders_2('#skF_1'('#skF_5', '#skF_6', '#skF_8')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_600, c_12])).
% 3.89/1.68  tff(c_639, plain, (v4_orders_2('#skF_1'('#skF_5', '#skF_6', '#skF_8')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_471, c_612])).
% 3.89/1.68  tff(c_640, plain, (v4_orders_2('#skF_1'('#skF_5', '#skF_6', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_56, c_639])).
% 3.89/1.68  tff(c_10, plain, (![A_1, B_13, C_19]: (v7_waybel_0('#skF_1'(A_1, B_13, C_19)) | ~r2_hidden(C_19, k2_pre_topc(A_1, B_13)) | ~m1_subset_1(C_19, u1_struct_0(A_1)) | ~m1_subset_1(B_13, k1_zfmisc_1(u1_struct_0(A_1))) | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.89/1.68  tff(c_608, plain, (v7_waybel_0('#skF_1'('#skF_5', '#skF_6', '#skF_8')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_600, c_10])).
% 3.89/1.68  tff(c_631, plain, (v7_waybel_0('#skF_1'('#skF_5', '#skF_6', '#skF_8')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_471, c_608])).
% 3.89/1.68  tff(c_632, plain, (v7_waybel_0('#skF_1'('#skF_5', '#skF_6', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_56, c_631])).
% 3.89/1.68  tff(c_8, plain, (![A_1, B_13, C_19]: (l1_waybel_0('#skF_1'(A_1, B_13, C_19), A_1) | ~r2_hidden(C_19, k2_pre_topc(A_1, B_13)) | ~m1_subset_1(C_19, u1_struct_0(A_1)) | ~m1_subset_1(B_13, k1_zfmisc_1(u1_struct_0(A_1))) | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.89/1.68  tff(c_602, plain, (l1_waybel_0('#skF_1'('#skF_5', '#skF_6', '#skF_8'), '#skF_5') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_600, c_8])).
% 3.89/1.68  tff(c_619, plain, (l1_waybel_0('#skF_1'('#skF_5', '#skF_6', '#skF_8'), '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_471, c_602])).
% 3.89/1.68  tff(c_620, plain, (l1_waybel_0('#skF_1'('#skF_5', '#skF_6', '#skF_8'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_56, c_619])).
% 3.89/1.68  tff(c_532, plain, (![A_281, B_282, C_283]: (r1_waybel_0(A_281, '#skF_1'(A_281, B_282, C_283), B_282) | ~r2_hidden(C_283, k2_pre_topc(A_281, B_282)) | ~m1_subset_1(C_283, u1_struct_0(A_281)) | ~m1_subset_1(B_282, k1_zfmisc_1(u1_struct_0(A_281))) | ~l1_pre_topc(A_281) | ~v2_pre_topc(A_281) | v2_struct_0(A_281))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.89/1.68  tff(c_534, plain, (![C_283]: (r1_waybel_0('#skF_5', '#skF_1'('#skF_5', '#skF_6', C_283), '#skF_6') | ~r2_hidden(C_283, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_283, u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_50, c_532])).
% 3.89/1.68  tff(c_537, plain, (![C_283]: (r1_waybel_0('#skF_5', '#skF_1'('#skF_5', '#skF_6', C_283), '#skF_6') | ~r2_hidden(C_283, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_283, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_534])).
% 3.89/1.68  tff(c_538, plain, (![C_283]: (r1_waybel_0('#skF_5', '#skF_1'('#skF_5', '#skF_6', C_283), '#skF_6') | ~r2_hidden(C_283, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_283, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_56, c_537])).
% 3.89/1.68  tff(c_540, plain, (![A_285, B_286, C_287]: (r3_waybel_9(A_285, '#skF_1'(A_285, B_286, C_287), C_287) | ~r2_hidden(C_287, k2_pre_topc(A_285, B_286)) | ~m1_subset_1(C_287, u1_struct_0(A_285)) | ~m1_subset_1(B_286, k1_zfmisc_1(u1_struct_0(A_285))) | ~l1_pre_topc(A_285) | ~v2_pre_topc(A_285) | v2_struct_0(A_285))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.89/1.68  tff(c_542, plain, (![C_287]: (r3_waybel_9('#skF_5', '#skF_1'('#skF_5', '#skF_6', C_287), C_287) | ~r2_hidden(C_287, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_287, u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_50, c_540])).
% 3.89/1.68  tff(c_545, plain, (![C_287]: (r3_waybel_9('#skF_5', '#skF_1'('#skF_5', '#skF_6', C_287), C_287) | ~r2_hidden(C_287, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_287, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_542])).
% 3.89/1.68  tff(c_546, plain, (![C_287]: (r3_waybel_9('#skF_5', '#skF_1'('#skF_5', '#skF_6', C_287), C_287) | ~r2_hidden(C_287, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_287, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_56, c_545])).
% 3.89/1.68  tff(c_574, plain, (![D_300, B_301, A_302, C_303]: (r2_hidden(D_300, B_301) | ~r3_waybel_9(A_302, C_303, D_300) | ~m1_subset_1(D_300, u1_struct_0(A_302)) | ~r1_waybel_0(A_302, C_303, B_301) | ~l1_waybel_0(C_303, A_302) | ~v7_waybel_0(C_303) | ~v4_orders_2(C_303) | v2_struct_0(C_303) | ~v4_pre_topc(B_301, A_302) | ~m1_subset_1(B_301, k1_zfmisc_1(u1_struct_0(A_302))) | ~l1_pre_topc(A_302) | ~v2_pre_topc(A_302) | v2_struct_0(A_302))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.89/1.68  tff(c_576, plain, (![C_287, B_301]: (r2_hidden(C_287, B_301) | ~r1_waybel_0('#skF_5', '#skF_1'('#skF_5', '#skF_6', C_287), B_301) | ~l1_waybel_0('#skF_1'('#skF_5', '#skF_6', C_287), '#skF_5') | ~v7_waybel_0('#skF_1'('#skF_5', '#skF_6', C_287)) | ~v4_orders_2('#skF_1'('#skF_5', '#skF_6', C_287)) | v2_struct_0('#skF_1'('#skF_5', '#skF_6', C_287)) | ~v4_pre_topc(B_301, '#skF_5') | ~m1_subset_1(B_301, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~r2_hidden(C_287, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_287, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_546, c_574])).
% 3.89/1.68  tff(c_581, plain, (![C_287, B_301]: (r2_hidden(C_287, B_301) | ~r1_waybel_0('#skF_5', '#skF_1'('#skF_5', '#skF_6', C_287), B_301) | ~l1_waybel_0('#skF_1'('#skF_5', '#skF_6', C_287), '#skF_5') | ~v7_waybel_0('#skF_1'('#skF_5', '#skF_6', C_287)) | ~v4_orders_2('#skF_1'('#skF_5', '#skF_6', C_287)) | v2_struct_0('#skF_1'('#skF_5', '#skF_6', C_287)) | ~v4_pre_topc(B_301, '#skF_5') | ~m1_subset_1(B_301, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5') | ~r2_hidden(C_287, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_287, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_576])).
% 3.89/1.68  tff(c_688, plain, (![C_317, B_318]: (r2_hidden(C_317, B_318) | ~r1_waybel_0('#skF_5', '#skF_1'('#skF_5', '#skF_6', C_317), B_318) | ~l1_waybel_0('#skF_1'('#skF_5', '#skF_6', C_317), '#skF_5') | ~v7_waybel_0('#skF_1'('#skF_5', '#skF_6', C_317)) | ~v4_orders_2('#skF_1'('#skF_5', '#skF_6', C_317)) | v2_struct_0('#skF_1'('#skF_5', '#skF_6', C_317)) | ~v4_pre_topc(B_318, '#skF_5') | ~m1_subset_1(B_318, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r2_hidden(C_317, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_317, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_56, c_581])).
% 3.89/1.68  tff(c_690, plain, (![C_283]: (r2_hidden(C_283, '#skF_6') | ~l1_waybel_0('#skF_1'('#skF_5', '#skF_6', C_283), '#skF_5') | ~v7_waybel_0('#skF_1'('#skF_5', '#skF_6', C_283)) | ~v4_orders_2('#skF_1'('#skF_5', '#skF_6', C_283)) | v2_struct_0('#skF_1'('#skF_5', '#skF_6', C_283)) | ~v4_pre_topc('#skF_6', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r2_hidden(C_283, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_283, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_538, c_688])).
% 3.89/1.68  tff(c_694, plain, (![C_319]: (r2_hidden(C_319, '#skF_6') | ~l1_waybel_0('#skF_1'('#skF_5', '#skF_6', C_319), '#skF_5') | ~v7_waybel_0('#skF_1'('#skF_5', '#skF_6', C_319)) | ~v4_orders_2('#skF_1'('#skF_5', '#skF_6', C_319)) | v2_struct_0('#skF_1'('#skF_5', '#skF_6', C_319)) | ~r2_hidden(C_319, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_319, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_457, c_690])).
% 3.89/1.68  tff(c_701, plain, (r2_hidden('#skF_8', '#skF_6') | ~l1_waybel_0('#skF_1'('#skF_5', '#skF_6', '#skF_8'), '#skF_5') | ~v7_waybel_0('#skF_1'('#skF_5', '#skF_6', '#skF_8')) | ~v4_orders_2('#skF_1'('#skF_5', '#skF_6', '#skF_8')) | v2_struct_0('#skF_1'('#skF_5', '#skF_6', '#skF_8')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_600, c_694])).
% 3.89/1.68  tff(c_708, plain, (r2_hidden('#skF_8', '#skF_6') | v2_struct_0('#skF_1'('#skF_5', '#skF_6', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_471, c_640, c_632, c_620, c_701])).
% 3.89/1.68  tff(c_710, plain, $false, inference(negUnitSimplification, [status(thm)], [c_648, c_463, c_708])).
% 3.89/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.89/1.68  
% 3.89/1.68  Inference rules
% 3.89/1.68  ----------------------
% 3.89/1.68  #Ref     : 0
% 3.89/1.68  #Sup     : 93
% 3.89/1.68  #Fact    : 0
% 3.89/1.68  #Define  : 0
% 3.89/1.68  #Split   : 8
% 3.89/1.68  #Chain   : 0
% 3.89/1.68  #Close   : 0
% 3.89/1.68  
% 3.89/1.68  Ordering : KBO
% 3.89/1.68  
% 3.89/1.68  Simplification rules
% 3.89/1.68  ----------------------
% 3.89/1.68  #Subsume      : 24
% 3.89/1.68  #Demod        : 190
% 3.89/1.68  #Tautology    : 17
% 3.89/1.68  #SimpNegUnit  : 55
% 3.89/1.68  #BackRed      : 0
% 3.89/1.68  
% 3.89/1.68  #Partial instantiations: 0
% 3.89/1.68  #Strategies tried      : 1
% 3.89/1.68  
% 3.89/1.68  Timing (in seconds)
% 3.89/1.68  ----------------------
% 3.89/1.68  Preprocessing        : 0.34
% 3.89/1.68  Parsing              : 0.17
% 3.89/1.68  CNF conversion       : 0.03
% 3.89/1.68  Main loop            : 0.52
% 3.89/1.68  Inferencing          : 0.21
% 3.89/1.68  Reduction            : 0.15
% 3.89/1.68  Demodulation         : 0.10
% 3.89/1.68  BG Simplification    : 0.03
% 3.89/1.68  Subsumption          : 0.11
% 3.89/1.68  Abstraction          : 0.02
% 3.89/1.68  MUC search           : 0.00
% 3.89/1.68  Cooper               : 0.00
% 4.15/1.68  Total                : 0.94
% 4.15/1.68  Index Insertion      : 0.00
% 4.15/1.68  Index Deletion       : 0.00
% 4.15/1.68  Index Matching       : 0.00
% 4.15/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
