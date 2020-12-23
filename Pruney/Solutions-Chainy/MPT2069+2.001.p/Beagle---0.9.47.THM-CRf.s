%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:38 EST 2020

% Result     : Theorem 4.33s
% Output     : CNFRefutation 4.82s
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
%$ r3_waybel_9 > r1_waybel_7 > r1_waybel_0 > v4_pre_topc > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k2_pre_topc > #nlpp > u1_struct_0 > k3_yellow_1 > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2

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
                    & v1_subset_1(C,u1_struct_0(k3_yellow_1(k2_struct_0(A))))
                    & v2_waybel_0(C,k3_yellow_1(k2_struct_0(A)))
                    & v13_waybel_0(C,k3_yellow_1(k2_struct_0(A)))
                    & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))))) )
                 => ( r2_hidden(B,C)
                   => ! [D] :
                        ( m1_subset_1(D,u1_struct_0(A))
                       => ( r1_waybel_7(A,C,D)
                         => r2_hidden(D,B) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_yellow19)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_yellow19)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_yellow19)).

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
                    & v1_subset_1(D,u1_struct_0(k3_yellow_1(k2_struct_0(A))))
                    & v2_waybel_0(D,k3_yellow_1(k2_struct_0(A)))
                    & v13_waybel_0(D,k3_yellow_1(k2_struct_0(A)))
                    & m1_subset_1(D,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))
                    & r2_hidden(B,D)
                    & r1_waybel_7(A,D,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_yellow19)).

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

tff(c_206,plain,(
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

tff(c_215,plain,(
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
    inference(resolution,[status(thm)],[c_20,c_206])).

tff(c_286,plain,(
    ! [A_186,B_187,B_188] :
      ( r2_hidden('#skF_3'(A_186,B_187),k2_pre_topc(A_186,B_188))
      | ~ r1_waybel_0(A_186,'#skF_2'(A_186,B_187),B_188)
      | ~ l1_waybel_0('#skF_2'(A_186,B_187),A_186)
      | ~ v7_waybel_0('#skF_2'(A_186,B_187))
      | ~ v4_orders_2('#skF_2'(A_186,B_187))
      | v2_struct_0('#skF_2'(A_186,B_187))
      | ~ m1_subset_1('#skF_3'(A_186,B_187),u1_struct_0(A_186))
      | ~ m1_subset_1(B_188,k1_zfmisc_1(u1_struct_0(A_186)))
      | v4_pre_topc(B_187,A_186)
      | ~ m1_subset_1(B_187,k1_zfmisc_1(u1_struct_0(A_186)))
      | ~ l1_pre_topc(A_186)
      | ~ v2_pre_topc(A_186)
      | v2_struct_0(A_186) ) ),
    inference(resolution,[status(thm)],[c_20,c_206])).

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

tff(c_397,plain,(
    ! [B_231,A_232,B_233] :
      ( r2_hidden(B_231,'#skF_4'(A_232,B_231,'#skF_3'(A_232,B_233)))
      | ~ r1_waybel_0(A_232,'#skF_2'(A_232,B_233),B_231)
      | ~ l1_waybel_0('#skF_2'(A_232,B_233),A_232)
      | ~ v7_waybel_0('#skF_2'(A_232,B_233))
      | ~ v4_orders_2('#skF_2'(A_232,B_233))
      | v2_struct_0('#skF_2'(A_232,B_233))
      | ~ m1_subset_1('#skF_3'(A_232,B_233),u1_struct_0(A_232))
      | ~ m1_subset_1(B_231,k1_zfmisc_1(u1_struct_0(A_232)))
      | v4_pre_topc(B_233,A_232)
      | ~ m1_subset_1(B_233,k1_zfmisc_1(u1_struct_0(A_232)))
      | ~ l1_pre_topc(A_232)
      | ~ v2_pre_topc(A_232)
      | v2_struct_0(A_232) ) ),
    inference(resolution,[status(thm)],[c_286,c_38])).

tff(c_42,plain,(
    ! [A_48,B_60,C_66] :
      ( v13_waybel_0('#skF_4'(A_48,B_60,C_66),k3_yellow_1(k2_struct_0(A_48)))
      | ~ r2_hidden(C_66,k2_pre_topc(A_48,B_60))
      | ~ m1_subset_1(C_66,u1_struct_0(A_48))
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ l1_pre_topc(A_48)
      | ~ v2_pre_topc(A_48)
      | v2_struct_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_44,plain,(
    ! [A_48,B_60,C_66] :
      ( v2_waybel_0('#skF_4'(A_48,B_60,C_66),k3_yellow_1(k2_struct_0(A_48)))
      | ~ r2_hidden(C_66,k2_pre_topc(A_48,B_60))
      | ~ m1_subset_1(C_66,u1_struct_0(A_48))
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ l1_pre_topc(A_48)
      | ~ v2_pre_topc(A_48)
      | v2_struct_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_46,plain,(
    ! [A_48,B_60,C_66] :
      ( v1_subset_1('#skF_4'(A_48,B_60,C_66),u1_struct_0(k3_yellow_1(k2_struct_0(A_48))))
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

tff(c_148,plain,(
    ! [A_129,B_130,C_131] :
      ( r1_waybel_7(A_129,'#skF_4'(A_129,B_130,C_131),C_131)
      | ~ r2_hidden(C_131,k2_pre_topc(A_129,B_130))
      | ~ m1_subset_1(C_131,u1_struct_0(A_129))
      | ~ m1_subset_1(B_130,k1_zfmisc_1(u1_struct_0(A_129)))
      | ~ l1_pre_topc(A_129)
      | ~ v2_pre_topc(A_129)
      | v2_struct_0(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_150,plain,(
    ! [C_131] :
      ( r1_waybel_7('#skF_5','#skF_4'('#skF_5','#skF_6',C_131),C_131)
      | ~ r2_hidden(C_131,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_131,u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_50,c_148])).

tff(c_153,plain,(
    ! [C_131] :
      ( r1_waybel_7('#skF_5','#skF_4'('#skF_5','#skF_6',C_131),C_131)
      | ~ r2_hidden(C_131,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_131,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_150])).

tff(c_155,plain,(
    ! [C_132] :
      ( r1_waybel_7('#skF_5','#skF_4'('#skF_5','#skF_6',C_132),C_132)
      | ~ r2_hidden(C_132,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_132,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_153])).

tff(c_96,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_140,plain,(
    ! [D_92,C_90] :
      ( r2_hidden(D_92,'#skF_6')
      | ~ r1_waybel_7('#skF_5',C_90,D_92)
      | ~ m1_subset_1(D_92,u1_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_6',C_90)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))))
      | ~ v13_waybel_0(C_90,k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v2_waybel_0(C_90,k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v1_subset_1(C_90,u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))
      | v1_xboole_0(C_90) ) ),
    inference(negUnitSimplification,[status(thm)],[c_97,c_96])).

tff(c_239,plain,(
    ! [C_168] :
      ( r2_hidden(C_168,'#skF_6')
      | ~ r2_hidden('#skF_6','#skF_4'('#skF_5','#skF_6',C_168))
      | ~ m1_subset_1('#skF_4'('#skF_5','#skF_6',C_168),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))))
      | ~ v13_waybel_0('#skF_4'('#skF_5','#skF_6',C_168),k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v2_waybel_0('#skF_4'('#skF_5','#skF_6',C_168),k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v1_subset_1('#skF_4'('#skF_5','#skF_6',C_168),u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))
      | v1_xboole_0('#skF_4'('#skF_5','#skF_6',C_168))
      | ~ r2_hidden(C_168,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_168,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_155,c_140])).

tff(c_243,plain,(
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
    inference(resolution,[status(thm)],[c_40,c_239])).

tff(c_246,plain,(
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
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_243])).

tff(c_248,plain,(
    ! [C_169] :
      ( r2_hidden(C_169,'#skF_6')
      | ~ r2_hidden('#skF_6','#skF_4'('#skF_5','#skF_6',C_169))
      | ~ v13_waybel_0('#skF_4'('#skF_5','#skF_6',C_169),k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v2_waybel_0('#skF_4'('#skF_5','#skF_6',C_169),k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v1_subset_1('#skF_4'('#skF_5','#skF_6',C_169),u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))
      | v1_xboole_0('#skF_4'('#skF_5','#skF_6',C_169))
      | ~ r2_hidden(C_169,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_169,u1_struct_0('#skF_5')) ) ),
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
    inference(resolution,[status(thm)],[c_46,c_248])).

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
    ! [C_170] :
      ( r2_hidden(C_170,'#skF_6')
      | ~ r2_hidden('#skF_6','#skF_4'('#skF_5','#skF_6',C_170))
      | ~ v13_waybel_0('#skF_4'('#skF_5','#skF_6',C_170),k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v2_waybel_0('#skF_4'('#skF_5','#skF_6',C_170),k3_yellow_1(k2_struct_0('#skF_5')))
      | v1_xboole_0('#skF_4'('#skF_5','#skF_6',C_170))
      | ~ r2_hidden(C_170,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_170,u1_struct_0('#skF_5')) ) ),
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
    inference(resolution,[status(thm)],[c_44,c_257])).

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
    ! [C_171] :
      ( r2_hidden(C_171,'#skF_6')
      | ~ r2_hidden('#skF_6','#skF_4'('#skF_5','#skF_6',C_171))
      | ~ v13_waybel_0('#skF_4'('#skF_5','#skF_6',C_171),k3_yellow_1(k2_struct_0('#skF_5')))
      | v1_xboole_0('#skF_4'('#skF_5','#skF_6',C_171))
      | ~ r2_hidden(C_171,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_171,u1_struct_0('#skF_5')) ) ),
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
    inference(resolution,[status(thm)],[c_42,c_266])).

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

tff(c_403,plain,(
    ! [B_233] :
      ( r2_hidden('#skF_3'('#skF_5',B_233),'#skF_6')
      | v1_xboole_0('#skF_4'('#skF_5','#skF_6','#skF_3'('#skF_5',B_233)))
      | ~ r2_hidden('#skF_3'('#skF_5',B_233),k2_pre_topc('#skF_5','#skF_6'))
      | ~ r1_waybel_0('#skF_5','#skF_2'('#skF_5',B_233),'#skF_6')
      | ~ l1_waybel_0('#skF_2'('#skF_5',B_233),'#skF_5')
      | ~ v7_waybel_0('#skF_2'('#skF_5',B_233))
      | ~ v4_orders_2('#skF_2'('#skF_5',B_233))
      | v2_struct_0('#skF_2'('#skF_5',B_233))
      | ~ m1_subset_1('#skF_3'('#skF_5',B_233),u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v4_pre_topc(B_233,'#skF_5')
      | ~ m1_subset_1(B_233,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_397,c_274])).

tff(c_410,plain,(
    ! [B_233] :
      ( r2_hidden('#skF_3'('#skF_5',B_233),'#skF_6')
      | v1_xboole_0('#skF_4'('#skF_5','#skF_6','#skF_3'('#skF_5',B_233)))
      | ~ r2_hidden('#skF_3'('#skF_5',B_233),k2_pre_topc('#skF_5','#skF_6'))
      | ~ r1_waybel_0('#skF_5','#skF_2'('#skF_5',B_233),'#skF_6')
      | ~ l1_waybel_0('#skF_2'('#skF_5',B_233),'#skF_5')
      | ~ v7_waybel_0('#skF_2'('#skF_5',B_233))
      | ~ v4_orders_2('#skF_2'('#skF_5',B_233))
      | v2_struct_0('#skF_2'('#skF_5',B_233))
      | ~ m1_subset_1('#skF_3'('#skF_5',B_233),u1_struct_0('#skF_5'))
      | v4_pre_topc(B_233,'#skF_5')
      | ~ m1_subset_1(B_233,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_403])).

tff(c_412,plain,(
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
    inference(negUnitSimplification,[status(thm)],[c_56,c_410])).

tff(c_416,plain,(
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
    inference(resolution,[status(thm)],[c_215,c_412])).

tff(c_419,plain,(
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
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_416])).

tff(c_421,plain,(
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
    inference(negUnitSimplification,[status(thm)],[c_56,c_419])).

tff(c_425,plain,(
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
    inference(resolution,[status(thm)],[c_22,c_421])).

tff(c_428,plain,(
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
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_425])).

tff(c_430,plain,(
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
    inference(negUnitSimplification,[status(thm)],[c_56,c_428])).

tff(c_433,plain,
    ( r2_hidden('#skF_3'('#skF_5','#skF_6'),'#skF_6')
    | v1_xboole_0('#skF_4'('#skF_5','#skF_6','#skF_3'('#skF_5','#skF_6')))
    | ~ r1_waybel_0('#skF_5','#skF_2'('#skF_5','#skF_6'),'#skF_6')
    | ~ l1_waybel_0('#skF_2'('#skF_5','#skF_6'),'#skF_5')
    | ~ v7_waybel_0('#skF_2'('#skF_5','#skF_6'))
    | ~ v4_orders_2('#skF_2'('#skF_5','#skF_6'))
    | v2_struct_0('#skF_2'('#skF_5','#skF_6'))
    | v4_pre_topc('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_430])).

tff(c_436,plain,
    ( r2_hidden('#skF_3'('#skF_5','#skF_6'),'#skF_6')
    | v1_xboole_0('#skF_4'('#skF_5','#skF_6','#skF_3'('#skF_5','#skF_6')))
    | v2_struct_0('#skF_2'('#skF_5','#skF_6'))
    | v4_pre_topc('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_121,c_129,c_138,c_433])).

tff(c_437,plain,
    ( r2_hidden('#skF_3'('#skF_5','#skF_6'),'#skF_6')
    | v1_xboole_0('#skF_4'('#skF_5','#skF_6','#skF_3'('#skF_5','#skF_6'))) ),
    inference(negUnitSimplification,[status(thm)],[c_97,c_105,c_436])).

tff(c_438,plain,(
    v1_xboole_0('#skF_4'('#skF_5','#skF_6','#skF_3'('#skF_5','#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_437])).

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

tff(c_305,plain,(
    ! [A_186,B_188,B_187] :
      ( ~ v1_xboole_0('#skF_4'(A_186,B_188,'#skF_3'(A_186,B_187)))
      | ~ r1_waybel_0(A_186,'#skF_2'(A_186,B_187),B_188)
      | ~ l1_waybel_0('#skF_2'(A_186,B_187),A_186)
      | ~ v7_waybel_0('#skF_2'(A_186,B_187))
      | ~ v4_orders_2('#skF_2'(A_186,B_187))
      | v2_struct_0('#skF_2'(A_186,B_187))
      | ~ m1_subset_1('#skF_3'(A_186,B_187),u1_struct_0(A_186))
      | ~ m1_subset_1(B_188,k1_zfmisc_1(u1_struct_0(A_186)))
      | v4_pre_topc(B_187,A_186)
      | ~ m1_subset_1(B_187,k1_zfmisc_1(u1_struct_0(A_186)))
      | ~ l1_pre_topc(A_186)
      | ~ v2_pre_topc(A_186)
      | v2_struct_0(A_186) ) ),
    inference(resolution,[status(thm)],[c_286,c_48])).

tff(c_440,plain,
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
    inference(resolution,[status(thm)],[c_438,c_305])).

tff(c_443,plain,
    ( v2_struct_0('#skF_2'('#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_3'('#skF_5','#skF_6'),u1_struct_0('#skF_5'))
    | v4_pre_topc('#skF_6','#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_113,c_121,c_129,c_138,c_440])).

tff(c_444,plain,(
    ~ m1_subset_1('#skF_3'('#skF_5','#skF_6'),u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_97,c_105,c_443])).

tff(c_447,plain,
    ( v4_pre_topc('#skF_6','#skF_5')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_22,c_444])).

tff(c_450,plain,
    ( v4_pre_topc('#skF_6','#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_447])).

tff(c_452,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_97,c_450])).

tff(c_453,plain,(
    r2_hidden('#skF_3'('#skF_5','#skF_6'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_437])).

tff(c_18,plain,(
    ! [A_23,B_37] :
      ( ~ r2_hidden('#skF_3'(A_23,B_37),B_37)
      | v4_pre_topc(B_37,A_23)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_463,plain,
    ( v4_pre_topc('#skF_6','#skF_5')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_453,c_18])).

tff(c_466,plain,
    ( v4_pre_topc('#skF_6','#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_463])).

tff(c_468,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_97,c_466])).

tff(c_470,plain,(
    v4_pre_topc('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_62,plain,
    ( m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ v4_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_478,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_470,c_62])).

tff(c_64,plain,
    ( r2_hidden('#skF_6','#skF_7')
    | ~ v4_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_472,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_470,c_64])).

tff(c_469,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_72,plain,
    ( v1_subset_1('#skF_7',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))
    | ~ v4_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_484,plain,(
    v1_subset_1('#skF_7',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_470,c_72])).

tff(c_70,plain,
    ( v2_waybel_0('#skF_7',k3_yellow_1(k2_struct_0('#skF_5')))
    | ~ v4_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_480,plain,(
    v2_waybel_0('#skF_7',k3_yellow_1(k2_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_470,c_70])).

tff(c_68,plain,
    ( v13_waybel_0('#skF_7',k3_yellow_1(k2_struct_0('#skF_5')))
    | ~ v4_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_482,plain,(
    v13_waybel_0('#skF_7',k3_yellow_1(k2_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_470,c_68])).

tff(c_66,plain,
    ( m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))))
    | ~ v4_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_486,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_470,c_66])).

tff(c_60,plain,
    ( r1_waybel_7('#skF_5','#skF_7','#skF_8')
    | ~ v4_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_476,plain,(
    r1_waybel_7('#skF_5','#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_470,c_60])).

tff(c_660,plain,(
    ! [C_318,A_319,B_320,D_321] :
      ( r2_hidden(C_318,k2_pre_topc(A_319,B_320))
      | ~ r1_waybel_7(A_319,D_321,C_318)
      | ~ r2_hidden(B_320,D_321)
      | ~ m1_subset_1(D_321,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_319)))))
      | ~ v13_waybel_0(D_321,k3_yellow_1(k2_struct_0(A_319)))
      | ~ v2_waybel_0(D_321,k3_yellow_1(k2_struct_0(A_319)))
      | ~ v1_subset_1(D_321,u1_struct_0(k3_yellow_1(k2_struct_0(A_319))))
      | v1_xboole_0(D_321)
      | ~ m1_subset_1(C_318,u1_struct_0(A_319))
      | ~ m1_subset_1(B_320,k1_zfmisc_1(u1_struct_0(A_319)))
      | ~ l1_pre_topc(A_319)
      | ~ v2_pre_topc(A_319)
      | v2_struct_0(A_319) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_664,plain,(
    ! [B_320] :
      ( r2_hidden('#skF_8',k2_pre_topc('#skF_5',B_320))
      | ~ r2_hidden(B_320,'#skF_7')
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))))
      | ~ v13_waybel_0('#skF_7',k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v2_waybel_0('#skF_7',k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v1_subset_1('#skF_7',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))
      | v1_xboole_0('#skF_7')
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_320,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_476,c_660])).

tff(c_671,plain,(
    ! [B_320] :
      ( r2_hidden('#skF_8',k2_pre_topc('#skF_5',B_320))
      | ~ r2_hidden(B_320,'#skF_7')
      | v1_xboole_0('#skF_7')
      | ~ m1_subset_1(B_320,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_478,c_484,c_480,c_482,c_486,c_664])).

tff(c_673,plain,(
    ! [B_322] :
      ( r2_hidden('#skF_8',k2_pre_topc('#skF_5',B_322))
      | ~ r2_hidden(B_322,'#skF_7')
      | ~ m1_subset_1(B_322,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_469,c_671])).

tff(c_676,plain,
    ( r2_hidden('#skF_8',k2_pre_topc('#skF_5','#skF_6'))
    | ~ r2_hidden('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_50,c_673])).

tff(c_679,plain,(
    r2_hidden('#skF_8',k2_pre_topc('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_472,c_676])).

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
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_478,c_690])).

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
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_478,c_692])).

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
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_478,c_688])).

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
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_478,c_686])).

tff(c_706,plain,(
    l1_waybel_0('#skF_1'('#skF_5','#skF_6','#skF_8'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_705])).

tff(c_58,plain,
    ( ~ r2_hidden('#skF_8','#skF_6')
    | ~ v4_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_474,plain,(
    ~ r2_hidden('#skF_8','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_470,c_58])).

tff(c_576,plain,(
    ! [A_283,B_284,C_285] :
      ( r1_waybel_0(A_283,'#skF_1'(A_283,B_284,C_285),B_284)
      | ~ r2_hidden(C_285,k2_pre_topc(A_283,B_284))
      | ~ m1_subset_1(C_285,u1_struct_0(A_283))
      | ~ m1_subset_1(B_284,k1_zfmisc_1(u1_struct_0(A_283)))
      | ~ l1_pre_topc(A_283)
      | ~ v2_pre_topc(A_283)
      | v2_struct_0(A_283) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_580,plain,(
    ! [C_285] :
      ( r1_waybel_0('#skF_5','#skF_1'('#skF_5','#skF_6',C_285),'#skF_6')
      | ~ r2_hidden(C_285,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_285,u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_50,c_576])).

tff(c_584,plain,(
    ! [C_285] :
      ( r1_waybel_0('#skF_5','#skF_1'('#skF_5','#skF_6',C_285),'#skF_6')
      | ~ r2_hidden(C_285,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_285,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_580])).

tff(c_585,plain,(
    ! [C_285] :
      ( r1_waybel_0('#skF_5','#skF_1'('#skF_5','#skF_6',C_285),'#skF_6')
      | ~ r2_hidden(C_285,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_285,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_584])).

tff(c_565,plain,(
    ! [A_279,B_280,C_281] :
      ( r3_waybel_9(A_279,'#skF_1'(A_279,B_280,C_281),C_281)
      | ~ r2_hidden(C_281,k2_pre_topc(A_279,B_280))
      | ~ m1_subset_1(C_281,u1_struct_0(A_279))
      | ~ m1_subset_1(B_280,k1_zfmisc_1(u1_struct_0(A_279)))
      | ~ l1_pre_topc(A_279)
      | ~ v2_pre_topc(A_279)
      | v2_struct_0(A_279) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_569,plain,(
    ! [C_281] :
      ( r3_waybel_9('#skF_5','#skF_1'('#skF_5','#skF_6',C_281),C_281)
      | ~ r2_hidden(C_281,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_281,u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_50,c_565])).

tff(c_573,plain,(
    ! [C_281] :
      ( r3_waybel_9('#skF_5','#skF_1'('#skF_5','#skF_6',C_281),C_281)
      | ~ r2_hidden(C_281,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_281,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_569])).

tff(c_574,plain,(
    ! [C_281] :
      ( r3_waybel_9('#skF_5','#skF_1'('#skF_5','#skF_6',C_281),C_281)
      | ~ r2_hidden(C_281,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_281,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_573])).

tff(c_629,plain,(
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

tff(c_631,plain,(
    ! [C_281,B_304] :
      ( r2_hidden(C_281,B_304)
      | ~ r1_waybel_0('#skF_5','#skF_1'('#skF_5','#skF_6',C_281),B_304)
      | ~ l1_waybel_0('#skF_1'('#skF_5','#skF_6',C_281),'#skF_5')
      | ~ v7_waybel_0('#skF_1'('#skF_5','#skF_6',C_281))
      | ~ v4_orders_2('#skF_1'('#skF_5','#skF_6',C_281))
      | v2_struct_0('#skF_1'('#skF_5','#skF_6',C_281))
      | ~ v4_pre_topc(B_304,'#skF_5')
      | ~ m1_subset_1(B_304,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r2_hidden(C_281,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_281,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_574,c_629])).

tff(c_636,plain,(
    ! [C_281,B_304] :
      ( r2_hidden(C_281,B_304)
      | ~ r1_waybel_0('#skF_5','#skF_1'('#skF_5','#skF_6',C_281),B_304)
      | ~ l1_waybel_0('#skF_1'('#skF_5','#skF_6',C_281),'#skF_5')
      | ~ v7_waybel_0('#skF_1'('#skF_5','#skF_6',C_281))
      | ~ v4_orders_2('#skF_1'('#skF_5','#skF_6',C_281))
      | v2_struct_0('#skF_1'('#skF_5','#skF_6',C_281))
      | ~ v4_pre_topc(B_304,'#skF_5')
      | ~ m1_subset_1(B_304,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v2_struct_0('#skF_5')
      | ~ r2_hidden(C_281,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_281,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_631])).

tff(c_651,plain,(
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
    inference(negUnitSimplification,[status(thm)],[c_56,c_636])).

tff(c_653,plain,(
    ! [C_285] :
      ( r2_hidden(C_285,'#skF_6')
      | ~ l1_waybel_0('#skF_1'('#skF_5','#skF_6',C_285),'#skF_5')
      | ~ v7_waybel_0('#skF_1'('#skF_5','#skF_6',C_285))
      | ~ v4_orders_2('#skF_1'('#skF_5','#skF_6',C_285))
      | v2_struct_0('#skF_1'('#skF_5','#skF_6',C_285))
      | ~ v4_pre_topc('#skF_6','#skF_5')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r2_hidden(C_285,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_285,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_585,c_651])).

tff(c_656,plain,(
    ! [C_285] :
      ( r2_hidden(C_285,'#skF_6')
      | ~ l1_waybel_0('#skF_1'('#skF_5','#skF_6',C_285),'#skF_5')
      | ~ v7_waybel_0('#skF_1'('#skF_5','#skF_6',C_285))
      | ~ v4_orders_2('#skF_1'('#skF_5','#skF_6',C_285))
      | v2_struct_0('#skF_1'('#skF_5','#skF_6',C_285))
      | ~ r2_hidden(C_285,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_285,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_470,c_653])).

tff(c_682,plain,
    ( r2_hidden('#skF_8','#skF_6')
    | ~ l1_waybel_0('#skF_1'('#skF_5','#skF_6','#skF_8'),'#skF_5')
    | ~ v7_waybel_0('#skF_1'('#skF_5','#skF_6','#skF_8'))
    | ~ v4_orders_2('#skF_1'('#skF_5','#skF_6','#skF_8'))
    | v2_struct_0('#skF_1'('#skF_5','#skF_6','#skF_8'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_679,c_656])).

tff(c_697,plain,
    ( r2_hidden('#skF_8','#skF_6')
    | ~ l1_waybel_0('#skF_1'('#skF_5','#skF_6','#skF_8'),'#skF_5')
    | ~ v7_waybel_0('#skF_1'('#skF_5','#skF_6','#skF_8'))
    | ~ v4_orders_2('#skF_1'('#skF_5','#skF_6','#skF_8'))
    | v2_struct_0('#skF_1'('#skF_5','#skF_6','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_478,c_682])).

tff(c_698,plain,
    ( ~ l1_waybel_0('#skF_1'('#skF_5','#skF_6','#skF_8'),'#skF_5')
    | ~ v7_waybel_0('#skF_1'('#skF_5','#skF_6','#skF_8'))
    | ~ v4_orders_2('#skF_1'('#skF_5','#skF_6','#skF_8'))
    | v2_struct_0('#skF_1'('#skF_5','#skF_6','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_474,c_697])).

tff(c_724,plain,(
    v2_struct_0('#skF_1'('#skF_5','#skF_6','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_718,c_710,c_706,c_698])).

tff(c_725,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_714,c_724])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:44:40 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.33/1.76  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.62/1.80  
% 4.62/1.80  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.73/1.80  %$ r3_waybel_9 > r1_waybel_7 > r1_waybel_0 > v4_pre_topc > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k2_pre_topc > #nlpp > u1_struct_0 > k3_yellow_1 > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2
% 4.73/1.80  
% 4.73/1.80  %Foreground sorts:
% 4.73/1.80  
% 4.73/1.80  
% 4.73/1.80  %Background operators:
% 4.73/1.80  
% 4.73/1.80  
% 4.73/1.80  %Foreground operators:
% 4.73/1.80  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.73/1.80  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.73/1.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.73/1.80  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.73/1.80  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 4.73/1.80  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 4.73/1.80  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 4.73/1.80  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.73/1.80  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 4.73/1.80  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 4.73/1.80  tff('#skF_7', type, '#skF_7': $i).
% 4.73/1.80  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.73/1.80  tff('#skF_5', type, '#skF_5': $i).
% 4.73/1.80  tff(r3_waybel_9, type, r3_waybel_9: ($i * $i * $i) > $o).
% 4.73/1.80  tff(r1_waybel_0, type, r1_waybel_0: ($i * $i * $i) > $o).
% 4.73/1.80  tff('#skF_6', type, '#skF_6': $i).
% 4.73/1.80  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 4.73/1.80  tff(r1_waybel_7, type, r1_waybel_7: ($i * $i * $i) > $o).
% 4.73/1.80  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.73/1.80  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 4.73/1.80  tff('#skF_8', type, '#skF_8': $i).
% 4.73/1.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.73/1.80  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 4.73/1.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.73/1.80  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.73/1.80  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 4.73/1.80  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.73/1.80  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.73/1.80  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.73/1.80  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.73/1.80  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.73/1.80  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.73/1.80  
% 4.82/1.85  tff(f_150, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (![C]: (((((~v1_xboole_0(C) & v1_subset_1(C, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(C, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(C, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (r2_hidden(B, C) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r1_waybel_7(A, C, D) => r2_hidden(D, B)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_yellow19)).
% 4.82/1.85  tff(f_85, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (![C]: ((((~v2_struct_0(C) & v4_orders_2(C)) & v7_waybel_0(C)) & l1_waybel_0(C, A)) => (r1_waybel_0(A, C, B) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r3_waybel_9(A, C, D) => r2_hidden(D, B)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_yellow19)).
% 4.82/1.85  tff(f_54, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, k2_pre_topc(A, B)) <=> (?[D]: (((((~v2_struct_0(D) & v4_orders_2(D)) & v7_waybel_0(D)) & l1_waybel_0(D, A)) & r1_waybel_0(A, D, B)) & r3_waybel_9(A, D, C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_yellow19)).
% 4.82/1.85  tff(f_116, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, k2_pre_topc(A, B)) <=> (?[D]: ((((((~v1_xboole_0(D) & v1_subset_1(D, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(D, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(D, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(D, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) & r2_hidden(B, D)) & r1_waybel_7(A, D, C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_yellow19)).
% 4.82/1.85  tff(c_56, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_150])).
% 4.82/1.85  tff(c_54, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_150])).
% 4.82/1.85  tff(c_52, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_150])).
% 4.82/1.85  tff(c_50, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_150])).
% 4.82/1.85  tff(c_74, plain, (~v1_xboole_0('#skF_7') | ~v4_pre_topc('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_150])).
% 4.82/1.85  tff(c_97, plain, (~v4_pre_topc('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_74])).
% 4.82/1.85  tff(c_22, plain, (![A_23, B_37]: (m1_subset_1('#skF_3'(A_23, B_37), u1_struct_0(A_23)) | v4_pre_topc(B_37, A_23) | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0(A_23))) | ~l1_pre_topc(A_23) | ~v2_pre_topc(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.82/1.85  tff(c_98, plain, (![A_93, B_94]: (~v2_struct_0('#skF_2'(A_93, B_94)) | v4_pre_topc(B_94, A_93) | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0(A_93))) | ~l1_pre_topc(A_93) | ~v2_pre_topc(A_93) | v2_struct_0(A_93))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.82/1.85  tff(c_101, plain, (~v2_struct_0('#skF_2'('#skF_5', '#skF_6')) | v4_pre_topc('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_50, c_98])).
% 4.82/1.85  tff(c_104, plain, (~v2_struct_0('#skF_2'('#skF_5', '#skF_6')) | v4_pre_topc('#skF_6', '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_101])).
% 4.82/1.85  tff(c_105, plain, (~v2_struct_0('#skF_2'('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_56, c_97, c_104])).
% 4.82/1.85  tff(c_106, plain, (![A_95, B_96]: (v4_orders_2('#skF_2'(A_95, B_96)) | v4_pre_topc(B_96, A_95) | ~m1_subset_1(B_96, k1_zfmisc_1(u1_struct_0(A_95))) | ~l1_pre_topc(A_95) | ~v2_pre_topc(A_95) | v2_struct_0(A_95))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.82/1.85  tff(c_109, plain, (v4_orders_2('#skF_2'('#skF_5', '#skF_6')) | v4_pre_topc('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_50, c_106])).
% 4.82/1.85  tff(c_112, plain, (v4_orders_2('#skF_2'('#skF_5', '#skF_6')) | v4_pre_topc('#skF_6', '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_109])).
% 4.82/1.85  tff(c_113, plain, (v4_orders_2('#skF_2'('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_56, c_97, c_112])).
% 4.82/1.85  tff(c_114, plain, (![A_97, B_98]: (v7_waybel_0('#skF_2'(A_97, B_98)) | v4_pre_topc(B_98, A_97) | ~m1_subset_1(B_98, k1_zfmisc_1(u1_struct_0(A_97))) | ~l1_pre_topc(A_97) | ~v2_pre_topc(A_97) | v2_struct_0(A_97))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.82/1.85  tff(c_117, plain, (v7_waybel_0('#skF_2'('#skF_5', '#skF_6')) | v4_pre_topc('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_50, c_114])).
% 4.82/1.85  tff(c_120, plain, (v7_waybel_0('#skF_2'('#skF_5', '#skF_6')) | v4_pre_topc('#skF_6', '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_117])).
% 4.82/1.85  tff(c_121, plain, (v7_waybel_0('#skF_2'('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_56, c_97, c_120])).
% 4.82/1.85  tff(c_123, plain, (![A_99, B_100]: (l1_waybel_0('#skF_2'(A_99, B_100), A_99) | v4_pre_topc(B_100, A_99) | ~m1_subset_1(B_100, k1_zfmisc_1(u1_struct_0(A_99))) | ~l1_pre_topc(A_99) | ~v2_pre_topc(A_99) | v2_struct_0(A_99))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.82/1.85  tff(c_125, plain, (l1_waybel_0('#skF_2'('#skF_5', '#skF_6'), '#skF_5') | v4_pre_topc('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_50, c_123])).
% 4.82/1.85  tff(c_128, plain, (l1_waybel_0('#skF_2'('#skF_5', '#skF_6'), '#skF_5') | v4_pre_topc('#skF_6', '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_125])).
% 4.82/1.85  tff(c_129, plain, (l1_waybel_0('#skF_2'('#skF_5', '#skF_6'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_56, c_97, c_128])).
% 4.82/1.85  tff(c_132, plain, (![A_105, B_106]: (r1_waybel_0(A_105, '#skF_2'(A_105, B_106), B_106) | v4_pre_topc(B_106, A_105) | ~m1_subset_1(B_106, k1_zfmisc_1(u1_struct_0(A_105))) | ~l1_pre_topc(A_105) | ~v2_pre_topc(A_105) | v2_struct_0(A_105))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.82/1.85  tff(c_134, plain, (r1_waybel_0('#skF_5', '#skF_2'('#skF_5', '#skF_6'), '#skF_6') | v4_pre_topc('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_50, c_132])).
% 4.82/1.85  tff(c_137, plain, (r1_waybel_0('#skF_5', '#skF_2'('#skF_5', '#skF_6'), '#skF_6') | v4_pre_topc('#skF_6', '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_134])).
% 4.82/1.85  tff(c_138, plain, (r1_waybel_0('#skF_5', '#skF_2'('#skF_5', '#skF_6'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_56, c_97, c_137])).
% 4.82/1.85  tff(c_20, plain, (![A_23, B_37]: (r3_waybel_9(A_23, '#skF_2'(A_23, B_37), '#skF_3'(A_23, B_37)) | v4_pre_topc(B_37, A_23) | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0(A_23))) | ~l1_pre_topc(A_23) | ~v2_pre_topc(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.82/1.85  tff(c_206, plain, (![C_153, A_154, B_155, D_156]: (r2_hidden(C_153, k2_pre_topc(A_154, B_155)) | ~r3_waybel_9(A_154, D_156, C_153) | ~r1_waybel_0(A_154, D_156, B_155) | ~l1_waybel_0(D_156, A_154) | ~v7_waybel_0(D_156) | ~v4_orders_2(D_156) | v2_struct_0(D_156) | ~m1_subset_1(C_153, u1_struct_0(A_154)) | ~m1_subset_1(B_155, k1_zfmisc_1(u1_struct_0(A_154))) | ~l1_pre_topc(A_154) | ~v2_pre_topc(A_154) | v2_struct_0(A_154))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.82/1.85  tff(c_215, plain, (![A_23, B_37, B_155]: (r2_hidden('#skF_3'(A_23, B_37), k2_pre_topc(A_23, B_155)) | ~r1_waybel_0(A_23, '#skF_2'(A_23, B_37), B_155) | ~l1_waybel_0('#skF_2'(A_23, B_37), A_23) | ~v7_waybel_0('#skF_2'(A_23, B_37)) | ~v4_orders_2('#skF_2'(A_23, B_37)) | v2_struct_0('#skF_2'(A_23, B_37)) | ~m1_subset_1('#skF_3'(A_23, B_37), u1_struct_0(A_23)) | ~m1_subset_1(B_155, k1_zfmisc_1(u1_struct_0(A_23))) | v4_pre_topc(B_37, A_23) | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0(A_23))) | ~l1_pre_topc(A_23) | ~v2_pre_topc(A_23) | v2_struct_0(A_23))), inference(resolution, [status(thm)], [c_20, c_206])).
% 4.82/1.85  tff(c_286, plain, (![A_186, B_187, B_188]: (r2_hidden('#skF_3'(A_186, B_187), k2_pre_topc(A_186, B_188)) | ~r1_waybel_0(A_186, '#skF_2'(A_186, B_187), B_188) | ~l1_waybel_0('#skF_2'(A_186, B_187), A_186) | ~v7_waybel_0('#skF_2'(A_186, B_187)) | ~v4_orders_2('#skF_2'(A_186, B_187)) | v2_struct_0('#skF_2'(A_186, B_187)) | ~m1_subset_1('#skF_3'(A_186, B_187), u1_struct_0(A_186)) | ~m1_subset_1(B_188, k1_zfmisc_1(u1_struct_0(A_186))) | v4_pre_topc(B_187, A_186) | ~m1_subset_1(B_187, k1_zfmisc_1(u1_struct_0(A_186))) | ~l1_pre_topc(A_186) | ~v2_pre_topc(A_186) | v2_struct_0(A_186))), inference(resolution, [status(thm)], [c_20, c_206])).
% 4.82/1.85  tff(c_38, plain, (![B_60, A_48, C_66]: (r2_hidden(B_60, '#skF_4'(A_48, B_60, C_66)) | ~r2_hidden(C_66, k2_pre_topc(A_48, B_60)) | ~m1_subset_1(C_66, u1_struct_0(A_48)) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_48))) | ~l1_pre_topc(A_48) | ~v2_pre_topc(A_48) | v2_struct_0(A_48))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.82/1.85  tff(c_397, plain, (![B_231, A_232, B_233]: (r2_hidden(B_231, '#skF_4'(A_232, B_231, '#skF_3'(A_232, B_233))) | ~r1_waybel_0(A_232, '#skF_2'(A_232, B_233), B_231) | ~l1_waybel_0('#skF_2'(A_232, B_233), A_232) | ~v7_waybel_0('#skF_2'(A_232, B_233)) | ~v4_orders_2('#skF_2'(A_232, B_233)) | v2_struct_0('#skF_2'(A_232, B_233)) | ~m1_subset_1('#skF_3'(A_232, B_233), u1_struct_0(A_232)) | ~m1_subset_1(B_231, k1_zfmisc_1(u1_struct_0(A_232))) | v4_pre_topc(B_233, A_232) | ~m1_subset_1(B_233, k1_zfmisc_1(u1_struct_0(A_232))) | ~l1_pre_topc(A_232) | ~v2_pre_topc(A_232) | v2_struct_0(A_232))), inference(resolution, [status(thm)], [c_286, c_38])).
% 4.82/1.85  tff(c_42, plain, (![A_48, B_60, C_66]: (v13_waybel_0('#skF_4'(A_48, B_60, C_66), k3_yellow_1(k2_struct_0(A_48))) | ~r2_hidden(C_66, k2_pre_topc(A_48, B_60)) | ~m1_subset_1(C_66, u1_struct_0(A_48)) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_48))) | ~l1_pre_topc(A_48) | ~v2_pre_topc(A_48) | v2_struct_0(A_48))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.82/1.85  tff(c_44, plain, (![A_48, B_60, C_66]: (v2_waybel_0('#skF_4'(A_48, B_60, C_66), k3_yellow_1(k2_struct_0(A_48))) | ~r2_hidden(C_66, k2_pre_topc(A_48, B_60)) | ~m1_subset_1(C_66, u1_struct_0(A_48)) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_48))) | ~l1_pre_topc(A_48) | ~v2_pre_topc(A_48) | v2_struct_0(A_48))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.82/1.85  tff(c_46, plain, (![A_48, B_60, C_66]: (v1_subset_1('#skF_4'(A_48, B_60, C_66), u1_struct_0(k3_yellow_1(k2_struct_0(A_48)))) | ~r2_hidden(C_66, k2_pre_topc(A_48, B_60)) | ~m1_subset_1(C_66, u1_struct_0(A_48)) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_48))) | ~l1_pre_topc(A_48) | ~v2_pre_topc(A_48) | v2_struct_0(A_48))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.82/1.85  tff(c_40, plain, (![A_48, B_60, C_66]: (m1_subset_1('#skF_4'(A_48, B_60, C_66), k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_48))))) | ~r2_hidden(C_66, k2_pre_topc(A_48, B_60)) | ~m1_subset_1(C_66, u1_struct_0(A_48)) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_48))) | ~l1_pre_topc(A_48) | ~v2_pre_topc(A_48) | v2_struct_0(A_48))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.82/1.85  tff(c_148, plain, (![A_129, B_130, C_131]: (r1_waybel_7(A_129, '#skF_4'(A_129, B_130, C_131), C_131) | ~r2_hidden(C_131, k2_pre_topc(A_129, B_130)) | ~m1_subset_1(C_131, u1_struct_0(A_129)) | ~m1_subset_1(B_130, k1_zfmisc_1(u1_struct_0(A_129))) | ~l1_pre_topc(A_129) | ~v2_pre_topc(A_129) | v2_struct_0(A_129))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.82/1.85  tff(c_150, plain, (![C_131]: (r1_waybel_7('#skF_5', '#skF_4'('#skF_5', '#skF_6', C_131), C_131) | ~r2_hidden(C_131, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_131, u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_50, c_148])).
% 4.82/1.85  tff(c_153, plain, (![C_131]: (r1_waybel_7('#skF_5', '#skF_4'('#skF_5', '#skF_6', C_131), C_131) | ~r2_hidden(C_131, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_131, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_150])).
% 4.82/1.85  tff(c_155, plain, (![C_132]: (r1_waybel_7('#skF_5', '#skF_4'('#skF_5', '#skF_6', C_132), C_132) | ~r2_hidden(C_132, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_132, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_56, c_153])).
% 4.82/1.85  tff(c_96, plain, (![D_92, C_90]: (v4_pre_topc('#skF_6', '#skF_5') | r2_hidden(D_92, '#skF_6') | ~r1_waybel_7('#skF_5', C_90, D_92) | ~m1_subset_1(D_92, u1_struct_0('#skF_5')) | ~r2_hidden('#skF_6', C_90) | ~m1_subset_1(C_90, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))) | ~v13_waybel_0(C_90, k3_yellow_1(k2_struct_0('#skF_5'))) | ~v2_waybel_0(C_90, k3_yellow_1(k2_struct_0('#skF_5'))) | ~v1_subset_1(C_90, u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))) | v1_xboole_0(C_90))), inference(cnfTransformation, [status(thm)], [f_150])).
% 4.82/1.85  tff(c_140, plain, (![D_92, C_90]: (r2_hidden(D_92, '#skF_6') | ~r1_waybel_7('#skF_5', C_90, D_92) | ~m1_subset_1(D_92, u1_struct_0('#skF_5')) | ~r2_hidden('#skF_6', C_90) | ~m1_subset_1(C_90, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))) | ~v13_waybel_0(C_90, k3_yellow_1(k2_struct_0('#skF_5'))) | ~v2_waybel_0(C_90, k3_yellow_1(k2_struct_0('#skF_5'))) | ~v1_subset_1(C_90, u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))) | v1_xboole_0(C_90))), inference(negUnitSimplification, [status(thm)], [c_97, c_96])).
% 4.82/1.85  tff(c_239, plain, (![C_168]: (r2_hidden(C_168, '#skF_6') | ~r2_hidden('#skF_6', '#skF_4'('#skF_5', '#skF_6', C_168)) | ~m1_subset_1('#skF_4'('#skF_5', '#skF_6', C_168), k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))) | ~v13_waybel_0('#skF_4'('#skF_5', '#skF_6', C_168), k3_yellow_1(k2_struct_0('#skF_5'))) | ~v2_waybel_0('#skF_4'('#skF_5', '#skF_6', C_168), k3_yellow_1(k2_struct_0('#skF_5'))) | ~v1_subset_1('#skF_4'('#skF_5', '#skF_6', C_168), u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))) | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', C_168)) | ~r2_hidden(C_168, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_168, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_155, c_140])).
% 4.82/1.85  tff(c_243, plain, (![C_66]: (r2_hidden(C_66, '#skF_6') | ~r2_hidden('#skF_6', '#skF_4'('#skF_5', '#skF_6', C_66)) | ~v13_waybel_0('#skF_4'('#skF_5', '#skF_6', C_66), k3_yellow_1(k2_struct_0('#skF_5'))) | ~v2_waybel_0('#skF_4'('#skF_5', '#skF_6', C_66), k3_yellow_1(k2_struct_0('#skF_5'))) | ~v1_subset_1('#skF_4'('#skF_5', '#skF_6', C_66), u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))) | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', C_66)) | ~r2_hidden(C_66, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_66, u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_40, c_239])).
% 4.82/1.85  tff(c_246, plain, (![C_66]: (r2_hidden(C_66, '#skF_6') | ~r2_hidden('#skF_6', '#skF_4'('#skF_5', '#skF_6', C_66)) | ~v13_waybel_0('#skF_4'('#skF_5', '#skF_6', C_66), k3_yellow_1(k2_struct_0('#skF_5'))) | ~v2_waybel_0('#skF_4'('#skF_5', '#skF_6', C_66), k3_yellow_1(k2_struct_0('#skF_5'))) | ~v1_subset_1('#skF_4'('#skF_5', '#skF_6', C_66), u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))) | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', C_66)) | ~r2_hidden(C_66, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_66, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_243])).
% 4.82/1.85  tff(c_248, plain, (![C_169]: (r2_hidden(C_169, '#skF_6') | ~r2_hidden('#skF_6', '#skF_4'('#skF_5', '#skF_6', C_169)) | ~v13_waybel_0('#skF_4'('#skF_5', '#skF_6', C_169), k3_yellow_1(k2_struct_0('#skF_5'))) | ~v2_waybel_0('#skF_4'('#skF_5', '#skF_6', C_169), k3_yellow_1(k2_struct_0('#skF_5'))) | ~v1_subset_1('#skF_4'('#skF_5', '#skF_6', C_169), u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))) | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', C_169)) | ~r2_hidden(C_169, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_169, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_56, c_246])).
% 4.82/1.85  tff(c_252, plain, (![C_66]: (r2_hidden(C_66, '#skF_6') | ~r2_hidden('#skF_6', '#skF_4'('#skF_5', '#skF_6', C_66)) | ~v13_waybel_0('#skF_4'('#skF_5', '#skF_6', C_66), k3_yellow_1(k2_struct_0('#skF_5'))) | ~v2_waybel_0('#skF_4'('#skF_5', '#skF_6', C_66), k3_yellow_1(k2_struct_0('#skF_5'))) | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', C_66)) | ~r2_hidden(C_66, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_66, u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_46, c_248])).
% 4.82/1.85  tff(c_255, plain, (![C_66]: (r2_hidden(C_66, '#skF_6') | ~r2_hidden('#skF_6', '#skF_4'('#skF_5', '#skF_6', C_66)) | ~v13_waybel_0('#skF_4'('#skF_5', '#skF_6', C_66), k3_yellow_1(k2_struct_0('#skF_5'))) | ~v2_waybel_0('#skF_4'('#skF_5', '#skF_6', C_66), k3_yellow_1(k2_struct_0('#skF_5'))) | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', C_66)) | ~r2_hidden(C_66, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_66, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_252])).
% 4.82/1.85  tff(c_257, plain, (![C_170]: (r2_hidden(C_170, '#skF_6') | ~r2_hidden('#skF_6', '#skF_4'('#skF_5', '#skF_6', C_170)) | ~v13_waybel_0('#skF_4'('#skF_5', '#skF_6', C_170), k3_yellow_1(k2_struct_0('#skF_5'))) | ~v2_waybel_0('#skF_4'('#skF_5', '#skF_6', C_170), k3_yellow_1(k2_struct_0('#skF_5'))) | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', C_170)) | ~r2_hidden(C_170, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_170, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_56, c_255])).
% 4.82/1.85  tff(c_261, plain, (![C_66]: (r2_hidden(C_66, '#skF_6') | ~r2_hidden('#skF_6', '#skF_4'('#skF_5', '#skF_6', C_66)) | ~v13_waybel_0('#skF_4'('#skF_5', '#skF_6', C_66), k3_yellow_1(k2_struct_0('#skF_5'))) | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', C_66)) | ~r2_hidden(C_66, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_66, u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_44, c_257])).
% 4.82/1.85  tff(c_264, plain, (![C_66]: (r2_hidden(C_66, '#skF_6') | ~r2_hidden('#skF_6', '#skF_4'('#skF_5', '#skF_6', C_66)) | ~v13_waybel_0('#skF_4'('#skF_5', '#skF_6', C_66), k3_yellow_1(k2_struct_0('#skF_5'))) | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', C_66)) | ~r2_hidden(C_66, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_66, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_261])).
% 4.82/1.85  tff(c_266, plain, (![C_171]: (r2_hidden(C_171, '#skF_6') | ~r2_hidden('#skF_6', '#skF_4'('#skF_5', '#skF_6', C_171)) | ~v13_waybel_0('#skF_4'('#skF_5', '#skF_6', C_171), k3_yellow_1(k2_struct_0('#skF_5'))) | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', C_171)) | ~r2_hidden(C_171, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_171, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_56, c_264])).
% 4.82/1.85  tff(c_270, plain, (![C_66]: (r2_hidden(C_66, '#skF_6') | ~r2_hidden('#skF_6', '#skF_4'('#skF_5', '#skF_6', C_66)) | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', C_66)) | ~r2_hidden(C_66, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_66, u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_42, c_266])).
% 4.82/1.85  tff(c_273, plain, (![C_66]: (r2_hidden(C_66, '#skF_6') | ~r2_hidden('#skF_6', '#skF_4'('#skF_5', '#skF_6', C_66)) | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', C_66)) | ~r2_hidden(C_66, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_66, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_270])).
% 4.82/1.85  tff(c_274, plain, (![C_66]: (r2_hidden(C_66, '#skF_6') | ~r2_hidden('#skF_6', '#skF_4'('#skF_5', '#skF_6', C_66)) | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', C_66)) | ~r2_hidden(C_66, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_66, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_56, c_273])).
% 4.82/1.85  tff(c_403, plain, (![B_233]: (r2_hidden('#skF_3'('#skF_5', B_233), '#skF_6') | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_233))) | ~r2_hidden('#skF_3'('#skF_5', B_233), k2_pre_topc('#skF_5', '#skF_6')) | ~r1_waybel_0('#skF_5', '#skF_2'('#skF_5', B_233), '#skF_6') | ~l1_waybel_0('#skF_2'('#skF_5', B_233), '#skF_5') | ~v7_waybel_0('#skF_2'('#skF_5', B_233)) | ~v4_orders_2('#skF_2'('#skF_5', B_233)) | v2_struct_0('#skF_2'('#skF_5', B_233)) | ~m1_subset_1('#skF_3'('#skF_5', B_233), u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | v4_pre_topc(B_233, '#skF_5') | ~m1_subset_1(B_233, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_397, c_274])).
% 4.82/1.85  tff(c_410, plain, (![B_233]: (r2_hidden('#skF_3'('#skF_5', B_233), '#skF_6') | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_233))) | ~r2_hidden('#skF_3'('#skF_5', B_233), k2_pre_topc('#skF_5', '#skF_6')) | ~r1_waybel_0('#skF_5', '#skF_2'('#skF_5', B_233), '#skF_6') | ~l1_waybel_0('#skF_2'('#skF_5', B_233), '#skF_5') | ~v7_waybel_0('#skF_2'('#skF_5', B_233)) | ~v4_orders_2('#skF_2'('#skF_5', B_233)) | v2_struct_0('#skF_2'('#skF_5', B_233)) | ~m1_subset_1('#skF_3'('#skF_5', B_233), u1_struct_0('#skF_5')) | v4_pre_topc(B_233, '#skF_5') | ~m1_subset_1(B_233, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_403])).
% 4.82/1.85  tff(c_412, plain, (![B_234]: (r2_hidden('#skF_3'('#skF_5', B_234), '#skF_6') | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_234))) | ~r2_hidden('#skF_3'('#skF_5', B_234), k2_pre_topc('#skF_5', '#skF_6')) | ~r1_waybel_0('#skF_5', '#skF_2'('#skF_5', B_234), '#skF_6') | ~l1_waybel_0('#skF_2'('#skF_5', B_234), '#skF_5') | ~v7_waybel_0('#skF_2'('#skF_5', B_234)) | ~v4_orders_2('#skF_2'('#skF_5', B_234)) | v2_struct_0('#skF_2'('#skF_5', B_234)) | ~m1_subset_1('#skF_3'('#skF_5', B_234), u1_struct_0('#skF_5')) | v4_pre_topc(B_234, '#skF_5') | ~m1_subset_1(B_234, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_56, c_410])).
% 4.82/1.85  tff(c_416, plain, (![B_37]: (r2_hidden('#skF_3'('#skF_5', B_37), '#skF_6') | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_37))) | ~r1_waybel_0('#skF_5', '#skF_2'('#skF_5', B_37), '#skF_6') | ~l1_waybel_0('#skF_2'('#skF_5', B_37), '#skF_5') | ~v7_waybel_0('#skF_2'('#skF_5', B_37)) | ~v4_orders_2('#skF_2'('#skF_5', B_37)) | v2_struct_0('#skF_2'('#skF_5', B_37)) | ~m1_subset_1('#skF_3'('#skF_5', B_37), u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | v4_pre_topc(B_37, '#skF_5') | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_215, c_412])).
% 4.82/1.85  tff(c_419, plain, (![B_37]: (r2_hidden('#skF_3'('#skF_5', B_37), '#skF_6') | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_37))) | ~r1_waybel_0('#skF_5', '#skF_2'('#skF_5', B_37), '#skF_6') | ~l1_waybel_0('#skF_2'('#skF_5', B_37), '#skF_5') | ~v7_waybel_0('#skF_2'('#skF_5', B_37)) | ~v4_orders_2('#skF_2'('#skF_5', B_37)) | v2_struct_0('#skF_2'('#skF_5', B_37)) | ~m1_subset_1('#skF_3'('#skF_5', B_37), u1_struct_0('#skF_5')) | v4_pre_topc(B_37, '#skF_5') | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_416])).
% 4.82/1.86  tff(c_421, plain, (![B_235]: (r2_hidden('#skF_3'('#skF_5', B_235), '#skF_6') | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_235))) | ~r1_waybel_0('#skF_5', '#skF_2'('#skF_5', B_235), '#skF_6') | ~l1_waybel_0('#skF_2'('#skF_5', B_235), '#skF_5') | ~v7_waybel_0('#skF_2'('#skF_5', B_235)) | ~v4_orders_2('#skF_2'('#skF_5', B_235)) | v2_struct_0('#skF_2'('#skF_5', B_235)) | ~m1_subset_1('#skF_3'('#skF_5', B_235), u1_struct_0('#skF_5')) | v4_pre_topc(B_235, '#skF_5') | ~m1_subset_1(B_235, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_56, c_419])).
% 4.82/1.86  tff(c_425, plain, (![B_37]: (r2_hidden('#skF_3'('#skF_5', B_37), '#skF_6') | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_37))) | ~r1_waybel_0('#skF_5', '#skF_2'('#skF_5', B_37), '#skF_6') | ~l1_waybel_0('#skF_2'('#skF_5', B_37), '#skF_5') | ~v7_waybel_0('#skF_2'('#skF_5', B_37)) | ~v4_orders_2('#skF_2'('#skF_5', B_37)) | v2_struct_0('#skF_2'('#skF_5', B_37)) | v4_pre_topc(B_37, '#skF_5') | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_22, c_421])).
% 4.82/1.86  tff(c_428, plain, (![B_37]: (r2_hidden('#skF_3'('#skF_5', B_37), '#skF_6') | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_37))) | ~r1_waybel_0('#skF_5', '#skF_2'('#skF_5', B_37), '#skF_6') | ~l1_waybel_0('#skF_2'('#skF_5', B_37), '#skF_5') | ~v7_waybel_0('#skF_2'('#skF_5', B_37)) | ~v4_orders_2('#skF_2'('#skF_5', B_37)) | v2_struct_0('#skF_2'('#skF_5', B_37)) | v4_pre_topc(B_37, '#skF_5') | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_425])).
% 4.82/1.86  tff(c_430, plain, (![B_236]: (r2_hidden('#skF_3'('#skF_5', B_236), '#skF_6') | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', '#skF_3'('#skF_5', B_236))) | ~r1_waybel_0('#skF_5', '#skF_2'('#skF_5', B_236), '#skF_6') | ~l1_waybel_0('#skF_2'('#skF_5', B_236), '#skF_5') | ~v7_waybel_0('#skF_2'('#skF_5', B_236)) | ~v4_orders_2('#skF_2'('#skF_5', B_236)) | v2_struct_0('#skF_2'('#skF_5', B_236)) | v4_pre_topc(B_236, '#skF_5') | ~m1_subset_1(B_236, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_56, c_428])).
% 4.82/1.86  tff(c_433, plain, (r2_hidden('#skF_3'('#skF_5', '#skF_6'), '#skF_6') | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', '#skF_3'('#skF_5', '#skF_6'))) | ~r1_waybel_0('#skF_5', '#skF_2'('#skF_5', '#skF_6'), '#skF_6') | ~l1_waybel_0('#skF_2'('#skF_5', '#skF_6'), '#skF_5') | ~v7_waybel_0('#skF_2'('#skF_5', '#skF_6')) | ~v4_orders_2('#skF_2'('#skF_5', '#skF_6')) | v2_struct_0('#skF_2'('#skF_5', '#skF_6')) | v4_pre_topc('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_50, c_430])).
% 4.82/1.86  tff(c_436, plain, (r2_hidden('#skF_3'('#skF_5', '#skF_6'), '#skF_6') | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', '#skF_3'('#skF_5', '#skF_6'))) | v2_struct_0('#skF_2'('#skF_5', '#skF_6')) | v4_pre_topc('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_113, c_121, c_129, c_138, c_433])).
% 4.82/1.86  tff(c_437, plain, (r2_hidden('#skF_3'('#skF_5', '#skF_6'), '#skF_6') | v1_xboole_0('#skF_4'('#skF_5', '#skF_6', '#skF_3'('#skF_5', '#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_97, c_105, c_436])).
% 4.82/1.86  tff(c_438, plain, (v1_xboole_0('#skF_4'('#skF_5', '#skF_6', '#skF_3'('#skF_5', '#skF_6')))), inference(splitLeft, [status(thm)], [c_437])).
% 4.82/1.86  tff(c_48, plain, (![A_48, B_60, C_66]: (~v1_xboole_0('#skF_4'(A_48, B_60, C_66)) | ~r2_hidden(C_66, k2_pre_topc(A_48, B_60)) | ~m1_subset_1(C_66, u1_struct_0(A_48)) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_48))) | ~l1_pre_topc(A_48) | ~v2_pre_topc(A_48) | v2_struct_0(A_48))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.82/1.86  tff(c_305, plain, (![A_186, B_188, B_187]: (~v1_xboole_0('#skF_4'(A_186, B_188, '#skF_3'(A_186, B_187))) | ~r1_waybel_0(A_186, '#skF_2'(A_186, B_187), B_188) | ~l1_waybel_0('#skF_2'(A_186, B_187), A_186) | ~v7_waybel_0('#skF_2'(A_186, B_187)) | ~v4_orders_2('#skF_2'(A_186, B_187)) | v2_struct_0('#skF_2'(A_186, B_187)) | ~m1_subset_1('#skF_3'(A_186, B_187), u1_struct_0(A_186)) | ~m1_subset_1(B_188, k1_zfmisc_1(u1_struct_0(A_186))) | v4_pre_topc(B_187, A_186) | ~m1_subset_1(B_187, k1_zfmisc_1(u1_struct_0(A_186))) | ~l1_pre_topc(A_186) | ~v2_pre_topc(A_186) | v2_struct_0(A_186))), inference(resolution, [status(thm)], [c_286, c_48])).
% 4.82/1.86  tff(c_440, plain, (~r1_waybel_0('#skF_5', '#skF_2'('#skF_5', '#skF_6'), '#skF_6') | ~l1_waybel_0('#skF_2'('#skF_5', '#skF_6'), '#skF_5') | ~v7_waybel_0('#skF_2'('#skF_5', '#skF_6')) | ~v4_orders_2('#skF_2'('#skF_5', '#skF_6')) | v2_struct_0('#skF_2'('#skF_5', '#skF_6')) | ~m1_subset_1('#skF_3'('#skF_5', '#skF_6'), u1_struct_0('#skF_5')) | v4_pre_topc('#skF_6', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_438, c_305])).
% 4.82/1.86  tff(c_443, plain, (v2_struct_0('#skF_2'('#skF_5', '#skF_6')) | ~m1_subset_1('#skF_3'('#skF_5', '#skF_6'), u1_struct_0('#skF_5')) | v4_pre_topc('#skF_6', '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_113, c_121, c_129, c_138, c_440])).
% 4.82/1.86  tff(c_444, plain, (~m1_subset_1('#skF_3'('#skF_5', '#skF_6'), u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_56, c_97, c_105, c_443])).
% 4.82/1.86  tff(c_447, plain, (v4_pre_topc('#skF_6', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_22, c_444])).
% 4.82/1.86  tff(c_450, plain, (v4_pre_topc('#skF_6', '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_447])).
% 4.82/1.86  tff(c_452, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_97, c_450])).
% 4.82/1.86  tff(c_453, plain, (r2_hidden('#skF_3'('#skF_5', '#skF_6'), '#skF_6')), inference(splitRight, [status(thm)], [c_437])).
% 4.82/1.86  tff(c_18, plain, (![A_23, B_37]: (~r2_hidden('#skF_3'(A_23, B_37), B_37) | v4_pre_topc(B_37, A_23) | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0(A_23))) | ~l1_pre_topc(A_23) | ~v2_pre_topc(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.82/1.86  tff(c_463, plain, (v4_pre_topc('#skF_6', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_453, c_18])).
% 4.82/1.86  tff(c_466, plain, (v4_pre_topc('#skF_6', '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_463])).
% 4.82/1.86  tff(c_468, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_97, c_466])).
% 4.82/1.86  tff(c_470, plain, (v4_pre_topc('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_74])).
% 4.82/1.86  tff(c_62, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~v4_pre_topc('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_150])).
% 4.82/1.86  tff(c_478, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_470, c_62])).
% 4.82/1.86  tff(c_64, plain, (r2_hidden('#skF_6', '#skF_7') | ~v4_pre_topc('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_150])).
% 4.82/1.86  tff(c_472, plain, (r2_hidden('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_470, c_64])).
% 4.82/1.86  tff(c_469, plain, (~v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_74])).
% 4.82/1.86  tff(c_72, plain, (v1_subset_1('#skF_7', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))) | ~v4_pre_topc('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_150])).
% 4.82/1.86  tff(c_484, plain, (v1_subset_1('#skF_7', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_470, c_72])).
% 4.82/1.86  tff(c_70, plain, (v2_waybel_0('#skF_7', k3_yellow_1(k2_struct_0('#skF_5'))) | ~v4_pre_topc('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_150])).
% 4.82/1.86  tff(c_480, plain, (v2_waybel_0('#skF_7', k3_yellow_1(k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_470, c_70])).
% 4.82/1.86  tff(c_68, plain, (v13_waybel_0('#skF_7', k3_yellow_1(k2_struct_0('#skF_5'))) | ~v4_pre_topc('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_150])).
% 4.82/1.86  tff(c_482, plain, (v13_waybel_0('#skF_7', k3_yellow_1(k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_470, c_68])).
% 4.82/1.86  tff(c_66, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))) | ~v4_pre_topc('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_150])).
% 4.82/1.86  tff(c_486, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))))), inference(demodulation, [status(thm), theory('equality')], [c_470, c_66])).
% 4.82/1.86  tff(c_60, plain, (r1_waybel_7('#skF_5', '#skF_7', '#skF_8') | ~v4_pre_topc('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_150])).
% 4.82/1.86  tff(c_476, plain, (r1_waybel_7('#skF_5', '#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_470, c_60])).
% 4.82/1.86  tff(c_660, plain, (![C_318, A_319, B_320, D_321]: (r2_hidden(C_318, k2_pre_topc(A_319, B_320)) | ~r1_waybel_7(A_319, D_321, C_318) | ~r2_hidden(B_320, D_321) | ~m1_subset_1(D_321, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_319))))) | ~v13_waybel_0(D_321, k3_yellow_1(k2_struct_0(A_319))) | ~v2_waybel_0(D_321, k3_yellow_1(k2_struct_0(A_319))) | ~v1_subset_1(D_321, u1_struct_0(k3_yellow_1(k2_struct_0(A_319)))) | v1_xboole_0(D_321) | ~m1_subset_1(C_318, u1_struct_0(A_319)) | ~m1_subset_1(B_320, k1_zfmisc_1(u1_struct_0(A_319))) | ~l1_pre_topc(A_319) | ~v2_pre_topc(A_319) | v2_struct_0(A_319))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.82/1.86  tff(c_664, plain, (![B_320]: (r2_hidden('#skF_8', k2_pre_topc('#skF_5', B_320)) | ~r2_hidden(B_320, '#skF_7') | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))) | ~v13_waybel_0('#skF_7', k3_yellow_1(k2_struct_0('#skF_5'))) | ~v2_waybel_0('#skF_7', k3_yellow_1(k2_struct_0('#skF_5'))) | ~v1_subset_1('#skF_7', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))) | v1_xboole_0('#skF_7') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1(B_320, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_476, c_660])).
% 4.82/1.86  tff(c_671, plain, (![B_320]: (r2_hidden('#skF_8', k2_pre_topc('#skF_5', B_320)) | ~r2_hidden(B_320, '#skF_7') | v1_xboole_0('#skF_7') | ~m1_subset_1(B_320, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_478, c_484, c_480, c_482, c_486, c_664])).
% 4.82/1.86  tff(c_673, plain, (![B_322]: (r2_hidden('#skF_8', k2_pre_topc('#skF_5', B_322)) | ~r2_hidden(B_322, '#skF_7') | ~m1_subset_1(B_322, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_56, c_469, c_671])).
% 4.82/1.86  tff(c_676, plain, (r2_hidden('#skF_8', k2_pre_topc('#skF_5', '#skF_6')) | ~r2_hidden('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_50, c_673])).
% 4.82/1.86  tff(c_679, plain, (r2_hidden('#skF_8', k2_pre_topc('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_472, c_676])).
% 4.82/1.86  tff(c_14, plain, (![A_1, B_13, C_19]: (~v2_struct_0('#skF_1'(A_1, B_13, C_19)) | ~r2_hidden(C_19, k2_pre_topc(A_1, B_13)) | ~m1_subset_1(C_19, u1_struct_0(A_1)) | ~m1_subset_1(B_13, k1_zfmisc_1(u1_struct_0(A_1))) | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.82/1.86  tff(c_690, plain, (~v2_struct_0('#skF_1'('#skF_5', '#skF_6', '#skF_8')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_679, c_14])).
% 4.82/1.86  tff(c_713, plain, (~v2_struct_0('#skF_1'('#skF_5', '#skF_6', '#skF_8')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_478, c_690])).
% 4.82/1.86  tff(c_714, plain, (~v2_struct_0('#skF_1'('#skF_5', '#skF_6', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_56, c_713])).
% 4.82/1.86  tff(c_12, plain, (![A_1, B_13, C_19]: (v4_orders_2('#skF_1'(A_1, B_13, C_19)) | ~r2_hidden(C_19, k2_pre_topc(A_1, B_13)) | ~m1_subset_1(C_19, u1_struct_0(A_1)) | ~m1_subset_1(B_13, k1_zfmisc_1(u1_struct_0(A_1))) | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.82/1.86  tff(c_692, plain, (v4_orders_2('#skF_1'('#skF_5', '#skF_6', '#skF_8')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_679, c_12])).
% 4.82/1.86  tff(c_717, plain, (v4_orders_2('#skF_1'('#skF_5', '#skF_6', '#skF_8')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_478, c_692])).
% 4.82/1.86  tff(c_718, plain, (v4_orders_2('#skF_1'('#skF_5', '#skF_6', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_56, c_717])).
% 4.82/1.86  tff(c_10, plain, (![A_1, B_13, C_19]: (v7_waybel_0('#skF_1'(A_1, B_13, C_19)) | ~r2_hidden(C_19, k2_pre_topc(A_1, B_13)) | ~m1_subset_1(C_19, u1_struct_0(A_1)) | ~m1_subset_1(B_13, k1_zfmisc_1(u1_struct_0(A_1))) | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.82/1.86  tff(c_688, plain, (v7_waybel_0('#skF_1'('#skF_5', '#skF_6', '#skF_8')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_679, c_10])).
% 4.82/1.86  tff(c_709, plain, (v7_waybel_0('#skF_1'('#skF_5', '#skF_6', '#skF_8')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_478, c_688])).
% 4.82/1.86  tff(c_710, plain, (v7_waybel_0('#skF_1'('#skF_5', '#skF_6', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_56, c_709])).
% 4.82/1.86  tff(c_8, plain, (![A_1, B_13, C_19]: (l1_waybel_0('#skF_1'(A_1, B_13, C_19), A_1) | ~r2_hidden(C_19, k2_pre_topc(A_1, B_13)) | ~m1_subset_1(C_19, u1_struct_0(A_1)) | ~m1_subset_1(B_13, k1_zfmisc_1(u1_struct_0(A_1))) | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.82/1.86  tff(c_686, plain, (l1_waybel_0('#skF_1'('#skF_5', '#skF_6', '#skF_8'), '#skF_5') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_679, c_8])).
% 4.82/1.86  tff(c_705, plain, (l1_waybel_0('#skF_1'('#skF_5', '#skF_6', '#skF_8'), '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_478, c_686])).
% 4.82/1.86  tff(c_706, plain, (l1_waybel_0('#skF_1'('#skF_5', '#skF_6', '#skF_8'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_56, c_705])).
% 4.82/1.86  tff(c_58, plain, (~r2_hidden('#skF_8', '#skF_6') | ~v4_pre_topc('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_150])).
% 4.82/1.86  tff(c_474, plain, (~r2_hidden('#skF_8', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_470, c_58])).
% 4.82/1.86  tff(c_576, plain, (![A_283, B_284, C_285]: (r1_waybel_0(A_283, '#skF_1'(A_283, B_284, C_285), B_284) | ~r2_hidden(C_285, k2_pre_topc(A_283, B_284)) | ~m1_subset_1(C_285, u1_struct_0(A_283)) | ~m1_subset_1(B_284, k1_zfmisc_1(u1_struct_0(A_283))) | ~l1_pre_topc(A_283) | ~v2_pre_topc(A_283) | v2_struct_0(A_283))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.82/1.86  tff(c_580, plain, (![C_285]: (r1_waybel_0('#skF_5', '#skF_1'('#skF_5', '#skF_6', C_285), '#skF_6') | ~r2_hidden(C_285, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_285, u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_50, c_576])).
% 4.82/1.86  tff(c_584, plain, (![C_285]: (r1_waybel_0('#skF_5', '#skF_1'('#skF_5', '#skF_6', C_285), '#skF_6') | ~r2_hidden(C_285, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_285, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_580])).
% 4.82/1.86  tff(c_585, plain, (![C_285]: (r1_waybel_0('#skF_5', '#skF_1'('#skF_5', '#skF_6', C_285), '#skF_6') | ~r2_hidden(C_285, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_285, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_56, c_584])).
% 4.82/1.86  tff(c_565, plain, (![A_279, B_280, C_281]: (r3_waybel_9(A_279, '#skF_1'(A_279, B_280, C_281), C_281) | ~r2_hidden(C_281, k2_pre_topc(A_279, B_280)) | ~m1_subset_1(C_281, u1_struct_0(A_279)) | ~m1_subset_1(B_280, k1_zfmisc_1(u1_struct_0(A_279))) | ~l1_pre_topc(A_279) | ~v2_pre_topc(A_279) | v2_struct_0(A_279))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.82/1.86  tff(c_569, plain, (![C_281]: (r3_waybel_9('#skF_5', '#skF_1'('#skF_5', '#skF_6', C_281), C_281) | ~r2_hidden(C_281, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_281, u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_50, c_565])).
% 4.82/1.86  tff(c_573, plain, (![C_281]: (r3_waybel_9('#skF_5', '#skF_1'('#skF_5', '#skF_6', C_281), C_281) | ~r2_hidden(C_281, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_281, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_569])).
% 4.82/1.86  tff(c_574, plain, (![C_281]: (r3_waybel_9('#skF_5', '#skF_1'('#skF_5', '#skF_6', C_281), C_281) | ~r2_hidden(C_281, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_281, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_56, c_573])).
% 4.82/1.86  tff(c_629, plain, (![D_303, B_304, A_305, C_306]: (r2_hidden(D_303, B_304) | ~r3_waybel_9(A_305, C_306, D_303) | ~m1_subset_1(D_303, u1_struct_0(A_305)) | ~r1_waybel_0(A_305, C_306, B_304) | ~l1_waybel_0(C_306, A_305) | ~v7_waybel_0(C_306) | ~v4_orders_2(C_306) | v2_struct_0(C_306) | ~v4_pre_topc(B_304, A_305) | ~m1_subset_1(B_304, k1_zfmisc_1(u1_struct_0(A_305))) | ~l1_pre_topc(A_305) | ~v2_pre_topc(A_305) | v2_struct_0(A_305))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.82/1.86  tff(c_631, plain, (![C_281, B_304]: (r2_hidden(C_281, B_304) | ~r1_waybel_0('#skF_5', '#skF_1'('#skF_5', '#skF_6', C_281), B_304) | ~l1_waybel_0('#skF_1'('#skF_5', '#skF_6', C_281), '#skF_5') | ~v7_waybel_0('#skF_1'('#skF_5', '#skF_6', C_281)) | ~v4_orders_2('#skF_1'('#skF_5', '#skF_6', C_281)) | v2_struct_0('#skF_1'('#skF_5', '#skF_6', C_281)) | ~v4_pre_topc(B_304, '#skF_5') | ~m1_subset_1(B_304, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~r2_hidden(C_281, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_281, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_574, c_629])).
% 4.82/1.86  tff(c_636, plain, (![C_281, B_304]: (r2_hidden(C_281, B_304) | ~r1_waybel_0('#skF_5', '#skF_1'('#skF_5', '#skF_6', C_281), B_304) | ~l1_waybel_0('#skF_1'('#skF_5', '#skF_6', C_281), '#skF_5') | ~v7_waybel_0('#skF_1'('#skF_5', '#skF_6', C_281)) | ~v4_orders_2('#skF_1'('#skF_5', '#skF_6', C_281)) | v2_struct_0('#skF_1'('#skF_5', '#skF_6', C_281)) | ~v4_pre_topc(B_304, '#skF_5') | ~m1_subset_1(B_304, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5') | ~r2_hidden(C_281, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_281, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_631])).
% 4.82/1.86  tff(c_651, plain, (![C_309, B_310]: (r2_hidden(C_309, B_310) | ~r1_waybel_0('#skF_5', '#skF_1'('#skF_5', '#skF_6', C_309), B_310) | ~l1_waybel_0('#skF_1'('#skF_5', '#skF_6', C_309), '#skF_5') | ~v7_waybel_0('#skF_1'('#skF_5', '#skF_6', C_309)) | ~v4_orders_2('#skF_1'('#skF_5', '#skF_6', C_309)) | v2_struct_0('#skF_1'('#skF_5', '#skF_6', C_309)) | ~v4_pre_topc(B_310, '#skF_5') | ~m1_subset_1(B_310, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r2_hidden(C_309, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_309, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_56, c_636])).
% 4.82/1.86  tff(c_653, plain, (![C_285]: (r2_hidden(C_285, '#skF_6') | ~l1_waybel_0('#skF_1'('#skF_5', '#skF_6', C_285), '#skF_5') | ~v7_waybel_0('#skF_1'('#skF_5', '#skF_6', C_285)) | ~v4_orders_2('#skF_1'('#skF_5', '#skF_6', C_285)) | v2_struct_0('#skF_1'('#skF_5', '#skF_6', C_285)) | ~v4_pre_topc('#skF_6', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r2_hidden(C_285, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_285, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_585, c_651])).
% 4.82/1.86  tff(c_656, plain, (![C_285]: (r2_hidden(C_285, '#skF_6') | ~l1_waybel_0('#skF_1'('#skF_5', '#skF_6', C_285), '#skF_5') | ~v7_waybel_0('#skF_1'('#skF_5', '#skF_6', C_285)) | ~v4_orders_2('#skF_1'('#skF_5', '#skF_6', C_285)) | v2_struct_0('#skF_1'('#skF_5', '#skF_6', C_285)) | ~r2_hidden(C_285, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_285, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_470, c_653])).
% 4.82/1.86  tff(c_682, plain, (r2_hidden('#skF_8', '#skF_6') | ~l1_waybel_0('#skF_1'('#skF_5', '#skF_6', '#skF_8'), '#skF_5') | ~v7_waybel_0('#skF_1'('#skF_5', '#skF_6', '#skF_8')) | ~v4_orders_2('#skF_1'('#skF_5', '#skF_6', '#skF_8')) | v2_struct_0('#skF_1'('#skF_5', '#skF_6', '#skF_8')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_679, c_656])).
% 4.82/1.86  tff(c_697, plain, (r2_hidden('#skF_8', '#skF_6') | ~l1_waybel_0('#skF_1'('#skF_5', '#skF_6', '#skF_8'), '#skF_5') | ~v7_waybel_0('#skF_1'('#skF_5', '#skF_6', '#skF_8')) | ~v4_orders_2('#skF_1'('#skF_5', '#skF_6', '#skF_8')) | v2_struct_0('#skF_1'('#skF_5', '#skF_6', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_478, c_682])).
% 4.82/1.86  tff(c_698, plain, (~l1_waybel_0('#skF_1'('#skF_5', '#skF_6', '#skF_8'), '#skF_5') | ~v7_waybel_0('#skF_1'('#skF_5', '#skF_6', '#skF_8')) | ~v4_orders_2('#skF_1'('#skF_5', '#skF_6', '#skF_8')) | v2_struct_0('#skF_1'('#skF_5', '#skF_6', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_474, c_697])).
% 4.82/1.86  tff(c_724, plain, (v2_struct_0('#skF_1'('#skF_5', '#skF_6', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_718, c_710, c_706, c_698])).
% 4.82/1.86  tff(c_725, plain, $false, inference(negUnitSimplification, [status(thm)], [c_714, c_724])).
% 4.82/1.86  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.82/1.86  
% 4.82/1.86  Inference rules
% 4.82/1.86  ----------------------
% 4.82/1.86  #Ref     : 0
% 4.82/1.86  #Sup     : 101
% 4.82/1.86  #Fact    : 0
% 4.82/1.86  #Define  : 0
% 4.82/1.86  #Split   : 4
% 4.82/1.86  #Chain   : 0
% 4.82/1.86  #Close   : 0
% 4.82/1.86  
% 4.82/1.86  Ordering : KBO
% 4.82/1.86  
% 4.82/1.86  Simplification rules
% 4.82/1.86  ----------------------
% 4.82/1.86  #Subsume      : 37
% 4.82/1.86  #Demod        : 170
% 4.82/1.86  #Tautology    : 18
% 4.82/1.86  #SimpNegUnit  : 51
% 4.82/1.86  #BackRed      : 0
% 4.82/1.86  
% 4.82/1.86  #Partial instantiations: 0
% 4.82/1.86  #Strategies tried      : 1
% 4.82/1.86  
% 4.82/1.86  Timing (in seconds)
% 4.82/1.86  ----------------------
% 4.82/1.86  Preprocessing        : 0.36
% 4.82/1.86  Parsing              : 0.18
% 4.82/1.86  CNF conversion       : 0.04
% 4.82/1.86  Main loop            : 0.66
% 4.82/1.86  Inferencing          : 0.26
% 4.82/1.86  Reduction            : 0.18
% 4.82/1.86  Demodulation         : 0.12
% 4.82/1.86  BG Simplification    : 0.04
% 4.82/1.86  Subsumption          : 0.14
% 4.82/1.86  Abstraction          : 0.02
% 4.82/1.86  MUC search           : 0.00
% 4.82/1.86  Cooper               : 0.00
% 4.82/1.86  Total                : 1.12
% 4.82/1.86  Index Insertion      : 0.00
% 4.82/1.86  Index Deletion       : 0.00
% 4.82/1.86  Index Matching       : 0.00
% 4.82/1.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
