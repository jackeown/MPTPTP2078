%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:17 EST 2020

% Result     : Theorem 3.22s
% Output     : CNFRefutation 3.22s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 276 expanded)
%              Number of leaves         :   38 ( 118 expanded)
%              Depth                    :   20
%              Number of atoms          :  405 (1496 expanded)
%              Number of equality atoms :    3 (  74 expanded)
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

tff(f_193,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_waybel_9)).

tff(f_35,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_163,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_waybel_0(B,A) )
         => r1_waybel_0(A,B,k2_relset_1(u1_struct_0(B),u1_struct_0(A),u1_waybel_0(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_waybel_9)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r2_hidden(C,k2_pre_topc(A,B))
              <=> ( ~ v2_struct_0(A)
                  & ! [D] :
                      ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                     => ~ ( v3_pre_topc(D,A)
                          & r2_hidden(C,D)
                          & r1_xboole_0(B,D) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_pre_topc)).

tff(f_127,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & v4_orders_2(B)
        & v7_waybel_0(B)
        & l1_waybel_0(B,A) )
     => m1_subset_1(k10_yellow_6(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_yellow_6)).

tff(f_77,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_connsp_2)).

tff(f_109,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_yellow_6)).

tff(f_150,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_yellow_6)).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_58,plain,(
    v4_orders_2('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_56,plain,(
    v7_waybel_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_54,plain,(
    l1_waybel_0('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_64,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_4,plain,(
    ! [A_4] :
      ( l1_struct_0(A_4)
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_48,plain,(
    k2_relset_1(u1_struct_0('#skF_7'),u1_struct_0('#skF_5'),u1_waybel_0('#skF_5','#skF_7')) = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_80,plain,(
    ! [A_153,B_154] :
      ( r1_waybel_0(A_153,B_154,k2_relset_1(u1_struct_0(B_154),u1_struct_0(A_153),u1_waybel_0(A_153,B_154)))
      | ~ l1_waybel_0(B_154,A_153)
      | v2_struct_0(B_154)
      | ~ l1_struct_0(A_153)
      | v2_struct_0(A_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_83,plain,
    ( r1_waybel_0('#skF_5','#skF_7','#skF_8')
    | ~ l1_waybel_0('#skF_7','#skF_5')
    | v2_struct_0('#skF_7')
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_80])).

tff(c_85,plain,
    ( r1_waybel_0('#skF_5','#skF_7','#skF_8')
    | v2_struct_0('#skF_7')
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_83])).

tff(c_86,plain,
    ( r1_waybel_0('#skF_5','#skF_7','#skF_8')
    | ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_60,c_85])).

tff(c_87,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_90,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_87])).

tff(c_94,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_90])).

tff(c_95,plain,(
    r1_waybel_0('#skF_5','#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_52,plain,(
    r2_hidden('#skF_6',k10_yellow_6('#skF_5','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_46,plain,(
    ~ r2_hidden('#skF_6',k2_pre_topc('#skF_5','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_62,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_50,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_123,plain,(
    ! [A_161,B_162,C_163] :
      ( v3_pre_topc('#skF_1'(A_161,B_162,C_163),A_161)
      | r2_hidden(C_163,k2_pre_topc(A_161,B_162))
      | v2_struct_0(A_161)
      | ~ m1_subset_1(C_163,u1_struct_0(A_161))
      | ~ m1_subset_1(B_162,k1_zfmisc_1(u1_struct_0(A_161)))
      | ~ l1_pre_topc(A_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_127,plain,(
    ! [C_163] :
      ( v3_pre_topc('#skF_1'('#skF_5','#skF_8',C_163),'#skF_5')
      | r2_hidden(C_163,k2_pre_topc('#skF_5','#skF_8'))
      | v2_struct_0('#skF_5')
      | ~ m1_subset_1(C_163,u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_50,c_123])).

tff(c_131,plain,(
    ! [C_163] :
      ( v3_pre_topc('#skF_1'('#skF_5','#skF_8',C_163),'#skF_5')
      | r2_hidden(C_163,k2_pre_topc('#skF_5','#skF_8'))
      | v2_struct_0('#skF_5')
      | ~ m1_subset_1(C_163,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_127])).

tff(c_132,plain,(
    ! [C_163] :
      ( v3_pre_topc('#skF_1'('#skF_5','#skF_8',C_163),'#skF_5')
      | r2_hidden(C_163,k2_pre_topc('#skF_5','#skF_8'))
      | ~ m1_subset_1(C_163,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_131])).

tff(c_12,plain,(
    ! [A_5,B_17,C_23] :
      ( m1_subset_1('#skF_1'(A_5,B_17,C_23),k1_zfmisc_1(u1_struct_0(A_5)))
      | r2_hidden(C_23,k2_pre_topc(A_5,B_17))
      | v2_struct_0(A_5)
      | ~ m1_subset_1(C_23,u1_struct_0(A_5))
      | ~ m1_subset_1(B_17,k1_zfmisc_1(u1_struct_0(A_5)))
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_101,plain,(
    ! [B_157,A_158,C_159] :
      ( r1_xboole_0(B_157,'#skF_1'(A_158,B_157,C_159))
      | r2_hidden(C_159,k2_pre_topc(A_158,B_157))
      | v2_struct_0(A_158)
      | ~ m1_subset_1(C_159,u1_struct_0(A_158))
      | ~ m1_subset_1(B_157,k1_zfmisc_1(u1_struct_0(A_158)))
      | ~ l1_pre_topc(A_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_105,plain,(
    ! [C_159] :
      ( r1_xboole_0('#skF_8','#skF_1'('#skF_5','#skF_8',C_159))
      | r2_hidden(C_159,k2_pre_topc('#skF_5','#skF_8'))
      | v2_struct_0('#skF_5')
      | ~ m1_subset_1(C_159,u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_50,c_101])).

tff(c_109,plain,(
    ! [C_159] :
      ( r1_xboole_0('#skF_8','#skF_1'('#skF_5','#skF_8',C_159))
      | r2_hidden(C_159,k2_pre_topc('#skF_5','#skF_8'))
      | v2_struct_0('#skF_5')
      | ~ m1_subset_1(C_159,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_105])).

tff(c_111,plain,(
    ! [C_160] :
      ( r1_xboole_0('#skF_8','#skF_1'('#skF_5','#skF_8',C_160))
      | r2_hidden(C_160,k2_pre_topc('#skF_5','#skF_8'))
      | ~ m1_subset_1(C_160,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_109])).

tff(c_116,plain,
    ( r1_xboole_0('#skF_8','#skF_1'('#skF_5','#skF_8','#skF_6'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_111,c_46])).

tff(c_122,plain,(
    r1_xboole_0('#skF_8','#skF_1'('#skF_5','#skF_8','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_116])).

tff(c_250,plain,(
    ! [B_194,D_195,C_196,A_197] :
      ( ~ r1_xboole_0(B_194,D_195)
      | ~ r2_hidden(C_196,D_195)
      | ~ v3_pre_topc(D_195,A_197)
      | ~ m1_subset_1(D_195,k1_zfmisc_1(u1_struct_0(A_197)))
      | ~ r2_hidden(C_196,k2_pre_topc(A_197,B_194))
      | ~ m1_subset_1(C_196,u1_struct_0(A_197))
      | ~ m1_subset_1(B_194,k1_zfmisc_1(u1_struct_0(A_197)))
      | ~ l1_pre_topc(A_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_312,plain,(
    ! [C_221,A_222] :
      ( ~ r2_hidden(C_221,'#skF_1'('#skF_5','#skF_8','#skF_6'))
      | ~ v3_pre_topc('#skF_1'('#skF_5','#skF_8','#skF_6'),A_222)
      | ~ m1_subset_1('#skF_1'('#skF_5','#skF_8','#skF_6'),k1_zfmisc_1(u1_struct_0(A_222)))
      | ~ r2_hidden(C_221,k2_pre_topc(A_222,'#skF_8'))
      | ~ m1_subset_1(C_221,u1_struct_0(A_222))
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0(A_222)))
      | ~ l1_pre_topc(A_222) ) ),
    inference(resolution,[status(thm)],[c_122,c_250])).

tff(c_315,plain,(
    ! [C_221] :
      ( ~ r2_hidden(C_221,'#skF_1'('#skF_5','#skF_8','#skF_6'))
      | ~ v3_pre_topc('#skF_1'('#skF_5','#skF_8','#skF_6'),'#skF_5')
      | ~ r2_hidden(C_221,k2_pre_topc('#skF_5','#skF_8'))
      | ~ m1_subset_1(C_221,u1_struct_0('#skF_5'))
      | r2_hidden('#skF_6',k2_pre_topc('#skF_5','#skF_8'))
      | v2_struct_0('#skF_5')
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_12,c_312])).

tff(c_318,plain,(
    ! [C_221] :
      ( ~ r2_hidden(C_221,'#skF_1'('#skF_5','#skF_8','#skF_6'))
      | ~ v3_pre_topc('#skF_1'('#skF_5','#skF_8','#skF_6'),'#skF_5')
      | ~ r2_hidden(C_221,k2_pre_topc('#skF_5','#skF_8'))
      | ~ m1_subset_1(C_221,u1_struct_0('#skF_5'))
      | r2_hidden('#skF_6',k2_pre_topc('#skF_5','#skF_8'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_50,c_62,c_315])).

tff(c_319,plain,(
    ! [C_221] :
      ( ~ r2_hidden(C_221,'#skF_1'('#skF_5','#skF_8','#skF_6'))
      | ~ v3_pre_topc('#skF_1'('#skF_5','#skF_8','#skF_6'),'#skF_5')
      | ~ r2_hidden(C_221,k2_pre_topc('#skF_5','#skF_8'))
      | ~ m1_subset_1(C_221,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_46,c_318])).

tff(c_320,plain,(
    ~ v3_pre_topc('#skF_1'('#skF_5','#skF_8','#skF_6'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_319])).

tff(c_323,plain,
    ( r2_hidden('#skF_6',k2_pre_topc('#skF_5','#skF_8'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_132,c_320])).

tff(c_326,plain,(
    r2_hidden('#skF_6',k2_pre_topc('#skF_5','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_323])).

tff(c_328,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_326])).

tff(c_330,plain,(
    v3_pre_topc('#skF_1'('#skF_5','#skF_8','#skF_6'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_319])).

tff(c_134,plain,(
    ! [C_165,A_166,B_167] :
      ( r2_hidden(C_165,'#skF_1'(A_166,B_167,C_165))
      | r2_hidden(C_165,k2_pre_topc(A_166,B_167))
      | v2_struct_0(A_166)
      | ~ m1_subset_1(C_165,u1_struct_0(A_166))
      | ~ m1_subset_1(B_167,k1_zfmisc_1(u1_struct_0(A_166)))
      | ~ l1_pre_topc(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_138,plain,(
    ! [C_165] :
      ( r2_hidden(C_165,'#skF_1'('#skF_5','#skF_8',C_165))
      | r2_hidden(C_165,k2_pre_topc('#skF_5','#skF_8'))
      | v2_struct_0('#skF_5')
      | ~ m1_subset_1(C_165,u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_50,c_134])).

tff(c_142,plain,(
    ! [C_165] :
      ( r2_hidden(C_165,'#skF_1'('#skF_5','#skF_8',C_165))
      | r2_hidden(C_165,k2_pre_topc('#skF_5','#skF_8'))
      | v2_struct_0('#skF_5')
      | ~ m1_subset_1(C_165,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_138])).

tff(c_144,plain,(
    ! [C_168] :
      ( r2_hidden(C_168,'#skF_1'('#skF_5','#skF_8',C_168))
      | r2_hidden(C_168,k2_pre_topc('#skF_5','#skF_8'))
      | ~ m1_subset_1(C_168,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_142])).

tff(c_149,plain,
    ( r2_hidden('#skF_6','#skF_1'('#skF_5','#skF_8','#skF_6'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_144,c_46])).

tff(c_155,plain,(
    r2_hidden('#skF_6','#skF_1'('#skF_5','#skF_8','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_149])).

tff(c_96,plain,(
    l1_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_66,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_40,plain,(
    ! [A_118,B_119] :
      ( m1_subset_1(k10_yellow_6(A_118,B_119),k1_zfmisc_1(u1_struct_0(A_118)))
      | ~ l1_waybel_0(B_119,A_118)
      | ~ v7_waybel_0(B_119)
      | ~ v4_orders_2(B_119)
      | v2_struct_0(B_119)
      | ~ l1_pre_topc(A_118)
      | ~ v2_pre_topc(A_118)
      | v2_struct_0(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_195,plain,(
    ! [A_182,B_183,C_184] :
      ( m1_subset_1('#skF_1'(A_182,B_183,C_184),k1_zfmisc_1(u1_struct_0(A_182)))
      | r2_hidden(C_184,k2_pre_topc(A_182,B_183))
      | v2_struct_0(A_182)
      | ~ m1_subset_1(C_184,u1_struct_0(A_182))
      | ~ m1_subset_1(B_183,k1_zfmisc_1(u1_struct_0(A_182)))
      | ~ l1_pre_topc(A_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_169,plain,(
    ! [B_178,A_179,C_180] :
      ( m1_connsp_2(B_178,A_179,C_180)
      | ~ r2_hidden(C_180,B_178)
      | ~ v3_pre_topc(B_178,A_179)
      | ~ m1_subset_1(C_180,u1_struct_0(A_179))
      | ~ m1_subset_1(B_178,k1_zfmisc_1(u1_struct_0(A_179)))
      | ~ l1_pre_topc(A_179)
      | ~ v2_pre_topc(A_179)
      | v2_struct_0(A_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_173,plain,(
    ! [B_178] :
      ( m1_connsp_2(B_178,'#skF_5','#skF_6')
      | ~ r2_hidden('#skF_6',B_178)
      | ~ v3_pre_topc(B_178,'#skF_5')
      | ~ m1_subset_1(B_178,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_62,c_169])).

tff(c_180,plain,(
    ! [B_178] :
      ( m1_connsp_2(B_178,'#skF_5','#skF_6')
      | ~ r2_hidden('#skF_6',B_178)
      | ~ v3_pre_topc(B_178,'#skF_5')
      | ~ m1_subset_1(B_178,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_173])).

tff(c_181,plain,(
    ! [B_178] :
      ( m1_connsp_2(B_178,'#skF_5','#skF_6')
      | ~ r2_hidden('#skF_6',B_178)
      | ~ v3_pre_topc(B_178,'#skF_5')
      | ~ m1_subset_1(B_178,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_180])).

tff(c_199,plain,(
    ! [B_183,C_184] :
      ( m1_connsp_2('#skF_1'('#skF_5',B_183,C_184),'#skF_5','#skF_6')
      | ~ r2_hidden('#skF_6','#skF_1'('#skF_5',B_183,C_184))
      | ~ v3_pre_topc('#skF_1'('#skF_5',B_183,C_184),'#skF_5')
      | r2_hidden(C_184,k2_pre_topc('#skF_5',B_183))
      | v2_struct_0('#skF_5')
      | ~ m1_subset_1(C_184,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_183,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_195,c_181])).

tff(c_210,plain,(
    ! [B_183,C_184] :
      ( m1_connsp_2('#skF_1'('#skF_5',B_183,C_184),'#skF_5','#skF_6')
      | ~ r2_hidden('#skF_6','#skF_1'('#skF_5',B_183,C_184))
      | ~ v3_pre_topc('#skF_1'('#skF_5',B_183,C_184),'#skF_5')
      | r2_hidden(C_184,k2_pre_topc('#skF_5',B_183))
      | v2_struct_0('#skF_5')
      | ~ m1_subset_1(C_184,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_183,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_199])).

tff(c_258,plain,(
    ! [B_201,C_202] :
      ( m1_connsp_2('#skF_1'('#skF_5',B_201,C_202),'#skF_5','#skF_6')
      | ~ r2_hidden('#skF_6','#skF_1'('#skF_5',B_201,C_202))
      | ~ v3_pre_topc('#skF_1'('#skF_5',B_201,C_202),'#skF_5')
      | r2_hidden(C_202,k2_pre_topc('#skF_5',B_201))
      | ~ m1_subset_1(C_202,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_201,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_210])).

tff(c_275,plain,(
    ! [C_202] :
      ( m1_connsp_2('#skF_1'('#skF_5','#skF_8',C_202),'#skF_5','#skF_6')
      | ~ r2_hidden('#skF_6','#skF_1'('#skF_5','#skF_8',C_202))
      | ~ v3_pre_topc('#skF_1'('#skF_5','#skF_8',C_202),'#skF_5')
      | r2_hidden(C_202,k2_pre_topc('#skF_5','#skF_8'))
      | ~ m1_subset_1(C_202,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_50,c_258])).

tff(c_331,plain,(
    ! [A_223,B_224,E_225,D_226] :
      ( r1_waybel_0(A_223,B_224,E_225)
      | ~ m1_connsp_2(E_225,A_223,D_226)
      | ~ r2_hidden(D_226,k10_yellow_6(A_223,B_224))
      | ~ m1_subset_1(D_226,u1_struct_0(A_223))
      | ~ m1_subset_1(k10_yellow_6(A_223,B_224),k1_zfmisc_1(u1_struct_0(A_223)))
      | ~ l1_waybel_0(B_224,A_223)
      | ~ v7_waybel_0(B_224)
      | ~ v4_orders_2(B_224)
      | v2_struct_0(B_224)
      | ~ l1_pre_topc(A_223)
      | ~ v2_pre_topc(A_223)
      | v2_struct_0(A_223) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_335,plain,(
    ! [B_224,C_202] :
      ( r1_waybel_0('#skF_5',B_224,'#skF_1'('#skF_5','#skF_8',C_202))
      | ~ r2_hidden('#skF_6',k10_yellow_6('#skF_5',B_224))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
      | ~ m1_subset_1(k10_yellow_6('#skF_5',B_224),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_waybel_0(B_224,'#skF_5')
      | ~ v7_waybel_0(B_224)
      | ~ v4_orders_2(B_224)
      | v2_struct_0(B_224)
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r2_hidden('#skF_6','#skF_1'('#skF_5','#skF_8',C_202))
      | ~ v3_pre_topc('#skF_1'('#skF_5','#skF_8',C_202),'#skF_5')
      | r2_hidden(C_202,k2_pre_topc('#skF_5','#skF_8'))
      | ~ m1_subset_1(C_202,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_275,c_331])).

tff(c_346,plain,(
    ! [B_224,C_202] :
      ( r1_waybel_0('#skF_5',B_224,'#skF_1'('#skF_5','#skF_8',C_202))
      | ~ r2_hidden('#skF_6',k10_yellow_6('#skF_5',B_224))
      | ~ m1_subset_1(k10_yellow_6('#skF_5',B_224),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_waybel_0(B_224,'#skF_5')
      | ~ v7_waybel_0(B_224)
      | ~ v4_orders_2(B_224)
      | v2_struct_0(B_224)
      | v2_struct_0('#skF_5')
      | ~ r2_hidden('#skF_6','#skF_1'('#skF_5','#skF_8',C_202))
      | ~ v3_pre_topc('#skF_1'('#skF_5','#skF_8',C_202),'#skF_5')
      | r2_hidden(C_202,k2_pre_topc('#skF_5','#skF_8'))
      | ~ m1_subset_1(C_202,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_335])).

tff(c_505,plain,(
    ! [B_283,C_284] :
      ( r1_waybel_0('#skF_5',B_283,'#skF_1'('#skF_5','#skF_8',C_284))
      | ~ r2_hidden('#skF_6',k10_yellow_6('#skF_5',B_283))
      | ~ m1_subset_1(k10_yellow_6('#skF_5',B_283),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_waybel_0(B_283,'#skF_5')
      | ~ v7_waybel_0(B_283)
      | ~ v4_orders_2(B_283)
      | v2_struct_0(B_283)
      | ~ r2_hidden('#skF_6','#skF_1'('#skF_5','#skF_8',C_284))
      | ~ v3_pre_topc('#skF_1'('#skF_5','#skF_8',C_284),'#skF_5')
      | r2_hidden(C_284,k2_pre_topc('#skF_5','#skF_8'))
      | ~ m1_subset_1(C_284,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_346])).

tff(c_508,plain,(
    ! [B_119,C_284] :
      ( r1_waybel_0('#skF_5',B_119,'#skF_1'('#skF_5','#skF_8',C_284))
      | ~ r2_hidden('#skF_6',k10_yellow_6('#skF_5',B_119))
      | ~ r2_hidden('#skF_6','#skF_1'('#skF_5','#skF_8',C_284))
      | ~ v3_pre_topc('#skF_1'('#skF_5','#skF_8',C_284),'#skF_5')
      | r2_hidden(C_284,k2_pre_topc('#skF_5','#skF_8'))
      | ~ m1_subset_1(C_284,u1_struct_0('#skF_5'))
      | ~ l1_waybel_0(B_119,'#skF_5')
      | ~ v7_waybel_0(B_119)
      | ~ v4_orders_2(B_119)
      | v2_struct_0(B_119)
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_40,c_505])).

tff(c_511,plain,(
    ! [B_119,C_284] :
      ( r1_waybel_0('#skF_5',B_119,'#skF_1'('#skF_5','#skF_8',C_284))
      | ~ r2_hidden('#skF_6',k10_yellow_6('#skF_5',B_119))
      | ~ r2_hidden('#skF_6','#skF_1'('#skF_5','#skF_8',C_284))
      | ~ v3_pre_topc('#skF_1'('#skF_5','#skF_8',C_284),'#skF_5')
      | r2_hidden(C_284,k2_pre_topc('#skF_5','#skF_8'))
      | ~ m1_subset_1(C_284,u1_struct_0('#skF_5'))
      | ~ l1_waybel_0(B_119,'#skF_5')
      | ~ v7_waybel_0(B_119)
      | ~ v4_orders_2(B_119)
      | v2_struct_0(B_119)
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_508])).

tff(c_513,plain,(
    ! [B_285,C_286] :
      ( r1_waybel_0('#skF_5',B_285,'#skF_1'('#skF_5','#skF_8',C_286))
      | ~ r2_hidden('#skF_6',k10_yellow_6('#skF_5',B_285))
      | ~ r2_hidden('#skF_6','#skF_1'('#skF_5','#skF_8',C_286))
      | ~ v3_pre_topc('#skF_1'('#skF_5','#skF_8',C_286),'#skF_5')
      | r2_hidden(C_286,k2_pre_topc('#skF_5','#skF_8'))
      | ~ m1_subset_1(C_286,u1_struct_0('#skF_5'))
      | ~ l1_waybel_0(B_285,'#skF_5')
      | ~ v7_waybel_0(B_285)
      | ~ v4_orders_2(B_285)
      | v2_struct_0(B_285) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_511])).

tff(c_156,plain,(
    ! [C_169,D_170,A_171,B_172] :
      ( ~ r1_xboole_0(C_169,D_170)
      | ~ r1_waybel_0(A_171,B_172,D_170)
      | ~ r1_waybel_0(A_171,B_172,C_169)
      | ~ l1_waybel_0(B_172,A_171)
      | ~ v7_waybel_0(B_172)
      | ~ v4_orders_2(B_172)
      | v2_struct_0(B_172)
      | ~ l1_struct_0(A_171)
      | v2_struct_0(A_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_159,plain,(
    ! [A_171,B_172] :
      ( ~ r1_waybel_0(A_171,B_172,'#skF_1'('#skF_5','#skF_8','#skF_6'))
      | ~ r1_waybel_0(A_171,B_172,'#skF_8')
      | ~ l1_waybel_0(B_172,A_171)
      | ~ v7_waybel_0(B_172)
      | ~ v4_orders_2(B_172)
      | v2_struct_0(B_172)
      | ~ l1_struct_0(A_171)
      | v2_struct_0(A_171) ) ),
    inference(resolution,[status(thm)],[c_122,c_156])).

tff(c_517,plain,(
    ! [B_285] :
      ( ~ r1_waybel_0('#skF_5',B_285,'#skF_8')
      | ~ l1_struct_0('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r2_hidden('#skF_6',k10_yellow_6('#skF_5',B_285))
      | ~ r2_hidden('#skF_6','#skF_1'('#skF_5','#skF_8','#skF_6'))
      | ~ v3_pre_topc('#skF_1'('#skF_5','#skF_8','#skF_6'),'#skF_5')
      | r2_hidden('#skF_6',k2_pre_topc('#skF_5','#skF_8'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
      | ~ l1_waybel_0(B_285,'#skF_5')
      | ~ v7_waybel_0(B_285)
      | ~ v4_orders_2(B_285)
      | v2_struct_0(B_285) ) ),
    inference(resolution,[status(thm)],[c_513,c_159])).

tff(c_520,plain,(
    ! [B_285] :
      ( ~ r1_waybel_0('#skF_5',B_285,'#skF_8')
      | v2_struct_0('#skF_5')
      | ~ r2_hidden('#skF_6',k10_yellow_6('#skF_5',B_285))
      | r2_hidden('#skF_6',k2_pre_topc('#skF_5','#skF_8'))
      | ~ l1_waybel_0(B_285,'#skF_5')
      | ~ v7_waybel_0(B_285)
      | ~ v4_orders_2(B_285)
      | v2_struct_0(B_285) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_330,c_155,c_96,c_517])).

tff(c_522,plain,(
    ! [B_287] :
      ( ~ r1_waybel_0('#skF_5',B_287,'#skF_8')
      | ~ r2_hidden('#skF_6',k10_yellow_6('#skF_5',B_287))
      | ~ l1_waybel_0(B_287,'#skF_5')
      | ~ v7_waybel_0(B_287)
      | ~ v4_orders_2(B_287)
      | v2_struct_0(B_287) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_68,c_520])).

tff(c_525,plain,
    ( ~ r1_waybel_0('#skF_5','#skF_7','#skF_8')
    | ~ l1_waybel_0('#skF_7','#skF_5')
    | ~ v7_waybel_0('#skF_7')
    | ~ v4_orders_2('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_52,c_522])).

tff(c_528,plain,(
    v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_95,c_525])).

tff(c_530,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_528])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:01:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.22/1.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/1.59  
% 3.22/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/1.60  %$ r1_waybel_0 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_xboole_0 > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k2_relset_1 > u1_waybel_0 > k2_pre_topc > k10_yellow_6 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_3
% 3.22/1.60  
% 3.22/1.60  %Foreground sorts:
% 3.22/1.60  
% 3.22/1.60  
% 3.22/1.60  %Background operators:
% 3.22/1.60  
% 3.22/1.60  
% 3.22/1.60  %Foreground operators:
% 3.22/1.60  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.22/1.60  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.22/1.60  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 3.22/1.60  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.22/1.60  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.22/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.22/1.60  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.22/1.60  tff(k10_yellow_6, type, k10_yellow_6: ($i * $i) > $i).
% 3.22/1.60  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.22/1.60  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 3.22/1.60  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.22/1.60  tff('#skF_7', type, '#skF_7': $i).
% 3.22/1.60  tff('#skF_5', type, '#skF_5': $i).
% 3.22/1.60  tff(r1_waybel_0, type, r1_waybel_0: ($i * $i * $i) > $o).
% 3.22/1.60  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.22/1.60  tff('#skF_6', type, '#skF_6': $i).
% 3.22/1.60  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.22/1.60  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.22/1.60  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.22/1.60  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.22/1.60  tff(u1_waybel_0, type, u1_waybel_0: ($i * $i) > $i).
% 3.22/1.60  tff('#skF_8', type, '#skF_8': $i).
% 3.22/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.22/1.60  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 3.22/1.60  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.22/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.22/1.60  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.22/1.60  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.22/1.60  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.22/1.60  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.22/1.60  
% 3.22/1.62  tff(f_193, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((((~v2_struct_0(C) & v4_orders_2(C)) & v7_waybel_0(C)) & l1_waybel_0(C, A)) => (r2_hidden(B, k10_yellow_6(A, C)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ((D = k2_relset_1(u1_struct_0(C), u1_struct_0(A), u1_waybel_0(A, C))) => r2_hidden(B, k2_pre_topc(A, D)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_waybel_9)).
% 3.22/1.62  tff(f_35, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.22/1.62  tff(f_163, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => r1_waybel_0(A, B, k2_relset_1(u1_struct_0(B), u1_struct_0(A), u1_waybel_0(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_waybel_9)).
% 3.22/1.62  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, k2_pre_topc(A, B)) <=> (~v2_struct_0(A) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~((v3_pre_topc(D, A) & r2_hidden(C, D)) & r1_xboole_0(B, D)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_pre_topc)).
% 3.22/1.62  tff(f_127, axiom, (![A, B]: (((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => m1_subset_1(k10_yellow_6(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k10_yellow_6)).
% 3.22/1.62  tff(f_77, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((v3_pre_topc(B, A) & r2_hidden(C, B)) => m1_connsp_2(B, A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_connsp_2)).
% 3.22/1.62  tff(f_109, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = k10_yellow_6(A, B)) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) <=> (![E]: (m1_connsp_2(E, A, D) => r1_waybel_0(A, B, E))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_yellow_6)).
% 3.22/1.62  tff(f_150, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C, D]: ~((r1_waybel_0(A, B, C) & r1_waybel_0(A, B, D)) & r1_xboole_0(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_yellow_6)).
% 3.22/1.62  tff(c_60, plain, (~v2_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_193])).
% 3.22/1.62  tff(c_58, plain, (v4_orders_2('#skF_7')), inference(cnfTransformation, [status(thm)], [f_193])).
% 3.22/1.62  tff(c_56, plain, (v7_waybel_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_193])).
% 3.22/1.62  tff(c_54, plain, (l1_waybel_0('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_193])).
% 3.22/1.62  tff(c_64, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_193])).
% 3.22/1.62  tff(c_4, plain, (![A_4]: (l1_struct_0(A_4) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.22/1.62  tff(c_68, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_193])).
% 3.22/1.62  tff(c_48, plain, (k2_relset_1(u1_struct_0('#skF_7'), u1_struct_0('#skF_5'), u1_waybel_0('#skF_5', '#skF_7'))='#skF_8'), inference(cnfTransformation, [status(thm)], [f_193])).
% 3.22/1.62  tff(c_80, plain, (![A_153, B_154]: (r1_waybel_0(A_153, B_154, k2_relset_1(u1_struct_0(B_154), u1_struct_0(A_153), u1_waybel_0(A_153, B_154))) | ~l1_waybel_0(B_154, A_153) | v2_struct_0(B_154) | ~l1_struct_0(A_153) | v2_struct_0(A_153))), inference(cnfTransformation, [status(thm)], [f_163])).
% 3.22/1.62  tff(c_83, plain, (r1_waybel_0('#skF_5', '#skF_7', '#skF_8') | ~l1_waybel_0('#skF_7', '#skF_5') | v2_struct_0('#skF_7') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_48, c_80])).
% 3.22/1.62  tff(c_85, plain, (r1_waybel_0('#skF_5', '#skF_7', '#skF_8') | v2_struct_0('#skF_7') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_83])).
% 3.22/1.62  tff(c_86, plain, (r1_waybel_0('#skF_5', '#skF_7', '#skF_8') | ~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_68, c_60, c_85])).
% 3.22/1.62  tff(c_87, plain, (~l1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_86])).
% 3.22/1.62  tff(c_90, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_4, c_87])).
% 3.22/1.62  tff(c_94, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_90])).
% 3.22/1.62  tff(c_95, plain, (r1_waybel_0('#skF_5', '#skF_7', '#skF_8')), inference(splitRight, [status(thm)], [c_86])).
% 3.22/1.62  tff(c_52, plain, (r2_hidden('#skF_6', k10_yellow_6('#skF_5', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_193])).
% 3.22/1.62  tff(c_46, plain, (~r2_hidden('#skF_6', k2_pre_topc('#skF_5', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_193])).
% 3.22/1.62  tff(c_62, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_193])).
% 3.22/1.62  tff(c_50, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_193])).
% 3.22/1.62  tff(c_123, plain, (![A_161, B_162, C_163]: (v3_pre_topc('#skF_1'(A_161, B_162, C_163), A_161) | r2_hidden(C_163, k2_pre_topc(A_161, B_162)) | v2_struct_0(A_161) | ~m1_subset_1(C_163, u1_struct_0(A_161)) | ~m1_subset_1(B_162, k1_zfmisc_1(u1_struct_0(A_161))) | ~l1_pre_topc(A_161))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.22/1.62  tff(c_127, plain, (![C_163]: (v3_pre_topc('#skF_1'('#skF_5', '#skF_8', C_163), '#skF_5') | r2_hidden(C_163, k2_pre_topc('#skF_5', '#skF_8')) | v2_struct_0('#skF_5') | ~m1_subset_1(C_163, u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5'))), inference(resolution, [status(thm)], [c_50, c_123])).
% 3.22/1.62  tff(c_131, plain, (![C_163]: (v3_pre_topc('#skF_1'('#skF_5', '#skF_8', C_163), '#skF_5') | r2_hidden(C_163, k2_pre_topc('#skF_5', '#skF_8')) | v2_struct_0('#skF_5') | ~m1_subset_1(C_163, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_127])).
% 3.22/1.62  tff(c_132, plain, (![C_163]: (v3_pre_topc('#skF_1'('#skF_5', '#skF_8', C_163), '#skF_5') | r2_hidden(C_163, k2_pre_topc('#skF_5', '#skF_8')) | ~m1_subset_1(C_163, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_68, c_131])).
% 3.22/1.62  tff(c_12, plain, (![A_5, B_17, C_23]: (m1_subset_1('#skF_1'(A_5, B_17, C_23), k1_zfmisc_1(u1_struct_0(A_5))) | r2_hidden(C_23, k2_pre_topc(A_5, B_17)) | v2_struct_0(A_5) | ~m1_subset_1(C_23, u1_struct_0(A_5)) | ~m1_subset_1(B_17, k1_zfmisc_1(u1_struct_0(A_5))) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.22/1.62  tff(c_101, plain, (![B_157, A_158, C_159]: (r1_xboole_0(B_157, '#skF_1'(A_158, B_157, C_159)) | r2_hidden(C_159, k2_pre_topc(A_158, B_157)) | v2_struct_0(A_158) | ~m1_subset_1(C_159, u1_struct_0(A_158)) | ~m1_subset_1(B_157, k1_zfmisc_1(u1_struct_0(A_158))) | ~l1_pre_topc(A_158))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.22/1.62  tff(c_105, plain, (![C_159]: (r1_xboole_0('#skF_8', '#skF_1'('#skF_5', '#skF_8', C_159)) | r2_hidden(C_159, k2_pre_topc('#skF_5', '#skF_8')) | v2_struct_0('#skF_5') | ~m1_subset_1(C_159, u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5'))), inference(resolution, [status(thm)], [c_50, c_101])).
% 3.22/1.62  tff(c_109, plain, (![C_159]: (r1_xboole_0('#skF_8', '#skF_1'('#skF_5', '#skF_8', C_159)) | r2_hidden(C_159, k2_pre_topc('#skF_5', '#skF_8')) | v2_struct_0('#skF_5') | ~m1_subset_1(C_159, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_105])).
% 3.22/1.62  tff(c_111, plain, (![C_160]: (r1_xboole_0('#skF_8', '#skF_1'('#skF_5', '#skF_8', C_160)) | r2_hidden(C_160, k2_pre_topc('#skF_5', '#skF_8')) | ~m1_subset_1(C_160, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_68, c_109])).
% 3.22/1.62  tff(c_116, plain, (r1_xboole_0('#skF_8', '#skF_1'('#skF_5', '#skF_8', '#skF_6')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_111, c_46])).
% 3.22/1.62  tff(c_122, plain, (r1_xboole_0('#skF_8', '#skF_1'('#skF_5', '#skF_8', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_116])).
% 3.22/1.62  tff(c_250, plain, (![B_194, D_195, C_196, A_197]: (~r1_xboole_0(B_194, D_195) | ~r2_hidden(C_196, D_195) | ~v3_pre_topc(D_195, A_197) | ~m1_subset_1(D_195, k1_zfmisc_1(u1_struct_0(A_197))) | ~r2_hidden(C_196, k2_pre_topc(A_197, B_194)) | ~m1_subset_1(C_196, u1_struct_0(A_197)) | ~m1_subset_1(B_194, k1_zfmisc_1(u1_struct_0(A_197))) | ~l1_pre_topc(A_197))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.22/1.62  tff(c_312, plain, (![C_221, A_222]: (~r2_hidden(C_221, '#skF_1'('#skF_5', '#skF_8', '#skF_6')) | ~v3_pre_topc('#skF_1'('#skF_5', '#skF_8', '#skF_6'), A_222) | ~m1_subset_1('#skF_1'('#skF_5', '#skF_8', '#skF_6'), k1_zfmisc_1(u1_struct_0(A_222))) | ~r2_hidden(C_221, k2_pre_topc(A_222, '#skF_8')) | ~m1_subset_1(C_221, u1_struct_0(A_222)) | ~m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0(A_222))) | ~l1_pre_topc(A_222))), inference(resolution, [status(thm)], [c_122, c_250])).
% 3.22/1.62  tff(c_315, plain, (![C_221]: (~r2_hidden(C_221, '#skF_1'('#skF_5', '#skF_8', '#skF_6')) | ~v3_pre_topc('#skF_1'('#skF_5', '#skF_8', '#skF_6'), '#skF_5') | ~r2_hidden(C_221, k2_pre_topc('#skF_5', '#skF_8')) | ~m1_subset_1(C_221, u1_struct_0('#skF_5')) | r2_hidden('#skF_6', k2_pre_topc('#skF_5', '#skF_8')) | v2_struct_0('#skF_5') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(resolution, [status(thm)], [c_12, c_312])).
% 3.22/1.62  tff(c_318, plain, (![C_221]: (~r2_hidden(C_221, '#skF_1'('#skF_5', '#skF_8', '#skF_6')) | ~v3_pre_topc('#skF_1'('#skF_5', '#skF_8', '#skF_6'), '#skF_5') | ~r2_hidden(C_221, k2_pre_topc('#skF_5', '#skF_8')) | ~m1_subset_1(C_221, u1_struct_0('#skF_5')) | r2_hidden('#skF_6', k2_pre_topc('#skF_5', '#skF_8')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_50, c_62, c_315])).
% 3.22/1.62  tff(c_319, plain, (![C_221]: (~r2_hidden(C_221, '#skF_1'('#skF_5', '#skF_8', '#skF_6')) | ~v3_pre_topc('#skF_1'('#skF_5', '#skF_8', '#skF_6'), '#skF_5') | ~r2_hidden(C_221, k2_pre_topc('#skF_5', '#skF_8')) | ~m1_subset_1(C_221, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_68, c_46, c_318])).
% 3.22/1.62  tff(c_320, plain, (~v3_pre_topc('#skF_1'('#skF_5', '#skF_8', '#skF_6'), '#skF_5')), inference(splitLeft, [status(thm)], [c_319])).
% 3.22/1.62  tff(c_323, plain, (r2_hidden('#skF_6', k2_pre_topc('#skF_5', '#skF_8')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_132, c_320])).
% 3.22/1.62  tff(c_326, plain, (r2_hidden('#skF_6', k2_pre_topc('#skF_5', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_323])).
% 3.22/1.62  tff(c_328, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_326])).
% 3.22/1.62  tff(c_330, plain, (v3_pre_topc('#skF_1'('#skF_5', '#skF_8', '#skF_6'), '#skF_5')), inference(splitRight, [status(thm)], [c_319])).
% 3.22/1.62  tff(c_134, plain, (![C_165, A_166, B_167]: (r2_hidden(C_165, '#skF_1'(A_166, B_167, C_165)) | r2_hidden(C_165, k2_pre_topc(A_166, B_167)) | v2_struct_0(A_166) | ~m1_subset_1(C_165, u1_struct_0(A_166)) | ~m1_subset_1(B_167, k1_zfmisc_1(u1_struct_0(A_166))) | ~l1_pre_topc(A_166))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.22/1.62  tff(c_138, plain, (![C_165]: (r2_hidden(C_165, '#skF_1'('#skF_5', '#skF_8', C_165)) | r2_hidden(C_165, k2_pre_topc('#skF_5', '#skF_8')) | v2_struct_0('#skF_5') | ~m1_subset_1(C_165, u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5'))), inference(resolution, [status(thm)], [c_50, c_134])).
% 3.22/1.62  tff(c_142, plain, (![C_165]: (r2_hidden(C_165, '#skF_1'('#skF_5', '#skF_8', C_165)) | r2_hidden(C_165, k2_pre_topc('#skF_5', '#skF_8')) | v2_struct_0('#skF_5') | ~m1_subset_1(C_165, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_138])).
% 3.22/1.62  tff(c_144, plain, (![C_168]: (r2_hidden(C_168, '#skF_1'('#skF_5', '#skF_8', C_168)) | r2_hidden(C_168, k2_pre_topc('#skF_5', '#skF_8')) | ~m1_subset_1(C_168, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_68, c_142])).
% 3.22/1.62  tff(c_149, plain, (r2_hidden('#skF_6', '#skF_1'('#skF_5', '#skF_8', '#skF_6')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_144, c_46])).
% 3.22/1.62  tff(c_155, plain, (r2_hidden('#skF_6', '#skF_1'('#skF_5', '#skF_8', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_149])).
% 3.22/1.62  tff(c_96, plain, (l1_struct_0('#skF_5')), inference(splitRight, [status(thm)], [c_86])).
% 3.22/1.62  tff(c_66, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_193])).
% 3.22/1.62  tff(c_40, plain, (![A_118, B_119]: (m1_subset_1(k10_yellow_6(A_118, B_119), k1_zfmisc_1(u1_struct_0(A_118))) | ~l1_waybel_0(B_119, A_118) | ~v7_waybel_0(B_119) | ~v4_orders_2(B_119) | v2_struct_0(B_119) | ~l1_pre_topc(A_118) | ~v2_pre_topc(A_118) | v2_struct_0(A_118))), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.22/1.62  tff(c_195, plain, (![A_182, B_183, C_184]: (m1_subset_1('#skF_1'(A_182, B_183, C_184), k1_zfmisc_1(u1_struct_0(A_182))) | r2_hidden(C_184, k2_pre_topc(A_182, B_183)) | v2_struct_0(A_182) | ~m1_subset_1(C_184, u1_struct_0(A_182)) | ~m1_subset_1(B_183, k1_zfmisc_1(u1_struct_0(A_182))) | ~l1_pre_topc(A_182))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.22/1.62  tff(c_169, plain, (![B_178, A_179, C_180]: (m1_connsp_2(B_178, A_179, C_180) | ~r2_hidden(C_180, B_178) | ~v3_pre_topc(B_178, A_179) | ~m1_subset_1(C_180, u1_struct_0(A_179)) | ~m1_subset_1(B_178, k1_zfmisc_1(u1_struct_0(A_179))) | ~l1_pre_topc(A_179) | ~v2_pre_topc(A_179) | v2_struct_0(A_179))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.22/1.62  tff(c_173, plain, (![B_178]: (m1_connsp_2(B_178, '#skF_5', '#skF_6') | ~r2_hidden('#skF_6', B_178) | ~v3_pre_topc(B_178, '#skF_5') | ~m1_subset_1(B_178, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_62, c_169])).
% 3.22/1.62  tff(c_180, plain, (![B_178]: (m1_connsp_2(B_178, '#skF_5', '#skF_6') | ~r2_hidden('#skF_6', B_178) | ~v3_pre_topc(B_178, '#skF_5') | ~m1_subset_1(B_178, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_173])).
% 3.22/1.62  tff(c_181, plain, (![B_178]: (m1_connsp_2(B_178, '#skF_5', '#skF_6') | ~r2_hidden('#skF_6', B_178) | ~v3_pre_topc(B_178, '#skF_5') | ~m1_subset_1(B_178, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_68, c_180])).
% 3.22/1.62  tff(c_199, plain, (![B_183, C_184]: (m1_connsp_2('#skF_1'('#skF_5', B_183, C_184), '#skF_5', '#skF_6') | ~r2_hidden('#skF_6', '#skF_1'('#skF_5', B_183, C_184)) | ~v3_pre_topc('#skF_1'('#skF_5', B_183, C_184), '#skF_5') | r2_hidden(C_184, k2_pre_topc('#skF_5', B_183)) | v2_struct_0('#skF_5') | ~m1_subset_1(C_184, u1_struct_0('#skF_5')) | ~m1_subset_1(B_183, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(resolution, [status(thm)], [c_195, c_181])).
% 3.22/1.62  tff(c_210, plain, (![B_183, C_184]: (m1_connsp_2('#skF_1'('#skF_5', B_183, C_184), '#skF_5', '#skF_6') | ~r2_hidden('#skF_6', '#skF_1'('#skF_5', B_183, C_184)) | ~v3_pre_topc('#skF_1'('#skF_5', B_183, C_184), '#skF_5') | r2_hidden(C_184, k2_pre_topc('#skF_5', B_183)) | v2_struct_0('#skF_5') | ~m1_subset_1(C_184, u1_struct_0('#skF_5')) | ~m1_subset_1(B_183, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_199])).
% 3.22/1.62  tff(c_258, plain, (![B_201, C_202]: (m1_connsp_2('#skF_1'('#skF_5', B_201, C_202), '#skF_5', '#skF_6') | ~r2_hidden('#skF_6', '#skF_1'('#skF_5', B_201, C_202)) | ~v3_pre_topc('#skF_1'('#skF_5', B_201, C_202), '#skF_5') | r2_hidden(C_202, k2_pre_topc('#skF_5', B_201)) | ~m1_subset_1(C_202, u1_struct_0('#skF_5')) | ~m1_subset_1(B_201, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_68, c_210])).
% 3.22/1.62  tff(c_275, plain, (![C_202]: (m1_connsp_2('#skF_1'('#skF_5', '#skF_8', C_202), '#skF_5', '#skF_6') | ~r2_hidden('#skF_6', '#skF_1'('#skF_5', '#skF_8', C_202)) | ~v3_pre_topc('#skF_1'('#skF_5', '#skF_8', C_202), '#skF_5') | r2_hidden(C_202, k2_pre_topc('#skF_5', '#skF_8')) | ~m1_subset_1(C_202, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_50, c_258])).
% 3.22/1.62  tff(c_331, plain, (![A_223, B_224, E_225, D_226]: (r1_waybel_0(A_223, B_224, E_225) | ~m1_connsp_2(E_225, A_223, D_226) | ~r2_hidden(D_226, k10_yellow_6(A_223, B_224)) | ~m1_subset_1(D_226, u1_struct_0(A_223)) | ~m1_subset_1(k10_yellow_6(A_223, B_224), k1_zfmisc_1(u1_struct_0(A_223))) | ~l1_waybel_0(B_224, A_223) | ~v7_waybel_0(B_224) | ~v4_orders_2(B_224) | v2_struct_0(B_224) | ~l1_pre_topc(A_223) | ~v2_pre_topc(A_223) | v2_struct_0(A_223))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.22/1.62  tff(c_335, plain, (![B_224, C_202]: (r1_waybel_0('#skF_5', B_224, '#skF_1'('#skF_5', '#skF_8', C_202)) | ~r2_hidden('#skF_6', k10_yellow_6('#skF_5', B_224)) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~m1_subset_1(k10_yellow_6('#skF_5', B_224), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_waybel_0(B_224, '#skF_5') | ~v7_waybel_0(B_224) | ~v4_orders_2(B_224) | v2_struct_0(B_224) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~r2_hidden('#skF_6', '#skF_1'('#skF_5', '#skF_8', C_202)) | ~v3_pre_topc('#skF_1'('#skF_5', '#skF_8', C_202), '#skF_5') | r2_hidden(C_202, k2_pre_topc('#skF_5', '#skF_8')) | ~m1_subset_1(C_202, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_275, c_331])).
% 3.22/1.62  tff(c_346, plain, (![B_224, C_202]: (r1_waybel_0('#skF_5', B_224, '#skF_1'('#skF_5', '#skF_8', C_202)) | ~r2_hidden('#skF_6', k10_yellow_6('#skF_5', B_224)) | ~m1_subset_1(k10_yellow_6('#skF_5', B_224), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_waybel_0(B_224, '#skF_5') | ~v7_waybel_0(B_224) | ~v4_orders_2(B_224) | v2_struct_0(B_224) | v2_struct_0('#skF_5') | ~r2_hidden('#skF_6', '#skF_1'('#skF_5', '#skF_8', C_202)) | ~v3_pre_topc('#skF_1'('#skF_5', '#skF_8', C_202), '#skF_5') | r2_hidden(C_202, k2_pre_topc('#skF_5', '#skF_8')) | ~m1_subset_1(C_202, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_335])).
% 3.22/1.62  tff(c_505, plain, (![B_283, C_284]: (r1_waybel_0('#skF_5', B_283, '#skF_1'('#skF_5', '#skF_8', C_284)) | ~r2_hidden('#skF_6', k10_yellow_6('#skF_5', B_283)) | ~m1_subset_1(k10_yellow_6('#skF_5', B_283), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_waybel_0(B_283, '#skF_5') | ~v7_waybel_0(B_283) | ~v4_orders_2(B_283) | v2_struct_0(B_283) | ~r2_hidden('#skF_6', '#skF_1'('#skF_5', '#skF_8', C_284)) | ~v3_pre_topc('#skF_1'('#skF_5', '#skF_8', C_284), '#skF_5') | r2_hidden(C_284, k2_pre_topc('#skF_5', '#skF_8')) | ~m1_subset_1(C_284, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_68, c_346])).
% 3.22/1.62  tff(c_508, plain, (![B_119, C_284]: (r1_waybel_0('#skF_5', B_119, '#skF_1'('#skF_5', '#skF_8', C_284)) | ~r2_hidden('#skF_6', k10_yellow_6('#skF_5', B_119)) | ~r2_hidden('#skF_6', '#skF_1'('#skF_5', '#skF_8', C_284)) | ~v3_pre_topc('#skF_1'('#skF_5', '#skF_8', C_284), '#skF_5') | r2_hidden(C_284, k2_pre_topc('#skF_5', '#skF_8')) | ~m1_subset_1(C_284, u1_struct_0('#skF_5')) | ~l1_waybel_0(B_119, '#skF_5') | ~v7_waybel_0(B_119) | ~v4_orders_2(B_119) | v2_struct_0(B_119) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_40, c_505])).
% 3.22/1.62  tff(c_511, plain, (![B_119, C_284]: (r1_waybel_0('#skF_5', B_119, '#skF_1'('#skF_5', '#skF_8', C_284)) | ~r2_hidden('#skF_6', k10_yellow_6('#skF_5', B_119)) | ~r2_hidden('#skF_6', '#skF_1'('#skF_5', '#skF_8', C_284)) | ~v3_pre_topc('#skF_1'('#skF_5', '#skF_8', C_284), '#skF_5') | r2_hidden(C_284, k2_pre_topc('#skF_5', '#skF_8')) | ~m1_subset_1(C_284, u1_struct_0('#skF_5')) | ~l1_waybel_0(B_119, '#skF_5') | ~v7_waybel_0(B_119) | ~v4_orders_2(B_119) | v2_struct_0(B_119) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_508])).
% 3.22/1.62  tff(c_513, plain, (![B_285, C_286]: (r1_waybel_0('#skF_5', B_285, '#skF_1'('#skF_5', '#skF_8', C_286)) | ~r2_hidden('#skF_6', k10_yellow_6('#skF_5', B_285)) | ~r2_hidden('#skF_6', '#skF_1'('#skF_5', '#skF_8', C_286)) | ~v3_pre_topc('#skF_1'('#skF_5', '#skF_8', C_286), '#skF_5') | r2_hidden(C_286, k2_pre_topc('#skF_5', '#skF_8')) | ~m1_subset_1(C_286, u1_struct_0('#skF_5')) | ~l1_waybel_0(B_285, '#skF_5') | ~v7_waybel_0(B_285) | ~v4_orders_2(B_285) | v2_struct_0(B_285))), inference(negUnitSimplification, [status(thm)], [c_68, c_511])).
% 3.22/1.62  tff(c_156, plain, (![C_169, D_170, A_171, B_172]: (~r1_xboole_0(C_169, D_170) | ~r1_waybel_0(A_171, B_172, D_170) | ~r1_waybel_0(A_171, B_172, C_169) | ~l1_waybel_0(B_172, A_171) | ~v7_waybel_0(B_172) | ~v4_orders_2(B_172) | v2_struct_0(B_172) | ~l1_struct_0(A_171) | v2_struct_0(A_171))), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.22/1.62  tff(c_159, plain, (![A_171, B_172]: (~r1_waybel_0(A_171, B_172, '#skF_1'('#skF_5', '#skF_8', '#skF_6')) | ~r1_waybel_0(A_171, B_172, '#skF_8') | ~l1_waybel_0(B_172, A_171) | ~v7_waybel_0(B_172) | ~v4_orders_2(B_172) | v2_struct_0(B_172) | ~l1_struct_0(A_171) | v2_struct_0(A_171))), inference(resolution, [status(thm)], [c_122, c_156])).
% 3.22/1.62  tff(c_517, plain, (![B_285]: (~r1_waybel_0('#skF_5', B_285, '#skF_8') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5') | ~r2_hidden('#skF_6', k10_yellow_6('#skF_5', B_285)) | ~r2_hidden('#skF_6', '#skF_1'('#skF_5', '#skF_8', '#skF_6')) | ~v3_pre_topc('#skF_1'('#skF_5', '#skF_8', '#skF_6'), '#skF_5') | r2_hidden('#skF_6', k2_pre_topc('#skF_5', '#skF_8')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l1_waybel_0(B_285, '#skF_5') | ~v7_waybel_0(B_285) | ~v4_orders_2(B_285) | v2_struct_0(B_285))), inference(resolution, [status(thm)], [c_513, c_159])).
% 3.22/1.62  tff(c_520, plain, (![B_285]: (~r1_waybel_0('#skF_5', B_285, '#skF_8') | v2_struct_0('#skF_5') | ~r2_hidden('#skF_6', k10_yellow_6('#skF_5', B_285)) | r2_hidden('#skF_6', k2_pre_topc('#skF_5', '#skF_8')) | ~l1_waybel_0(B_285, '#skF_5') | ~v7_waybel_0(B_285) | ~v4_orders_2(B_285) | v2_struct_0(B_285))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_330, c_155, c_96, c_517])).
% 3.22/1.62  tff(c_522, plain, (![B_287]: (~r1_waybel_0('#skF_5', B_287, '#skF_8') | ~r2_hidden('#skF_6', k10_yellow_6('#skF_5', B_287)) | ~l1_waybel_0(B_287, '#skF_5') | ~v7_waybel_0(B_287) | ~v4_orders_2(B_287) | v2_struct_0(B_287))), inference(negUnitSimplification, [status(thm)], [c_46, c_68, c_520])).
% 3.22/1.62  tff(c_525, plain, (~r1_waybel_0('#skF_5', '#skF_7', '#skF_8') | ~l1_waybel_0('#skF_7', '#skF_5') | ~v7_waybel_0('#skF_7') | ~v4_orders_2('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_52, c_522])).
% 3.22/1.62  tff(c_528, plain, (v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_95, c_525])).
% 3.22/1.62  tff(c_530, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_528])).
% 3.22/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/1.62  
% 3.22/1.62  Inference rules
% 3.22/1.62  ----------------------
% 3.22/1.62  #Ref     : 0
% 3.22/1.62  #Sup     : 80
% 3.22/1.62  #Fact    : 0
% 3.22/1.62  #Define  : 0
% 3.22/1.62  #Split   : 3
% 3.22/1.62  #Chain   : 0
% 3.22/1.62  #Close   : 0
% 3.22/1.62  
% 3.22/1.62  Ordering : KBO
% 3.22/1.62  
% 3.22/1.62  Simplification rules
% 3.22/1.62  ----------------------
% 3.22/1.62  #Subsume      : 8
% 3.22/1.62  #Demod        : 88
% 3.22/1.62  #Tautology    : 13
% 3.22/1.62  #SimpNegUnit  : 36
% 3.22/1.62  #BackRed      : 0
% 3.22/1.62  
% 3.22/1.62  #Partial instantiations: 0
% 3.22/1.62  #Strategies tried      : 1
% 3.22/1.62  
% 3.22/1.62  Timing (in seconds)
% 3.22/1.62  ----------------------
% 3.22/1.62  Preprocessing        : 0.36
% 3.22/1.62  Parsing              : 0.18
% 3.22/1.62  CNF conversion       : 0.04
% 3.22/1.62  Main loop            : 0.42
% 3.22/1.62  Inferencing          : 0.17
% 3.22/1.62  Reduction            : 0.12
% 3.22/1.62  Demodulation         : 0.08
% 3.22/1.62  BG Simplification    : 0.04
% 3.22/1.62  Subsumption          : 0.09
% 3.22/1.62  Abstraction          : 0.02
% 3.22/1.62  MUC search           : 0.00
% 3.22/1.62  Cooper               : 0.00
% 3.22/1.62  Total                : 0.82
% 3.22/1.62  Index Insertion      : 0.00
% 3.22/1.62  Index Deletion       : 0.00
% 3.22/1.62  Index Matching       : 0.00
% 3.22/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
