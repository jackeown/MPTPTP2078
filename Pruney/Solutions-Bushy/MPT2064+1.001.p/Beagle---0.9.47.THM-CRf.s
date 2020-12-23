%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT2064+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:49 EST 2020

% Result     : Theorem 5.61s
% Output     : CNFRefutation 6.46s
% Verified   : 
% Statistics : Number of formulae       :  596 (2493 expanded)
%              Number of leaves         :   40 ( 920 expanded)
%              Depth                    :   26
%              Number of atoms          : 3723 (17868 expanded)
%              Number of equality atoms :   67 (  91 expanded)
%              Maximal formula depth    :   18 (   8 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_waybel_9 > r1_waybel_0 > m2_yellow_6 > v3_yellow_6 > r2_hidden > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k2_pre_topc > k10_yellow_6 > #nlpp > u1_struct_0 > k1_zfmisc_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m2_yellow_6,type,(
    m2_yellow_6: ( $i * $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k10_yellow_6,type,(
    k10_yellow_6: ( $i * $i ) > $i )).

tff(v3_yellow_6,type,(
    v3_yellow_6: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v7_waybel_0,type,(
    v7_waybel_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r3_waybel_9,type,(
    r3_waybel_9: ( $i * $i * $i ) > $o )).

tff(r1_waybel_0,type,(
    r1_waybel_0: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(l1_waybel_0,type,(
    l1_waybel_0: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_229,negated_conjecture,(
    ~ ! [A] :
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

tff(f_157,axiom,(
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
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r2_hidden(C,k10_yellow_6(A,B))
               => r3_waybel_9(A,B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_waybel_9)).

tff(f_133,axiom,(
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

tff(f_47,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_xboole_0)).

tff(f_78,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_51,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_192,axiom,(
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
              ( m1_subset_1(C,u1_struct_0(A))
             => ~ ( r3_waybel_9(A,B,C)
                  & ! [D] :
                      ( m2_yellow_6(D,A,B)
                     => ~ r2_hidden(C,k10_yellow_6(A,D)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_waybel_9)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A)
        & ~ v2_struct_0(B)
        & v4_orders_2(B)
        & v7_waybel_0(B)
        & l1_waybel_0(B,A) )
     => ! [C] :
          ( m2_yellow_6(C,A,B)
         => ( ~ v2_struct_0(C)
            & v4_orders_2(C)
            & v7_waybel_0(C)
            & l1_waybel_0(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_yellow_6)).

tff(f_46,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v4_orders_2(B)
            & v7_waybel_0(B)
            & l1_waybel_0(B,A) )
         => ( v3_yellow_6(B,A)
          <=> k10_yellow_6(A,B) != k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_yellow_6)).

tff(f_104,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B,C] :
          ( ( ~ v2_struct_0(C)
            & v4_orders_2(C)
            & v7_waybel_0(C)
            & l1_waybel_0(C,A) )
         => ( r1_waybel_0(A,C,B)
           => ! [D] :
                ( m2_yellow_6(D,A,C)
               => r1_waybel_0(A,D,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_yellow19)).

tff(f_197,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

tff(c_48,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_88,plain,
    ( r2_hidden('#skF_5',k2_pre_topc('#skF_3','#skF_4'))
    | ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_96,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_84,plain,
    ( r2_hidden('#skF_5',k2_pre_topc('#skF_3','#skF_4'))
    | v4_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_98,plain,(
    v4_orders_2('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_80,plain,
    ( r2_hidden('#skF_5',k2_pre_topc('#skF_3','#skF_4'))
    | v7_waybel_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_99,plain,(
    v7_waybel_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_76,plain,
    ( r2_hidden('#skF_5',k2_pre_topc('#skF_3','#skF_4'))
    | v3_yellow_6('#skF_6','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_100,plain,(
    v3_yellow_6('#skF_6','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_72,plain,
    ( r2_hidden('#skF_5',k2_pre_topc('#skF_3','#skF_4'))
    | l1_waybel_0('#skF_6','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_110,plain,(
    l1_waybel_0('#skF_6','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_68,plain,
    ( r2_hidden('#skF_5',k2_pre_topc('#skF_3','#skF_4'))
    | r1_waybel_0('#skF_3','#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_111,plain,(
    r1_waybel_0('#skF_3','#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_64,plain,
    ( r2_hidden('#skF_5',k2_pre_topc('#skF_3','#skF_4'))
    | r2_hidden('#skF_5',k10_yellow_6('#skF_3','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_112,plain,(
    r2_hidden('#skF_5',k10_yellow_6('#skF_3','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_58,plain,(
    ! [D_85] :
      ( ~ r2_hidden('#skF_5',k10_yellow_6('#skF_3',D_85))
      | ~ r1_waybel_0('#skF_3',D_85,'#skF_4')
      | ~ l1_waybel_0(D_85,'#skF_3')
      | ~ v3_yellow_6(D_85,'#skF_3')
      | ~ v7_waybel_0(D_85)
      | ~ v4_orders_2(D_85)
      | v2_struct_0(D_85)
      | ~ r2_hidden('#skF_5',k2_pre_topc('#skF_3','#skF_4')) ) ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_164,plain,(
    ~ r2_hidden('#skF_5',k2_pre_topc('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_50,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_54,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_52,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_187,plain,(
    ! [A_133,B_134,C_135] :
      ( r3_waybel_9(A_133,B_134,C_135)
      | ~ r2_hidden(C_135,k10_yellow_6(A_133,B_134))
      | ~ m1_subset_1(C_135,u1_struct_0(A_133))
      | ~ l1_waybel_0(B_134,A_133)
      | ~ v7_waybel_0(B_134)
      | ~ v4_orders_2(B_134)
      | v2_struct_0(B_134)
      | ~ l1_pre_topc(A_133)
      | ~ v2_pre_topc(A_133)
      | v2_struct_0(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_190,plain,
    ( r3_waybel_9('#skF_3','#skF_6','#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ l1_waybel_0('#skF_6','#skF_3')
    | ~ v7_waybel_0('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | v2_struct_0('#skF_6')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_112,c_187])).

tff(c_197,plain,
    ( r3_waybel_9('#skF_3','#skF_6','#skF_5')
    | v2_struct_0('#skF_6')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_98,c_99,c_110,c_48,c_190])).

tff(c_198,plain,(
    r3_waybel_9('#skF_3','#skF_6','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_96,c_197])).

tff(c_292,plain,(
    ! [C_169,A_170,B_171,D_172] :
      ( r2_hidden(C_169,k2_pre_topc(A_170,B_171))
      | ~ r3_waybel_9(A_170,D_172,C_169)
      | ~ r1_waybel_0(A_170,D_172,B_171)
      | ~ l1_waybel_0(D_172,A_170)
      | ~ v7_waybel_0(D_172)
      | ~ v4_orders_2(D_172)
      | v2_struct_0(D_172)
      | ~ m1_subset_1(C_169,u1_struct_0(A_170))
      | ~ m1_subset_1(B_171,k1_zfmisc_1(u1_struct_0(A_170)))
      | ~ l1_pre_topc(A_170)
      | ~ v2_pre_topc(A_170)
      | v2_struct_0(A_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_294,plain,(
    ! [B_171] :
      ( r2_hidden('#skF_5',k2_pre_topc('#skF_3',B_171))
      | ~ r1_waybel_0('#skF_3','#skF_6',B_171)
      | ~ l1_waybel_0('#skF_6','#skF_3')
      | ~ v7_waybel_0('#skF_6')
      | ~ v4_orders_2('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_171,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_198,c_292])).

tff(c_299,plain,(
    ! [B_171] :
      ( r2_hidden('#skF_5',k2_pre_topc('#skF_3',B_171))
      | ~ r1_waybel_0('#skF_3','#skF_6',B_171)
      | v2_struct_0('#skF_6')
      | ~ m1_subset_1(B_171,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_98,c_99,c_110,c_294])).

tff(c_305,plain,(
    ! [B_173] :
      ( r2_hidden('#skF_5',k2_pre_topc('#skF_3',B_173))
      | ~ r1_waybel_0('#skF_3','#skF_6',B_173)
      | ~ m1_subset_1(B_173,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_96,c_299])).

tff(c_308,plain,
    ( r2_hidden('#skF_5',k2_pre_topc('#skF_3','#skF_4'))
    | ~ r1_waybel_0('#skF_3','#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_305])).

tff(c_311,plain,(
    r2_hidden('#skF_5',k2_pre_topc('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_308])).

tff(c_313,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_164,c_311])).

tff(c_349,plain,(
    ! [D_174] :
      ( ~ r2_hidden('#skF_5',k10_yellow_6('#skF_3',D_174))
      | ~ r1_waybel_0('#skF_3',D_174,'#skF_4')
      | ~ l1_waybel_0(D_174,'#skF_3')
      | ~ v3_yellow_6(D_174,'#skF_3')
      | ~ v7_waybel_0(D_174)
      | ~ v4_orders_2(D_174)
      | v2_struct_0(D_174) ) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_352,plain,
    ( ~ r1_waybel_0('#skF_3','#skF_6','#skF_4')
    | ~ l1_waybel_0('#skF_6','#skF_3')
    | ~ v3_yellow_6('#skF_6','#skF_3')
    | ~ v7_waybel_0('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_112,c_349])).

tff(c_358,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_99,c_100,c_110,c_111,c_352])).

tff(c_360,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_358])).

tff(c_361,plain,(
    r2_hidden('#skF_5',k2_pre_topc('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_452,plain,(
    ! [A_209,B_210,C_211] :
      ( r1_waybel_0(A_209,'#skF_1'(A_209,B_210,C_211),B_210)
      | ~ r2_hidden(C_211,k2_pre_topc(A_209,B_210))
      | ~ m1_subset_1(C_211,u1_struct_0(A_209))
      | ~ m1_subset_1(B_210,k1_zfmisc_1(u1_struct_0(A_209)))
      | ~ l1_pre_topc(A_209)
      | ~ v2_pre_topc(A_209)
      | v2_struct_0(A_209) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_454,plain,(
    ! [C_211] :
      ( r1_waybel_0('#skF_3','#skF_1'('#skF_3','#skF_4',C_211),'#skF_4')
      | ~ r2_hidden(C_211,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_211,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_50,c_452])).

tff(c_457,plain,(
    ! [C_211] :
      ( r1_waybel_0('#skF_3','#skF_1'('#skF_3','#skF_4',C_211),'#skF_4')
      | ~ r2_hidden(C_211,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_211,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_454])).

tff(c_458,plain,(
    ! [C_211] :
      ( r1_waybel_0('#skF_3','#skF_1'('#skF_3','#skF_4',C_211),'#skF_4')
      | ~ r2_hidden(C_211,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_211,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_457])).

tff(c_428,plain,(
    ! [A_202,B_203,C_204] :
      ( ~ v2_struct_0('#skF_1'(A_202,B_203,C_204))
      | ~ r2_hidden(C_204,k2_pre_topc(A_202,B_203))
      | ~ m1_subset_1(C_204,u1_struct_0(A_202))
      | ~ m1_subset_1(B_203,k1_zfmisc_1(u1_struct_0(A_202)))
      | ~ l1_pre_topc(A_202)
      | ~ v2_pre_topc(A_202)
      | v2_struct_0(A_202) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_430,plain,
    ( ~ v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_361,c_428])).

tff(c_436,plain,
    ( ~ v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_430])).

tff(c_437,plain,(
    ~ v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_436])).

tff(c_397,plain,(
    ! [A_191,B_192,C_193] :
      ( v4_orders_2('#skF_1'(A_191,B_192,C_193))
      | ~ r2_hidden(C_193,k2_pre_topc(A_191,B_192))
      | ~ m1_subset_1(C_193,u1_struct_0(A_191))
      | ~ m1_subset_1(B_192,k1_zfmisc_1(u1_struct_0(A_191)))
      | ~ l1_pre_topc(A_191)
      | ~ v2_pre_topc(A_191)
      | v2_struct_0(A_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_399,plain,
    ( v4_orders_2('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_361,c_397])).

tff(c_405,plain,
    ( v4_orders_2('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_399])).

tff(c_406,plain,(
    v4_orders_2('#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_405])).

tff(c_410,plain,(
    ! [A_198,B_199,C_200] :
      ( v7_waybel_0('#skF_1'(A_198,B_199,C_200))
      | ~ r2_hidden(C_200,k2_pre_topc(A_198,B_199))
      | ~ m1_subset_1(C_200,u1_struct_0(A_198))
      | ~ m1_subset_1(B_199,k1_zfmisc_1(u1_struct_0(A_198)))
      | ~ l1_pre_topc(A_198)
      | ~ v2_pre_topc(A_198)
      | v2_struct_0(A_198) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_412,plain,
    ( v7_waybel_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_361,c_410])).

tff(c_418,plain,
    ( v7_waybel_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_412])).

tff(c_419,plain,(
    v7_waybel_0('#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_418])).

tff(c_440,plain,(
    ! [A_206,B_207,C_208] :
      ( l1_waybel_0('#skF_1'(A_206,B_207,C_208),A_206)
      | ~ r2_hidden(C_208,k2_pre_topc(A_206,B_207))
      | ~ m1_subset_1(C_208,u1_struct_0(A_206))
      | ~ m1_subset_1(B_207,k1_zfmisc_1(u1_struct_0(A_206)))
      | ~ l1_pre_topc(A_206)
      | ~ v2_pre_topc(A_206)
      | v2_struct_0(A_206) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_442,plain,
    ( l1_waybel_0('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_361,c_440])).

tff(c_448,plain,
    ( l1_waybel_0('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_442])).

tff(c_449,plain,(
    l1_waybel_0('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_448])).

tff(c_460,plain,(
    ! [A_213,B_214,C_215] :
      ( r3_waybel_9(A_213,'#skF_1'(A_213,B_214,C_215),C_215)
      | ~ r2_hidden(C_215,k2_pre_topc(A_213,B_214))
      | ~ m1_subset_1(C_215,u1_struct_0(A_213))
      | ~ m1_subset_1(B_214,k1_zfmisc_1(u1_struct_0(A_213)))
      | ~ l1_pre_topc(A_213)
      | ~ v2_pre_topc(A_213)
      | v2_struct_0(A_213) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_462,plain,(
    ! [C_215] :
      ( r3_waybel_9('#skF_3','#skF_1'('#skF_3','#skF_4',C_215),C_215)
      | ~ r2_hidden(C_215,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_215,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_50,c_460])).

tff(c_465,plain,(
    ! [C_215] :
      ( r3_waybel_9('#skF_3','#skF_1'('#skF_3','#skF_4',C_215),C_215)
      | ~ r2_hidden(C_215,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_215,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_462])).

tff(c_466,plain,(
    ! [C_215] :
      ( r3_waybel_9('#skF_3','#skF_1'('#skF_3','#skF_4',C_215),C_215)
      | ~ r2_hidden(C_215,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_215,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_465])).

tff(c_6,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_18,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_89,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_18])).

tff(c_8,plain,(
    ! [A_4] :
      ( l1_struct_0(A_4)
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_495,plain,(
    ! [A_227,B_228,C_229] :
      ( m2_yellow_6('#skF_2'(A_227,B_228,C_229),A_227,B_228)
      | ~ r3_waybel_9(A_227,B_228,C_229)
      | ~ m1_subset_1(C_229,u1_struct_0(A_227))
      | ~ l1_waybel_0(B_228,A_227)
      | ~ v7_waybel_0(B_228)
      | ~ v4_orders_2(B_228)
      | v2_struct_0(B_228)
      | ~ l1_pre_topc(A_227)
      | ~ v2_pre_topc(A_227)
      | v2_struct_0(A_227) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_12,plain,(
    ! [C_8,A_5,B_6] :
      ( v7_waybel_0(C_8)
      | ~ m2_yellow_6(C_8,A_5,B_6)
      | ~ l1_waybel_0(B_6,A_5)
      | ~ v7_waybel_0(B_6)
      | ~ v4_orders_2(B_6)
      | v2_struct_0(B_6)
      | ~ l1_struct_0(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_572,plain,(
    ! [A_245,B_246,C_247] :
      ( v7_waybel_0('#skF_2'(A_245,B_246,C_247))
      | ~ l1_struct_0(A_245)
      | ~ r3_waybel_9(A_245,B_246,C_247)
      | ~ m1_subset_1(C_247,u1_struct_0(A_245))
      | ~ l1_waybel_0(B_246,A_245)
      | ~ v7_waybel_0(B_246)
      | ~ v4_orders_2(B_246)
      | v2_struct_0(B_246)
      | ~ l1_pre_topc(A_245)
      | ~ v2_pre_topc(A_245)
      | v2_struct_0(A_245) ) ),
    inference(resolution,[status(thm)],[c_495,c_12])).

tff(c_574,plain,(
    ! [B_246] :
      ( v7_waybel_0('#skF_2'('#skF_3',B_246,'#skF_5'))
      | ~ l1_struct_0('#skF_3')
      | ~ r3_waybel_9('#skF_3',B_246,'#skF_5')
      | ~ l1_waybel_0(B_246,'#skF_3')
      | ~ v7_waybel_0(B_246)
      | ~ v4_orders_2(B_246)
      | v2_struct_0(B_246)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_48,c_572])).

tff(c_577,plain,(
    ! [B_246] :
      ( v7_waybel_0('#skF_2'('#skF_3',B_246,'#skF_5'))
      | ~ l1_struct_0('#skF_3')
      | ~ r3_waybel_9('#skF_3',B_246,'#skF_5')
      | ~ l1_waybel_0(B_246,'#skF_3')
      | ~ v7_waybel_0(B_246)
      | ~ v4_orders_2(B_246)
      | v2_struct_0(B_246)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_574])).

tff(c_578,plain,(
    ! [B_246] :
      ( v7_waybel_0('#skF_2'('#skF_3',B_246,'#skF_5'))
      | ~ l1_struct_0('#skF_3')
      | ~ r3_waybel_9('#skF_3',B_246,'#skF_5')
      | ~ l1_waybel_0(B_246,'#skF_3')
      | ~ v7_waybel_0(B_246)
      | ~ v4_orders_2(B_246)
      | v2_struct_0(B_246) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_577])).

tff(c_579,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_578])).

tff(c_589,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_579])).

tff(c_593,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_589])).

tff(c_595,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_578])).

tff(c_14,plain,(
    ! [C_8,A_5,B_6] :
      ( v4_orders_2(C_8)
      | ~ m2_yellow_6(C_8,A_5,B_6)
      | ~ l1_waybel_0(B_6,A_5)
      | ~ v7_waybel_0(B_6)
      | ~ v4_orders_2(B_6)
      | v2_struct_0(B_6)
      | ~ l1_struct_0(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_599,plain,(
    ! [A_257,B_258,C_259] :
      ( v4_orders_2('#skF_2'(A_257,B_258,C_259))
      | ~ l1_struct_0(A_257)
      | ~ r3_waybel_9(A_257,B_258,C_259)
      | ~ m1_subset_1(C_259,u1_struct_0(A_257))
      | ~ l1_waybel_0(B_258,A_257)
      | ~ v7_waybel_0(B_258)
      | ~ v4_orders_2(B_258)
      | v2_struct_0(B_258)
      | ~ l1_pre_topc(A_257)
      | ~ v2_pre_topc(A_257)
      | v2_struct_0(A_257) ) ),
    inference(resolution,[status(thm)],[c_495,c_14])).

tff(c_601,plain,(
    ! [B_258] :
      ( v4_orders_2('#skF_2'('#skF_3',B_258,'#skF_5'))
      | ~ l1_struct_0('#skF_3')
      | ~ r3_waybel_9('#skF_3',B_258,'#skF_5')
      | ~ l1_waybel_0(B_258,'#skF_3')
      | ~ v7_waybel_0(B_258)
      | ~ v4_orders_2(B_258)
      | v2_struct_0(B_258)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_48,c_599])).

tff(c_604,plain,(
    ! [B_258] :
      ( v4_orders_2('#skF_2'('#skF_3',B_258,'#skF_5'))
      | ~ r3_waybel_9('#skF_3',B_258,'#skF_5')
      | ~ l1_waybel_0(B_258,'#skF_3')
      | ~ v7_waybel_0(B_258)
      | ~ v4_orders_2(B_258)
      | v2_struct_0(B_258)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_595,c_601])).

tff(c_605,plain,(
    ! [B_258] :
      ( v4_orders_2('#skF_2'('#skF_3',B_258,'#skF_5'))
      | ~ r3_waybel_9('#skF_3',B_258,'#skF_5')
      | ~ l1_waybel_0(B_258,'#skF_3')
      | ~ v7_waybel_0(B_258)
      | ~ v4_orders_2(B_258)
      | v2_struct_0(B_258) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_604])).

tff(c_594,plain,(
    ! [B_246] :
      ( v7_waybel_0('#skF_2'('#skF_3',B_246,'#skF_5'))
      | ~ r3_waybel_9('#skF_3',B_246,'#skF_5')
      | ~ l1_waybel_0(B_246,'#skF_3')
      | ~ v7_waybel_0(B_246)
      | ~ v4_orders_2(B_246)
      | v2_struct_0(B_246) ) ),
    inference(splitRight,[status(thm)],[c_578])).

tff(c_10,plain,(
    ! [C_8,A_5,B_6] :
      ( l1_waybel_0(C_8,A_5)
      | ~ m2_yellow_6(C_8,A_5,B_6)
      | ~ l1_waybel_0(B_6,A_5)
      | ~ v7_waybel_0(B_6)
      | ~ v4_orders_2(B_6)
      | v2_struct_0(B_6)
      | ~ l1_struct_0(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_607,plain,(
    ! [A_261,B_262,C_263] :
      ( l1_waybel_0('#skF_2'(A_261,B_262,C_263),A_261)
      | ~ l1_struct_0(A_261)
      | ~ r3_waybel_9(A_261,B_262,C_263)
      | ~ m1_subset_1(C_263,u1_struct_0(A_261))
      | ~ l1_waybel_0(B_262,A_261)
      | ~ v7_waybel_0(B_262)
      | ~ v4_orders_2(B_262)
      | v2_struct_0(B_262)
      | ~ l1_pre_topc(A_261)
      | ~ v2_pre_topc(A_261)
      | v2_struct_0(A_261) ) ),
    inference(resolution,[status(thm)],[c_495,c_10])).

tff(c_609,plain,(
    ! [B_262] :
      ( l1_waybel_0('#skF_2'('#skF_3',B_262,'#skF_5'),'#skF_3')
      | ~ l1_struct_0('#skF_3')
      | ~ r3_waybel_9('#skF_3',B_262,'#skF_5')
      | ~ l1_waybel_0(B_262,'#skF_3')
      | ~ v7_waybel_0(B_262)
      | ~ v4_orders_2(B_262)
      | v2_struct_0(B_262)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_48,c_607])).

tff(c_612,plain,(
    ! [B_262] :
      ( l1_waybel_0('#skF_2'('#skF_3',B_262,'#skF_5'),'#skF_3')
      | ~ r3_waybel_9('#skF_3',B_262,'#skF_5')
      | ~ l1_waybel_0(B_262,'#skF_3')
      | ~ v7_waybel_0(B_262)
      | ~ v4_orders_2(B_262)
      | v2_struct_0(B_262)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_595,c_609])).

tff(c_613,plain,(
    ! [B_262] :
      ( l1_waybel_0('#skF_2'('#skF_3',B_262,'#skF_5'),'#skF_3')
      | ~ r3_waybel_9('#skF_3',B_262,'#skF_5')
      | ~ l1_waybel_0(B_262,'#skF_3')
      | ~ v7_waybel_0(B_262)
      | ~ v4_orders_2(B_262)
      | v2_struct_0(B_262) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_612])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v3_yellow_6(B_3,A_1)
      | k10_yellow_6(A_1,B_3) = k1_xboole_0
      | ~ l1_waybel_0(B_3,A_1)
      | ~ v7_waybel_0(B_3)
      | ~ v4_orders_2(B_3)
      | v2_struct_0(B_3)
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_22,plain,(
    ! [A_11,D_19,B_16,C_17] :
      ( r1_waybel_0(A_11,D_19,B_16)
      | ~ m2_yellow_6(D_19,A_11,C_17)
      | ~ r1_waybel_0(A_11,C_17,B_16)
      | ~ l1_waybel_0(C_17,A_11)
      | ~ v7_waybel_0(C_17)
      | ~ v4_orders_2(C_17)
      | v2_struct_0(C_17)
      | ~ l1_struct_0(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_636,plain,(
    ! [A_275,B_276,C_277,B_278] :
      ( r1_waybel_0(A_275,'#skF_2'(A_275,B_276,C_277),B_278)
      | ~ r1_waybel_0(A_275,B_276,B_278)
      | ~ l1_struct_0(A_275)
      | ~ r3_waybel_9(A_275,B_276,C_277)
      | ~ m1_subset_1(C_277,u1_struct_0(A_275))
      | ~ l1_waybel_0(B_276,A_275)
      | ~ v7_waybel_0(B_276)
      | ~ v4_orders_2(B_276)
      | v2_struct_0(B_276)
      | ~ l1_pre_topc(A_275)
      | ~ v2_pre_topc(A_275)
      | v2_struct_0(A_275) ) ),
    inference(resolution,[status(thm)],[c_495,c_22])).

tff(c_536,plain,(
    ! [C_235,A_236,B_237] :
      ( r2_hidden(C_235,k10_yellow_6(A_236,'#skF_2'(A_236,B_237,C_235)))
      | ~ r3_waybel_9(A_236,B_237,C_235)
      | ~ m1_subset_1(C_235,u1_struct_0(A_236))
      | ~ l1_waybel_0(B_237,A_236)
      | ~ v7_waybel_0(B_237)
      | ~ v4_orders_2(B_237)
      | v2_struct_0(B_237)
      | ~ l1_pre_topc(A_236)
      | ~ v2_pre_topc(A_236)
      | v2_struct_0(A_236) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_422,plain,(
    ! [D_85] :
      ( ~ r2_hidden('#skF_5',k10_yellow_6('#skF_3',D_85))
      | ~ r1_waybel_0('#skF_3',D_85,'#skF_4')
      | ~ l1_waybel_0(D_85,'#skF_3')
      | ~ v3_yellow_6(D_85,'#skF_3')
      | ~ v7_waybel_0(D_85)
      | ~ v4_orders_2(D_85)
      | v2_struct_0(D_85) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_361,c_58])).

tff(c_543,plain,(
    ! [B_237] :
      ( ~ r1_waybel_0('#skF_3','#skF_2'('#skF_3',B_237,'#skF_5'),'#skF_4')
      | ~ l1_waybel_0('#skF_2'('#skF_3',B_237,'#skF_5'),'#skF_3')
      | ~ v3_yellow_6('#skF_2'('#skF_3',B_237,'#skF_5'),'#skF_3')
      | ~ v7_waybel_0('#skF_2'('#skF_3',B_237,'#skF_5'))
      | ~ v4_orders_2('#skF_2'('#skF_3',B_237,'#skF_5'))
      | v2_struct_0('#skF_2'('#skF_3',B_237,'#skF_5'))
      | ~ r3_waybel_9('#skF_3',B_237,'#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
      | ~ l1_waybel_0(B_237,'#skF_3')
      | ~ v7_waybel_0(B_237)
      | ~ v4_orders_2(B_237)
      | v2_struct_0(B_237)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_536,c_422])).

tff(c_553,plain,(
    ! [B_237] :
      ( ~ r1_waybel_0('#skF_3','#skF_2'('#skF_3',B_237,'#skF_5'),'#skF_4')
      | ~ l1_waybel_0('#skF_2'('#skF_3',B_237,'#skF_5'),'#skF_3')
      | ~ v3_yellow_6('#skF_2'('#skF_3',B_237,'#skF_5'),'#skF_3')
      | ~ v7_waybel_0('#skF_2'('#skF_3',B_237,'#skF_5'))
      | ~ v4_orders_2('#skF_2'('#skF_3',B_237,'#skF_5'))
      | v2_struct_0('#skF_2'('#skF_3',B_237,'#skF_5'))
      | ~ r3_waybel_9('#skF_3',B_237,'#skF_5')
      | ~ l1_waybel_0(B_237,'#skF_3')
      | ~ v7_waybel_0(B_237)
      | ~ v4_orders_2(B_237)
      | v2_struct_0(B_237)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_543])).

tff(c_554,plain,(
    ! [B_237] :
      ( ~ r1_waybel_0('#skF_3','#skF_2'('#skF_3',B_237,'#skF_5'),'#skF_4')
      | ~ l1_waybel_0('#skF_2'('#skF_3',B_237,'#skF_5'),'#skF_3')
      | ~ v3_yellow_6('#skF_2'('#skF_3',B_237,'#skF_5'),'#skF_3')
      | ~ v7_waybel_0('#skF_2'('#skF_3',B_237,'#skF_5'))
      | ~ v4_orders_2('#skF_2'('#skF_3',B_237,'#skF_5'))
      | v2_struct_0('#skF_2'('#skF_3',B_237,'#skF_5'))
      | ~ r3_waybel_9('#skF_3',B_237,'#skF_5')
      | ~ l1_waybel_0(B_237,'#skF_3')
      | ~ v7_waybel_0(B_237)
      | ~ v4_orders_2(B_237)
      | v2_struct_0(B_237) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_553])).

tff(c_640,plain,(
    ! [B_276] :
      ( ~ l1_waybel_0('#skF_2'('#skF_3',B_276,'#skF_5'),'#skF_3')
      | ~ v3_yellow_6('#skF_2'('#skF_3',B_276,'#skF_5'),'#skF_3')
      | ~ v7_waybel_0('#skF_2'('#skF_3',B_276,'#skF_5'))
      | ~ v4_orders_2('#skF_2'('#skF_3',B_276,'#skF_5'))
      | v2_struct_0('#skF_2'('#skF_3',B_276,'#skF_5'))
      | ~ r1_waybel_0('#skF_3',B_276,'#skF_4')
      | ~ l1_struct_0('#skF_3')
      | ~ r3_waybel_9('#skF_3',B_276,'#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
      | ~ l1_waybel_0(B_276,'#skF_3')
      | ~ v7_waybel_0(B_276)
      | ~ v4_orders_2(B_276)
      | v2_struct_0(B_276)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_636,c_554])).

tff(c_643,plain,(
    ! [B_276] :
      ( ~ l1_waybel_0('#skF_2'('#skF_3',B_276,'#skF_5'),'#skF_3')
      | ~ v3_yellow_6('#skF_2'('#skF_3',B_276,'#skF_5'),'#skF_3')
      | ~ v7_waybel_0('#skF_2'('#skF_3',B_276,'#skF_5'))
      | ~ v4_orders_2('#skF_2'('#skF_3',B_276,'#skF_5'))
      | v2_struct_0('#skF_2'('#skF_3',B_276,'#skF_5'))
      | ~ r1_waybel_0('#skF_3',B_276,'#skF_4')
      | ~ r3_waybel_9('#skF_3',B_276,'#skF_5')
      | ~ l1_waybel_0(B_276,'#skF_3')
      | ~ v7_waybel_0(B_276)
      | ~ v4_orders_2(B_276)
      | v2_struct_0(B_276)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_595,c_640])).

tff(c_645,plain,(
    ! [B_279] :
      ( ~ l1_waybel_0('#skF_2'('#skF_3',B_279,'#skF_5'),'#skF_3')
      | ~ v3_yellow_6('#skF_2'('#skF_3',B_279,'#skF_5'),'#skF_3')
      | ~ v7_waybel_0('#skF_2'('#skF_3',B_279,'#skF_5'))
      | ~ v4_orders_2('#skF_2'('#skF_3',B_279,'#skF_5'))
      | v2_struct_0('#skF_2'('#skF_3',B_279,'#skF_5'))
      | ~ r1_waybel_0('#skF_3',B_279,'#skF_4')
      | ~ r3_waybel_9('#skF_3',B_279,'#skF_5')
      | ~ l1_waybel_0(B_279,'#skF_3')
      | ~ v7_waybel_0(B_279)
      | ~ v4_orders_2(B_279)
      | v2_struct_0(B_279) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_643])).

tff(c_648,plain,(
    ! [B_279] :
      ( ~ r1_waybel_0('#skF_3',B_279,'#skF_4')
      | ~ r3_waybel_9('#skF_3',B_279,'#skF_5')
      | ~ l1_waybel_0(B_279,'#skF_3')
      | ~ v7_waybel_0(B_279)
      | ~ v4_orders_2(B_279)
      | v2_struct_0(B_279)
      | k10_yellow_6('#skF_3','#skF_2'('#skF_3',B_279,'#skF_5')) = k1_xboole_0
      | ~ l1_waybel_0('#skF_2'('#skF_3',B_279,'#skF_5'),'#skF_3')
      | ~ v7_waybel_0('#skF_2'('#skF_3',B_279,'#skF_5'))
      | ~ v4_orders_2('#skF_2'('#skF_3',B_279,'#skF_5'))
      | v2_struct_0('#skF_2'('#skF_3',B_279,'#skF_5'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_2,c_645])).

tff(c_651,plain,(
    ! [B_279] :
      ( ~ r1_waybel_0('#skF_3',B_279,'#skF_4')
      | ~ r3_waybel_9('#skF_3',B_279,'#skF_5')
      | ~ l1_waybel_0(B_279,'#skF_3')
      | ~ v7_waybel_0(B_279)
      | ~ v4_orders_2(B_279)
      | v2_struct_0(B_279)
      | k10_yellow_6('#skF_3','#skF_2'('#skF_3',B_279,'#skF_5')) = k1_xboole_0
      | ~ l1_waybel_0('#skF_2'('#skF_3',B_279,'#skF_5'),'#skF_3')
      | ~ v7_waybel_0('#skF_2'('#skF_3',B_279,'#skF_5'))
      | ~ v4_orders_2('#skF_2'('#skF_3',B_279,'#skF_5'))
      | v2_struct_0('#skF_2'('#skF_3',B_279,'#skF_5'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_648])).

tff(c_653,plain,(
    ! [B_280] :
      ( ~ r1_waybel_0('#skF_3',B_280,'#skF_4')
      | ~ r3_waybel_9('#skF_3',B_280,'#skF_5')
      | ~ l1_waybel_0(B_280,'#skF_3')
      | ~ v7_waybel_0(B_280)
      | ~ v4_orders_2(B_280)
      | v2_struct_0(B_280)
      | k10_yellow_6('#skF_3','#skF_2'('#skF_3',B_280,'#skF_5')) = k1_xboole_0
      | ~ l1_waybel_0('#skF_2'('#skF_3',B_280,'#skF_5'),'#skF_3')
      | ~ v7_waybel_0('#skF_2'('#skF_3',B_280,'#skF_5'))
      | ~ v4_orders_2('#skF_2'('#skF_3',B_280,'#skF_5'))
      | v2_struct_0('#skF_2'('#skF_3',B_280,'#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_651])).

tff(c_658,plain,(
    ! [B_281] :
      ( ~ r1_waybel_0('#skF_3',B_281,'#skF_4')
      | k10_yellow_6('#skF_3','#skF_2'('#skF_3',B_281,'#skF_5')) = k1_xboole_0
      | ~ v7_waybel_0('#skF_2'('#skF_3',B_281,'#skF_5'))
      | ~ v4_orders_2('#skF_2'('#skF_3',B_281,'#skF_5'))
      | v2_struct_0('#skF_2'('#skF_3',B_281,'#skF_5'))
      | ~ r3_waybel_9('#skF_3',B_281,'#skF_5')
      | ~ l1_waybel_0(B_281,'#skF_3')
      | ~ v7_waybel_0(B_281)
      | ~ v4_orders_2(B_281)
      | v2_struct_0(B_281) ) ),
    inference(resolution,[status(thm)],[c_613,c_653])).

tff(c_663,plain,(
    ! [B_282] :
      ( ~ r1_waybel_0('#skF_3',B_282,'#skF_4')
      | k10_yellow_6('#skF_3','#skF_2'('#skF_3',B_282,'#skF_5')) = k1_xboole_0
      | ~ v4_orders_2('#skF_2'('#skF_3',B_282,'#skF_5'))
      | v2_struct_0('#skF_2'('#skF_3',B_282,'#skF_5'))
      | ~ r3_waybel_9('#skF_3',B_282,'#skF_5')
      | ~ l1_waybel_0(B_282,'#skF_3')
      | ~ v7_waybel_0(B_282)
      | ~ v4_orders_2(B_282)
      | v2_struct_0(B_282) ) ),
    inference(resolution,[status(thm)],[c_594,c_658])).

tff(c_668,plain,(
    ! [B_283] :
      ( ~ r1_waybel_0('#skF_3',B_283,'#skF_4')
      | k10_yellow_6('#skF_3','#skF_2'('#skF_3',B_283,'#skF_5')) = k1_xboole_0
      | v2_struct_0('#skF_2'('#skF_3',B_283,'#skF_5'))
      | ~ r3_waybel_9('#skF_3',B_283,'#skF_5')
      | ~ l1_waybel_0(B_283,'#skF_3')
      | ~ v7_waybel_0(B_283)
      | ~ v4_orders_2(B_283)
      | v2_struct_0(B_283) ) ),
    inference(resolution,[status(thm)],[c_605,c_663])).

tff(c_16,plain,(
    ! [C_8,A_5,B_6] :
      ( ~ v2_struct_0(C_8)
      | ~ m2_yellow_6(C_8,A_5,B_6)
      | ~ l1_waybel_0(B_6,A_5)
      | ~ v7_waybel_0(B_6)
      | ~ v4_orders_2(B_6)
      | v2_struct_0(B_6)
      | ~ l1_struct_0(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_513,plain,(
    ! [A_227,B_228,C_229] :
      ( ~ v2_struct_0('#skF_2'(A_227,B_228,C_229))
      | ~ l1_struct_0(A_227)
      | ~ r3_waybel_9(A_227,B_228,C_229)
      | ~ m1_subset_1(C_229,u1_struct_0(A_227))
      | ~ l1_waybel_0(B_228,A_227)
      | ~ v7_waybel_0(B_228)
      | ~ v4_orders_2(B_228)
      | v2_struct_0(B_228)
      | ~ l1_pre_topc(A_227)
      | ~ v2_pre_topc(A_227)
      | v2_struct_0(A_227) ) ),
    inference(resolution,[status(thm)],[c_495,c_16])).

tff(c_670,plain,(
    ! [B_283] :
      ( ~ l1_struct_0('#skF_3')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r1_waybel_0('#skF_3',B_283,'#skF_4')
      | k10_yellow_6('#skF_3','#skF_2'('#skF_3',B_283,'#skF_5')) = k1_xboole_0
      | ~ r3_waybel_9('#skF_3',B_283,'#skF_5')
      | ~ l1_waybel_0(B_283,'#skF_3')
      | ~ v7_waybel_0(B_283)
      | ~ v4_orders_2(B_283)
      | v2_struct_0(B_283) ) ),
    inference(resolution,[status(thm)],[c_668,c_513])).

tff(c_673,plain,(
    ! [B_283] :
      ( v2_struct_0('#skF_3')
      | ~ r1_waybel_0('#skF_3',B_283,'#skF_4')
      | k10_yellow_6('#skF_3','#skF_2'('#skF_3',B_283,'#skF_5')) = k1_xboole_0
      | ~ r3_waybel_9('#skF_3',B_283,'#skF_5')
      | ~ l1_waybel_0(B_283,'#skF_3')
      | ~ v7_waybel_0(B_283)
      | ~ v4_orders_2(B_283)
      | v2_struct_0(B_283) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_595,c_670])).

tff(c_675,plain,(
    ! [B_284] :
      ( ~ r1_waybel_0('#skF_3',B_284,'#skF_4')
      | k10_yellow_6('#skF_3','#skF_2'('#skF_3',B_284,'#skF_5')) = k1_xboole_0
      | ~ r3_waybel_9('#skF_3',B_284,'#skF_5')
      | ~ l1_waybel_0(B_284,'#skF_3')
      | ~ v7_waybel_0(B_284)
      | ~ v4_orders_2(B_284)
      | v2_struct_0(B_284) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_673])).

tff(c_46,plain,(
    ! [B_66,A_65] :
      ( ~ v1_xboole_0(B_66)
      | ~ r2_hidden(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_556,plain,(
    ! [A_236,B_237,C_235] :
      ( ~ v1_xboole_0(k10_yellow_6(A_236,'#skF_2'(A_236,B_237,C_235)))
      | ~ r3_waybel_9(A_236,B_237,C_235)
      | ~ m1_subset_1(C_235,u1_struct_0(A_236))
      | ~ l1_waybel_0(B_237,A_236)
      | ~ v7_waybel_0(B_237)
      | ~ v4_orders_2(B_237)
      | v2_struct_0(B_237)
      | ~ l1_pre_topc(A_236)
      | ~ v2_pre_topc(A_236)
      | v2_struct_0(A_236) ) ),
    inference(resolution,[status(thm)],[c_536,c_46])).

tff(c_687,plain,(
    ! [B_284] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r3_waybel_9('#skF_3',B_284,'#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
      | ~ l1_waybel_0(B_284,'#skF_3')
      | ~ v7_waybel_0(B_284)
      | ~ v4_orders_2(B_284)
      | v2_struct_0(B_284)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r1_waybel_0('#skF_3',B_284,'#skF_4')
      | ~ r3_waybel_9('#skF_3',B_284,'#skF_5')
      | ~ l1_waybel_0(B_284,'#skF_3')
      | ~ v7_waybel_0(B_284)
      | ~ v4_orders_2(B_284)
      | v2_struct_0(B_284) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_675,c_556])).

tff(c_711,plain,(
    ! [B_284] :
      ( v2_struct_0('#skF_3')
      | ~ r1_waybel_0('#skF_3',B_284,'#skF_4')
      | ~ r3_waybel_9('#skF_3',B_284,'#skF_5')
      | ~ l1_waybel_0(B_284,'#skF_3')
      | ~ v7_waybel_0(B_284)
      | ~ v4_orders_2(B_284)
      | v2_struct_0(B_284) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_89,c_687])).

tff(c_724,plain,(
    ! [B_288] :
      ( ~ r1_waybel_0('#skF_3',B_288,'#skF_4')
      | ~ r3_waybel_9('#skF_3',B_288,'#skF_5')
      | ~ l1_waybel_0(B_288,'#skF_3')
      | ~ v7_waybel_0(B_288)
      | ~ v4_orders_2(B_288)
      | v2_struct_0(B_288) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_711])).

tff(c_732,plain,
    ( ~ r1_waybel_0('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | ~ l1_waybel_0('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | ~ v7_waybel_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ v4_orders_2('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ r2_hidden('#skF_5',k2_pre_topc('#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_466,c_724])).

tff(c_739,plain,
    ( ~ r1_waybel_0('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_361,c_406,c_419,c_449,c_732])).

tff(c_740,plain,(
    ~ r1_waybel_0('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_437,c_739])).

tff(c_743,plain,
    ( ~ r2_hidden('#skF_5',k2_pre_topc('#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_458,c_740])).

tff(c_747,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_361,c_743])).

tff(c_748,plain,(
    r2_hidden('#skF_5',k2_pre_topc('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_865,plain,(
    ! [A_327,B_328,C_329] :
      ( r1_waybel_0(A_327,'#skF_1'(A_327,B_328,C_329),B_328)
      | ~ r2_hidden(C_329,k2_pre_topc(A_327,B_328))
      | ~ m1_subset_1(C_329,u1_struct_0(A_327))
      | ~ m1_subset_1(B_328,k1_zfmisc_1(u1_struct_0(A_327)))
      | ~ l1_pre_topc(A_327)
      | ~ v2_pre_topc(A_327)
      | v2_struct_0(A_327) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_867,plain,(
    ! [C_329] :
      ( r1_waybel_0('#skF_3','#skF_1'('#skF_3','#skF_4',C_329),'#skF_4')
      | ~ r2_hidden(C_329,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_329,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_50,c_865])).

tff(c_870,plain,(
    ! [C_329] :
      ( r1_waybel_0('#skF_3','#skF_1'('#skF_3','#skF_4',C_329),'#skF_4')
      | ~ r2_hidden(C_329,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_329,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_867])).

tff(c_871,plain,(
    ! [C_329] :
      ( r1_waybel_0('#skF_3','#skF_1'('#skF_3','#skF_4',C_329),'#skF_4')
      | ~ r2_hidden(C_329,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_329,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_870])).

tff(c_824,plain,(
    ! [A_316,B_317,C_318] :
      ( ~ v2_struct_0('#skF_1'(A_316,B_317,C_318))
      | ~ r2_hidden(C_318,k2_pre_topc(A_316,B_317))
      | ~ m1_subset_1(C_318,u1_struct_0(A_316))
      | ~ m1_subset_1(B_317,k1_zfmisc_1(u1_struct_0(A_316)))
      | ~ l1_pre_topc(A_316)
      | ~ v2_pre_topc(A_316)
      | v2_struct_0(A_316) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_826,plain,
    ( ~ v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_748,c_824])).

tff(c_832,plain,
    ( ~ v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_826])).

tff(c_833,plain,(
    ~ v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_832])).

tff(c_788,plain,(
    ! [A_305,B_306,C_307] :
      ( v4_orders_2('#skF_1'(A_305,B_306,C_307))
      | ~ r2_hidden(C_307,k2_pre_topc(A_305,B_306))
      | ~ m1_subset_1(C_307,u1_struct_0(A_305))
      | ~ m1_subset_1(B_306,k1_zfmisc_1(u1_struct_0(A_305)))
      | ~ l1_pre_topc(A_305)
      | ~ v2_pre_topc(A_305)
      | v2_struct_0(A_305) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_790,plain,
    ( v4_orders_2('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_748,c_788])).

tff(c_796,plain,
    ( v4_orders_2('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_790])).

tff(c_797,plain,(
    v4_orders_2('#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_796])).

tff(c_813,plain,(
    ! [A_313,B_314,C_315] :
      ( v7_waybel_0('#skF_1'(A_313,B_314,C_315))
      | ~ r2_hidden(C_315,k2_pre_topc(A_313,B_314))
      | ~ m1_subset_1(C_315,u1_struct_0(A_313))
      | ~ m1_subset_1(B_314,k1_zfmisc_1(u1_struct_0(A_313)))
      | ~ l1_pre_topc(A_313)
      | ~ v2_pre_topc(A_313)
      | v2_struct_0(A_313) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_815,plain,
    ( v7_waybel_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_748,c_813])).

tff(c_821,plain,
    ( v7_waybel_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_815])).

tff(c_822,plain,(
    v7_waybel_0('#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_821])).

tff(c_835,plain,(
    ! [A_319,B_320,C_321] :
      ( l1_waybel_0('#skF_1'(A_319,B_320,C_321),A_319)
      | ~ r2_hidden(C_321,k2_pre_topc(A_319,B_320))
      | ~ m1_subset_1(C_321,u1_struct_0(A_319))
      | ~ m1_subset_1(B_320,k1_zfmisc_1(u1_struct_0(A_319)))
      | ~ l1_pre_topc(A_319)
      | ~ v2_pre_topc(A_319)
      | v2_struct_0(A_319) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_837,plain,
    ( l1_waybel_0('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_748,c_835])).

tff(c_843,plain,
    ( l1_waybel_0('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_837])).

tff(c_844,plain,(
    l1_waybel_0('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_843])).

tff(c_857,plain,(
    ! [A_323,B_324,C_325] :
      ( r3_waybel_9(A_323,'#skF_1'(A_323,B_324,C_325),C_325)
      | ~ r2_hidden(C_325,k2_pre_topc(A_323,B_324))
      | ~ m1_subset_1(C_325,u1_struct_0(A_323))
      | ~ m1_subset_1(B_324,k1_zfmisc_1(u1_struct_0(A_323)))
      | ~ l1_pre_topc(A_323)
      | ~ v2_pre_topc(A_323)
      | v2_struct_0(A_323) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_859,plain,(
    ! [C_325] :
      ( r3_waybel_9('#skF_3','#skF_1'('#skF_3','#skF_4',C_325),C_325)
      | ~ r2_hidden(C_325,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_325,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_50,c_857])).

tff(c_862,plain,(
    ! [C_325] :
      ( r3_waybel_9('#skF_3','#skF_1'('#skF_3','#skF_4',C_325),C_325)
      | ~ r2_hidden(C_325,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_325,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_859])).

tff(c_863,plain,(
    ! [C_325] :
      ( r3_waybel_9('#skF_3','#skF_1'('#skF_3','#skF_4',C_325),C_325)
      | ~ r2_hidden(C_325,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_325,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_862])).

tff(c_900,plain,(
    ! [A_338,B_339,C_340] :
      ( m2_yellow_6('#skF_2'(A_338,B_339,C_340),A_338,B_339)
      | ~ r3_waybel_9(A_338,B_339,C_340)
      | ~ m1_subset_1(C_340,u1_struct_0(A_338))
      | ~ l1_waybel_0(B_339,A_338)
      | ~ v7_waybel_0(B_339)
      | ~ v4_orders_2(B_339)
      | v2_struct_0(B_339)
      | ~ l1_pre_topc(A_338)
      | ~ v2_pre_topc(A_338)
      | v2_struct_0(A_338) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_983,plain,(
    ! [A_356,B_357,C_358] :
      ( v4_orders_2('#skF_2'(A_356,B_357,C_358))
      | ~ l1_struct_0(A_356)
      | ~ r3_waybel_9(A_356,B_357,C_358)
      | ~ m1_subset_1(C_358,u1_struct_0(A_356))
      | ~ l1_waybel_0(B_357,A_356)
      | ~ v7_waybel_0(B_357)
      | ~ v4_orders_2(B_357)
      | v2_struct_0(B_357)
      | ~ l1_pre_topc(A_356)
      | ~ v2_pre_topc(A_356)
      | v2_struct_0(A_356) ) ),
    inference(resolution,[status(thm)],[c_900,c_14])).

tff(c_985,plain,(
    ! [B_357] :
      ( v4_orders_2('#skF_2'('#skF_3',B_357,'#skF_5'))
      | ~ l1_struct_0('#skF_3')
      | ~ r3_waybel_9('#skF_3',B_357,'#skF_5')
      | ~ l1_waybel_0(B_357,'#skF_3')
      | ~ v7_waybel_0(B_357)
      | ~ v4_orders_2(B_357)
      | v2_struct_0(B_357)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_48,c_983])).

tff(c_988,plain,(
    ! [B_357] :
      ( v4_orders_2('#skF_2'('#skF_3',B_357,'#skF_5'))
      | ~ l1_struct_0('#skF_3')
      | ~ r3_waybel_9('#skF_3',B_357,'#skF_5')
      | ~ l1_waybel_0(B_357,'#skF_3')
      | ~ v7_waybel_0(B_357)
      | ~ v4_orders_2(B_357)
      | v2_struct_0(B_357)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_985])).

tff(c_989,plain,(
    ! [B_357] :
      ( v4_orders_2('#skF_2'('#skF_3',B_357,'#skF_5'))
      | ~ l1_struct_0('#skF_3')
      | ~ r3_waybel_9('#skF_3',B_357,'#skF_5')
      | ~ l1_waybel_0(B_357,'#skF_3')
      | ~ v7_waybel_0(B_357)
      | ~ v4_orders_2(B_357)
      | v2_struct_0(B_357) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_988])).

tff(c_990,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_989])).

tff(c_994,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_990])).

tff(c_998,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_994])).

tff(c_1000,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_989])).

tff(c_999,plain,(
    ! [B_357] :
      ( v4_orders_2('#skF_2'('#skF_3',B_357,'#skF_5'))
      | ~ r3_waybel_9('#skF_3',B_357,'#skF_5')
      | ~ l1_waybel_0(B_357,'#skF_3')
      | ~ v7_waybel_0(B_357)
      | ~ v4_orders_2(B_357)
      | v2_struct_0(B_357) ) ),
    inference(splitRight,[status(thm)],[c_989])).

tff(c_1002,plain,(
    ! [A_361,B_362,C_363] :
      ( v7_waybel_0('#skF_2'(A_361,B_362,C_363))
      | ~ l1_struct_0(A_361)
      | ~ r3_waybel_9(A_361,B_362,C_363)
      | ~ m1_subset_1(C_363,u1_struct_0(A_361))
      | ~ l1_waybel_0(B_362,A_361)
      | ~ v7_waybel_0(B_362)
      | ~ v4_orders_2(B_362)
      | v2_struct_0(B_362)
      | ~ l1_pre_topc(A_361)
      | ~ v2_pre_topc(A_361)
      | v2_struct_0(A_361) ) ),
    inference(resolution,[status(thm)],[c_900,c_12])).

tff(c_1004,plain,(
    ! [B_362] :
      ( v7_waybel_0('#skF_2'('#skF_3',B_362,'#skF_5'))
      | ~ l1_struct_0('#skF_3')
      | ~ r3_waybel_9('#skF_3',B_362,'#skF_5')
      | ~ l1_waybel_0(B_362,'#skF_3')
      | ~ v7_waybel_0(B_362)
      | ~ v4_orders_2(B_362)
      | v2_struct_0(B_362)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_48,c_1002])).

tff(c_1007,plain,(
    ! [B_362] :
      ( v7_waybel_0('#skF_2'('#skF_3',B_362,'#skF_5'))
      | ~ r3_waybel_9('#skF_3',B_362,'#skF_5')
      | ~ l1_waybel_0(B_362,'#skF_3')
      | ~ v7_waybel_0(B_362)
      | ~ v4_orders_2(B_362)
      | v2_struct_0(B_362)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_1000,c_1004])).

tff(c_1008,plain,(
    ! [B_362] :
      ( v7_waybel_0('#skF_2'('#skF_3',B_362,'#skF_5'))
      | ~ r3_waybel_9('#skF_3',B_362,'#skF_5')
      | ~ l1_waybel_0(B_362,'#skF_3')
      | ~ v7_waybel_0(B_362)
      | ~ v4_orders_2(B_362)
      | v2_struct_0(B_362) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1007])).

tff(c_1032,plain,(
    ! [A_377,B_378,C_379] :
      ( l1_waybel_0('#skF_2'(A_377,B_378,C_379),A_377)
      | ~ l1_struct_0(A_377)
      | ~ r3_waybel_9(A_377,B_378,C_379)
      | ~ m1_subset_1(C_379,u1_struct_0(A_377))
      | ~ l1_waybel_0(B_378,A_377)
      | ~ v7_waybel_0(B_378)
      | ~ v4_orders_2(B_378)
      | v2_struct_0(B_378)
      | ~ l1_pre_topc(A_377)
      | ~ v2_pre_topc(A_377)
      | v2_struct_0(A_377) ) ),
    inference(resolution,[status(thm)],[c_900,c_10])).

tff(c_1034,plain,(
    ! [B_378] :
      ( l1_waybel_0('#skF_2'('#skF_3',B_378,'#skF_5'),'#skF_3')
      | ~ l1_struct_0('#skF_3')
      | ~ r3_waybel_9('#skF_3',B_378,'#skF_5')
      | ~ l1_waybel_0(B_378,'#skF_3')
      | ~ v7_waybel_0(B_378)
      | ~ v4_orders_2(B_378)
      | v2_struct_0(B_378)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_48,c_1032])).

tff(c_1037,plain,(
    ! [B_378] :
      ( l1_waybel_0('#skF_2'('#skF_3',B_378,'#skF_5'),'#skF_3')
      | ~ r3_waybel_9('#skF_3',B_378,'#skF_5')
      | ~ l1_waybel_0(B_378,'#skF_3')
      | ~ v7_waybel_0(B_378)
      | ~ v4_orders_2(B_378)
      | v2_struct_0(B_378)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_1000,c_1034])).

tff(c_1038,plain,(
    ! [B_378] :
      ( l1_waybel_0('#skF_2'('#skF_3',B_378,'#skF_5'),'#skF_3')
      | ~ r3_waybel_9('#skF_3',B_378,'#skF_5')
      | ~ l1_waybel_0(B_378,'#skF_3')
      | ~ v7_waybel_0(B_378)
      | ~ v4_orders_2(B_378)
      | v2_struct_0(B_378) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1037])).

tff(c_1061,plain,(
    ! [A_387,B_388,C_389,B_390] :
      ( r1_waybel_0(A_387,'#skF_2'(A_387,B_388,C_389),B_390)
      | ~ r1_waybel_0(A_387,B_388,B_390)
      | ~ l1_struct_0(A_387)
      | ~ r3_waybel_9(A_387,B_388,C_389)
      | ~ m1_subset_1(C_389,u1_struct_0(A_387))
      | ~ l1_waybel_0(B_388,A_387)
      | ~ v7_waybel_0(B_388)
      | ~ v4_orders_2(B_388)
      | v2_struct_0(B_388)
      | ~ l1_pre_topc(A_387)
      | ~ v2_pre_topc(A_387)
      | v2_struct_0(A_387) ) ),
    inference(resolution,[status(thm)],[c_900,c_22])).

tff(c_955,plain,(
    ! [C_352,A_353,B_354] :
      ( r2_hidden(C_352,k10_yellow_6(A_353,'#skF_2'(A_353,B_354,C_352)))
      | ~ r3_waybel_9(A_353,B_354,C_352)
      | ~ m1_subset_1(C_352,u1_struct_0(A_353))
      | ~ l1_waybel_0(B_354,A_353)
      | ~ v7_waybel_0(B_354)
      | ~ v4_orders_2(B_354)
      | v2_struct_0(B_354)
      | ~ l1_pre_topc(A_353)
      | ~ v2_pre_topc(A_353)
      | v2_struct_0(A_353) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_749,plain,(
    ~ r1_waybel_0('#skF_3','#skF_6','#skF_4') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_66,plain,(
    ! [D_85] :
      ( ~ r2_hidden('#skF_5',k10_yellow_6('#skF_3',D_85))
      | ~ r1_waybel_0('#skF_3',D_85,'#skF_4')
      | ~ l1_waybel_0(D_85,'#skF_3')
      | ~ v3_yellow_6(D_85,'#skF_3')
      | ~ v7_waybel_0(D_85)
      | ~ v4_orders_2(D_85)
      | v2_struct_0(D_85)
      | r1_waybel_0('#skF_3','#skF_6','#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_799,plain,(
    ! [D_85] :
      ( ~ r2_hidden('#skF_5',k10_yellow_6('#skF_3',D_85))
      | ~ r1_waybel_0('#skF_3',D_85,'#skF_4')
      | ~ l1_waybel_0(D_85,'#skF_3')
      | ~ v3_yellow_6(D_85,'#skF_3')
      | ~ v7_waybel_0(D_85)
      | ~ v4_orders_2(D_85)
      | v2_struct_0(D_85) ) ),
    inference(negUnitSimplification,[status(thm)],[c_749,c_66])).

tff(c_962,plain,(
    ! [B_354] :
      ( ~ r1_waybel_0('#skF_3','#skF_2'('#skF_3',B_354,'#skF_5'),'#skF_4')
      | ~ l1_waybel_0('#skF_2'('#skF_3',B_354,'#skF_5'),'#skF_3')
      | ~ v3_yellow_6('#skF_2'('#skF_3',B_354,'#skF_5'),'#skF_3')
      | ~ v7_waybel_0('#skF_2'('#skF_3',B_354,'#skF_5'))
      | ~ v4_orders_2('#skF_2'('#skF_3',B_354,'#skF_5'))
      | v2_struct_0('#skF_2'('#skF_3',B_354,'#skF_5'))
      | ~ r3_waybel_9('#skF_3',B_354,'#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
      | ~ l1_waybel_0(B_354,'#skF_3')
      | ~ v7_waybel_0(B_354)
      | ~ v4_orders_2(B_354)
      | v2_struct_0(B_354)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_955,c_799])).

tff(c_972,plain,(
    ! [B_354] :
      ( ~ r1_waybel_0('#skF_3','#skF_2'('#skF_3',B_354,'#skF_5'),'#skF_4')
      | ~ l1_waybel_0('#skF_2'('#skF_3',B_354,'#skF_5'),'#skF_3')
      | ~ v3_yellow_6('#skF_2'('#skF_3',B_354,'#skF_5'),'#skF_3')
      | ~ v7_waybel_0('#skF_2'('#skF_3',B_354,'#skF_5'))
      | ~ v4_orders_2('#skF_2'('#skF_3',B_354,'#skF_5'))
      | v2_struct_0('#skF_2'('#skF_3',B_354,'#skF_5'))
      | ~ r3_waybel_9('#skF_3',B_354,'#skF_5')
      | ~ l1_waybel_0(B_354,'#skF_3')
      | ~ v7_waybel_0(B_354)
      | ~ v4_orders_2(B_354)
      | v2_struct_0(B_354)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_962])).

tff(c_973,plain,(
    ! [B_354] :
      ( ~ r1_waybel_0('#skF_3','#skF_2'('#skF_3',B_354,'#skF_5'),'#skF_4')
      | ~ l1_waybel_0('#skF_2'('#skF_3',B_354,'#skF_5'),'#skF_3')
      | ~ v3_yellow_6('#skF_2'('#skF_3',B_354,'#skF_5'),'#skF_3')
      | ~ v7_waybel_0('#skF_2'('#skF_3',B_354,'#skF_5'))
      | ~ v4_orders_2('#skF_2'('#skF_3',B_354,'#skF_5'))
      | v2_struct_0('#skF_2'('#skF_3',B_354,'#skF_5'))
      | ~ r3_waybel_9('#skF_3',B_354,'#skF_5')
      | ~ l1_waybel_0(B_354,'#skF_3')
      | ~ v7_waybel_0(B_354)
      | ~ v4_orders_2(B_354)
      | v2_struct_0(B_354) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_972])).

tff(c_1065,plain,(
    ! [B_388] :
      ( ~ l1_waybel_0('#skF_2'('#skF_3',B_388,'#skF_5'),'#skF_3')
      | ~ v3_yellow_6('#skF_2'('#skF_3',B_388,'#skF_5'),'#skF_3')
      | ~ v7_waybel_0('#skF_2'('#skF_3',B_388,'#skF_5'))
      | ~ v4_orders_2('#skF_2'('#skF_3',B_388,'#skF_5'))
      | v2_struct_0('#skF_2'('#skF_3',B_388,'#skF_5'))
      | ~ r1_waybel_0('#skF_3',B_388,'#skF_4')
      | ~ l1_struct_0('#skF_3')
      | ~ r3_waybel_9('#skF_3',B_388,'#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
      | ~ l1_waybel_0(B_388,'#skF_3')
      | ~ v7_waybel_0(B_388)
      | ~ v4_orders_2(B_388)
      | v2_struct_0(B_388)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1061,c_973])).

tff(c_1068,plain,(
    ! [B_388] :
      ( ~ l1_waybel_0('#skF_2'('#skF_3',B_388,'#skF_5'),'#skF_3')
      | ~ v3_yellow_6('#skF_2'('#skF_3',B_388,'#skF_5'),'#skF_3')
      | ~ v7_waybel_0('#skF_2'('#skF_3',B_388,'#skF_5'))
      | ~ v4_orders_2('#skF_2'('#skF_3',B_388,'#skF_5'))
      | v2_struct_0('#skF_2'('#skF_3',B_388,'#skF_5'))
      | ~ r1_waybel_0('#skF_3',B_388,'#skF_4')
      | ~ r3_waybel_9('#skF_3',B_388,'#skF_5')
      | ~ l1_waybel_0(B_388,'#skF_3')
      | ~ v7_waybel_0(B_388)
      | ~ v4_orders_2(B_388)
      | v2_struct_0(B_388)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_1000,c_1065])).

tff(c_1074,plain,(
    ! [B_394] :
      ( ~ l1_waybel_0('#skF_2'('#skF_3',B_394,'#skF_5'),'#skF_3')
      | ~ v3_yellow_6('#skF_2'('#skF_3',B_394,'#skF_5'),'#skF_3')
      | ~ v7_waybel_0('#skF_2'('#skF_3',B_394,'#skF_5'))
      | ~ v4_orders_2('#skF_2'('#skF_3',B_394,'#skF_5'))
      | v2_struct_0('#skF_2'('#skF_3',B_394,'#skF_5'))
      | ~ r1_waybel_0('#skF_3',B_394,'#skF_4')
      | ~ r3_waybel_9('#skF_3',B_394,'#skF_5')
      | ~ l1_waybel_0(B_394,'#skF_3')
      | ~ v7_waybel_0(B_394)
      | ~ v4_orders_2(B_394)
      | v2_struct_0(B_394) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1068])).

tff(c_1077,plain,(
    ! [B_394] :
      ( ~ r1_waybel_0('#skF_3',B_394,'#skF_4')
      | ~ r3_waybel_9('#skF_3',B_394,'#skF_5')
      | ~ l1_waybel_0(B_394,'#skF_3')
      | ~ v7_waybel_0(B_394)
      | ~ v4_orders_2(B_394)
      | v2_struct_0(B_394)
      | k10_yellow_6('#skF_3','#skF_2'('#skF_3',B_394,'#skF_5')) = k1_xboole_0
      | ~ l1_waybel_0('#skF_2'('#skF_3',B_394,'#skF_5'),'#skF_3')
      | ~ v7_waybel_0('#skF_2'('#skF_3',B_394,'#skF_5'))
      | ~ v4_orders_2('#skF_2'('#skF_3',B_394,'#skF_5'))
      | v2_struct_0('#skF_2'('#skF_3',B_394,'#skF_5'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_2,c_1074])).

tff(c_1080,plain,(
    ! [B_394] :
      ( ~ r1_waybel_0('#skF_3',B_394,'#skF_4')
      | ~ r3_waybel_9('#skF_3',B_394,'#skF_5')
      | ~ l1_waybel_0(B_394,'#skF_3')
      | ~ v7_waybel_0(B_394)
      | ~ v4_orders_2(B_394)
      | v2_struct_0(B_394)
      | k10_yellow_6('#skF_3','#skF_2'('#skF_3',B_394,'#skF_5')) = k1_xboole_0
      | ~ l1_waybel_0('#skF_2'('#skF_3',B_394,'#skF_5'),'#skF_3')
      | ~ v7_waybel_0('#skF_2'('#skF_3',B_394,'#skF_5'))
      | ~ v4_orders_2('#skF_2'('#skF_3',B_394,'#skF_5'))
      | v2_struct_0('#skF_2'('#skF_3',B_394,'#skF_5'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_1077])).

tff(c_1082,plain,(
    ! [B_395] :
      ( ~ r1_waybel_0('#skF_3',B_395,'#skF_4')
      | ~ r3_waybel_9('#skF_3',B_395,'#skF_5')
      | ~ l1_waybel_0(B_395,'#skF_3')
      | ~ v7_waybel_0(B_395)
      | ~ v4_orders_2(B_395)
      | v2_struct_0(B_395)
      | k10_yellow_6('#skF_3','#skF_2'('#skF_3',B_395,'#skF_5')) = k1_xboole_0
      | ~ l1_waybel_0('#skF_2'('#skF_3',B_395,'#skF_5'),'#skF_3')
      | ~ v7_waybel_0('#skF_2'('#skF_3',B_395,'#skF_5'))
      | ~ v4_orders_2('#skF_2'('#skF_3',B_395,'#skF_5'))
      | v2_struct_0('#skF_2'('#skF_3',B_395,'#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1080])).

tff(c_1087,plain,(
    ! [B_396] :
      ( ~ r1_waybel_0('#skF_3',B_396,'#skF_4')
      | k10_yellow_6('#skF_3','#skF_2'('#skF_3',B_396,'#skF_5')) = k1_xboole_0
      | ~ v7_waybel_0('#skF_2'('#skF_3',B_396,'#skF_5'))
      | ~ v4_orders_2('#skF_2'('#skF_3',B_396,'#skF_5'))
      | v2_struct_0('#skF_2'('#skF_3',B_396,'#skF_5'))
      | ~ r3_waybel_9('#skF_3',B_396,'#skF_5')
      | ~ l1_waybel_0(B_396,'#skF_3')
      | ~ v7_waybel_0(B_396)
      | ~ v4_orders_2(B_396)
      | v2_struct_0(B_396) ) ),
    inference(resolution,[status(thm)],[c_1038,c_1082])).

tff(c_1098,plain,(
    ! [B_399] :
      ( ~ r1_waybel_0('#skF_3',B_399,'#skF_4')
      | k10_yellow_6('#skF_3','#skF_2'('#skF_3',B_399,'#skF_5')) = k1_xboole_0
      | ~ v4_orders_2('#skF_2'('#skF_3',B_399,'#skF_5'))
      | v2_struct_0('#skF_2'('#skF_3',B_399,'#skF_5'))
      | ~ r3_waybel_9('#skF_3',B_399,'#skF_5')
      | ~ l1_waybel_0(B_399,'#skF_3')
      | ~ v7_waybel_0(B_399)
      | ~ v4_orders_2(B_399)
      | v2_struct_0(B_399) ) ),
    inference(resolution,[status(thm)],[c_1008,c_1087])).

tff(c_1103,plain,(
    ! [B_400] :
      ( ~ r1_waybel_0('#skF_3',B_400,'#skF_4')
      | k10_yellow_6('#skF_3','#skF_2'('#skF_3',B_400,'#skF_5')) = k1_xboole_0
      | v2_struct_0('#skF_2'('#skF_3',B_400,'#skF_5'))
      | ~ r3_waybel_9('#skF_3',B_400,'#skF_5')
      | ~ l1_waybel_0(B_400,'#skF_3')
      | ~ v7_waybel_0(B_400)
      | ~ v4_orders_2(B_400)
      | v2_struct_0(B_400) ) ),
    inference(resolution,[status(thm)],[c_999,c_1098])).

tff(c_917,plain,(
    ! [A_338,B_339,C_340] :
      ( ~ v2_struct_0('#skF_2'(A_338,B_339,C_340))
      | ~ l1_struct_0(A_338)
      | ~ r3_waybel_9(A_338,B_339,C_340)
      | ~ m1_subset_1(C_340,u1_struct_0(A_338))
      | ~ l1_waybel_0(B_339,A_338)
      | ~ v7_waybel_0(B_339)
      | ~ v4_orders_2(B_339)
      | v2_struct_0(B_339)
      | ~ l1_pre_topc(A_338)
      | ~ v2_pre_topc(A_338)
      | v2_struct_0(A_338) ) ),
    inference(resolution,[status(thm)],[c_900,c_16])).

tff(c_1105,plain,(
    ! [B_400] :
      ( ~ l1_struct_0('#skF_3')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r1_waybel_0('#skF_3',B_400,'#skF_4')
      | k10_yellow_6('#skF_3','#skF_2'('#skF_3',B_400,'#skF_5')) = k1_xboole_0
      | ~ r3_waybel_9('#skF_3',B_400,'#skF_5')
      | ~ l1_waybel_0(B_400,'#skF_3')
      | ~ v7_waybel_0(B_400)
      | ~ v4_orders_2(B_400)
      | v2_struct_0(B_400) ) ),
    inference(resolution,[status(thm)],[c_1103,c_917])).

tff(c_1108,plain,(
    ! [B_400] :
      ( v2_struct_0('#skF_3')
      | ~ r1_waybel_0('#skF_3',B_400,'#skF_4')
      | k10_yellow_6('#skF_3','#skF_2'('#skF_3',B_400,'#skF_5')) = k1_xboole_0
      | ~ r3_waybel_9('#skF_3',B_400,'#skF_5')
      | ~ l1_waybel_0(B_400,'#skF_3')
      | ~ v7_waybel_0(B_400)
      | ~ v4_orders_2(B_400)
      | v2_struct_0(B_400) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_1000,c_1105])).

tff(c_1110,plain,(
    ! [B_401] :
      ( ~ r1_waybel_0('#skF_3',B_401,'#skF_4')
      | k10_yellow_6('#skF_3','#skF_2'('#skF_3',B_401,'#skF_5')) = k1_xboole_0
      | ~ r3_waybel_9('#skF_3',B_401,'#skF_5')
      | ~ l1_waybel_0(B_401,'#skF_3')
      | ~ v7_waybel_0(B_401)
      | ~ v4_orders_2(B_401)
      | v2_struct_0(B_401) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1108])).

tff(c_975,plain,(
    ! [A_353,B_354,C_352] :
      ( ~ v1_xboole_0(k10_yellow_6(A_353,'#skF_2'(A_353,B_354,C_352)))
      | ~ r3_waybel_9(A_353,B_354,C_352)
      | ~ m1_subset_1(C_352,u1_struct_0(A_353))
      | ~ l1_waybel_0(B_354,A_353)
      | ~ v7_waybel_0(B_354)
      | ~ v4_orders_2(B_354)
      | v2_struct_0(B_354)
      | ~ l1_pre_topc(A_353)
      | ~ v2_pre_topc(A_353)
      | v2_struct_0(A_353) ) ),
    inference(resolution,[status(thm)],[c_955,c_46])).

tff(c_1122,plain,(
    ! [B_401] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r3_waybel_9('#skF_3',B_401,'#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
      | ~ l1_waybel_0(B_401,'#skF_3')
      | ~ v7_waybel_0(B_401)
      | ~ v4_orders_2(B_401)
      | v2_struct_0(B_401)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r1_waybel_0('#skF_3',B_401,'#skF_4')
      | ~ r3_waybel_9('#skF_3',B_401,'#skF_5')
      | ~ l1_waybel_0(B_401,'#skF_3')
      | ~ v7_waybel_0(B_401)
      | ~ v4_orders_2(B_401)
      | v2_struct_0(B_401) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1110,c_975])).

tff(c_1146,plain,(
    ! [B_401] :
      ( v2_struct_0('#skF_3')
      | ~ r1_waybel_0('#skF_3',B_401,'#skF_4')
      | ~ r3_waybel_9('#skF_3',B_401,'#skF_5')
      | ~ l1_waybel_0(B_401,'#skF_3')
      | ~ v7_waybel_0(B_401)
      | ~ v4_orders_2(B_401)
      | v2_struct_0(B_401) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_89,c_1122])).

tff(c_1155,plain,(
    ! [B_402] :
      ( ~ r1_waybel_0('#skF_3',B_402,'#skF_4')
      | ~ r3_waybel_9('#skF_3',B_402,'#skF_5')
      | ~ l1_waybel_0(B_402,'#skF_3')
      | ~ v7_waybel_0(B_402)
      | ~ v4_orders_2(B_402)
      | v2_struct_0(B_402) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1146])).

tff(c_1166,plain,
    ( ~ r1_waybel_0('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | ~ l1_waybel_0('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | ~ v7_waybel_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ v4_orders_2('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ r2_hidden('#skF_5',k2_pre_topc('#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_863,c_1155])).

tff(c_1177,plain,
    ( ~ r1_waybel_0('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_748,c_797,c_822,c_844,c_1166])).

tff(c_1178,plain,(
    ~ r1_waybel_0('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_833,c_1177])).

tff(c_1181,plain,
    ( ~ r2_hidden('#skF_5',k2_pre_topc('#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_871,c_1178])).

tff(c_1185,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_748,c_1181])).

tff(c_1186,plain,(
    r2_hidden('#skF_5',k2_pre_topc('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_1272,plain,(
    ! [A_437,B_438,C_439] :
      ( r1_waybel_0(A_437,'#skF_1'(A_437,B_438,C_439),B_438)
      | ~ r2_hidden(C_439,k2_pre_topc(A_437,B_438))
      | ~ m1_subset_1(C_439,u1_struct_0(A_437))
      | ~ m1_subset_1(B_438,k1_zfmisc_1(u1_struct_0(A_437)))
      | ~ l1_pre_topc(A_437)
      | ~ v2_pre_topc(A_437)
      | v2_struct_0(A_437) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_1274,plain,(
    ! [C_439] :
      ( r1_waybel_0('#skF_3','#skF_1'('#skF_3','#skF_4',C_439),'#skF_4')
      | ~ r2_hidden(C_439,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_439,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_50,c_1272])).

tff(c_1277,plain,(
    ! [C_439] :
      ( r1_waybel_0('#skF_3','#skF_1'('#skF_3','#skF_4',C_439),'#skF_4')
      | ~ r2_hidden(C_439,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_439,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_1274])).

tff(c_1278,plain,(
    ! [C_439] :
      ( r1_waybel_0('#skF_3','#skF_1'('#skF_3','#skF_4',C_439),'#skF_4')
      | ~ r2_hidden(C_439,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_439,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1277])).

tff(c_1224,plain,(
    ! [A_420,B_421,C_422] :
      ( ~ v2_struct_0('#skF_1'(A_420,B_421,C_422))
      | ~ r2_hidden(C_422,k2_pre_topc(A_420,B_421))
      | ~ m1_subset_1(C_422,u1_struct_0(A_420))
      | ~ m1_subset_1(B_421,k1_zfmisc_1(u1_struct_0(A_420)))
      | ~ l1_pre_topc(A_420)
      | ~ v2_pre_topc(A_420)
      | v2_struct_0(A_420) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_1226,plain,
    ( ~ v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1186,c_1224])).

tff(c_1232,plain,
    ( ~ v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_1226])).

tff(c_1233,plain,(
    ~ v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1232])).

tff(c_1235,plain,(
    ! [A_423,B_424,C_425] :
      ( v4_orders_2('#skF_1'(A_423,B_424,C_425))
      | ~ r2_hidden(C_425,k2_pre_topc(A_423,B_424))
      | ~ m1_subset_1(C_425,u1_struct_0(A_423))
      | ~ m1_subset_1(B_424,k1_zfmisc_1(u1_struct_0(A_423)))
      | ~ l1_pre_topc(A_423)
      | ~ v2_pre_topc(A_423)
      | v2_struct_0(A_423) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_1237,plain,
    ( v4_orders_2('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1186,c_1235])).

tff(c_1243,plain,
    ( v4_orders_2('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_1237])).

tff(c_1244,plain,(
    v4_orders_2('#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1243])).

tff(c_1247,plain,(
    ! [A_430,B_431,C_432] :
      ( v7_waybel_0('#skF_1'(A_430,B_431,C_432))
      | ~ r2_hidden(C_432,k2_pre_topc(A_430,B_431))
      | ~ m1_subset_1(C_432,u1_struct_0(A_430))
      | ~ m1_subset_1(B_431,k1_zfmisc_1(u1_struct_0(A_430)))
      | ~ l1_pre_topc(A_430)
      | ~ v2_pre_topc(A_430)
      | v2_struct_0(A_430) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_1249,plain,
    ( v7_waybel_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1186,c_1247])).

tff(c_1255,plain,
    ( v7_waybel_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_1249])).

tff(c_1256,plain,(
    v7_waybel_0('#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1255])).

tff(c_1261,plain,(
    ! [A_434,B_435,C_436] :
      ( l1_waybel_0('#skF_1'(A_434,B_435,C_436),A_434)
      | ~ r2_hidden(C_436,k2_pre_topc(A_434,B_435))
      | ~ m1_subset_1(C_436,u1_struct_0(A_434))
      | ~ m1_subset_1(B_435,k1_zfmisc_1(u1_struct_0(A_434)))
      | ~ l1_pre_topc(A_434)
      | ~ v2_pre_topc(A_434)
      | v2_struct_0(A_434) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_1263,plain,
    ( l1_waybel_0('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1186,c_1261])).

tff(c_1269,plain,
    ( l1_waybel_0('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_1263])).

tff(c_1270,plain,(
    l1_waybel_0('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1269])).

tff(c_1280,plain,(
    ! [A_441,B_442,C_443] :
      ( r3_waybel_9(A_441,'#skF_1'(A_441,B_442,C_443),C_443)
      | ~ r2_hidden(C_443,k2_pre_topc(A_441,B_442))
      | ~ m1_subset_1(C_443,u1_struct_0(A_441))
      | ~ m1_subset_1(B_442,k1_zfmisc_1(u1_struct_0(A_441)))
      | ~ l1_pre_topc(A_441)
      | ~ v2_pre_topc(A_441)
      | v2_struct_0(A_441) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_1282,plain,(
    ! [C_443] :
      ( r3_waybel_9('#skF_3','#skF_1'('#skF_3','#skF_4',C_443),C_443)
      | ~ r2_hidden(C_443,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_443,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_50,c_1280])).

tff(c_1285,plain,(
    ! [C_443] :
      ( r3_waybel_9('#skF_3','#skF_1'('#skF_3','#skF_4',C_443),C_443)
      | ~ r2_hidden(C_443,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_443,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_1282])).

tff(c_1286,plain,(
    ! [C_443] :
      ( r3_waybel_9('#skF_3','#skF_1'('#skF_3','#skF_4',C_443),C_443)
      | ~ r2_hidden(C_443,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_443,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1285])).

tff(c_1329,plain,(
    ! [A_459,B_460,C_461] :
      ( m2_yellow_6('#skF_2'(A_459,B_460,C_461),A_459,B_460)
      | ~ r3_waybel_9(A_459,B_460,C_461)
      | ~ m1_subset_1(C_461,u1_struct_0(A_459))
      | ~ l1_waybel_0(B_460,A_459)
      | ~ v7_waybel_0(B_460)
      | ~ v4_orders_2(B_460)
      | v2_struct_0(B_460)
      | ~ l1_pre_topc(A_459)
      | ~ v2_pre_topc(A_459)
      | v2_struct_0(A_459) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_1393,plain,(
    ! [A_476,B_477,C_478] :
      ( v7_waybel_0('#skF_2'(A_476,B_477,C_478))
      | ~ l1_struct_0(A_476)
      | ~ r3_waybel_9(A_476,B_477,C_478)
      | ~ m1_subset_1(C_478,u1_struct_0(A_476))
      | ~ l1_waybel_0(B_477,A_476)
      | ~ v7_waybel_0(B_477)
      | ~ v4_orders_2(B_477)
      | v2_struct_0(B_477)
      | ~ l1_pre_topc(A_476)
      | ~ v2_pre_topc(A_476)
      | v2_struct_0(A_476) ) ),
    inference(resolution,[status(thm)],[c_1329,c_12])).

tff(c_1395,plain,(
    ! [B_477] :
      ( v7_waybel_0('#skF_2'('#skF_3',B_477,'#skF_5'))
      | ~ l1_struct_0('#skF_3')
      | ~ r3_waybel_9('#skF_3',B_477,'#skF_5')
      | ~ l1_waybel_0(B_477,'#skF_3')
      | ~ v7_waybel_0(B_477)
      | ~ v4_orders_2(B_477)
      | v2_struct_0(B_477)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_48,c_1393])).

tff(c_1398,plain,(
    ! [B_477] :
      ( v7_waybel_0('#skF_2'('#skF_3',B_477,'#skF_5'))
      | ~ l1_struct_0('#skF_3')
      | ~ r3_waybel_9('#skF_3',B_477,'#skF_5')
      | ~ l1_waybel_0(B_477,'#skF_3')
      | ~ v7_waybel_0(B_477)
      | ~ v4_orders_2(B_477)
      | v2_struct_0(B_477)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_1395])).

tff(c_1399,plain,(
    ! [B_477] :
      ( v7_waybel_0('#skF_2'('#skF_3',B_477,'#skF_5'))
      | ~ l1_struct_0('#skF_3')
      | ~ r3_waybel_9('#skF_3',B_477,'#skF_5')
      | ~ l1_waybel_0(B_477,'#skF_3')
      | ~ v7_waybel_0(B_477)
      | ~ v4_orders_2(B_477)
      | v2_struct_0(B_477) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1398])).

tff(c_1400,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1399])).

tff(c_1403,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_1400])).

tff(c_1407,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1403])).

tff(c_1409,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1399])).

tff(c_1418,plain,(
    ! [A_484,B_485,C_486] :
      ( v4_orders_2('#skF_2'(A_484,B_485,C_486))
      | ~ l1_struct_0(A_484)
      | ~ r3_waybel_9(A_484,B_485,C_486)
      | ~ m1_subset_1(C_486,u1_struct_0(A_484))
      | ~ l1_waybel_0(B_485,A_484)
      | ~ v7_waybel_0(B_485)
      | ~ v4_orders_2(B_485)
      | v2_struct_0(B_485)
      | ~ l1_pre_topc(A_484)
      | ~ v2_pre_topc(A_484)
      | v2_struct_0(A_484) ) ),
    inference(resolution,[status(thm)],[c_1329,c_14])).

tff(c_1420,plain,(
    ! [B_485] :
      ( v4_orders_2('#skF_2'('#skF_3',B_485,'#skF_5'))
      | ~ l1_struct_0('#skF_3')
      | ~ r3_waybel_9('#skF_3',B_485,'#skF_5')
      | ~ l1_waybel_0(B_485,'#skF_3')
      | ~ v7_waybel_0(B_485)
      | ~ v4_orders_2(B_485)
      | v2_struct_0(B_485)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_48,c_1418])).

tff(c_1423,plain,(
    ! [B_485] :
      ( v4_orders_2('#skF_2'('#skF_3',B_485,'#skF_5'))
      | ~ r3_waybel_9('#skF_3',B_485,'#skF_5')
      | ~ l1_waybel_0(B_485,'#skF_3')
      | ~ v7_waybel_0(B_485)
      | ~ v4_orders_2(B_485)
      | v2_struct_0(B_485)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_1409,c_1420])).

tff(c_1424,plain,(
    ! [B_485] :
      ( v4_orders_2('#skF_2'('#skF_3',B_485,'#skF_5'))
      | ~ r3_waybel_9('#skF_3',B_485,'#skF_5')
      | ~ l1_waybel_0(B_485,'#skF_3')
      | ~ v7_waybel_0(B_485)
      | ~ v4_orders_2(B_485)
      | v2_struct_0(B_485) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1423])).

tff(c_1408,plain,(
    ! [B_477] :
      ( v7_waybel_0('#skF_2'('#skF_3',B_477,'#skF_5'))
      | ~ r3_waybel_9('#skF_3',B_477,'#skF_5')
      | ~ l1_waybel_0(B_477,'#skF_3')
      | ~ v7_waybel_0(B_477)
      | ~ v4_orders_2(B_477)
      | v2_struct_0(B_477) ) ),
    inference(splitRight,[status(thm)],[c_1399])).

tff(c_1435,plain,(
    ! [A_491,B_492,C_493] :
      ( l1_waybel_0('#skF_2'(A_491,B_492,C_493),A_491)
      | ~ l1_struct_0(A_491)
      | ~ r3_waybel_9(A_491,B_492,C_493)
      | ~ m1_subset_1(C_493,u1_struct_0(A_491))
      | ~ l1_waybel_0(B_492,A_491)
      | ~ v7_waybel_0(B_492)
      | ~ v4_orders_2(B_492)
      | v2_struct_0(B_492)
      | ~ l1_pre_topc(A_491)
      | ~ v2_pre_topc(A_491)
      | v2_struct_0(A_491) ) ),
    inference(resolution,[status(thm)],[c_1329,c_10])).

tff(c_1437,plain,(
    ! [B_492] :
      ( l1_waybel_0('#skF_2'('#skF_3',B_492,'#skF_5'),'#skF_3')
      | ~ l1_struct_0('#skF_3')
      | ~ r3_waybel_9('#skF_3',B_492,'#skF_5')
      | ~ l1_waybel_0(B_492,'#skF_3')
      | ~ v7_waybel_0(B_492)
      | ~ v4_orders_2(B_492)
      | v2_struct_0(B_492)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_48,c_1435])).

tff(c_1440,plain,(
    ! [B_492] :
      ( l1_waybel_0('#skF_2'('#skF_3',B_492,'#skF_5'),'#skF_3')
      | ~ r3_waybel_9('#skF_3',B_492,'#skF_5')
      | ~ l1_waybel_0(B_492,'#skF_3')
      | ~ v7_waybel_0(B_492)
      | ~ v4_orders_2(B_492)
      | v2_struct_0(B_492)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_1409,c_1437])).

tff(c_1441,plain,(
    ! [B_492] :
      ( l1_waybel_0('#skF_2'('#skF_3',B_492,'#skF_5'),'#skF_3')
      | ~ r3_waybel_9('#skF_3',B_492,'#skF_5')
      | ~ l1_waybel_0(B_492,'#skF_3')
      | ~ v7_waybel_0(B_492)
      | ~ v4_orders_2(B_492)
      | v2_struct_0(B_492) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1440])).

tff(c_1344,plain,(
    ! [A_459,B_460,C_461,B_16] :
      ( r1_waybel_0(A_459,'#skF_2'(A_459,B_460,C_461),B_16)
      | ~ r1_waybel_0(A_459,B_460,B_16)
      | ~ l1_struct_0(A_459)
      | ~ r3_waybel_9(A_459,B_460,C_461)
      | ~ m1_subset_1(C_461,u1_struct_0(A_459))
      | ~ l1_waybel_0(B_460,A_459)
      | ~ v7_waybel_0(B_460)
      | ~ v4_orders_2(B_460)
      | v2_struct_0(B_460)
      | ~ l1_pre_topc(A_459)
      | ~ v2_pre_topc(A_459)
      | v2_struct_0(A_459) ) ),
    inference(resolution,[status(thm)],[c_1329,c_22])).

tff(c_1370,plain,(
    ! [C_467,A_468,B_469] :
      ( r2_hidden(C_467,k10_yellow_6(A_468,'#skF_2'(A_468,B_469,C_467)))
      | ~ r3_waybel_9(A_468,B_469,C_467)
      | ~ m1_subset_1(C_467,u1_struct_0(A_468))
      | ~ l1_waybel_0(B_469,A_468)
      | ~ v7_waybel_0(B_469)
      | ~ v4_orders_2(B_469)
      | v2_struct_0(B_469)
      | ~ l1_pre_topc(A_468)
      | ~ v2_pre_topc(A_468)
      | v2_struct_0(A_468) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_1187,plain,(
    ~ l1_waybel_0('#skF_6','#skF_3') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_70,plain,(
    ! [D_85] :
      ( ~ r2_hidden('#skF_5',k10_yellow_6('#skF_3',D_85))
      | ~ r1_waybel_0('#skF_3',D_85,'#skF_4')
      | ~ l1_waybel_0(D_85,'#skF_3')
      | ~ v3_yellow_6(D_85,'#skF_3')
      | ~ v7_waybel_0(D_85)
      | ~ v4_orders_2(D_85)
      | v2_struct_0(D_85)
      | l1_waybel_0('#skF_6','#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_1217,plain,(
    ! [D_85] :
      ( ~ r2_hidden('#skF_5',k10_yellow_6('#skF_3',D_85))
      | ~ r1_waybel_0('#skF_3',D_85,'#skF_4')
      | ~ l1_waybel_0(D_85,'#skF_3')
      | ~ v3_yellow_6(D_85,'#skF_3')
      | ~ v7_waybel_0(D_85)
      | ~ v4_orders_2(D_85)
      | v2_struct_0(D_85) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1187,c_70])).

tff(c_1377,plain,(
    ! [B_469] :
      ( ~ r1_waybel_0('#skF_3','#skF_2'('#skF_3',B_469,'#skF_5'),'#skF_4')
      | ~ l1_waybel_0('#skF_2'('#skF_3',B_469,'#skF_5'),'#skF_3')
      | ~ v3_yellow_6('#skF_2'('#skF_3',B_469,'#skF_5'),'#skF_3')
      | ~ v7_waybel_0('#skF_2'('#skF_3',B_469,'#skF_5'))
      | ~ v4_orders_2('#skF_2'('#skF_3',B_469,'#skF_5'))
      | v2_struct_0('#skF_2'('#skF_3',B_469,'#skF_5'))
      | ~ r3_waybel_9('#skF_3',B_469,'#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
      | ~ l1_waybel_0(B_469,'#skF_3')
      | ~ v7_waybel_0(B_469)
      | ~ v4_orders_2(B_469)
      | v2_struct_0(B_469)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1370,c_1217])).

tff(c_1387,plain,(
    ! [B_469] :
      ( ~ r1_waybel_0('#skF_3','#skF_2'('#skF_3',B_469,'#skF_5'),'#skF_4')
      | ~ l1_waybel_0('#skF_2'('#skF_3',B_469,'#skF_5'),'#skF_3')
      | ~ v3_yellow_6('#skF_2'('#skF_3',B_469,'#skF_5'),'#skF_3')
      | ~ v7_waybel_0('#skF_2'('#skF_3',B_469,'#skF_5'))
      | ~ v4_orders_2('#skF_2'('#skF_3',B_469,'#skF_5'))
      | v2_struct_0('#skF_2'('#skF_3',B_469,'#skF_5'))
      | ~ r3_waybel_9('#skF_3',B_469,'#skF_5')
      | ~ l1_waybel_0(B_469,'#skF_3')
      | ~ v7_waybel_0(B_469)
      | ~ v4_orders_2(B_469)
      | v2_struct_0(B_469)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_1377])).

tff(c_1449,plain,(
    ! [B_502] :
      ( ~ r1_waybel_0('#skF_3','#skF_2'('#skF_3',B_502,'#skF_5'),'#skF_4')
      | ~ l1_waybel_0('#skF_2'('#skF_3',B_502,'#skF_5'),'#skF_3')
      | ~ v3_yellow_6('#skF_2'('#skF_3',B_502,'#skF_5'),'#skF_3')
      | ~ v7_waybel_0('#skF_2'('#skF_3',B_502,'#skF_5'))
      | ~ v4_orders_2('#skF_2'('#skF_3',B_502,'#skF_5'))
      | v2_struct_0('#skF_2'('#skF_3',B_502,'#skF_5'))
      | ~ r3_waybel_9('#skF_3',B_502,'#skF_5')
      | ~ l1_waybel_0(B_502,'#skF_3')
      | ~ v7_waybel_0(B_502)
      | ~ v4_orders_2(B_502)
      | v2_struct_0(B_502) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1387])).

tff(c_1453,plain,(
    ! [B_460] :
      ( ~ l1_waybel_0('#skF_2'('#skF_3',B_460,'#skF_5'),'#skF_3')
      | ~ v3_yellow_6('#skF_2'('#skF_3',B_460,'#skF_5'),'#skF_3')
      | ~ v7_waybel_0('#skF_2'('#skF_3',B_460,'#skF_5'))
      | ~ v4_orders_2('#skF_2'('#skF_3',B_460,'#skF_5'))
      | v2_struct_0('#skF_2'('#skF_3',B_460,'#skF_5'))
      | ~ r1_waybel_0('#skF_3',B_460,'#skF_4')
      | ~ l1_struct_0('#skF_3')
      | ~ r3_waybel_9('#skF_3',B_460,'#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
      | ~ l1_waybel_0(B_460,'#skF_3')
      | ~ v7_waybel_0(B_460)
      | ~ v4_orders_2(B_460)
      | v2_struct_0(B_460)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1344,c_1449])).

tff(c_1456,plain,(
    ! [B_460] :
      ( ~ l1_waybel_0('#skF_2'('#skF_3',B_460,'#skF_5'),'#skF_3')
      | ~ v3_yellow_6('#skF_2'('#skF_3',B_460,'#skF_5'),'#skF_3')
      | ~ v7_waybel_0('#skF_2'('#skF_3',B_460,'#skF_5'))
      | ~ v4_orders_2('#skF_2'('#skF_3',B_460,'#skF_5'))
      | v2_struct_0('#skF_2'('#skF_3',B_460,'#skF_5'))
      | ~ r1_waybel_0('#skF_3',B_460,'#skF_4')
      | ~ r3_waybel_9('#skF_3',B_460,'#skF_5')
      | ~ l1_waybel_0(B_460,'#skF_3')
      | ~ v7_waybel_0(B_460)
      | ~ v4_orders_2(B_460)
      | v2_struct_0(B_460)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_1409,c_1453])).

tff(c_1458,plain,(
    ! [B_503] :
      ( ~ l1_waybel_0('#skF_2'('#skF_3',B_503,'#skF_5'),'#skF_3')
      | ~ v3_yellow_6('#skF_2'('#skF_3',B_503,'#skF_5'),'#skF_3')
      | ~ v7_waybel_0('#skF_2'('#skF_3',B_503,'#skF_5'))
      | ~ v4_orders_2('#skF_2'('#skF_3',B_503,'#skF_5'))
      | v2_struct_0('#skF_2'('#skF_3',B_503,'#skF_5'))
      | ~ r1_waybel_0('#skF_3',B_503,'#skF_4')
      | ~ r3_waybel_9('#skF_3',B_503,'#skF_5')
      | ~ l1_waybel_0(B_503,'#skF_3')
      | ~ v7_waybel_0(B_503)
      | ~ v4_orders_2(B_503)
      | v2_struct_0(B_503) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1456])).

tff(c_1461,plain,(
    ! [B_503] :
      ( ~ r1_waybel_0('#skF_3',B_503,'#skF_4')
      | ~ r3_waybel_9('#skF_3',B_503,'#skF_5')
      | ~ l1_waybel_0(B_503,'#skF_3')
      | ~ v7_waybel_0(B_503)
      | ~ v4_orders_2(B_503)
      | v2_struct_0(B_503)
      | k10_yellow_6('#skF_3','#skF_2'('#skF_3',B_503,'#skF_5')) = k1_xboole_0
      | ~ l1_waybel_0('#skF_2'('#skF_3',B_503,'#skF_5'),'#skF_3')
      | ~ v7_waybel_0('#skF_2'('#skF_3',B_503,'#skF_5'))
      | ~ v4_orders_2('#skF_2'('#skF_3',B_503,'#skF_5'))
      | v2_struct_0('#skF_2'('#skF_3',B_503,'#skF_5'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_2,c_1458])).

tff(c_1464,plain,(
    ! [B_503] :
      ( ~ r1_waybel_0('#skF_3',B_503,'#skF_4')
      | ~ r3_waybel_9('#skF_3',B_503,'#skF_5')
      | ~ l1_waybel_0(B_503,'#skF_3')
      | ~ v7_waybel_0(B_503)
      | ~ v4_orders_2(B_503)
      | v2_struct_0(B_503)
      | k10_yellow_6('#skF_3','#skF_2'('#skF_3',B_503,'#skF_5')) = k1_xboole_0
      | ~ l1_waybel_0('#skF_2'('#skF_3',B_503,'#skF_5'),'#skF_3')
      | ~ v7_waybel_0('#skF_2'('#skF_3',B_503,'#skF_5'))
      | ~ v4_orders_2('#skF_2'('#skF_3',B_503,'#skF_5'))
      | v2_struct_0('#skF_2'('#skF_3',B_503,'#skF_5'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_1461])).

tff(c_1466,plain,(
    ! [B_504] :
      ( ~ r1_waybel_0('#skF_3',B_504,'#skF_4')
      | ~ r3_waybel_9('#skF_3',B_504,'#skF_5')
      | ~ l1_waybel_0(B_504,'#skF_3')
      | ~ v7_waybel_0(B_504)
      | ~ v4_orders_2(B_504)
      | v2_struct_0(B_504)
      | k10_yellow_6('#skF_3','#skF_2'('#skF_3',B_504,'#skF_5')) = k1_xboole_0
      | ~ l1_waybel_0('#skF_2'('#skF_3',B_504,'#skF_5'),'#skF_3')
      | ~ v7_waybel_0('#skF_2'('#skF_3',B_504,'#skF_5'))
      | ~ v4_orders_2('#skF_2'('#skF_3',B_504,'#skF_5'))
      | v2_struct_0('#skF_2'('#skF_3',B_504,'#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1464])).

tff(c_1471,plain,(
    ! [B_505] :
      ( ~ r1_waybel_0('#skF_3',B_505,'#skF_4')
      | k10_yellow_6('#skF_3','#skF_2'('#skF_3',B_505,'#skF_5')) = k1_xboole_0
      | ~ v7_waybel_0('#skF_2'('#skF_3',B_505,'#skF_5'))
      | ~ v4_orders_2('#skF_2'('#skF_3',B_505,'#skF_5'))
      | v2_struct_0('#skF_2'('#skF_3',B_505,'#skF_5'))
      | ~ r3_waybel_9('#skF_3',B_505,'#skF_5')
      | ~ l1_waybel_0(B_505,'#skF_3')
      | ~ v7_waybel_0(B_505)
      | ~ v4_orders_2(B_505)
      | v2_struct_0(B_505) ) ),
    inference(resolution,[status(thm)],[c_1441,c_1466])).

tff(c_1482,plain,(
    ! [B_508] :
      ( ~ r1_waybel_0('#skF_3',B_508,'#skF_4')
      | k10_yellow_6('#skF_3','#skF_2'('#skF_3',B_508,'#skF_5')) = k1_xboole_0
      | ~ v4_orders_2('#skF_2'('#skF_3',B_508,'#skF_5'))
      | v2_struct_0('#skF_2'('#skF_3',B_508,'#skF_5'))
      | ~ r3_waybel_9('#skF_3',B_508,'#skF_5')
      | ~ l1_waybel_0(B_508,'#skF_3')
      | ~ v7_waybel_0(B_508)
      | ~ v4_orders_2(B_508)
      | v2_struct_0(B_508) ) ),
    inference(resolution,[status(thm)],[c_1408,c_1471])).

tff(c_1487,plain,(
    ! [B_509] :
      ( ~ r1_waybel_0('#skF_3',B_509,'#skF_4')
      | k10_yellow_6('#skF_3','#skF_2'('#skF_3',B_509,'#skF_5')) = k1_xboole_0
      | v2_struct_0('#skF_2'('#skF_3',B_509,'#skF_5'))
      | ~ r3_waybel_9('#skF_3',B_509,'#skF_5')
      | ~ l1_waybel_0(B_509,'#skF_3')
      | ~ v7_waybel_0(B_509)
      | ~ v4_orders_2(B_509)
      | v2_struct_0(B_509) ) ),
    inference(resolution,[status(thm)],[c_1424,c_1482])).

tff(c_1346,plain,(
    ! [A_459,B_460,C_461] :
      ( ~ v2_struct_0('#skF_2'(A_459,B_460,C_461))
      | ~ l1_struct_0(A_459)
      | ~ r3_waybel_9(A_459,B_460,C_461)
      | ~ m1_subset_1(C_461,u1_struct_0(A_459))
      | ~ l1_waybel_0(B_460,A_459)
      | ~ v7_waybel_0(B_460)
      | ~ v4_orders_2(B_460)
      | v2_struct_0(B_460)
      | ~ l1_pre_topc(A_459)
      | ~ v2_pre_topc(A_459)
      | v2_struct_0(A_459) ) ),
    inference(resolution,[status(thm)],[c_1329,c_16])).

tff(c_1489,plain,(
    ! [B_509] :
      ( ~ l1_struct_0('#skF_3')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r1_waybel_0('#skF_3',B_509,'#skF_4')
      | k10_yellow_6('#skF_3','#skF_2'('#skF_3',B_509,'#skF_5')) = k1_xboole_0
      | ~ r3_waybel_9('#skF_3',B_509,'#skF_5')
      | ~ l1_waybel_0(B_509,'#skF_3')
      | ~ v7_waybel_0(B_509)
      | ~ v4_orders_2(B_509)
      | v2_struct_0(B_509) ) ),
    inference(resolution,[status(thm)],[c_1487,c_1346])).

tff(c_1492,plain,(
    ! [B_509] :
      ( v2_struct_0('#skF_3')
      | ~ r1_waybel_0('#skF_3',B_509,'#skF_4')
      | k10_yellow_6('#skF_3','#skF_2'('#skF_3',B_509,'#skF_5')) = k1_xboole_0
      | ~ r3_waybel_9('#skF_3',B_509,'#skF_5')
      | ~ l1_waybel_0(B_509,'#skF_3')
      | ~ v7_waybel_0(B_509)
      | ~ v4_orders_2(B_509)
      | v2_struct_0(B_509) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_1409,c_1489])).

tff(c_1494,plain,(
    ! [B_510] :
      ( ~ r1_waybel_0('#skF_3',B_510,'#skF_4')
      | k10_yellow_6('#skF_3','#skF_2'('#skF_3',B_510,'#skF_5')) = k1_xboole_0
      | ~ r3_waybel_9('#skF_3',B_510,'#skF_5')
      | ~ l1_waybel_0(B_510,'#skF_3')
      | ~ v7_waybel_0(B_510)
      | ~ v4_orders_2(B_510)
      | v2_struct_0(B_510) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1492])).

tff(c_1390,plain,(
    ! [A_468,B_469,C_467] :
      ( ~ v1_xboole_0(k10_yellow_6(A_468,'#skF_2'(A_468,B_469,C_467)))
      | ~ r3_waybel_9(A_468,B_469,C_467)
      | ~ m1_subset_1(C_467,u1_struct_0(A_468))
      | ~ l1_waybel_0(B_469,A_468)
      | ~ v7_waybel_0(B_469)
      | ~ v4_orders_2(B_469)
      | v2_struct_0(B_469)
      | ~ l1_pre_topc(A_468)
      | ~ v2_pre_topc(A_468)
      | v2_struct_0(A_468) ) ),
    inference(resolution,[status(thm)],[c_1370,c_46])).

tff(c_1506,plain,(
    ! [B_510] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r3_waybel_9('#skF_3',B_510,'#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
      | ~ l1_waybel_0(B_510,'#skF_3')
      | ~ v7_waybel_0(B_510)
      | ~ v4_orders_2(B_510)
      | v2_struct_0(B_510)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r1_waybel_0('#skF_3',B_510,'#skF_4')
      | ~ r3_waybel_9('#skF_3',B_510,'#skF_5')
      | ~ l1_waybel_0(B_510,'#skF_3')
      | ~ v7_waybel_0(B_510)
      | ~ v4_orders_2(B_510)
      | v2_struct_0(B_510) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1494,c_1390])).

tff(c_1530,plain,(
    ! [B_510] :
      ( v2_struct_0('#skF_3')
      | ~ r1_waybel_0('#skF_3',B_510,'#skF_4')
      | ~ r3_waybel_9('#skF_3',B_510,'#skF_5')
      | ~ l1_waybel_0(B_510,'#skF_3')
      | ~ v7_waybel_0(B_510)
      | ~ v4_orders_2(B_510)
      | v2_struct_0(B_510) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_89,c_1506])).

tff(c_1539,plain,(
    ! [B_511] :
      ( ~ r1_waybel_0('#skF_3',B_511,'#skF_4')
      | ~ r3_waybel_9('#skF_3',B_511,'#skF_5')
      | ~ l1_waybel_0(B_511,'#skF_3')
      | ~ v7_waybel_0(B_511)
      | ~ v4_orders_2(B_511)
      | v2_struct_0(B_511) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1530])).

tff(c_1543,plain,
    ( ~ r1_waybel_0('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | ~ l1_waybel_0('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | ~ v7_waybel_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ v4_orders_2('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ r2_hidden('#skF_5',k2_pre_topc('#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1286,c_1539])).

tff(c_1546,plain,
    ( ~ r1_waybel_0('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1186,c_1244,c_1256,c_1270,c_1543])).

tff(c_1547,plain,(
    ~ r1_waybel_0('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_1233,c_1546])).

tff(c_1550,plain,
    ( ~ r2_hidden('#skF_5',k2_pre_topc('#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1278,c_1547])).

tff(c_1554,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1186,c_1550])).

tff(c_1555,plain,(
    r2_hidden('#skF_5',k2_pre_topc('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_1660,plain,(
    ! [A_552,B_553,C_554] :
      ( r1_waybel_0(A_552,'#skF_1'(A_552,B_553,C_554),B_553)
      | ~ r2_hidden(C_554,k2_pre_topc(A_552,B_553))
      | ~ m1_subset_1(C_554,u1_struct_0(A_552))
      | ~ m1_subset_1(B_553,k1_zfmisc_1(u1_struct_0(A_552)))
      | ~ l1_pre_topc(A_552)
      | ~ v2_pre_topc(A_552)
      | v2_struct_0(A_552) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_1662,plain,(
    ! [C_554] :
      ( r1_waybel_0('#skF_3','#skF_1'('#skF_3','#skF_4',C_554),'#skF_4')
      | ~ r2_hidden(C_554,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_554,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_50,c_1660])).

tff(c_1665,plain,(
    ! [C_554] :
      ( r1_waybel_0('#skF_3','#skF_1'('#skF_3','#skF_4',C_554),'#skF_4')
      | ~ r2_hidden(C_554,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_554,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_1662])).

tff(c_1666,plain,(
    ! [C_554] :
      ( r1_waybel_0('#skF_3','#skF_1'('#skF_3','#skF_4',C_554),'#skF_4')
      | ~ r2_hidden(C_554,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_554,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1665])).

tff(c_1627,plain,(
    ! [A_541,B_542,C_543] :
      ( ~ v2_struct_0('#skF_1'(A_541,B_542,C_543))
      | ~ r2_hidden(C_543,k2_pre_topc(A_541,B_542))
      | ~ m1_subset_1(C_543,u1_struct_0(A_541))
      | ~ m1_subset_1(B_542,k1_zfmisc_1(u1_struct_0(A_541)))
      | ~ l1_pre_topc(A_541)
      | ~ v2_pre_topc(A_541)
      | v2_struct_0(A_541) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_1632,plain,
    ( ~ v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1555,c_1627])).

tff(c_1636,plain,
    ( ~ v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_1632])).

tff(c_1637,plain,(
    ~ v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1636])).

tff(c_1616,plain,(
    ! [A_538,B_539,C_540] :
      ( v4_orders_2('#skF_1'(A_538,B_539,C_540))
      | ~ r2_hidden(C_540,k2_pre_topc(A_538,B_539))
      | ~ m1_subset_1(C_540,u1_struct_0(A_538))
      | ~ m1_subset_1(B_539,k1_zfmisc_1(u1_struct_0(A_538)))
      | ~ l1_pre_topc(A_538)
      | ~ v2_pre_topc(A_538)
      | v2_struct_0(A_538) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_1621,plain,
    ( v4_orders_2('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1555,c_1616])).

tff(c_1625,plain,
    ( v4_orders_2('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_1621])).

tff(c_1626,plain,(
    v4_orders_2('#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1625])).

tff(c_1604,plain,(
    ! [A_531,B_532,C_533] :
      ( v7_waybel_0('#skF_1'(A_531,B_532,C_533))
      | ~ r2_hidden(C_533,k2_pre_topc(A_531,B_532))
      | ~ m1_subset_1(C_533,u1_struct_0(A_531))
      | ~ m1_subset_1(B_532,k1_zfmisc_1(u1_struct_0(A_531)))
      | ~ l1_pre_topc(A_531)
      | ~ v2_pre_topc(A_531)
      | v2_struct_0(A_531) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_1609,plain,
    ( v7_waybel_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1555,c_1604])).

tff(c_1613,plain,
    ( v7_waybel_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_1609])).

tff(c_1614,plain,(
    v7_waybel_0('#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1613])).

tff(c_1641,plain,(
    ! [A_545,B_546,C_547] :
      ( l1_waybel_0('#skF_1'(A_545,B_546,C_547),A_545)
      | ~ r2_hidden(C_547,k2_pre_topc(A_545,B_546))
      | ~ m1_subset_1(C_547,u1_struct_0(A_545))
      | ~ m1_subset_1(B_546,k1_zfmisc_1(u1_struct_0(A_545)))
      | ~ l1_pre_topc(A_545)
      | ~ v2_pre_topc(A_545)
      | v2_struct_0(A_545) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_1646,plain,
    ( l1_waybel_0('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1555,c_1641])).

tff(c_1650,plain,
    ( l1_waybel_0('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_1646])).

tff(c_1651,plain,(
    l1_waybel_0('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1650])).

tff(c_1652,plain,(
    ! [A_548,B_549,C_550] :
      ( r3_waybel_9(A_548,'#skF_1'(A_548,B_549,C_550),C_550)
      | ~ r2_hidden(C_550,k2_pre_topc(A_548,B_549))
      | ~ m1_subset_1(C_550,u1_struct_0(A_548))
      | ~ m1_subset_1(B_549,k1_zfmisc_1(u1_struct_0(A_548)))
      | ~ l1_pre_topc(A_548)
      | ~ v2_pre_topc(A_548)
      | v2_struct_0(A_548) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_1654,plain,(
    ! [C_550] :
      ( r3_waybel_9('#skF_3','#skF_1'('#skF_3','#skF_4',C_550),C_550)
      | ~ r2_hidden(C_550,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_550,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_50,c_1652])).

tff(c_1657,plain,(
    ! [C_550] :
      ( r3_waybel_9('#skF_3','#skF_1'('#skF_3','#skF_4',C_550),C_550)
      | ~ r2_hidden(C_550,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_550,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_1654])).

tff(c_1658,plain,(
    ! [C_550] :
      ( r3_waybel_9('#skF_3','#skF_1'('#skF_3','#skF_4',C_550),C_550)
      | ~ r2_hidden(C_550,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_550,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1657])).

tff(c_1681,plain,(
    ! [A_562,B_563,C_564] :
      ( m2_yellow_6('#skF_2'(A_562,B_563,C_564),A_562,B_563)
      | ~ r3_waybel_9(A_562,B_563,C_564)
      | ~ m1_subset_1(C_564,u1_struct_0(A_562))
      | ~ l1_waybel_0(B_563,A_562)
      | ~ v7_waybel_0(B_563)
      | ~ v4_orders_2(B_563)
      | v2_struct_0(B_563)
      | ~ l1_pre_topc(A_562)
      | ~ v2_pre_topc(A_562)
      | v2_struct_0(A_562) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_1758,plain,(
    ! [A_580,B_581,C_582] :
      ( v7_waybel_0('#skF_2'(A_580,B_581,C_582))
      | ~ l1_struct_0(A_580)
      | ~ r3_waybel_9(A_580,B_581,C_582)
      | ~ m1_subset_1(C_582,u1_struct_0(A_580))
      | ~ l1_waybel_0(B_581,A_580)
      | ~ v7_waybel_0(B_581)
      | ~ v4_orders_2(B_581)
      | v2_struct_0(B_581)
      | ~ l1_pre_topc(A_580)
      | ~ v2_pre_topc(A_580)
      | v2_struct_0(A_580) ) ),
    inference(resolution,[status(thm)],[c_1681,c_12])).

tff(c_1760,plain,(
    ! [B_581] :
      ( v7_waybel_0('#skF_2'('#skF_3',B_581,'#skF_5'))
      | ~ l1_struct_0('#skF_3')
      | ~ r3_waybel_9('#skF_3',B_581,'#skF_5')
      | ~ l1_waybel_0(B_581,'#skF_3')
      | ~ v7_waybel_0(B_581)
      | ~ v4_orders_2(B_581)
      | v2_struct_0(B_581)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_48,c_1758])).

tff(c_1763,plain,(
    ! [B_581] :
      ( v7_waybel_0('#skF_2'('#skF_3',B_581,'#skF_5'))
      | ~ l1_struct_0('#skF_3')
      | ~ r3_waybel_9('#skF_3',B_581,'#skF_5')
      | ~ l1_waybel_0(B_581,'#skF_3')
      | ~ v7_waybel_0(B_581)
      | ~ v4_orders_2(B_581)
      | v2_struct_0(B_581)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_1760])).

tff(c_1764,plain,(
    ! [B_581] :
      ( v7_waybel_0('#skF_2'('#skF_3',B_581,'#skF_5'))
      | ~ l1_struct_0('#skF_3')
      | ~ r3_waybel_9('#skF_3',B_581,'#skF_5')
      | ~ l1_waybel_0(B_581,'#skF_3')
      | ~ v7_waybel_0(B_581)
      | ~ v4_orders_2(B_581)
      | v2_struct_0(B_581) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1763])).

tff(c_1765,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1764])).

tff(c_1775,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_1765])).

tff(c_1779,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1775])).

tff(c_1781,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1764])).

tff(c_1798,plain,(
    ! [A_593,B_594,C_595] :
      ( v4_orders_2('#skF_2'(A_593,B_594,C_595))
      | ~ l1_struct_0(A_593)
      | ~ r3_waybel_9(A_593,B_594,C_595)
      | ~ m1_subset_1(C_595,u1_struct_0(A_593))
      | ~ l1_waybel_0(B_594,A_593)
      | ~ v7_waybel_0(B_594)
      | ~ v4_orders_2(B_594)
      | v2_struct_0(B_594)
      | ~ l1_pre_topc(A_593)
      | ~ v2_pre_topc(A_593)
      | v2_struct_0(A_593) ) ),
    inference(resolution,[status(thm)],[c_1681,c_14])).

tff(c_1800,plain,(
    ! [B_594] :
      ( v4_orders_2('#skF_2'('#skF_3',B_594,'#skF_5'))
      | ~ l1_struct_0('#skF_3')
      | ~ r3_waybel_9('#skF_3',B_594,'#skF_5')
      | ~ l1_waybel_0(B_594,'#skF_3')
      | ~ v7_waybel_0(B_594)
      | ~ v4_orders_2(B_594)
      | v2_struct_0(B_594)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_48,c_1798])).

tff(c_1803,plain,(
    ! [B_594] :
      ( v4_orders_2('#skF_2'('#skF_3',B_594,'#skF_5'))
      | ~ r3_waybel_9('#skF_3',B_594,'#skF_5')
      | ~ l1_waybel_0(B_594,'#skF_3')
      | ~ v7_waybel_0(B_594)
      | ~ v4_orders_2(B_594)
      | v2_struct_0(B_594)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_1781,c_1800])).

tff(c_1804,plain,(
    ! [B_594] :
      ( v4_orders_2('#skF_2'('#skF_3',B_594,'#skF_5'))
      | ~ r3_waybel_9('#skF_3',B_594,'#skF_5')
      | ~ l1_waybel_0(B_594,'#skF_3')
      | ~ v7_waybel_0(B_594)
      | ~ v4_orders_2(B_594)
      | v2_struct_0(B_594) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1803])).

tff(c_1780,plain,(
    ! [B_581] :
      ( v7_waybel_0('#skF_2'('#skF_3',B_581,'#skF_5'))
      | ~ r3_waybel_9('#skF_3',B_581,'#skF_5')
      | ~ l1_waybel_0(B_581,'#skF_3')
      | ~ v7_waybel_0(B_581)
      | ~ v4_orders_2(B_581)
      | v2_struct_0(B_581) ) ),
    inference(splitRight,[status(thm)],[c_1764])).

tff(c_1823,plain,(
    ! [A_607,B_608,C_609] :
      ( l1_waybel_0('#skF_2'(A_607,B_608,C_609),A_607)
      | ~ l1_struct_0(A_607)
      | ~ r3_waybel_9(A_607,B_608,C_609)
      | ~ m1_subset_1(C_609,u1_struct_0(A_607))
      | ~ l1_waybel_0(B_608,A_607)
      | ~ v7_waybel_0(B_608)
      | ~ v4_orders_2(B_608)
      | v2_struct_0(B_608)
      | ~ l1_pre_topc(A_607)
      | ~ v2_pre_topc(A_607)
      | v2_struct_0(A_607) ) ),
    inference(resolution,[status(thm)],[c_1681,c_10])).

tff(c_1825,plain,(
    ! [B_608] :
      ( l1_waybel_0('#skF_2'('#skF_3',B_608,'#skF_5'),'#skF_3')
      | ~ l1_struct_0('#skF_3')
      | ~ r3_waybel_9('#skF_3',B_608,'#skF_5')
      | ~ l1_waybel_0(B_608,'#skF_3')
      | ~ v7_waybel_0(B_608)
      | ~ v4_orders_2(B_608)
      | v2_struct_0(B_608)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_48,c_1823])).

tff(c_1828,plain,(
    ! [B_608] :
      ( l1_waybel_0('#skF_2'('#skF_3',B_608,'#skF_5'),'#skF_3')
      | ~ r3_waybel_9('#skF_3',B_608,'#skF_5')
      | ~ l1_waybel_0(B_608,'#skF_3')
      | ~ v7_waybel_0(B_608)
      | ~ v4_orders_2(B_608)
      | v2_struct_0(B_608)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_1781,c_1825])).

tff(c_1829,plain,(
    ! [B_608] :
      ( l1_waybel_0('#skF_2'('#skF_3',B_608,'#skF_5'),'#skF_3')
      | ~ r3_waybel_9('#skF_3',B_608,'#skF_5')
      | ~ l1_waybel_0(B_608,'#skF_3')
      | ~ v7_waybel_0(B_608)
      | ~ v4_orders_2(B_608)
      | v2_struct_0(B_608) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1828])).

tff(c_1842,plain,(
    ! [A_616,B_617,C_618,B_619] :
      ( r1_waybel_0(A_616,'#skF_2'(A_616,B_617,C_618),B_619)
      | ~ r1_waybel_0(A_616,B_617,B_619)
      | ~ l1_struct_0(A_616)
      | ~ r3_waybel_9(A_616,B_617,C_618)
      | ~ m1_subset_1(C_618,u1_struct_0(A_616))
      | ~ l1_waybel_0(B_617,A_616)
      | ~ v7_waybel_0(B_617)
      | ~ v4_orders_2(B_617)
      | v2_struct_0(B_617)
      | ~ l1_pre_topc(A_616)
      | ~ v2_pre_topc(A_616)
      | v2_struct_0(A_616) ) ),
    inference(resolution,[status(thm)],[c_1681,c_22])).

tff(c_1722,plain,(
    ! [C_570,A_571,B_572] :
      ( r2_hidden(C_570,k10_yellow_6(A_571,'#skF_2'(A_571,B_572,C_570)))
      | ~ r3_waybel_9(A_571,B_572,C_570)
      | ~ m1_subset_1(C_570,u1_struct_0(A_571))
      | ~ l1_waybel_0(B_572,A_571)
      | ~ v7_waybel_0(B_572)
      | ~ v4_orders_2(B_572)
      | v2_struct_0(B_572)
      | ~ l1_pre_topc(A_571)
      | ~ v2_pre_topc(A_571)
      | v2_struct_0(A_571) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_1556,plain,(
    ~ v3_yellow_6('#skF_6','#skF_3') ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_74,plain,(
    ! [D_85] :
      ( ~ r2_hidden('#skF_5',k10_yellow_6('#skF_3',D_85))
      | ~ r1_waybel_0('#skF_3',D_85,'#skF_4')
      | ~ l1_waybel_0(D_85,'#skF_3')
      | ~ v3_yellow_6(D_85,'#skF_3')
      | ~ v7_waybel_0(D_85)
      | ~ v4_orders_2(D_85)
      | v2_struct_0(D_85)
      | v3_yellow_6('#skF_6','#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_1597,plain,(
    ! [D_85] :
      ( ~ r2_hidden('#skF_5',k10_yellow_6('#skF_3',D_85))
      | ~ r1_waybel_0('#skF_3',D_85,'#skF_4')
      | ~ l1_waybel_0(D_85,'#skF_3')
      | ~ v3_yellow_6(D_85,'#skF_3')
      | ~ v7_waybel_0(D_85)
      | ~ v4_orders_2(D_85)
      | v2_struct_0(D_85) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1556,c_74])).

tff(c_1729,plain,(
    ! [B_572] :
      ( ~ r1_waybel_0('#skF_3','#skF_2'('#skF_3',B_572,'#skF_5'),'#skF_4')
      | ~ l1_waybel_0('#skF_2'('#skF_3',B_572,'#skF_5'),'#skF_3')
      | ~ v3_yellow_6('#skF_2'('#skF_3',B_572,'#skF_5'),'#skF_3')
      | ~ v7_waybel_0('#skF_2'('#skF_3',B_572,'#skF_5'))
      | ~ v4_orders_2('#skF_2'('#skF_3',B_572,'#skF_5'))
      | v2_struct_0('#skF_2'('#skF_3',B_572,'#skF_5'))
      | ~ r3_waybel_9('#skF_3',B_572,'#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
      | ~ l1_waybel_0(B_572,'#skF_3')
      | ~ v7_waybel_0(B_572)
      | ~ v4_orders_2(B_572)
      | v2_struct_0(B_572)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1722,c_1597])).

tff(c_1739,plain,(
    ! [B_572] :
      ( ~ r1_waybel_0('#skF_3','#skF_2'('#skF_3',B_572,'#skF_5'),'#skF_4')
      | ~ l1_waybel_0('#skF_2'('#skF_3',B_572,'#skF_5'),'#skF_3')
      | ~ v3_yellow_6('#skF_2'('#skF_3',B_572,'#skF_5'),'#skF_3')
      | ~ v7_waybel_0('#skF_2'('#skF_3',B_572,'#skF_5'))
      | ~ v4_orders_2('#skF_2'('#skF_3',B_572,'#skF_5'))
      | v2_struct_0('#skF_2'('#skF_3',B_572,'#skF_5'))
      | ~ r3_waybel_9('#skF_3',B_572,'#skF_5')
      | ~ l1_waybel_0(B_572,'#skF_3')
      | ~ v7_waybel_0(B_572)
      | ~ v4_orders_2(B_572)
      | v2_struct_0(B_572)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_1729])).

tff(c_1740,plain,(
    ! [B_572] :
      ( ~ r1_waybel_0('#skF_3','#skF_2'('#skF_3',B_572,'#skF_5'),'#skF_4')
      | ~ l1_waybel_0('#skF_2'('#skF_3',B_572,'#skF_5'),'#skF_3')
      | ~ v3_yellow_6('#skF_2'('#skF_3',B_572,'#skF_5'),'#skF_3')
      | ~ v7_waybel_0('#skF_2'('#skF_3',B_572,'#skF_5'))
      | ~ v4_orders_2('#skF_2'('#skF_3',B_572,'#skF_5'))
      | v2_struct_0('#skF_2'('#skF_3',B_572,'#skF_5'))
      | ~ r3_waybel_9('#skF_3',B_572,'#skF_5')
      | ~ l1_waybel_0(B_572,'#skF_3')
      | ~ v7_waybel_0(B_572)
      | ~ v4_orders_2(B_572)
      | v2_struct_0(B_572) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1739])).

tff(c_1846,plain,(
    ! [B_617] :
      ( ~ l1_waybel_0('#skF_2'('#skF_3',B_617,'#skF_5'),'#skF_3')
      | ~ v3_yellow_6('#skF_2'('#skF_3',B_617,'#skF_5'),'#skF_3')
      | ~ v7_waybel_0('#skF_2'('#skF_3',B_617,'#skF_5'))
      | ~ v4_orders_2('#skF_2'('#skF_3',B_617,'#skF_5'))
      | v2_struct_0('#skF_2'('#skF_3',B_617,'#skF_5'))
      | ~ r1_waybel_0('#skF_3',B_617,'#skF_4')
      | ~ l1_struct_0('#skF_3')
      | ~ r3_waybel_9('#skF_3',B_617,'#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
      | ~ l1_waybel_0(B_617,'#skF_3')
      | ~ v7_waybel_0(B_617)
      | ~ v4_orders_2(B_617)
      | v2_struct_0(B_617)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1842,c_1740])).

tff(c_1849,plain,(
    ! [B_617] :
      ( ~ l1_waybel_0('#skF_2'('#skF_3',B_617,'#skF_5'),'#skF_3')
      | ~ v3_yellow_6('#skF_2'('#skF_3',B_617,'#skF_5'),'#skF_3')
      | ~ v7_waybel_0('#skF_2'('#skF_3',B_617,'#skF_5'))
      | ~ v4_orders_2('#skF_2'('#skF_3',B_617,'#skF_5'))
      | v2_struct_0('#skF_2'('#skF_3',B_617,'#skF_5'))
      | ~ r1_waybel_0('#skF_3',B_617,'#skF_4')
      | ~ r3_waybel_9('#skF_3',B_617,'#skF_5')
      | ~ l1_waybel_0(B_617,'#skF_3')
      | ~ v7_waybel_0(B_617)
      | ~ v4_orders_2(B_617)
      | v2_struct_0(B_617)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_1781,c_1846])).

tff(c_1851,plain,(
    ! [B_620] :
      ( ~ l1_waybel_0('#skF_2'('#skF_3',B_620,'#skF_5'),'#skF_3')
      | ~ v3_yellow_6('#skF_2'('#skF_3',B_620,'#skF_5'),'#skF_3')
      | ~ v7_waybel_0('#skF_2'('#skF_3',B_620,'#skF_5'))
      | ~ v4_orders_2('#skF_2'('#skF_3',B_620,'#skF_5'))
      | v2_struct_0('#skF_2'('#skF_3',B_620,'#skF_5'))
      | ~ r1_waybel_0('#skF_3',B_620,'#skF_4')
      | ~ r3_waybel_9('#skF_3',B_620,'#skF_5')
      | ~ l1_waybel_0(B_620,'#skF_3')
      | ~ v7_waybel_0(B_620)
      | ~ v4_orders_2(B_620)
      | v2_struct_0(B_620) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1849])).

tff(c_1854,plain,(
    ! [B_620] :
      ( ~ r1_waybel_0('#skF_3',B_620,'#skF_4')
      | ~ r3_waybel_9('#skF_3',B_620,'#skF_5')
      | ~ l1_waybel_0(B_620,'#skF_3')
      | ~ v7_waybel_0(B_620)
      | ~ v4_orders_2(B_620)
      | v2_struct_0(B_620)
      | k10_yellow_6('#skF_3','#skF_2'('#skF_3',B_620,'#skF_5')) = k1_xboole_0
      | ~ l1_waybel_0('#skF_2'('#skF_3',B_620,'#skF_5'),'#skF_3')
      | ~ v7_waybel_0('#skF_2'('#skF_3',B_620,'#skF_5'))
      | ~ v4_orders_2('#skF_2'('#skF_3',B_620,'#skF_5'))
      | v2_struct_0('#skF_2'('#skF_3',B_620,'#skF_5'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_2,c_1851])).

tff(c_1857,plain,(
    ! [B_620] :
      ( ~ r1_waybel_0('#skF_3',B_620,'#skF_4')
      | ~ r3_waybel_9('#skF_3',B_620,'#skF_5')
      | ~ l1_waybel_0(B_620,'#skF_3')
      | ~ v7_waybel_0(B_620)
      | ~ v4_orders_2(B_620)
      | v2_struct_0(B_620)
      | k10_yellow_6('#skF_3','#skF_2'('#skF_3',B_620,'#skF_5')) = k1_xboole_0
      | ~ l1_waybel_0('#skF_2'('#skF_3',B_620,'#skF_5'),'#skF_3')
      | ~ v7_waybel_0('#skF_2'('#skF_3',B_620,'#skF_5'))
      | ~ v4_orders_2('#skF_2'('#skF_3',B_620,'#skF_5'))
      | v2_struct_0('#skF_2'('#skF_3',B_620,'#skF_5'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_1854])).

tff(c_1859,plain,(
    ! [B_621] :
      ( ~ r1_waybel_0('#skF_3',B_621,'#skF_4')
      | ~ r3_waybel_9('#skF_3',B_621,'#skF_5')
      | ~ l1_waybel_0(B_621,'#skF_3')
      | ~ v7_waybel_0(B_621)
      | ~ v4_orders_2(B_621)
      | v2_struct_0(B_621)
      | k10_yellow_6('#skF_3','#skF_2'('#skF_3',B_621,'#skF_5')) = k1_xboole_0
      | ~ l1_waybel_0('#skF_2'('#skF_3',B_621,'#skF_5'),'#skF_3')
      | ~ v7_waybel_0('#skF_2'('#skF_3',B_621,'#skF_5'))
      | ~ v4_orders_2('#skF_2'('#skF_3',B_621,'#skF_5'))
      | v2_struct_0('#skF_2'('#skF_3',B_621,'#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1857])).

tff(c_1864,plain,(
    ! [B_622] :
      ( ~ r1_waybel_0('#skF_3',B_622,'#skF_4')
      | k10_yellow_6('#skF_3','#skF_2'('#skF_3',B_622,'#skF_5')) = k1_xboole_0
      | ~ v7_waybel_0('#skF_2'('#skF_3',B_622,'#skF_5'))
      | ~ v4_orders_2('#skF_2'('#skF_3',B_622,'#skF_5'))
      | v2_struct_0('#skF_2'('#skF_3',B_622,'#skF_5'))
      | ~ r3_waybel_9('#skF_3',B_622,'#skF_5')
      | ~ l1_waybel_0(B_622,'#skF_3')
      | ~ v7_waybel_0(B_622)
      | ~ v4_orders_2(B_622)
      | v2_struct_0(B_622) ) ),
    inference(resolution,[status(thm)],[c_1829,c_1859])).

tff(c_1873,plain,(
    ! [B_626] :
      ( ~ r1_waybel_0('#skF_3',B_626,'#skF_4')
      | k10_yellow_6('#skF_3','#skF_2'('#skF_3',B_626,'#skF_5')) = k1_xboole_0
      | ~ v4_orders_2('#skF_2'('#skF_3',B_626,'#skF_5'))
      | v2_struct_0('#skF_2'('#skF_3',B_626,'#skF_5'))
      | ~ r3_waybel_9('#skF_3',B_626,'#skF_5')
      | ~ l1_waybel_0(B_626,'#skF_3')
      | ~ v7_waybel_0(B_626)
      | ~ v4_orders_2(B_626)
      | v2_struct_0(B_626) ) ),
    inference(resolution,[status(thm)],[c_1780,c_1864])).

tff(c_1878,plain,(
    ! [B_627] :
      ( ~ r1_waybel_0('#skF_3',B_627,'#skF_4')
      | k10_yellow_6('#skF_3','#skF_2'('#skF_3',B_627,'#skF_5')) = k1_xboole_0
      | v2_struct_0('#skF_2'('#skF_3',B_627,'#skF_5'))
      | ~ r3_waybel_9('#skF_3',B_627,'#skF_5')
      | ~ l1_waybel_0(B_627,'#skF_3')
      | ~ v7_waybel_0(B_627)
      | ~ v4_orders_2(B_627)
      | v2_struct_0(B_627) ) ),
    inference(resolution,[status(thm)],[c_1804,c_1873])).

tff(c_1700,plain,(
    ! [A_562,B_563,C_564] :
      ( ~ v2_struct_0('#skF_2'(A_562,B_563,C_564))
      | ~ l1_struct_0(A_562)
      | ~ r3_waybel_9(A_562,B_563,C_564)
      | ~ m1_subset_1(C_564,u1_struct_0(A_562))
      | ~ l1_waybel_0(B_563,A_562)
      | ~ v7_waybel_0(B_563)
      | ~ v4_orders_2(B_563)
      | v2_struct_0(B_563)
      | ~ l1_pre_topc(A_562)
      | ~ v2_pre_topc(A_562)
      | v2_struct_0(A_562) ) ),
    inference(resolution,[status(thm)],[c_1681,c_16])).

tff(c_1880,plain,(
    ! [B_627] :
      ( ~ l1_struct_0('#skF_3')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r1_waybel_0('#skF_3',B_627,'#skF_4')
      | k10_yellow_6('#skF_3','#skF_2'('#skF_3',B_627,'#skF_5')) = k1_xboole_0
      | ~ r3_waybel_9('#skF_3',B_627,'#skF_5')
      | ~ l1_waybel_0(B_627,'#skF_3')
      | ~ v7_waybel_0(B_627)
      | ~ v4_orders_2(B_627)
      | v2_struct_0(B_627) ) ),
    inference(resolution,[status(thm)],[c_1878,c_1700])).

tff(c_1883,plain,(
    ! [B_627] :
      ( v2_struct_0('#skF_3')
      | ~ r1_waybel_0('#skF_3',B_627,'#skF_4')
      | k10_yellow_6('#skF_3','#skF_2'('#skF_3',B_627,'#skF_5')) = k1_xboole_0
      | ~ r3_waybel_9('#skF_3',B_627,'#skF_5')
      | ~ l1_waybel_0(B_627,'#skF_3')
      | ~ v7_waybel_0(B_627)
      | ~ v4_orders_2(B_627)
      | v2_struct_0(B_627) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_1781,c_1880])).

tff(c_1885,plain,(
    ! [B_628] :
      ( ~ r1_waybel_0('#skF_3',B_628,'#skF_4')
      | k10_yellow_6('#skF_3','#skF_2'('#skF_3',B_628,'#skF_5')) = k1_xboole_0
      | ~ r3_waybel_9('#skF_3',B_628,'#skF_5')
      | ~ l1_waybel_0(B_628,'#skF_3')
      | ~ v7_waybel_0(B_628)
      | ~ v4_orders_2(B_628)
      | v2_struct_0(B_628) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1883])).

tff(c_1742,plain,(
    ! [A_571,B_572,C_570] :
      ( ~ v1_xboole_0(k10_yellow_6(A_571,'#skF_2'(A_571,B_572,C_570)))
      | ~ r3_waybel_9(A_571,B_572,C_570)
      | ~ m1_subset_1(C_570,u1_struct_0(A_571))
      | ~ l1_waybel_0(B_572,A_571)
      | ~ v7_waybel_0(B_572)
      | ~ v4_orders_2(B_572)
      | v2_struct_0(B_572)
      | ~ l1_pre_topc(A_571)
      | ~ v2_pre_topc(A_571)
      | v2_struct_0(A_571) ) ),
    inference(resolution,[status(thm)],[c_1722,c_46])).

tff(c_1897,plain,(
    ! [B_628] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r3_waybel_9('#skF_3',B_628,'#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
      | ~ l1_waybel_0(B_628,'#skF_3')
      | ~ v7_waybel_0(B_628)
      | ~ v4_orders_2(B_628)
      | v2_struct_0(B_628)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r1_waybel_0('#skF_3',B_628,'#skF_4')
      | ~ r3_waybel_9('#skF_3',B_628,'#skF_5')
      | ~ l1_waybel_0(B_628,'#skF_3')
      | ~ v7_waybel_0(B_628)
      | ~ v4_orders_2(B_628)
      | v2_struct_0(B_628) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1885,c_1742])).

tff(c_1921,plain,(
    ! [B_628] :
      ( v2_struct_0('#skF_3')
      | ~ r1_waybel_0('#skF_3',B_628,'#skF_4')
      | ~ r3_waybel_9('#skF_3',B_628,'#skF_5')
      | ~ l1_waybel_0(B_628,'#skF_3')
      | ~ v7_waybel_0(B_628)
      | ~ v4_orders_2(B_628)
      | v2_struct_0(B_628) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_89,c_1897])).

tff(c_1930,plain,(
    ! [B_629] :
      ( ~ r1_waybel_0('#skF_3',B_629,'#skF_4')
      | ~ r3_waybel_9('#skF_3',B_629,'#skF_5')
      | ~ l1_waybel_0(B_629,'#skF_3')
      | ~ v7_waybel_0(B_629)
      | ~ v4_orders_2(B_629)
      | v2_struct_0(B_629) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1921])).

tff(c_1938,plain,
    ( ~ r1_waybel_0('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | ~ l1_waybel_0('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | ~ v7_waybel_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ v4_orders_2('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ r2_hidden('#skF_5',k2_pre_topc('#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1658,c_1930])).

tff(c_1945,plain,
    ( ~ r1_waybel_0('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1555,c_1626,c_1614,c_1651,c_1938])).

tff(c_1946,plain,(
    ~ r1_waybel_0('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_1637,c_1945])).

tff(c_1949,plain,
    ( ~ r2_hidden('#skF_5',k2_pre_topc('#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1666,c_1946])).

tff(c_1953,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1555,c_1949])).

tff(c_1954,plain,(
    r2_hidden('#skF_5',k2_pre_topc('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_2042,plain,(
    ! [A_666,B_667,C_668] :
      ( r1_waybel_0(A_666,'#skF_1'(A_666,B_667,C_668),B_667)
      | ~ r2_hidden(C_668,k2_pre_topc(A_666,B_667))
      | ~ m1_subset_1(C_668,u1_struct_0(A_666))
      | ~ m1_subset_1(B_667,k1_zfmisc_1(u1_struct_0(A_666)))
      | ~ l1_pre_topc(A_666)
      | ~ v2_pre_topc(A_666)
      | v2_struct_0(A_666) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_2044,plain,(
    ! [C_668] :
      ( r1_waybel_0('#skF_3','#skF_1'('#skF_3','#skF_4',C_668),'#skF_4')
      | ~ r2_hidden(C_668,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_668,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_50,c_2042])).

tff(c_2047,plain,(
    ! [C_668] :
      ( r1_waybel_0('#skF_3','#skF_1'('#skF_3','#skF_4',C_668),'#skF_4')
      | ~ r2_hidden(C_668,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_668,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_2044])).

tff(c_2048,plain,(
    ! [C_668] :
      ( r1_waybel_0('#skF_3','#skF_1'('#skF_3','#skF_4',C_668),'#skF_4')
      | ~ r2_hidden(C_668,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_668,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_2047])).

tff(c_2006,plain,(
    ! [A_656,B_657,C_658] :
      ( ~ v2_struct_0('#skF_1'(A_656,B_657,C_658))
      | ~ r2_hidden(C_658,k2_pre_topc(A_656,B_657))
      | ~ m1_subset_1(C_658,u1_struct_0(A_656))
      | ~ m1_subset_1(B_657,k1_zfmisc_1(u1_struct_0(A_656)))
      | ~ l1_pre_topc(A_656)
      | ~ v2_pre_topc(A_656)
      | v2_struct_0(A_656) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_2011,plain,
    ( ~ v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1954,c_2006])).

tff(c_2015,plain,
    ( ~ v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_2011])).

tff(c_2016,plain,(
    ~ v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_2015])).

tff(c_2017,plain,(
    ! [A_659,B_660,C_661] :
      ( v4_orders_2('#skF_1'(A_659,B_660,C_661))
      | ~ r2_hidden(C_661,k2_pre_topc(A_659,B_660))
      | ~ m1_subset_1(C_661,u1_struct_0(A_659))
      | ~ m1_subset_1(B_660,k1_zfmisc_1(u1_struct_0(A_659)))
      | ~ l1_pre_topc(A_659)
      | ~ v2_pre_topc(A_659)
      | v2_struct_0(A_659) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_2022,plain,
    ( v4_orders_2('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1954,c_2017])).

tff(c_2026,plain,
    ( v4_orders_2('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_2022])).

tff(c_2027,plain,(
    v4_orders_2('#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_2026])).

tff(c_1994,plain,(
    ! [A_649,B_650,C_651] :
      ( v7_waybel_0('#skF_1'(A_649,B_650,C_651))
      | ~ r2_hidden(C_651,k2_pre_topc(A_649,B_650))
      | ~ m1_subset_1(C_651,u1_struct_0(A_649))
      | ~ m1_subset_1(B_650,k1_zfmisc_1(u1_struct_0(A_649)))
      | ~ l1_pre_topc(A_649)
      | ~ v2_pre_topc(A_649)
      | v2_struct_0(A_649) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_1999,plain,
    ( v7_waybel_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1954,c_1994])).

tff(c_2003,plain,
    ( v7_waybel_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_1999])).

tff(c_2004,plain,(
    v7_waybel_0('#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_2003])).

tff(c_2031,plain,(
    ! [A_663,B_664,C_665] :
      ( l1_waybel_0('#skF_1'(A_663,B_664,C_665),A_663)
      | ~ r2_hidden(C_665,k2_pre_topc(A_663,B_664))
      | ~ m1_subset_1(C_665,u1_struct_0(A_663))
      | ~ m1_subset_1(B_664,k1_zfmisc_1(u1_struct_0(A_663)))
      | ~ l1_pre_topc(A_663)
      | ~ v2_pre_topc(A_663)
      | v2_struct_0(A_663) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_2036,plain,
    ( l1_waybel_0('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1954,c_2031])).

tff(c_2040,plain,
    ( l1_waybel_0('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_2036])).

tff(c_2041,plain,(
    l1_waybel_0('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_2040])).

tff(c_2049,plain,(
    ! [A_669,B_670,C_671] :
      ( r3_waybel_9(A_669,'#skF_1'(A_669,B_670,C_671),C_671)
      | ~ r2_hidden(C_671,k2_pre_topc(A_669,B_670))
      | ~ m1_subset_1(C_671,u1_struct_0(A_669))
      | ~ m1_subset_1(B_670,k1_zfmisc_1(u1_struct_0(A_669)))
      | ~ l1_pre_topc(A_669)
      | ~ v2_pre_topc(A_669)
      | v2_struct_0(A_669) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_2051,plain,(
    ! [C_671] :
      ( r3_waybel_9('#skF_3','#skF_1'('#skF_3','#skF_4',C_671),C_671)
      | ~ r2_hidden(C_671,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_671,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_50,c_2049])).

tff(c_2054,plain,(
    ! [C_671] :
      ( r3_waybel_9('#skF_3','#skF_1'('#skF_3','#skF_4',C_671),C_671)
      | ~ r2_hidden(C_671,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_671,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_2051])).

tff(c_2055,plain,(
    ! [C_671] :
      ( r3_waybel_9('#skF_3','#skF_1'('#skF_3','#skF_4',C_671),C_671)
      | ~ r2_hidden(C_671,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_671,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_2054])).

tff(c_2064,plain,(
    ! [A_677,B_678,C_679] :
      ( m2_yellow_6('#skF_2'(A_677,B_678,C_679),A_677,B_678)
      | ~ r3_waybel_9(A_677,B_678,C_679)
      | ~ m1_subset_1(C_679,u1_struct_0(A_677))
      | ~ l1_waybel_0(B_678,A_677)
      | ~ v7_waybel_0(B_678)
      | ~ v4_orders_2(B_678)
      | v2_struct_0(B_678)
      | ~ l1_pre_topc(A_677)
      | ~ v2_pre_topc(A_677)
      | v2_struct_0(A_677) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_2162,plain,(
    ! [A_702,B_703,C_704] :
      ( v4_orders_2('#skF_2'(A_702,B_703,C_704))
      | ~ l1_struct_0(A_702)
      | ~ r3_waybel_9(A_702,B_703,C_704)
      | ~ m1_subset_1(C_704,u1_struct_0(A_702))
      | ~ l1_waybel_0(B_703,A_702)
      | ~ v7_waybel_0(B_703)
      | ~ v4_orders_2(B_703)
      | v2_struct_0(B_703)
      | ~ l1_pre_topc(A_702)
      | ~ v2_pre_topc(A_702)
      | v2_struct_0(A_702) ) ),
    inference(resolution,[status(thm)],[c_2064,c_14])).

tff(c_2164,plain,(
    ! [B_703] :
      ( v4_orders_2('#skF_2'('#skF_3',B_703,'#skF_5'))
      | ~ l1_struct_0('#skF_3')
      | ~ r3_waybel_9('#skF_3',B_703,'#skF_5')
      | ~ l1_waybel_0(B_703,'#skF_3')
      | ~ v7_waybel_0(B_703)
      | ~ v4_orders_2(B_703)
      | v2_struct_0(B_703)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_48,c_2162])).

tff(c_2167,plain,(
    ! [B_703] :
      ( v4_orders_2('#skF_2'('#skF_3',B_703,'#skF_5'))
      | ~ l1_struct_0('#skF_3')
      | ~ r3_waybel_9('#skF_3',B_703,'#skF_5')
      | ~ l1_waybel_0(B_703,'#skF_3')
      | ~ v7_waybel_0(B_703)
      | ~ v4_orders_2(B_703)
      | v2_struct_0(B_703)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_2164])).

tff(c_2168,plain,(
    ! [B_703] :
      ( v4_orders_2('#skF_2'('#skF_3',B_703,'#skF_5'))
      | ~ l1_struct_0('#skF_3')
      | ~ r3_waybel_9('#skF_3',B_703,'#skF_5')
      | ~ l1_waybel_0(B_703,'#skF_3')
      | ~ v7_waybel_0(B_703)
      | ~ v4_orders_2(B_703)
      | v2_struct_0(B_703) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_2167])).

tff(c_2169,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_2168])).

tff(c_2172,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_2169])).

tff(c_2176,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_2172])).

tff(c_2178,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_2168])).

tff(c_2177,plain,(
    ! [B_703] :
      ( v4_orders_2('#skF_2'('#skF_3',B_703,'#skF_5'))
      | ~ r3_waybel_9('#skF_3',B_703,'#skF_5')
      | ~ l1_waybel_0(B_703,'#skF_3')
      | ~ v7_waybel_0(B_703)
      | ~ v4_orders_2(B_703)
      | v2_struct_0(B_703) ) ),
    inference(splitRight,[status(thm)],[c_2168])).

tff(c_2187,plain,(
    ! [A_710,B_711,C_712] :
      ( v7_waybel_0('#skF_2'(A_710,B_711,C_712))
      | ~ l1_struct_0(A_710)
      | ~ r3_waybel_9(A_710,B_711,C_712)
      | ~ m1_subset_1(C_712,u1_struct_0(A_710))
      | ~ l1_waybel_0(B_711,A_710)
      | ~ v7_waybel_0(B_711)
      | ~ v4_orders_2(B_711)
      | v2_struct_0(B_711)
      | ~ l1_pre_topc(A_710)
      | ~ v2_pre_topc(A_710)
      | v2_struct_0(A_710) ) ),
    inference(resolution,[status(thm)],[c_2064,c_12])).

tff(c_2189,plain,(
    ! [B_711] :
      ( v7_waybel_0('#skF_2'('#skF_3',B_711,'#skF_5'))
      | ~ l1_struct_0('#skF_3')
      | ~ r3_waybel_9('#skF_3',B_711,'#skF_5')
      | ~ l1_waybel_0(B_711,'#skF_3')
      | ~ v7_waybel_0(B_711)
      | ~ v4_orders_2(B_711)
      | v2_struct_0(B_711)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_48,c_2187])).

tff(c_2192,plain,(
    ! [B_711] :
      ( v7_waybel_0('#skF_2'('#skF_3',B_711,'#skF_5'))
      | ~ r3_waybel_9('#skF_3',B_711,'#skF_5')
      | ~ l1_waybel_0(B_711,'#skF_3')
      | ~ v7_waybel_0(B_711)
      | ~ v4_orders_2(B_711)
      | v2_struct_0(B_711)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_2178,c_2189])).

tff(c_2193,plain,(
    ! [B_711] :
      ( v7_waybel_0('#skF_2'('#skF_3',B_711,'#skF_5'))
      | ~ r3_waybel_9('#skF_3',B_711,'#skF_5')
      | ~ l1_waybel_0(B_711,'#skF_3')
      | ~ v7_waybel_0(B_711)
      | ~ v4_orders_2(B_711)
      | v2_struct_0(B_711) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_2192])).

tff(c_2197,plain,(
    ! [A_718,B_719,C_720] :
      ( l1_waybel_0('#skF_2'(A_718,B_719,C_720),A_718)
      | ~ l1_struct_0(A_718)
      | ~ r3_waybel_9(A_718,B_719,C_720)
      | ~ m1_subset_1(C_720,u1_struct_0(A_718))
      | ~ l1_waybel_0(B_719,A_718)
      | ~ v7_waybel_0(B_719)
      | ~ v4_orders_2(B_719)
      | v2_struct_0(B_719)
      | ~ l1_pre_topc(A_718)
      | ~ v2_pre_topc(A_718)
      | v2_struct_0(A_718) ) ),
    inference(resolution,[status(thm)],[c_2064,c_10])).

tff(c_2199,plain,(
    ! [B_719] :
      ( l1_waybel_0('#skF_2'('#skF_3',B_719,'#skF_5'),'#skF_3')
      | ~ l1_struct_0('#skF_3')
      | ~ r3_waybel_9('#skF_3',B_719,'#skF_5')
      | ~ l1_waybel_0(B_719,'#skF_3')
      | ~ v7_waybel_0(B_719)
      | ~ v4_orders_2(B_719)
      | v2_struct_0(B_719)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_48,c_2197])).

tff(c_2202,plain,(
    ! [B_719] :
      ( l1_waybel_0('#skF_2'('#skF_3',B_719,'#skF_5'),'#skF_3')
      | ~ r3_waybel_9('#skF_3',B_719,'#skF_5')
      | ~ l1_waybel_0(B_719,'#skF_3')
      | ~ v7_waybel_0(B_719)
      | ~ v4_orders_2(B_719)
      | v2_struct_0(B_719)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_2178,c_2199])).

tff(c_2203,plain,(
    ! [B_719] :
      ( l1_waybel_0('#skF_2'('#skF_3',B_719,'#skF_5'),'#skF_3')
      | ~ r3_waybel_9('#skF_3',B_719,'#skF_5')
      | ~ l1_waybel_0(B_719,'#skF_3')
      | ~ v7_waybel_0(B_719)
      | ~ v4_orders_2(B_719)
      | v2_struct_0(B_719) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_2202])).

tff(c_2219,plain,(
    ! [A_728,B_729,C_730,B_731] :
      ( r1_waybel_0(A_728,'#skF_2'(A_728,B_729,C_730),B_731)
      | ~ r1_waybel_0(A_728,B_729,B_731)
      | ~ l1_struct_0(A_728)
      | ~ r3_waybel_9(A_728,B_729,C_730)
      | ~ m1_subset_1(C_730,u1_struct_0(A_728))
      | ~ l1_waybel_0(B_729,A_728)
      | ~ v7_waybel_0(B_729)
      | ~ v4_orders_2(B_729)
      | v2_struct_0(B_729)
      | ~ l1_pre_topc(A_728)
      | ~ v2_pre_topc(A_728)
      | v2_struct_0(A_728) ) ),
    inference(resolution,[status(thm)],[c_2064,c_22])).

tff(c_2119,plain,(
    ! [C_691,A_692,B_693] :
      ( r2_hidden(C_691,k10_yellow_6(A_692,'#skF_2'(A_692,B_693,C_691)))
      | ~ r3_waybel_9(A_692,B_693,C_691)
      | ~ m1_subset_1(C_691,u1_struct_0(A_692))
      | ~ l1_waybel_0(B_693,A_692)
      | ~ v7_waybel_0(B_693)
      | ~ v4_orders_2(B_693)
      | v2_struct_0(B_693)
      | ~ l1_pre_topc(A_692)
      | ~ v2_pre_topc(A_692)
      | v2_struct_0(A_692) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_1955,plain,(
    ~ v7_waybel_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_78,plain,(
    ! [D_85] :
      ( ~ r2_hidden('#skF_5',k10_yellow_6('#skF_3',D_85))
      | ~ r1_waybel_0('#skF_3',D_85,'#skF_4')
      | ~ l1_waybel_0(D_85,'#skF_3')
      | ~ v3_yellow_6(D_85,'#skF_3')
      | ~ v7_waybel_0(D_85)
      | ~ v4_orders_2(D_85)
      | v2_struct_0(D_85)
      | v7_waybel_0('#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_1987,plain,(
    ! [D_85] :
      ( ~ r2_hidden('#skF_5',k10_yellow_6('#skF_3',D_85))
      | ~ r1_waybel_0('#skF_3',D_85,'#skF_4')
      | ~ l1_waybel_0(D_85,'#skF_3')
      | ~ v3_yellow_6(D_85,'#skF_3')
      | ~ v7_waybel_0(D_85)
      | ~ v4_orders_2(D_85)
      | v2_struct_0(D_85) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1955,c_78])).

tff(c_2126,plain,(
    ! [B_693] :
      ( ~ r1_waybel_0('#skF_3','#skF_2'('#skF_3',B_693,'#skF_5'),'#skF_4')
      | ~ l1_waybel_0('#skF_2'('#skF_3',B_693,'#skF_5'),'#skF_3')
      | ~ v3_yellow_6('#skF_2'('#skF_3',B_693,'#skF_5'),'#skF_3')
      | ~ v7_waybel_0('#skF_2'('#skF_3',B_693,'#skF_5'))
      | ~ v4_orders_2('#skF_2'('#skF_3',B_693,'#skF_5'))
      | v2_struct_0('#skF_2'('#skF_3',B_693,'#skF_5'))
      | ~ r3_waybel_9('#skF_3',B_693,'#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
      | ~ l1_waybel_0(B_693,'#skF_3')
      | ~ v7_waybel_0(B_693)
      | ~ v4_orders_2(B_693)
      | v2_struct_0(B_693)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_2119,c_1987])).

tff(c_2136,plain,(
    ! [B_693] :
      ( ~ r1_waybel_0('#skF_3','#skF_2'('#skF_3',B_693,'#skF_5'),'#skF_4')
      | ~ l1_waybel_0('#skF_2'('#skF_3',B_693,'#skF_5'),'#skF_3')
      | ~ v3_yellow_6('#skF_2'('#skF_3',B_693,'#skF_5'),'#skF_3')
      | ~ v7_waybel_0('#skF_2'('#skF_3',B_693,'#skF_5'))
      | ~ v4_orders_2('#skF_2'('#skF_3',B_693,'#skF_5'))
      | v2_struct_0('#skF_2'('#skF_3',B_693,'#skF_5'))
      | ~ r3_waybel_9('#skF_3',B_693,'#skF_5')
      | ~ l1_waybel_0(B_693,'#skF_3')
      | ~ v7_waybel_0(B_693)
      | ~ v4_orders_2(B_693)
      | v2_struct_0(B_693)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_2126])).

tff(c_2137,plain,(
    ! [B_693] :
      ( ~ r1_waybel_0('#skF_3','#skF_2'('#skF_3',B_693,'#skF_5'),'#skF_4')
      | ~ l1_waybel_0('#skF_2'('#skF_3',B_693,'#skF_5'),'#skF_3')
      | ~ v3_yellow_6('#skF_2'('#skF_3',B_693,'#skF_5'),'#skF_3')
      | ~ v7_waybel_0('#skF_2'('#skF_3',B_693,'#skF_5'))
      | ~ v4_orders_2('#skF_2'('#skF_3',B_693,'#skF_5'))
      | v2_struct_0('#skF_2'('#skF_3',B_693,'#skF_5'))
      | ~ r3_waybel_9('#skF_3',B_693,'#skF_5')
      | ~ l1_waybel_0(B_693,'#skF_3')
      | ~ v7_waybel_0(B_693)
      | ~ v4_orders_2(B_693)
      | v2_struct_0(B_693) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_2136])).

tff(c_2223,plain,(
    ! [B_729] :
      ( ~ l1_waybel_0('#skF_2'('#skF_3',B_729,'#skF_5'),'#skF_3')
      | ~ v3_yellow_6('#skF_2'('#skF_3',B_729,'#skF_5'),'#skF_3')
      | ~ v7_waybel_0('#skF_2'('#skF_3',B_729,'#skF_5'))
      | ~ v4_orders_2('#skF_2'('#skF_3',B_729,'#skF_5'))
      | v2_struct_0('#skF_2'('#skF_3',B_729,'#skF_5'))
      | ~ r1_waybel_0('#skF_3',B_729,'#skF_4')
      | ~ l1_struct_0('#skF_3')
      | ~ r3_waybel_9('#skF_3',B_729,'#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
      | ~ l1_waybel_0(B_729,'#skF_3')
      | ~ v7_waybel_0(B_729)
      | ~ v4_orders_2(B_729)
      | v2_struct_0(B_729)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_2219,c_2137])).

tff(c_2226,plain,(
    ! [B_729] :
      ( ~ l1_waybel_0('#skF_2'('#skF_3',B_729,'#skF_5'),'#skF_3')
      | ~ v3_yellow_6('#skF_2'('#skF_3',B_729,'#skF_5'),'#skF_3')
      | ~ v7_waybel_0('#skF_2'('#skF_3',B_729,'#skF_5'))
      | ~ v4_orders_2('#skF_2'('#skF_3',B_729,'#skF_5'))
      | v2_struct_0('#skF_2'('#skF_3',B_729,'#skF_5'))
      | ~ r1_waybel_0('#skF_3',B_729,'#skF_4')
      | ~ r3_waybel_9('#skF_3',B_729,'#skF_5')
      | ~ l1_waybel_0(B_729,'#skF_3')
      | ~ v7_waybel_0(B_729)
      | ~ v4_orders_2(B_729)
      | v2_struct_0(B_729)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_2178,c_2223])).

tff(c_2232,plain,(
    ! [B_735] :
      ( ~ l1_waybel_0('#skF_2'('#skF_3',B_735,'#skF_5'),'#skF_3')
      | ~ v3_yellow_6('#skF_2'('#skF_3',B_735,'#skF_5'),'#skF_3')
      | ~ v7_waybel_0('#skF_2'('#skF_3',B_735,'#skF_5'))
      | ~ v4_orders_2('#skF_2'('#skF_3',B_735,'#skF_5'))
      | v2_struct_0('#skF_2'('#skF_3',B_735,'#skF_5'))
      | ~ r1_waybel_0('#skF_3',B_735,'#skF_4')
      | ~ r3_waybel_9('#skF_3',B_735,'#skF_5')
      | ~ l1_waybel_0(B_735,'#skF_3')
      | ~ v7_waybel_0(B_735)
      | ~ v4_orders_2(B_735)
      | v2_struct_0(B_735) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_2226])).

tff(c_2235,plain,(
    ! [B_735] :
      ( ~ r1_waybel_0('#skF_3',B_735,'#skF_4')
      | ~ r3_waybel_9('#skF_3',B_735,'#skF_5')
      | ~ l1_waybel_0(B_735,'#skF_3')
      | ~ v7_waybel_0(B_735)
      | ~ v4_orders_2(B_735)
      | v2_struct_0(B_735)
      | k10_yellow_6('#skF_3','#skF_2'('#skF_3',B_735,'#skF_5')) = k1_xboole_0
      | ~ l1_waybel_0('#skF_2'('#skF_3',B_735,'#skF_5'),'#skF_3')
      | ~ v7_waybel_0('#skF_2'('#skF_3',B_735,'#skF_5'))
      | ~ v4_orders_2('#skF_2'('#skF_3',B_735,'#skF_5'))
      | v2_struct_0('#skF_2'('#skF_3',B_735,'#skF_5'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_2,c_2232])).

tff(c_2238,plain,(
    ! [B_735] :
      ( ~ r1_waybel_0('#skF_3',B_735,'#skF_4')
      | ~ r3_waybel_9('#skF_3',B_735,'#skF_5')
      | ~ l1_waybel_0(B_735,'#skF_3')
      | ~ v7_waybel_0(B_735)
      | ~ v4_orders_2(B_735)
      | v2_struct_0(B_735)
      | k10_yellow_6('#skF_3','#skF_2'('#skF_3',B_735,'#skF_5')) = k1_xboole_0
      | ~ l1_waybel_0('#skF_2'('#skF_3',B_735,'#skF_5'),'#skF_3')
      | ~ v7_waybel_0('#skF_2'('#skF_3',B_735,'#skF_5'))
      | ~ v4_orders_2('#skF_2'('#skF_3',B_735,'#skF_5'))
      | v2_struct_0('#skF_2'('#skF_3',B_735,'#skF_5'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_2235])).

tff(c_2240,plain,(
    ! [B_736] :
      ( ~ r1_waybel_0('#skF_3',B_736,'#skF_4')
      | ~ r3_waybel_9('#skF_3',B_736,'#skF_5')
      | ~ l1_waybel_0(B_736,'#skF_3')
      | ~ v7_waybel_0(B_736)
      | ~ v4_orders_2(B_736)
      | v2_struct_0(B_736)
      | k10_yellow_6('#skF_3','#skF_2'('#skF_3',B_736,'#skF_5')) = k1_xboole_0
      | ~ l1_waybel_0('#skF_2'('#skF_3',B_736,'#skF_5'),'#skF_3')
      | ~ v7_waybel_0('#skF_2'('#skF_3',B_736,'#skF_5'))
      | ~ v4_orders_2('#skF_2'('#skF_3',B_736,'#skF_5'))
      | v2_struct_0('#skF_2'('#skF_3',B_736,'#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_2238])).

tff(c_2245,plain,(
    ! [B_737] :
      ( ~ r1_waybel_0('#skF_3',B_737,'#skF_4')
      | k10_yellow_6('#skF_3','#skF_2'('#skF_3',B_737,'#skF_5')) = k1_xboole_0
      | ~ v7_waybel_0('#skF_2'('#skF_3',B_737,'#skF_5'))
      | ~ v4_orders_2('#skF_2'('#skF_3',B_737,'#skF_5'))
      | v2_struct_0('#skF_2'('#skF_3',B_737,'#skF_5'))
      | ~ r3_waybel_9('#skF_3',B_737,'#skF_5')
      | ~ l1_waybel_0(B_737,'#skF_3')
      | ~ v7_waybel_0(B_737)
      | ~ v4_orders_2(B_737)
      | v2_struct_0(B_737) ) ),
    inference(resolution,[status(thm)],[c_2203,c_2240])).

tff(c_2256,plain,(
    ! [B_740] :
      ( ~ r1_waybel_0('#skF_3',B_740,'#skF_4')
      | k10_yellow_6('#skF_3','#skF_2'('#skF_3',B_740,'#skF_5')) = k1_xboole_0
      | ~ v4_orders_2('#skF_2'('#skF_3',B_740,'#skF_5'))
      | v2_struct_0('#skF_2'('#skF_3',B_740,'#skF_5'))
      | ~ r3_waybel_9('#skF_3',B_740,'#skF_5')
      | ~ l1_waybel_0(B_740,'#skF_3')
      | ~ v7_waybel_0(B_740)
      | ~ v4_orders_2(B_740)
      | v2_struct_0(B_740) ) ),
    inference(resolution,[status(thm)],[c_2193,c_2245])).

tff(c_2261,plain,(
    ! [B_741] :
      ( ~ r1_waybel_0('#skF_3',B_741,'#skF_4')
      | k10_yellow_6('#skF_3','#skF_2'('#skF_3',B_741,'#skF_5')) = k1_xboole_0
      | v2_struct_0('#skF_2'('#skF_3',B_741,'#skF_5'))
      | ~ r3_waybel_9('#skF_3',B_741,'#skF_5')
      | ~ l1_waybel_0(B_741,'#skF_3')
      | ~ v7_waybel_0(B_741)
      | ~ v4_orders_2(B_741)
      | v2_struct_0(B_741) ) ),
    inference(resolution,[status(thm)],[c_2177,c_2256])).

tff(c_2081,plain,(
    ! [A_677,B_678,C_679] :
      ( ~ v2_struct_0('#skF_2'(A_677,B_678,C_679))
      | ~ l1_struct_0(A_677)
      | ~ r3_waybel_9(A_677,B_678,C_679)
      | ~ m1_subset_1(C_679,u1_struct_0(A_677))
      | ~ l1_waybel_0(B_678,A_677)
      | ~ v7_waybel_0(B_678)
      | ~ v4_orders_2(B_678)
      | v2_struct_0(B_678)
      | ~ l1_pre_topc(A_677)
      | ~ v2_pre_topc(A_677)
      | v2_struct_0(A_677) ) ),
    inference(resolution,[status(thm)],[c_2064,c_16])).

tff(c_2263,plain,(
    ! [B_741] :
      ( ~ l1_struct_0('#skF_3')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r1_waybel_0('#skF_3',B_741,'#skF_4')
      | k10_yellow_6('#skF_3','#skF_2'('#skF_3',B_741,'#skF_5')) = k1_xboole_0
      | ~ r3_waybel_9('#skF_3',B_741,'#skF_5')
      | ~ l1_waybel_0(B_741,'#skF_3')
      | ~ v7_waybel_0(B_741)
      | ~ v4_orders_2(B_741)
      | v2_struct_0(B_741) ) ),
    inference(resolution,[status(thm)],[c_2261,c_2081])).

tff(c_2266,plain,(
    ! [B_741] :
      ( v2_struct_0('#skF_3')
      | ~ r1_waybel_0('#skF_3',B_741,'#skF_4')
      | k10_yellow_6('#skF_3','#skF_2'('#skF_3',B_741,'#skF_5')) = k1_xboole_0
      | ~ r3_waybel_9('#skF_3',B_741,'#skF_5')
      | ~ l1_waybel_0(B_741,'#skF_3')
      | ~ v7_waybel_0(B_741)
      | ~ v4_orders_2(B_741)
      | v2_struct_0(B_741) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_2178,c_2263])).

tff(c_2268,plain,(
    ! [B_742] :
      ( ~ r1_waybel_0('#skF_3',B_742,'#skF_4')
      | k10_yellow_6('#skF_3','#skF_2'('#skF_3',B_742,'#skF_5')) = k1_xboole_0
      | ~ r3_waybel_9('#skF_3',B_742,'#skF_5')
      | ~ l1_waybel_0(B_742,'#skF_3')
      | ~ v7_waybel_0(B_742)
      | ~ v4_orders_2(B_742)
      | v2_struct_0(B_742) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_2266])).

tff(c_2139,plain,(
    ! [A_692,B_693,C_691] :
      ( ~ v1_xboole_0(k10_yellow_6(A_692,'#skF_2'(A_692,B_693,C_691)))
      | ~ r3_waybel_9(A_692,B_693,C_691)
      | ~ m1_subset_1(C_691,u1_struct_0(A_692))
      | ~ l1_waybel_0(B_693,A_692)
      | ~ v7_waybel_0(B_693)
      | ~ v4_orders_2(B_693)
      | v2_struct_0(B_693)
      | ~ l1_pre_topc(A_692)
      | ~ v2_pre_topc(A_692)
      | v2_struct_0(A_692) ) ),
    inference(resolution,[status(thm)],[c_2119,c_46])).

tff(c_2280,plain,(
    ! [B_742] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r3_waybel_9('#skF_3',B_742,'#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
      | ~ l1_waybel_0(B_742,'#skF_3')
      | ~ v7_waybel_0(B_742)
      | ~ v4_orders_2(B_742)
      | v2_struct_0(B_742)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r1_waybel_0('#skF_3',B_742,'#skF_4')
      | ~ r3_waybel_9('#skF_3',B_742,'#skF_5')
      | ~ l1_waybel_0(B_742,'#skF_3')
      | ~ v7_waybel_0(B_742)
      | ~ v4_orders_2(B_742)
      | v2_struct_0(B_742) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2268,c_2139])).

tff(c_2304,plain,(
    ! [B_742] :
      ( v2_struct_0('#skF_3')
      | ~ r1_waybel_0('#skF_3',B_742,'#skF_4')
      | ~ r3_waybel_9('#skF_3',B_742,'#skF_5')
      | ~ l1_waybel_0(B_742,'#skF_3')
      | ~ v7_waybel_0(B_742)
      | ~ v4_orders_2(B_742)
      | v2_struct_0(B_742) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_89,c_2280])).

tff(c_2313,plain,(
    ! [B_743] :
      ( ~ r1_waybel_0('#skF_3',B_743,'#skF_4')
      | ~ r3_waybel_9('#skF_3',B_743,'#skF_5')
      | ~ l1_waybel_0(B_743,'#skF_3')
      | ~ v7_waybel_0(B_743)
      | ~ v4_orders_2(B_743)
      | v2_struct_0(B_743) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_2304])).

tff(c_2321,plain,
    ( ~ r1_waybel_0('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | ~ l1_waybel_0('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | ~ v7_waybel_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ v4_orders_2('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ r2_hidden('#skF_5',k2_pre_topc('#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2055,c_2313])).

tff(c_2328,plain,
    ( ~ r1_waybel_0('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1954,c_2027,c_2004,c_2041,c_2321])).

tff(c_2329,plain,(
    ~ r1_waybel_0('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_2016,c_2328])).

tff(c_2332,plain,
    ( ~ r2_hidden('#skF_5',k2_pre_topc('#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2048,c_2329])).

tff(c_2336,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1954,c_2332])).

tff(c_2337,plain,(
    r2_hidden('#skF_5',k2_pre_topc('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_2433,plain,(
    ! [A_784,B_785,C_786] :
      ( r1_waybel_0(A_784,'#skF_1'(A_784,B_785,C_786),B_785)
      | ~ r2_hidden(C_786,k2_pre_topc(A_784,B_785))
      | ~ m1_subset_1(C_786,u1_struct_0(A_784))
      | ~ m1_subset_1(B_785,k1_zfmisc_1(u1_struct_0(A_784)))
      | ~ l1_pre_topc(A_784)
      | ~ v2_pre_topc(A_784)
      | v2_struct_0(A_784) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_2435,plain,(
    ! [C_786] :
      ( r1_waybel_0('#skF_3','#skF_1'('#skF_3','#skF_4',C_786),'#skF_4')
      | ~ r2_hidden(C_786,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_786,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_50,c_2433])).

tff(c_2438,plain,(
    ! [C_786] :
      ( r1_waybel_0('#skF_3','#skF_1'('#skF_3','#skF_4',C_786),'#skF_4')
      | ~ r2_hidden(C_786,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_786,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_2435])).

tff(c_2439,plain,(
    ! [C_786] :
      ( r1_waybel_0('#skF_3','#skF_1'('#skF_3','#skF_4',C_786),'#skF_4')
      | ~ r2_hidden(C_786,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_786,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_2438])).

tff(c_2377,plain,(
    ! [A_763,B_764,C_765] :
      ( ~ v2_struct_0('#skF_1'(A_763,B_764,C_765))
      | ~ r2_hidden(C_765,k2_pre_topc(A_763,B_764))
      | ~ m1_subset_1(C_765,u1_struct_0(A_763))
      | ~ m1_subset_1(B_764,k1_zfmisc_1(u1_struct_0(A_763)))
      | ~ l1_pre_topc(A_763)
      | ~ v2_pre_topc(A_763)
      | v2_struct_0(A_763) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_2382,plain,
    ( ~ v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_2337,c_2377])).

tff(c_2386,plain,
    ( ~ v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_2382])).

tff(c_2387,plain,(
    ~ v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_2386])).

tff(c_2391,plain,(
    ! [A_770,B_771,C_772] :
      ( v4_orders_2('#skF_1'(A_770,B_771,C_772))
      | ~ r2_hidden(C_772,k2_pre_topc(A_770,B_771))
      | ~ m1_subset_1(C_772,u1_struct_0(A_770))
      | ~ m1_subset_1(B_771,k1_zfmisc_1(u1_struct_0(A_770)))
      | ~ l1_pre_topc(A_770)
      | ~ v2_pre_topc(A_770)
      | v2_struct_0(A_770) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_2396,plain,
    ( v4_orders_2('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_2337,c_2391])).

tff(c_2400,plain,
    ( v4_orders_2('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_2396])).

tff(c_2401,plain,(
    v4_orders_2('#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_2400])).

tff(c_2402,plain,(
    ! [A_773,B_774,C_775] :
      ( v7_waybel_0('#skF_1'(A_773,B_774,C_775))
      | ~ r2_hidden(C_775,k2_pre_topc(A_773,B_774))
      | ~ m1_subset_1(C_775,u1_struct_0(A_773))
      | ~ m1_subset_1(B_774,k1_zfmisc_1(u1_struct_0(A_773)))
      | ~ l1_pre_topc(A_773)
      | ~ v2_pre_topc(A_773)
      | v2_struct_0(A_773) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_2407,plain,
    ( v7_waybel_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_2337,c_2402])).

tff(c_2411,plain,
    ( v7_waybel_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_2407])).

tff(c_2412,plain,(
    v7_waybel_0('#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_2411])).

tff(c_2414,plain,(
    ! [A_777,B_778,C_779] :
      ( l1_waybel_0('#skF_1'(A_777,B_778,C_779),A_777)
      | ~ r2_hidden(C_779,k2_pre_topc(A_777,B_778))
      | ~ m1_subset_1(C_779,u1_struct_0(A_777))
      | ~ m1_subset_1(B_778,k1_zfmisc_1(u1_struct_0(A_777)))
      | ~ l1_pre_topc(A_777)
      | ~ v2_pre_topc(A_777)
      | v2_struct_0(A_777) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_2419,plain,
    ( l1_waybel_0('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_2337,c_2414])).

tff(c_2423,plain,
    ( l1_waybel_0('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_2419])).

tff(c_2424,plain,(
    l1_waybel_0('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_2423])).

tff(c_2425,plain,(
    ! [A_780,B_781,C_782] :
      ( r3_waybel_9(A_780,'#skF_1'(A_780,B_781,C_782),C_782)
      | ~ r2_hidden(C_782,k2_pre_topc(A_780,B_781))
      | ~ m1_subset_1(C_782,u1_struct_0(A_780))
      | ~ m1_subset_1(B_781,k1_zfmisc_1(u1_struct_0(A_780)))
      | ~ l1_pre_topc(A_780)
      | ~ v2_pre_topc(A_780)
      | v2_struct_0(A_780) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_2427,plain,(
    ! [C_782] :
      ( r3_waybel_9('#skF_3','#skF_1'('#skF_3','#skF_4',C_782),C_782)
      | ~ r2_hidden(C_782,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_782,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_50,c_2425])).

tff(c_2430,plain,(
    ! [C_782] :
      ( r3_waybel_9('#skF_3','#skF_1'('#skF_3','#skF_4',C_782),C_782)
      | ~ r2_hidden(C_782,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_782,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_2427])).

tff(c_2431,plain,(
    ! [C_782] :
      ( r3_waybel_9('#skF_3','#skF_1'('#skF_3','#skF_4',C_782),C_782)
      | ~ r2_hidden(C_782,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_782,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_2430])).

tff(c_2454,plain,(
    ! [A_794,B_795,C_796] :
      ( m2_yellow_6('#skF_2'(A_794,B_795,C_796),A_794,B_795)
      | ~ r3_waybel_9(A_794,B_795,C_796)
      | ~ m1_subset_1(C_796,u1_struct_0(A_794))
      | ~ l1_waybel_0(B_795,A_794)
      | ~ v7_waybel_0(B_795)
      | ~ v4_orders_2(B_795)
      | v2_struct_0(B_795)
      | ~ l1_pre_topc(A_794)
      | ~ v2_pre_topc(A_794)
      | v2_struct_0(A_794) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_2531,plain,(
    ! [A_812,B_813,C_814] :
      ( v7_waybel_0('#skF_2'(A_812,B_813,C_814))
      | ~ l1_struct_0(A_812)
      | ~ r3_waybel_9(A_812,B_813,C_814)
      | ~ m1_subset_1(C_814,u1_struct_0(A_812))
      | ~ l1_waybel_0(B_813,A_812)
      | ~ v7_waybel_0(B_813)
      | ~ v4_orders_2(B_813)
      | v2_struct_0(B_813)
      | ~ l1_pre_topc(A_812)
      | ~ v2_pre_topc(A_812)
      | v2_struct_0(A_812) ) ),
    inference(resolution,[status(thm)],[c_2454,c_12])).

tff(c_2533,plain,(
    ! [B_813] :
      ( v7_waybel_0('#skF_2'('#skF_3',B_813,'#skF_5'))
      | ~ l1_struct_0('#skF_3')
      | ~ r3_waybel_9('#skF_3',B_813,'#skF_5')
      | ~ l1_waybel_0(B_813,'#skF_3')
      | ~ v7_waybel_0(B_813)
      | ~ v4_orders_2(B_813)
      | v2_struct_0(B_813)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_48,c_2531])).

tff(c_2536,plain,(
    ! [B_813] :
      ( v7_waybel_0('#skF_2'('#skF_3',B_813,'#skF_5'))
      | ~ l1_struct_0('#skF_3')
      | ~ r3_waybel_9('#skF_3',B_813,'#skF_5')
      | ~ l1_waybel_0(B_813,'#skF_3')
      | ~ v7_waybel_0(B_813)
      | ~ v4_orders_2(B_813)
      | v2_struct_0(B_813)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_2533])).

tff(c_2537,plain,(
    ! [B_813] :
      ( v7_waybel_0('#skF_2'('#skF_3',B_813,'#skF_5'))
      | ~ l1_struct_0('#skF_3')
      | ~ r3_waybel_9('#skF_3',B_813,'#skF_5')
      | ~ l1_waybel_0(B_813,'#skF_3')
      | ~ v7_waybel_0(B_813)
      | ~ v4_orders_2(B_813)
      | v2_struct_0(B_813) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_2536])).

tff(c_2538,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_2537])).

tff(c_2548,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_2538])).

tff(c_2552,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_2548])).

tff(c_2554,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_2537])).

tff(c_2571,plain,(
    ! [A_825,B_826,C_827] :
      ( v4_orders_2('#skF_2'(A_825,B_826,C_827))
      | ~ l1_struct_0(A_825)
      | ~ r3_waybel_9(A_825,B_826,C_827)
      | ~ m1_subset_1(C_827,u1_struct_0(A_825))
      | ~ l1_waybel_0(B_826,A_825)
      | ~ v7_waybel_0(B_826)
      | ~ v4_orders_2(B_826)
      | v2_struct_0(B_826)
      | ~ l1_pre_topc(A_825)
      | ~ v2_pre_topc(A_825)
      | v2_struct_0(A_825) ) ),
    inference(resolution,[status(thm)],[c_2454,c_14])).

tff(c_2573,plain,(
    ! [B_826] :
      ( v4_orders_2('#skF_2'('#skF_3',B_826,'#skF_5'))
      | ~ l1_struct_0('#skF_3')
      | ~ r3_waybel_9('#skF_3',B_826,'#skF_5')
      | ~ l1_waybel_0(B_826,'#skF_3')
      | ~ v7_waybel_0(B_826)
      | ~ v4_orders_2(B_826)
      | v2_struct_0(B_826)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_48,c_2571])).

tff(c_2576,plain,(
    ! [B_826] :
      ( v4_orders_2('#skF_2'('#skF_3',B_826,'#skF_5'))
      | ~ r3_waybel_9('#skF_3',B_826,'#skF_5')
      | ~ l1_waybel_0(B_826,'#skF_3')
      | ~ v7_waybel_0(B_826)
      | ~ v4_orders_2(B_826)
      | v2_struct_0(B_826)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_2554,c_2573])).

tff(c_2577,plain,(
    ! [B_826] :
      ( v4_orders_2('#skF_2'('#skF_3',B_826,'#skF_5'))
      | ~ r3_waybel_9('#skF_3',B_826,'#skF_5')
      | ~ l1_waybel_0(B_826,'#skF_3')
      | ~ v7_waybel_0(B_826)
      | ~ v4_orders_2(B_826)
      | v2_struct_0(B_826) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_2576])).

tff(c_2553,plain,(
    ! [B_813] :
      ( v7_waybel_0('#skF_2'('#skF_3',B_813,'#skF_5'))
      | ~ r3_waybel_9('#skF_3',B_813,'#skF_5')
      | ~ l1_waybel_0(B_813,'#skF_3')
      | ~ v7_waybel_0(B_813)
      | ~ v4_orders_2(B_813)
      | v2_struct_0(B_813) ) ),
    inference(splitRight,[status(thm)],[c_2537])).

tff(c_2596,plain,(
    ! [A_839,B_840,C_841] :
      ( l1_waybel_0('#skF_2'(A_839,B_840,C_841),A_839)
      | ~ l1_struct_0(A_839)
      | ~ r3_waybel_9(A_839,B_840,C_841)
      | ~ m1_subset_1(C_841,u1_struct_0(A_839))
      | ~ l1_waybel_0(B_840,A_839)
      | ~ v7_waybel_0(B_840)
      | ~ v4_orders_2(B_840)
      | v2_struct_0(B_840)
      | ~ l1_pre_topc(A_839)
      | ~ v2_pre_topc(A_839)
      | v2_struct_0(A_839) ) ),
    inference(resolution,[status(thm)],[c_2454,c_10])).

tff(c_2598,plain,(
    ! [B_840] :
      ( l1_waybel_0('#skF_2'('#skF_3',B_840,'#skF_5'),'#skF_3')
      | ~ l1_struct_0('#skF_3')
      | ~ r3_waybel_9('#skF_3',B_840,'#skF_5')
      | ~ l1_waybel_0(B_840,'#skF_3')
      | ~ v7_waybel_0(B_840)
      | ~ v4_orders_2(B_840)
      | v2_struct_0(B_840)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_48,c_2596])).

tff(c_2601,plain,(
    ! [B_840] :
      ( l1_waybel_0('#skF_2'('#skF_3',B_840,'#skF_5'),'#skF_3')
      | ~ r3_waybel_9('#skF_3',B_840,'#skF_5')
      | ~ l1_waybel_0(B_840,'#skF_3')
      | ~ v7_waybel_0(B_840)
      | ~ v4_orders_2(B_840)
      | v2_struct_0(B_840)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_2554,c_2598])).

tff(c_2602,plain,(
    ! [B_840] :
      ( l1_waybel_0('#skF_2'('#skF_3',B_840,'#skF_5'),'#skF_3')
      | ~ r3_waybel_9('#skF_3',B_840,'#skF_5')
      | ~ l1_waybel_0(B_840,'#skF_3')
      | ~ v7_waybel_0(B_840)
      | ~ v4_orders_2(B_840)
      | v2_struct_0(B_840) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_2601])).

tff(c_2615,plain,(
    ! [A_848,B_849,C_850,B_851] :
      ( r1_waybel_0(A_848,'#skF_2'(A_848,B_849,C_850),B_851)
      | ~ r1_waybel_0(A_848,B_849,B_851)
      | ~ l1_struct_0(A_848)
      | ~ r3_waybel_9(A_848,B_849,C_850)
      | ~ m1_subset_1(C_850,u1_struct_0(A_848))
      | ~ l1_waybel_0(B_849,A_848)
      | ~ v7_waybel_0(B_849)
      | ~ v4_orders_2(B_849)
      | v2_struct_0(B_849)
      | ~ l1_pre_topc(A_848)
      | ~ v2_pre_topc(A_848)
      | v2_struct_0(A_848) ) ),
    inference(resolution,[status(thm)],[c_2454,c_22])).

tff(c_2495,plain,(
    ! [C_802,A_803,B_804] :
      ( r2_hidden(C_802,k10_yellow_6(A_803,'#skF_2'(A_803,B_804,C_802)))
      | ~ r3_waybel_9(A_803,B_804,C_802)
      | ~ m1_subset_1(C_802,u1_struct_0(A_803))
      | ~ l1_waybel_0(B_804,A_803)
      | ~ v7_waybel_0(B_804)
      | ~ v4_orders_2(B_804)
      | v2_struct_0(B_804)
      | ~ l1_pre_topc(A_803)
      | ~ v2_pre_topc(A_803)
      | v2_struct_0(A_803) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_2338,plain,(
    ~ v4_orders_2('#skF_6') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_82,plain,(
    ! [D_85] :
      ( ~ r2_hidden('#skF_5',k10_yellow_6('#skF_3',D_85))
      | ~ r1_waybel_0('#skF_3',D_85,'#skF_4')
      | ~ l1_waybel_0(D_85,'#skF_3')
      | ~ v3_yellow_6(D_85,'#skF_3')
      | ~ v7_waybel_0(D_85)
      | ~ v4_orders_2(D_85)
      | v2_struct_0(D_85)
      | v4_orders_2('#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_2365,plain,(
    ! [D_85] :
      ( ~ r2_hidden('#skF_5',k10_yellow_6('#skF_3',D_85))
      | ~ r1_waybel_0('#skF_3',D_85,'#skF_4')
      | ~ l1_waybel_0(D_85,'#skF_3')
      | ~ v3_yellow_6(D_85,'#skF_3')
      | ~ v7_waybel_0(D_85)
      | ~ v4_orders_2(D_85)
      | v2_struct_0(D_85) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2338,c_82])).

tff(c_2502,plain,(
    ! [B_804] :
      ( ~ r1_waybel_0('#skF_3','#skF_2'('#skF_3',B_804,'#skF_5'),'#skF_4')
      | ~ l1_waybel_0('#skF_2'('#skF_3',B_804,'#skF_5'),'#skF_3')
      | ~ v3_yellow_6('#skF_2'('#skF_3',B_804,'#skF_5'),'#skF_3')
      | ~ v7_waybel_0('#skF_2'('#skF_3',B_804,'#skF_5'))
      | ~ v4_orders_2('#skF_2'('#skF_3',B_804,'#skF_5'))
      | v2_struct_0('#skF_2'('#skF_3',B_804,'#skF_5'))
      | ~ r3_waybel_9('#skF_3',B_804,'#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
      | ~ l1_waybel_0(B_804,'#skF_3')
      | ~ v7_waybel_0(B_804)
      | ~ v4_orders_2(B_804)
      | v2_struct_0(B_804)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_2495,c_2365])).

tff(c_2512,plain,(
    ! [B_804] :
      ( ~ r1_waybel_0('#skF_3','#skF_2'('#skF_3',B_804,'#skF_5'),'#skF_4')
      | ~ l1_waybel_0('#skF_2'('#skF_3',B_804,'#skF_5'),'#skF_3')
      | ~ v3_yellow_6('#skF_2'('#skF_3',B_804,'#skF_5'),'#skF_3')
      | ~ v7_waybel_0('#skF_2'('#skF_3',B_804,'#skF_5'))
      | ~ v4_orders_2('#skF_2'('#skF_3',B_804,'#skF_5'))
      | v2_struct_0('#skF_2'('#skF_3',B_804,'#skF_5'))
      | ~ r3_waybel_9('#skF_3',B_804,'#skF_5')
      | ~ l1_waybel_0(B_804,'#skF_3')
      | ~ v7_waybel_0(B_804)
      | ~ v4_orders_2(B_804)
      | v2_struct_0(B_804)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_2502])).

tff(c_2513,plain,(
    ! [B_804] :
      ( ~ r1_waybel_0('#skF_3','#skF_2'('#skF_3',B_804,'#skF_5'),'#skF_4')
      | ~ l1_waybel_0('#skF_2'('#skF_3',B_804,'#skF_5'),'#skF_3')
      | ~ v3_yellow_6('#skF_2'('#skF_3',B_804,'#skF_5'),'#skF_3')
      | ~ v7_waybel_0('#skF_2'('#skF_3',B_804,'#skF_5'))
      | ~ v4_orders_2('#skF_2'('#skF_3',B_804,'#skF_5'))
      | v2_struct_0('#skF_2'('#skF_3',B_804,'#skF_5'))
      | ~ r3_waybel_9('#skF_3',B_804,'#skF_5')
      | ~ l1_waybel_0(B_804,'#skF_3')
      | ~ v7_waybel_0(B_804)
      | ~ v4_orders_2(B_804)
      | v2_struct_0(B_804) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_2512])).

tff(c_2619,plain,(
    ! [B_849] :
      ( ~ l1_waybel_0('#skF_2'('#skF_3',B_849,'#skF_5'),'#skF_3')
      | ~ v3_yellow_6('#skF_2'('#skF_3',B_849,'#skF_5'),'#skF_3')
      | ~ v7_waybel_0('#skF_2'('#skF_3',B_849,'#skF_5'))
      | ~ v4_orders_2('#skF_2'('#skF_3',B_849,'#skF_5'))
      | v2_struct_0('#skF_2'('#skF_3',B_849,'#skF_5'))
      | ~ r1_waybel_0('#skF_3',B_849,'#skF_4')
      | ~ l1_struct_0('#skF_3')
      | ~ r3_waybel_9('#skF_3',B_849,'#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
      | ~ l1_waybel_0(B_849,'#skF_3')
      | ~ v7_waybel_0(B_849)
      | ~ v4_orders_2(B_849)
      | v2_struct_0(B_849)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_2615,c_2513])).

tff(c_2622,plain,(
    ! [B_849] :
      ( ~ l1_waybel_0('#skF_2'('#skF_3',B_849,'#skF_5'),'#skF_3')
      | ~ v3_yellow_6('#skF_2'('#skF_3',B_849,'#skF_5'),'#skF_3')
      | ~ v7_waybel_0('#skF_2'('#skF_3',B_849,'#skF_5'))
      | ~ v4_orders_2('#skF_2'('#skF_3',B_849,'#skF_5'))
      | v2_struct_0('#skF_2'('#skF_3',B_849,'#skF_5'))
      | ~ r1_waybel_0('#skF_3',B_849,'#skF_4')
      | ~ r3_waybel_9('#skF_3',B_849,'#skF_5')
      | ~ l1_waybel_0(B_849,'#skF_3')
      | ~ v7_waybel_0(B_849)
      | ~ v4_orders_2(B_849)
      | v2_struct_0(B_849)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_2554,c_2619])).

tff(c_2624,plain,(
    ! [B_852] :
      ( ~ l1_waybel_0('#skF_2'('#skF_3',B_852,'#skF_5'),'#skF_3')
      | ~ v3_yellow_6('#skF_2'('#skF_3',B_852,'#skF_5'),'#skF_3')
      | ~ v7_waybel_0('#skF_2'('#skF_3',B_852,'#skF_5'))
      | ~ v4_orders_2('#skF_2'('#skF_3',B_852,'#skF_5'))
      | v2_struct_0('#skF_2'('#skF_3',B_852,'#skF_5'))
      | ~ r1_waybel_0('#skF_3',B_852,'#skF_4')
      | ~ r3_waybel_9('#skF_3',B_852,'#skF_5')
      | ~ l1_waybel_0(B_852,'#skF_3')
      | ~ v7_waybel_0(B_852)
      | ~ v4_orders_2(B_852)
      | v2_struct_0(B_852) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_2622])).

tff(c_2627,plain,(
    ! [B_852] :
      ( ~ r1_waybel_0('#skF_3',B_852,'#skF_4')
      | ~ r3_waybel_9('#skF_3',B_852,'#skF_5')
      | ~ l1_waybel_0(B_852,'#skF_3')
      | ~ v7_waybel_0(B_852)
      | ~ v4_orders_2(B_852)
      | v2_struct_0(B_852)
      | k10_yellow_6('#skF_3','#skF_2'('#skF_3',B_852,'#skF_5')) = k1_xboole_0
      | ~ l1_waybel_0('#skF_2'('#skF_3',B_852,'#skF_5'),'#skF_3')
      | ~ v7_waybel_0('#skF_2'('#skF_3',B_852,'#skF_5'))
      | ~ v4_orders_2('#skF_2'('#skF_3',B_852,'#skF_5'))
      | v2_struct_0('#skF_2'('#skF_3',B_852,'#skF_5'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_2,c_2624])).

tff(c_2630,plain,(
    ! [B_852] :
      ( ~ r1_waybel_0('#skF_3',B_852,'#skF_4')
      | ~ r3_waybel_9('#skF_3',B_852,'#skF_5')
      | ~ l1_waybel_0(B_852,'#skF_3')
      | ~ v7_waybel_0(B_852)
      | ~ v4_orders_2(B_852)
      | v2_struct_0(B_852)
      | k10_yellow_6('#skF_3','#skF_2'('#skF_3',B_852,'#skF_5')) = k1_xboole_0
      | ~ l1_waybel_0('#skF_2'('#skF_3',B_852,'#skF_5'),'#skF_3')
      | ~ v7_waybel_0('#skF_2'('#skF_3',B_852,'#skF_5'))
      | ~ v4_orders_2('#skF_2'('#skF_3',B_852,'#skF_5'))
      | v2_struct_0('#skF_2'('#skF_3',B_852,'#skF_5'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_2627])).

tff(c_2632,plain,(
    ! [B_853] :
      ( ~ r1_waybel_0('#skF_3',B_853,'#skF_4')
      | ~ r3_waybel_9('#skF_3',B_853,'#skF_5')
      | ~ l1_waybel_0(B_853,'#skF_3')
      | ~ v7_waybel_0(B_853)
      | ~ v4_orders_2(B_853)
      | v2_struct_0(B_853)
      | k10_yellow_6('#skF_3','#skF_2'('#skF_3',B_853,'#skF_5')) = k1_xboole_0
      | ~ l1_waybel_0('#skF_2'('#skF_3',B_853,'#skF_5'),'#skF_3')
      | ~ v7_waybel_0('#skF_2'('#skF_3',B_853,'#skF_5'))
      | ~ v4_orders_2('#skF_2'('#skF_3',B_853,'#skF_5'))
      | v2_struct_0('#skF_2'('#skF_3',B_853,'#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_2630])).

tff(c_2637,plain,(
    ! [B_854] :
      ( ~ r1_waybel_0('#skF_3',B_854,'#skF_4')
      | k10_yellow_6('#skF_3','#skF_2'('#skF_3',B_854,'#skF_5')) = k1_xboole_0
      | ~ v7_waybel_0('#skF_2'('#skF_3',B_854,'#skF_5'))
      | ~ v4_orders_2('#skF_2'('#skF_3',B_854,'#skF_5'))
      | v2_struct_0('#skF_2'('#skF_3',B_854,'#skF_5'))
      | ~ r3_waybel_9('#skF_3',B_854,'#skF_5')
      | ~ l1_waybel_0(B_854,'#skF_3')
      | ~ v7_waybel_0(B_854)
      | ~ v4_orders_2(B_854)
      | v2_struct_0(B_854) ) ),
    inference(resolution,[status(thm)],[c_2602,c_2632])).

tff(c_2646,plain,(
    ! [B_858] :
      ( ~ r1_waybel_0('#skF_3',B_858,'#skF_4')
      | k10_yellow_6('#skF_3','#skF_2'('#skF_3',B_858,'#skF_5')) = k1_xboole_0
      | ~ v4_orders_2('#skF_2'('#skF_3',B_858,'#skF_5'))
      | v2_struct_0('#skF_2'('#skF_3',B_858,'#skF_5'))
      | ~ r3_waybel_9('#skF_3',B_858,'#skF_5')
      | ~ l1_waybel_0(B_858,'#skF_3')
      | ~ v7_waybel_0(B_858)
      | ~ v4_orders_2(B_858)
      | v2_struct_0(B_858) ) ),
    inference(resolution,[status(thm)],[c_2553,c_2637])).

tff(c_2651,plain,(
    ! [B_859] :
      ( ~ r1_waybel_0('#skF_3',B_859,'#skF_4')
      | k10_yellow_6('#skF_3','#skF_2'('#skF_3',B_859,'#skF_5')) = k1_xboole_0
      | v2_struct_0('#skF_2'('#skF_3',B_859,'#skF_5'))
      | ~ r3_waybel_9('#skF_3',B_859,'#skF_5')
      | ~ l1_waybel_0(B_859,'#skF_3')
      | ~ v7_waybel_0(B_859)
      | ~ v4_orders_2(B_859)
      | v2_struct_0(B_859) ) ),
    inference(resolution,[status(thm)],[c_2577,c_2646])).

tff(c_2473,plain,(
    ! [A_794,B_795,C_796] :
      ( ~ v2_struct_0('#skF_2'(A_794,B_795,C_796))
      | ~ l1_struct_0(A_794)
      | ~ r3_waybel_9(A_794,B_795,C_796)
      | ~ m1_subset_1(C_796,u1_struct_0(A_794))
      | ~ l1_waybel_0(B_795,A_794)
      | ~ v7_waybel_0(B_795)
      | ~ v4_orders_2(B_795)
      | v2_struct_0(B_795)
      | ~ l1_pre_topc(A_794)
      | ~ v2_pre_topc(A_794)
      | v2_struct_0(A_794) ) ),
    inference(resolution,[status(thm)],[c_2454,c_16])).

tff(c_2653,plain,(
    ! [B_859] :
      ( ~ l1_struct_0('#skF_3')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r1_waybel_0('#skF_3',B_859,'#skF_4')
      | k10_yellow_6('#skF_3','#skF_2'('#skF_3',B_859,'#skF_5')) = k1_xboole_0
      | ~ r3_waybel_9('#skF_3',B_859,'#skF_5')
      | ~ l1_waybel_0(B_859,'#skF_3')
      | ~ v7_waybel_0(B_859)
      | ~ v4_orders_2(B_859)
      | v2_struct_0(B_859) ) ),
    inference(resolution,[status(thm)],[c_2651,c_2473])).

tff(c_2656,plain,(
    ! [B_859] :
      ( v2_struct_0('#skF_3')
      | ~ r1_waybel_0('#skF_3',B_859,'#skF_4')
      | k10_yellow_6('#skF_3','#skF_2'('#skF_3',B_859,'#skF_5')) = k1_xboole_0
      | ~ r3_waybel_9('#skF_3',B_859,'#skF_5')
      | ~ l1_waybel_0(B_859,'#skF_3')
      | ~ v7_waybel_0(B_859)
      | ~ v4_orders_2(B_859)
      | v2_struct_0(B_859) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_2554,c_2653])).

tff(c_2658,plain,(
    ! [B_860] :
      ( ~ r1_waybel_0('#skF_3',B_860,'#skF_4')
      | k10_yellow_6('#skF_3','#skF_2'('#skF_3',B_860,'#skF_5')) = k1_xboole_0
      | ~ r3_waybel_9('#skF_3',B_860,'#skF_5')
      | ~ l1_waybel_0(B_860,'#skF_3')
      | ~ v7_waybel_0(B_860)
      | ~ v4_orders_2(B_860)
      | v2_struct_0(B_860) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_2656])).

tff(c_2515,plain,(
    ! [A_803,B_804,C_802] :
      ( ~ v1_xboole_0(k10_yellow_6(A_803,'#skF_2'(A_803,B_804,C_802)))
      | ~ r3_waybel_9(A_803,B_804,C_802)
      | ~ m1_subset_1(C_802,u1_struct_0(A_803))
      | ~ l1_waybel_0(B_804,A_803)
      | ~ v7_waybel_0(B_804)
      | ~ v4_orders_2(B_804)
      | v2_struct_0(B_804)
      | ~ l1_pre_topc(A_803)
      | ~ v2_pre_topc(A_803)
      | v2_struct_0(A_803) ) ),
    inference(resolution,[status(thm)],[c_2495,c_46])).

tff(c_2670,plain,(
    ! [B_860] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r3_waybel_9('#skF_3',B_860,'#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
      | ~ l1_waybel_0(B_860,'#skF_3')
      | ~ v7_waybel_0(B_860)
      | ~ v4_orders_2(B_860)
      | v2_struct_0(B_860)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r1_waybel_0('#skF_3',B_860,'#skF_4')
      | ~ r3_waybel_9('#skF_3',B_860,'#skF_5')
      | ~ l1_waybel_0(B_860,'#skF_3')
      | ~ v7_waybel_0(B_860)
      | ~ v4_orders_2(B_860)
      | v2_struct_0(B_860) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2658,c_2515])).

tff(c_2694,plain,(
    ! [B_860] :
      ( v2_struct_0('#skF_3')
      | ~ r1_waybel_0('#skF_3',B_860,'#skF_4')
      | ~ r3_waybel_9('#skF_3',B_860,'#skF_5')
      | ~ l1_waybel_0(B_860,'#skF_3')
      | ~ v7_waybel_0(B_860)
      | ~ v4_orders_2(B_860)
      | v2_struct_0(B_860) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_89,c_2670])).

tff(c_2703,plain,(
    ! [B_861] :
      ( ~ r1_waybel_0('#skF_3',B_861,'#skF_4')
      | ~ r3_waybel_9('#skF_3',B_861,'#skF_5')
      | ~ l1_waybel_0(B_861,'#skF_3')
      | ~ v7_waybel_0(B_861)
      | ~ v4_orders_2(B_861)
      | v2_struct_0(B_861) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_2694])).

tff(c_2711,plain,
    ( ~ r1_waybel_0('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | ~ l1_waybel_0('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | ~ v7_waybel_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ v4_orders_2('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ r2_hidden('#skF_5',k2_pre_topc('#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2431,c_2703])).

tff(c_2718,plain,
    ( ~ r1_waybel_0('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_2337,c_2401,c_2412,c_2424,c_2711])).

tff(c_2719,plain,(
    ~ r1_waybel_0('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_2387,c_2718])).

tff(c_2722,plain,
    ( ~ r2_hidden('#skF_5',k2_pre_topc('#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2439,c_2719])).

tff(c_2726,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_2337,c_2722])).

tff(c_2727,plain,(
    r2_hidden('#skF_5',k2_pre_topc('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_2828,plain,(
    ! [A_904,B_905,C_906] :
      ( r1_waybel_0(A_904,'#skF_1'(A_904,B_905,C_906),B_905)
      | ~ r2_hidden(C_906,k2_pre_topc(A_904,B_905))
      | ~ m1_subset_1(C_906,u1_struct_0(A_904))
      | ~ m1_subset_1(B_905,k1_zfmisc_1(u1_struct_0(A_904)))
      | ~ l1_pre_topc(A_904)
      | ~ v2_pre_topc(A_904)
      | v2_struct_0(A_904) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_2830,plain,(
    ! [C_906] :
      ( r1_waybel_0('#skF_3','#skF_1'('#skF_3','#skF_4',C_906),'#skF_4')
      | ~ r2_hidden(C_906,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_906,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_50,c_2828])).

tff(c_2833,plain,(
    ! [C_906] :
      ( r1_waybel_0('#skF_3','#skF_1'('#skF_3','#skF_4',C_906),'#skF_4')
      | ~ r2_hidden(C_906,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_906,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_2830])).

tff(c_2834,plain,(
    ! [C_906] :
      ( r1_waybel_0('#skF_3','#skF_1'('#skF_3','#skF_4',C_906),'#skF_4')
      | ~ r2_hidden(C_906,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_906,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_2833])).

tff(c_2772,plain,(
    ! [A_883,B_884,C_885] :
      ( ~ v2_struct_0('#skF_1'(A_883,B_884,C_885))
      | ~ r2_hidden(C_885,k2_pre_topc(A_883,B_884))
      | ~ m1_subset_1(C_885,u1_struct_0(A_883))
      | ~ m1_subset_1(B_884,k1_zfmisc_1(u1_struct_0(A_883)))
      | ~ l1_pre_topc(A_883)
      | ~ v2_pre_topc(A_883)
      | v2_struct_0(A_883) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_2777,plain,
    ( ~ v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_2727,c_2772])).

tff(c_2781,plain,
    ( ~ v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_2777])).

tff(c_2782,plain,(
    ~ v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_2781])).

tff(c_2784,plain,(
    ! [A_890,B_891,C_892] :
      ( v4_orders_2('#skF_1'(A_890,B_891,C_892))
      | ~ r2_hidden(C_892,k2_pre_topc(A_890,B_891))
      | ~ m1_subset_1(C_892,u1_struct_0(A_890))
      | ~ m1_subset_1(B_891,k1_zfmisc_1(u1_struct_0(A_890)))
      | ~ l1_pre_topc(A_890)
      | ~ v2_pre_topc(A_890)
      | v2_struct_0(A_890) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_2789,plain,
    ( v4_orders_2('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_2727,c_2784])).

tff(c_2793,plain,
    ( v4_orders_2('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_2789])).

tff(c_2794,plain,(
    v4_orders_2('#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_2793])).

tff(c_2795,plain,(
    ! [A_893,B_894,C_895] :
      ( v7_waybel_0('#skF_1'(A_893,B_894,C_895))
      | ~ r2_hidden(C_895,k2_pre_topc(A_893,B_894))
      | ~ m1_subset_1(C_895,u1_struct_0(A_893))
      | ~ m1_subset_1(B_894,k1_zfmisc_1(u1_struct_0(A_893)))
      | ~ l1_pre_topc(A_893)
      | ~ v2_pre_topc(A_893)
      | v2_struct_0(A_893) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_2800,plain,
    ( v7_waybel_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_2727,c_2795])).

tff(c_2804,plain,
    ( v7_waybel_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_2800])).

tff(c_2805,plain,(
    v7_waybel_0('#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_2804])).

tff(c_2809,plain,(
    ! [A_897,B_898,C_899] :
      ( l1_waybel_0('#skF_1'(A_897,B_898,C_899),A_897)
      | ~ r2_hidden(C_899,k2_pre_topc(A_897,B_898))
      | ~ m1_subset_1(C_899,u1_struct_0(A_897))
      | ~ m1_subset_1(B_898,k1_zfmisc_1(u1_struct_0(A_897)))
      | ~ l1_pre_topc(A_897)
      | ~ v2_pre_topc(A_897)
      | v2_struct_0(A_897) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_2814,plain,
    ( l1_waybel_0('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_2727,c_2809])).

tff(c_2818,plain,
    ( l1_waybel_0('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_2814])).

tff(c_2819,plain,(
    l1_waybel_0('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_2818])).

tff(c_2820,plain,(
    ! [A_900,B_901,C_902] :
      ( r3_waybel_9(A_900,'#skF_1'(A_900,B_901,C_902),C_902)
      | ~ r2_hidden(C_902,k2_pre_topc(A_900,B_901))
      | ~ m1_subset_1(C_902,u1_struct_0(A_900))
      | ~ m1_subset_1(B_901,k1_zfmisc_1(u1_struct_0(A_900)))
      | ~ l1_pre_topc(A_900)
      | ~ v2_pre_topc(A_900)
      | v2_struct_0(A_900) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_2822,plain,(
    ! [C_902] :
      ( r3_waybel_9('#skF_3','#skF_1'('#skF_3','#skF_4',C_902),C_902)
      | ~ r2_hidden(C_902,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_902,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_50,c_2820])).

tff(c_2825,plain,(
    ! [C_902] :
      ( r3_waybel_9('#skF_3','#skF_1'('#skF_3','#skF_4',C_902),C_902)
      | ~ r2_hidden(C_902,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_902,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_2822])).

tff(c_2826,plain,(
    ! [C_902] :
      ( r3_waybel_9('#skF_3','#skF_1'('#skF_3','#skF_4',C_902),C_902)
      | ~ r2_hidden(C_902,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_902,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_2825])).

tff(c_2849,plain,(
    ! [A_914,B_915,C_916] :
      ( m2_yellow_6('#skF_2'(A_914,B_915,C_916),A_914,B_915)
      | ~ r3_waybel_9(A_914,B_915,C_916)
      | ~ m1_subset_1(C_916,u1_struct_0(A_914))
      | ~ l1_waybel_0(B_915,A_914)
      | ~ v7_waybel_0(B_915)
      | ~ v4_orders_2(B_915)
      | v2_struct_0(B_915)
      | ~ l1_pre_topc(A_914)
      | ~ v2_pre_topc(A_914)
      | v2_struct_0(A_914) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_2926,plain,(
    ! [A_932,B_933,C_934] :
      ( v4_orders_2('#skF_2'(A_932,B_933,C_934))
      | ~ l1_struct_0(A_932)
      | ~ r3_waybel_9(A_932,B_933,C_934)
      | ~ m1_subset_1(C_934,u1_struct_0(A_932))
      | ~ l1_waybel_0(B_933,A_932)
      | ~ v7_waybel_0(B_933)
      | ~ v4_orders_2(B_933)
      | v2_struct_0(B_933)
      | ~ l1_pre_topc(A_932)
      | ~ v2_pre_topc(A_932)
      | v2_struct_0(A_932) ) ),
    inference(resolution,[status(thm)],[c_2849,c_14])).

tff(c_2928,plain,(
    ! [B_933] :
      ( v4_orders_2('#skF_2'('#skF_3',B_933,'#skF_5'))
      | ~ l1_struct_0('#skF_3')
      | ~ r3_waybel_9('#skF_3',B_933,'#skF_5')
      | ~ l1_waybel_0(B_933,'#skF_3')
      | ~ v7_waybel_0(B_933)
      | ~ v4_orders_2(B_933)
      | v2_struct_0(B_933)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_48,c_2926])).

tff(c_2931,plain,(
    ! [B_933] :
      ( v4_orders_2('#skF_2'('#skF_3',B_933,'#skF_5'))
      | ~ l1_struct_0('#skF_3')
      | ~ r3_waybel_9('#skF_3',B_933,'#skF_5')
      | ~ l1_waybel_0(B_933,'#skF_3')
      | ~ v7_waybel_0(B_933)
      | ~ v4_orders_2(B_933)
      | v2_struct_0(B_933)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_2928])).

tff(c_2932,plain,(
    ! [B_933] :
      ( v4_orders_2('#skF_2'('#skF_3',B_933,'#skF_5'))
      | ~ l1_struct_0('#skF_3')
      | ~ r3_waybel_9('#skF_3',B_933,'#skF_5')
      | ~ l1_waybel_0(B_933,'#skF_3')
      | ~ v7_waybel_0(B_933)
      | ~ v4_orders_2(B_933)
      | v2_struct_0(B_933) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_2931])).

tff(c_2933,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_2932])).

tff(c_2943,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_2933])).

tff(c_2947,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_2943])).

tff(c_2949,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_2932])).

tff(c_2948,plain,(
    ! [B_933] :
      ( v4_orders_2('#skF_2'('#skF_3',B_933,'#skF_5'))
      | ~ r3_waybel_9('#skF_3',B_933,'#skF_5')
      | ~ l1_waybel_0(B_933,'#skF_3')
      | ~ v7_waybel_0(B_933)
      | ~ v4_orders_2(B_933)
      | v2_struct_0(B_933) ) ),
    inference(splitRight,[status(thm)],[c_2932])).

tff(c_2966,plain,(
    ! [A_945,B_946,C_947] :
      ( v7_waybel_0('#skF_2'(A_945,B_946,C_947))
      | ~ l1_struct_0(A_945)
      | ~ r3_waybel_9(A_945,B_946,C_947)
      | ~ m1_subset_1(C_947,u1_struct_0(A_945))
      | ~ l1_waybel_0(B_946,A_945)
      | ~ v7_waybel_0(B_946)
      | ~ v4_orders_2(B_946)
      | v2_struct_0(B_946)
      | ~ l1_pre_topc(A_945)
      | ~ v2_pre_topc(A_945)
      | v2_struct_0(A_945) ) ),
    inference(resolution,[status(thm)],[c_2849,c_12])).

tff(c_2968,plain,(
    ! [B_946] :
      ( v7_waybel_0('#skF_2'('#skF_3',B_946,'#skF_5'))
      | ~ l1_struct_0('#skF_3')
      | ~ r3_waybel_9('#skF_3',B_946,'#skF_5')
      | ~ l1_waybel_0(B_946,'#skF_3')
      | ~ v7_waybel_0(B_946)
      | ~ v4_orders_2(B_946)
      | v2_struct_0(B_946)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_48,c_2966])).

tff(c_2971,plain,(
    ! [B_946] :
      ( v7_waybel_0('#skF_2'('#skF_3',B_946,'#skF_5'))
      | ~ r3_waybel_9('#skF_3',B_946,'#skF_5')
      | ~ l1_waybel_0(B_946,'#skF_3')
      | ~ v7_waybel_0(B_946)
      | ~ v4_orders_2(B_946)
      | v2_struct_0(B_946)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_2949,c_2968])).

tff(c_2972,plain,(
    ! [B_946] :
      ( v7_waybel_0('#skF_2'('#skF_3',B_946,'#skF_5'))
      | ~ r3_waybel_9('#skF_3',B_946,'#skF_5')
      | ~ l1_waybel_0(B_946,'#skF_3')
      | ~ v7_waybel_0(B_946)
      | ~ v4_orders_2(B_946)
      | v2_struct_0(B_946) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_2971])).

tff(c_2991,plain,(
    ! [A_959,B_960,C_961] :
      ( l1_waybel_0('#skF_2'(A_959,B_960,C_961),A_959)
      | ~ l1_struct_0(A_959)
      | ~ r3_waybel_9(A_959,B_960,C_961)
      | ~ m1_subset_1(C_961,u1_struct_0(A_959))
      | ~ l1_waybel_0(B_960,A_959)
      | ~ v7_waybel_0(B_960)
      | ~ v4_orders_2(B_960)
      | v2_struct_0(B_960)
      | ~ l1_pre_topc(A_959)
      | ~ v2_pre_topc(A_959)
      | v2_struct_0(A_959) ) ),
    inference(resolution,[status(thm)],[c_2849,c_10])).

tff(c_2993,plain,(
    ! [B_960] :
      ( l1_waybel_0('#skF_2'('#skF_3',B_960,'#skF_5'),'#skF_3')
      | ~ l1_struct_0('#skF_3')
      | ~ r3_waybel_9('#skF_3',B_960,'#skF_5')
      | ~ l1_waybel_0(B_960,'#skF_3')
      | ~ v7_waybel_0(B_960)
      | ~ v4_orders_2(B_960)
      | v2_struct_0(B_960)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_48,c_2991])).

tff(c_2996,plain,(
    ! [B_960] :
      ( l1_waybel_0('#skF_2'('#skF_3',B_960,'#skF_5'),'#skF_3')
      | ~ r3_waybel_9('#skF_3',B_960,'#skF_5')
      | ~ l1_waybel_0(B_960,'#skF_3')
      | ~ v7_waybel_0(B_960)
      | ~ v4_orders_2(B_960)
      | v2_struct_0(B_960)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_2949,c_2993])).

tff(c_2997,plain,(
    ! [B_960] :
      ( l1_waybel_0('#skF_2'('#skF_3',B_960,'#skF_5'),'#skF_3')
      | ~ r3_waybel_9('#skF_3',B_960,'#skF_5')
      | ~ l1_waybel_0(B_960,'#skF_3')
      | ~ v7_waybel_0(B_960)
      | ~ v4_orders_2(B_960)
      | v2_struct_0(B_960) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_2996])).

tff(c_3010,plain,(
    ! [A_968,B_969,C_970,B_971] :
      ( r1_waybel_0(A_968,'#skF_2'(A_968,B_969,C_970),B_971)
      | ~ r1_waybel_0(A_968,B_969,B_971)
      | ~ l1_struct_0(A_968)
      | ~ r3_waybel_9(A_968,B_969,C_970)
      | ~ m1_subset_1(C_970,u1_struct_0(A_968))
      | ~ l1_waybel_0(B_969,A_968)
      | ~ v7_waybel_0(B_969)
      | ~ v4_orders_2(B_969)
      | v2_struct_0(B_969)
      | ~ l1_pre_topc(A_968)
      | ~ v2_pre_topc(A_968)
      | v2_struct_0(A_968) ) ),
    inference(resolution,[status(thm)],[c_2849,c_22])).

tff(c_2890,plain,(
    ! [C_922,A_923,B_924] :
      ( r2_hidden(C_922,k10_yellow_6(A_923,'#skF_2'(A_923,B_924,C_922)))
      | ~ r3_waybel_9(A_923,B_924,C_922)
      | ~ m1_subset_1(C_922,u1_struct_0(A_923))
      | ~ l1_waybel_0(B_924,A_923)
      | ~ v7_waybel_0(B_924)
      | ~ v4_orders_2(B_924)
      | v2_struct_0(B_924)
      | ~ l1_pre_topc(A_923)
      | ~ v2_pre_topc(A_923)
      | v2_struct_0(A_923) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_2728,plain,(
    v2_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_86,plain,(
    ! [D_85] :
      ( ~ r2_hidden('#skF_5',k10_yellow_6('#skF_3',D_85))
      | ~ r1_waybel_0('#skF_3',D_85,'#skF_4')
      | ~ l1_waybel_0(D_85,'#skF_3')
      | ~ v3_yellow_6(D_85,'#skF_3')
      | ~ v7_waybel_0(D_85)
      | ~ v4_orders_2(D_85)
      | v2_struct_0(D_85)
      | ~ v2_struct_0('#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_2766,plain,(
    ! [D_85] :
      ( ~ r2_hidden('#skF_5',k10_yellow_6('#skF_3',D_85))
      | ~ r1_waybel_0('#skF_3',D_85,'#skF_4')
      | ~ l1_waybel_0(D_85,'#skF_3')
      | ~ v3_yellow_6(D_85,'#skF_3')
      | ~ v7_waybel_0(D_85)
      | ~ v4_orders_2(D_85)
      | v2_struct_0(D_85) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2728,c_86])).

tff(c_2897,plain,(
    ! [B_924] :
      ( ~ r1_waybel_0('#skF_3','#skF_2'('#skF_3',B_924,'#skF_5'),'#skF_4')
      | ~ l1_waybel_0('#skF_2'('#skF_3',B_924,'#skF_5'),'#skF_3')
      | ~ v3_yellow_6('#skF_2'('#skF_3',B_924,'#skF_5'),'#skF_3')
      | ~ v7_waybel_0('#skF_2'('#skF_3',B_924,'#skF_5'))
      | ~ v4_orders_2('#skF_2'('#skF_3',B_924,'#skF_5'))
      | v2_struct_0('#skF_2'('#skF_3',B_924,'#skF_5'))
      | ~ r3_waybel_9('#skF_3',B_924,'#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
      | ~ l1_waybel_0(B_924,'#skF_3')
      | ~ v7_waybel_0(B_924)
      | ~ v4_orders_2(B_924)
      | v2_struct_0(B_924)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_2890,c_2766])).

tff(c_2907,plain,(
    ! [B_924] :
      ( ~ r1_waybel_0('#skF_3','#skF_2'('#skF_3',B_924,'#skF_5'),'#skF_4')
      | ~ l1_waybel_0('#skF_2'('#skF_3',B_924,'#skF_5'),'#skF_3')
      | ~ v3_yellow_6('#skF_2'('#skF_3',B_924,'#skF_5'),'#skF_3')
      | ~ v7_waybel_0('#skF_2'('#skF_3',B_924,'#skF_5'))
      | ~ v4_orders_2('#skF_2'('#skF_3',B_924,'#skF_5'))
      | v2_struct_0('#skF_2'('#skF_3',B_924,'#skF_5'))
      | ~ r3_waybel_9('#skF_3',B_924,'#skF_5')
      | ~ l1_waybel_0(B_924,'#skF_3')
      | ~ v7_waybel_0(B_924)
      | ~ v4_orders_2(B_924)
      | v2_struct_0(B_924)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_2897])).

tff(c_2908,plain,(
    ! [B_924] :
      ( ~ r1_waybel_0('#skF_3','#skF_2'('#skF_3',B_924,'#skF_5'),'#skF_4')
      | ~ l1_waybel_0('#skF_2'('#skF_3',B_924,'#skF_5'),'#skF_3')
      | ~ v3_yellow_6('#skF_2'('#skF_3',B_924,'#skF_5'),'#skF_3')
      | ~ v7_waybel_0('#skF_2'('#skF_3',B_924,'#skF_5'))
      | ~ v4_orders_2('#skF_2'('#skF_3',B_924,'#skF_5'))
      | v2_struct_0('#skF_2'('#skF_3',B_924,'#skF_5'))
      | ~ r3_waybel_9('#skF_3',B_924,'#skF_5')
      | ~ l1_waybel_0(B_924,'#skF_3')
      | ~ v7_waybel_0(B_924)
      | ~ v4_orders_2(B_924)
      | v2_struct_0(B_924) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_2907])).

tff(c_3014,plain,(
    ! [B_969] :
      ( ~ l1_waybel_0('#skF_2'('#skF_3',B_969,'#skF_5'),'#skF_3')
      | ~ v3_yellow_6('#skF_2'('#skF_3',B_969,'#skF_5'),'#skF_3')
      | ~ v7_waybel_0('#skF_2'('#skF_3',B_969,'#skF_5'))
      | ~ v4_orders_2('#skF_2'('#skF_3',B_969,'#skF_5'))
      | v2_struct_0('#skF_2'('#skF_3',B_969,'#skF_5'))
      | ~ r1_waybel_0('#skF_3',B_969,'#skF_4')
      | ~ l1_struct_0('#skF_3')
      | ~ r3_waybel_9('#skF_3',B_969,'#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
      | ~ l1_waybel_0(B_969,'#skF_3')
      | ~ v7_waybel_0(B_969)
      | ~ v4_orders_2(B_969)
      | v2_struct_0(B_969)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_3010,c_2908])).

tff(c_3017,plain,(
    ! [B_969] :
      ( ~ l1_waybel_0('#skF_2'('#skF_3',B_969,'#skF_5'),'#skF_3')
      | ~ v3_yellow_6('#skF_2'('#skF_3',B_969,'#skF_5'),'#skF_3')
      | ~ v7_waybel_0('#skF_2'('#skF_3',B_969,'#skF_5'))
      | ~ v4_orders_2('#skF_2'('#skF_3',B_969,'#skF_5'))
      | v2_struct_0('#skF_2'('#skF_3',B_969,'#skF_5'))
      | ~ r1_waybel_0('#skF_3',B_969,'#skF_4')
      | ~ r3_waybel_9('#skF_3',B_969,'#skF_5')
      | ~ l1_waybel_0(B_969,'#skF_3')
      | ~ v7_waybel_0(B_969)
      | ~ v4_orders_2(B_969)
      | v2_struct_0(B_969)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_2949,c_3014])).

tff(c_3019,plain,(
    ! [B_972] :
      ( ~ l1_waybel_0('#skF_2'('#skF_3',B_972,'#skF_5'),'#skF_3')
      | ~ v3_yellow_6('#skF_2'('#skF_3',B_972,'#skF_5'),'#skF_3')
      | ~ v7_waybel_0('#skF_2'('#skF_3',B_972,'#skF_5'))
      | ~ v4_orders_2('#skF_2'('#skF_3',B_972,'#skF_5'))
      | v2_struct_0('#skF_2'('#skF_3',B_972,'#skF_5'))
      | ~ r1_waybel_0('#skF_3',B_972,'#skF_4')
      | ~ r3_waybel_9('#skF_3',B_972,'#skF_5')
      | ~ l1_waybel_0(B_972,'#skF_3')
      | ~ v7_waybel_0(B_972)
      | ~ v4_orders_2(B_972)
      | v2_struct_0(B_972) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_3017])).

tff(c_3022,plain,(
    ! [B_972] :
      ( ~ r1_waybel_0('#skF_3',B_972,'#skF_4')
      | ~ r3_waybel_9('#skF_3',B_972,'#skF_5')
      | ~ l1_waybel_0(B_972,'#skF_3')
      | ~ v7_waybel_0(B_972)
      | ~ v4_orders_2(B_972)
      | v2_struct_0(B_972)
      | k10_yellow_6('#skF_3','#skF_2'('#skF_3',B_972,'#skF_5')) = k1_xboole_0
      | ~ l1_waybel_0('#skF_2'('#skF_3',B_972,'#skF_5'),'#skF_3')
      | ~ v7_waybel_0('#skF_2'('#skF_3',B_972,'#skF_5'))
      | ~ v4_orders_2('#skF_2'('#skF_3',B_972,'#skF_5'))
      | v2_struct_0('#skF_2'('#skF_3',B_972,'#skF_5'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_2,c_3019])).

tff(c_3025,plain,(
    ! [B_972] :
      ( ~ r1_waybel_0('#skF_3',B_972,'#skF_4')
      | ~ r3_waybel_9('#skF_3',B_972,'#skF_5')
      | ~ l1_waybel_0(B_972,'#skF_3')
      | ~ v7_waybel_0(B_972)
      | ~ v4_orders_2(B_972)
      | v2_struct_0(B_972)
      | k10_yellow_6('#skF_3','#skF_2'('#skF_3',B_972,'#skF_5')) = k1_xboole_0
      | ~ l1_waybel_0('#skF_2'('#skF_3',B_972,'#skF_5'),'#skF_3')
      | ~ v7_waybel_0('#skF_2'('#skF_3',B_972,'#skF_5'))
      | ~ v4_orders_2('#skF_2'('#skF_3',B_972,'#skF_5'))
      | v2_struct_0('#skF_2'('#skF_3',B_972,'#skF_5'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_3022])).

tff(c_3027,plain,(
    ! [B_973] :
      ( ~ r1_waybel_0('#skF_3',B_973,'#skF_4')
      | ~ r3_waybel_9('#skF_3',B_973,'#skF_5')
      | ~ l1_waybel_0(B_973,'#skF_3')
      | ~ v7_waybel_0(B_973)
      | ~ v4_orders_2(B_973)
      | v2_struct_0(B_973)
      | k10_yellow_6('#skF_3','#skF_2'('#skF_3',B_973,'#skF_5')) = k1_xboole_0
      | ~ l1_waybel_0('#skF_2'('#skF_3',B_973,'#skF_5'),'#skF_3')
      | ~ v7_waybel_0('#skF_2'('#skF_3',B_973,'#skF_5'))
      | ~ v4_orders_2('#skF_2'('#skF_3',B_973,'#skF_5'))
      | v2_struct_0('#skF_2'('#skF_3',B_973,'#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_3025])).

tff(c_3032,plain,(
    ! [B_974] :
      ( ~ r1_waybel_0('#skF_3',B_974,'#skF_4')
      | k10_yellow_6('#skF_3','#skF_2'('#skF_3',B_974,'#skF_5')) = k1_xboole_0
      | ~ v7_waybel_0('#skF_2'('#skF_3',B_974,'#skF_5'))
      | ~ v4_orders_2('#skF_2'('#skF_3',B_974,'#skF_5'))
      | v2_struct_0('#skF_2'('#skF_3',B_974,'#skF_5'))
      | ~ r3_waybel_9('#skF_3',B_974,'#skF_5')
      | ~ l1_waybel_0(B_974,'#skF_3')
      | ~ v7_waybel_0(B_974)
      | ~ v4_orders_2(B_974)
      | v2_struct_0(B_974) ) ),
    inference(resolution,[status(thm)],[c_2997,c_3027])).

tff(c_3041,plain,(
    ! [B_978] :
      ( ~ r1_waybel_0('#skF_3',B_978,'#skF_4')
      | k10_yellow_6('#skF_3','#skF_2'('#skF_3',B_978,'#skF_5')) = k1_xboole_0
      | ~ v4_orders_2('#skF_2'('#skF_3',B_978,'#skF_5'))
      | v2_struct_0('#skF_2'('#skF_3',B_978,'#skF_5'))
      | ~ r3_waybel_9('#skF_3',B_978,'#skF_5')
      | ~ l1_waybel_0(B_978,'#skF_3')
      | ~ v7_waybel_0(B_978)
      | ~ v4_orders_2(B_978)
      | v2_struct_0(B_978) ) ),
    inference(resolution,[status(thm)],[c_2972,c_3032])).

tff(c_3046,plain,(
    ! [B_979] :
      ( ~ r1_waybel_0('#skF_3',B_979,'#skF_4')
      | k10_yellow_6('#skF_3','#skF_2'('#skF_3',B_979,'#skF_5')) = k1_xboole_0
      | v2_struct_0('#skF_2'('#skF_3',B_979,'#skF_5'))
      | ~ r3_waybel_9('#skF_3',B_979,'#skF_5')
      | ~ l1_waybel_0(B_979,'#skF_3')
      | ~ v7_waybel_0(B_979)
      | ~ v4_orders_2(B_979)
      | v2_struct_0(B_979) ) ),
    inference(resolution,[status(thm)],[c_2948,c_3041])).

tff(c_2868,plain,(
    ! [A_914,B_915,C_916] :
      ( ~ v2_struct_0('#skF_2'(A_914,B_915,C_916))
      | ~ l1_struct_0(A_914)
      | ~ r3_waybel_9(A_914,B_915,C_916)
      | ~ m1_subset_1(C_916,u1_struct_0(A_914))
      | ~ l1_waybel_0(B_915,A_914)
      | ~ v7_waybel_0(B_915)
      | ~ v4_orders_2(B_915)
      | v2_struct_0(B_915)
      | ~ l1_pre_topc(A_914)
      | ~ v2_pre_topc(A_914)
      | v2_struct_0(A_914) ) ),
    inference(resolution,[status(thm)],[c_2849,c_16])).

tff(c_3048,plain,(
    ! [B_979] :
      ( ~ l1_struct_0('#skF_3')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r1_waybel_0('#skF_3',B_979,'#skF_4')
      | k10_yellow_6('#skF_3','#skF_2'('#skF_3',B_979,'#skF_5')) = k1_xboole_0
      | ~ r3_waybel_9('#skF_3',B_979,'#skF_5')
      | ~ l1_waybel_0(B_979,'#skF_3')
      | ~ v7_waybel_0(B_979)
      | ~ v4_orders_2(B_979)
      | v2_struct_0(B_979) ) ),
    inference(resolution,[status(thm)],[c_3046,c_2868])).

tff(c_3051,plain,(
    ! [B_979] :
      ( v2_struct_0('#skF_3')
      | ~ r1_waybel_0('#skF_3',B_979,'#skF_4')
      | k10_yellow_6('#skF_3','#skF_2'('#skF_3',B_979,'#skF_5')) = k1_xboole_0
      | ~ r3_waybel_9('#skF_3',B_979,'#skF_5')
      | ~ l1_waybel_0(B_979,'#skF_3')
      | ~ v7_waybel_0(B_979)
      | ~ v4_orders_2(B_979)
      | v2_struct_0(B_979) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_2949,c_3048])).

tff(c_3053,plain,(
    ! [B_980] :
      ( ~ r1_waybel_0('#skF_3',B_980,'#skF_4')
      | k10_yellow_6('#skF_3','#skF_2'('#skF_3',B_980,'#skF_5')) = k1_xboole_0
      | ~ r3_waybel_9('#skF_3',B_980,'#skF_5')
      | ~ l1_waybel_0(B_980,'#skF_3')
      | ~ v7_waybel_0(B_980)
      | ~ v4_orders_2(B_980)
      | v2_struct_0(B_980) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_3051])).

tff(c_2910,plain,(
    ! [A_923,B_924,C_922] :
      ( ~ v1_xboole_0(k10_yellow_6(A_923,'#skF_2'(A_923,B_924,C_922)))
      | ~ r3_waybel_9(A_923,B_924,C_922)
      | ~ m1_subset_1(C_922,u1_struct_0(A_923))
      | ~ l1_waybel_0(B_924,A_923)
      | ~ v7_waybel_0(B_924)
      | ~ v4_orders_2(B_924)
      | v2_struct_0(B_924)
      | ~ l1_pre_topc(A_923)
      | ~ v2_pre_topc(A_923)
      | v2_struct_0(A_923) ) ),
    inference(resolution,[status(thm)],[c_2890,c_46])).

tff(c_3065,plain,(
    ! [B_980] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r3_waybel_9('#skF_3',B_980,'#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
      | ~ l1_waybel_0(B_980,'#skF_3')
      | ~ v7_waybel_0(B_980)
      | ~ v4_orders_2(B_980)
      | v2_struct_0(B_980)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r1_waybel_0('#skF_3',B_980,'#skF_4')
      | ~ r3_waybel_9('#skF_3',B_980,'#skF_5')
      | ~ l1_waybel_0(B_980,'#skF_3')
      | ~ v7_waybel_0(B_980)
      | ~ v4_orders_2(B_980)
      | v2_struct_0(B_980) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3053,c_2910])).

tff(c_3089,plain,(
    ! [B_980] :
      ( v2_struct_0('#skF_3')
      | ~ r1_waybel_0('#skF_3',B_980,'#skF_4')
      | ~ r3_waybel_9('#skF_3',B_980,'#skF_5')
      | ~ l1_waybel_0(B_980,'#skF_3')
      | ~ v7_waybel_0(B_980)
      | ~ v4_orders_2(B_980)
      | v2_struct_0(B_980) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_89,c_3065])).

tff(c_3098,plain,(
    ! [B_981] :
      ( ~ r1_waybel_0('#skF_3',B_981,'#skF_4')
      | ~ r3_waybel_9('#skF_3',B_981,'#skF_5')
      | ~ l1_waybel_0(B_981,'#skF_3')
      | ~ v7_waybel_0(B_981)
      | ~ v4_orders_2(B_981)
      | v2_struct_0(B_981) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_3089])).

tff(c_3106,plain,
    ( ~ r1_waybel_0('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | ~ l1_waybel_0('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | ~ v7_waybel_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ v4_orders_2('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ r2_hidden('#skF_5',k2_pre_topc('#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2826,c_3098])).

tff(c_3113,plain,
    ( ~ r1_waybel_0('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_2727,c_2794,c_2805,c_2819,c_3106])).

tff(c_3114,plain,(
    ~ r1_waybel_0('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_2782,c_3113])).

tff(c_3117,plain,
    ( ~ r2_hidden('#skF_5',k2_pre_topc('#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2834,c_3114])).

tff(c_3121,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_2727,c_3117])).

%------------------------------------------------------------------------------
