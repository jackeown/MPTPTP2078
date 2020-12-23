%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:16 EST 2020

% Result     : Theorem 2.32s
% Output     : CNFRefutation 2.46s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 156 expanded)
%              Number of leaves         :   36 (  75 expanded)
%              Depth                    :   16
%              Number of atoms          :  262 ( 769 expanded)
%              Number of equality atoms :    3 (  41 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_waybel_0 > m1_connsp_2 > r2_hidden > r1_xboole_0 > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k2_relset_1 > u1_waybel_0 > k2_pre_topc > k10_yellow_6 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_3

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

tff(f_166,negated_conjecture,(
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

tff(f_29,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_136,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_waybel_0(B,A) )
         => r1_waybel_0(A,B,k2_relset_1(u1_struct_0(B),u1_struct_0(A),u1_waybel_0(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_9)).

tff(f_100,axiom,(
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

tff(f_50,axiom,(
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
                    ( m1_connsp_2(D,A,C)
                   => ~ r1_xboole_0(D,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_connsp_2)).

tff(f_82,axiom,(
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

tff(f_123,axiom,(
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

tff(c_50,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_48,plain,(
    v4_orders_2('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_46,plain,(
    v7_waybel_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_44,plain,(
    l1_waybel_0('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_54,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_2,plain,(
    ! [A_1] :
      ( l1_struct_0(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_38,plain,(
    k2_relset_1(u1_struct_0('#skF_7'),u1_struct_0('#skF_5'),u1_waybel_0('#skF_5','#skF_7')) = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_64,plain,(
    ! [A_136,B_137] :
      ( r1_waybel_0(A_136,B_137,k2_relset_1(u1_struct_0(B_137),u1_struct_0(A_136),u1_waybel_0(A_136,B_137)))
      | ~ l1_waybel_0(B_137,A_136)
      | v2_struct_0(B_137)
      | ~ l1_struct_0(A_136)
      | v2_struct_0(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_67,plain,
    ( r1_waybel_0('#skF_5','#skF_7','#skF_8')
    | ~ l1_waybel_0('#skF_7','#skF_5')
    | v2_struct_0('#skF_7')
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_64])).

tff(c_69,plain,
    ( r1_waybel_0('#skF_5','#skF_7','#skF_8')
    | v2_struct_0('#skF_7')
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_67])).

tff(c_70,plain,
    ( r1_waybel_0('#skF_5','#skF_7','#skF_8')
    | ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_50,c_69])).

tff(c_71,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_75,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_2,c_71])).

tff(c_79,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_75])).

tff(c_80,plain,(
    r1_waybel_0('#skF_5','#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_42,plain,(
    r2_hidden('#skF_6',k10_yellow_6('#skF_5','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_36,plain,(
    ~ r2_hidden('#skF_6',k2_pre_topc('#skF_5','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_52,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_81,plain,(
    l1_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_56,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_30,plain,(
    ! [A_108,B_109] :
      ( m1_subset_1(k10_yellow_6(A_108,B_109),k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ l1_waybel_0(B_109,A_108)
      | ~ v7_waybel_0(B_109)
      | ~ v4_orders_2(B_109)
      | v2_struct_0(B_109)
      | ~ l1_pre_topc(A_108)
      | ~ v2_pre_topc(A_108)
      | v2_struct_0(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_40,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_109,plain,(
    ! [A_156,B_157,C_158] :
      ( m1_connsp_2('#skF_1'(A_156,B_157,C_158),A_156,C_158)
      | r2_hidden(C_158,k2_pre_topc(A_156,B_157))
      | ~ m1_subset_1(C_158,u1_struct_0(A_156))
      | ~ m1_subset_1(B_157,k1_zfmisc_1(u1_struct_0(A_156)))
      | ~ l1_pre_topc(A_156)
      | ~ v2_pre_topc(A_156)
      | v2_struct_0(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_113,plain,(
    ! [C_158] :
      ( m1_connsp_2('#skF_1'('#skF_5','#skF_8',C_158),'#skF_5',C_158)
      | r2_hidden(C_158,k2_pre_topc('#skF_5','#skF_8'))
      | ~ m1_subset_1(C_158,u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_40,c_109])).

tff(c_117,plain,(
    ! [C_158] :
      ( m1_connsp_2('#skF_1'('#skF_5','#skF_8',C_158),'#skF_5',C_158)
      | r2_hidden(C_158,k2_pre_topc('#skF_5','#skF_8'))
      | ~ m1_subset_1(C_158,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_113])).

tff(c_118,plain,(
    ! [C_158] :
      ( m1_connsp_2('#skF_1'('#skF_5','#skF_8',C_158),'#skF_5',C_158)
      | r2_hidden(C_158,k2_pre_topc('#skF_5','#skF_8'))
      | ~ m1_subset_1(C_158,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_117])).

tff(c_138,plain,(
    ! [A_174,B_175,E_176,D_177] :
      ( r1_waybel_0(A_174,B_175,E_176)
      | ~ m1_connsp_2(E_176,A_174,D_177)
      | ~ r2_hidden(D_177,k10_yellow_6(A_174,B_175))
      | ~ m1_subset_1(D_177,u1_struct_0(A_174))
      | ~ m1_subset_1(k10_yellow_6(A_174,B_175),k1_zfmisc_1(u1_struct_0(A_174)))
      | ~ l1_waybel_0(B_175,A_174)
      | ~ v7_waybel_0(B_175)
      | ~ v4_orders_2(B_175)
      | v2_struct_0(B_175)
      | ~ l1_pre_topc(A_174)
      | ~ v2_pre_topc(A_174)
      | v2_struct_0(A_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_142,plain,(
    ! [B_175,C_158] :
      ( r1_waybel_0('#skF_5',B_175,'#skF_1'('#skF_5','#skF_8',C_158))
      | ~ r2_hidden(C_158,k10_yellow_6('#skF_5',B_175))
      | ~ m1_subset_1(k10_yellow_6('#skF_5',B_175),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_waybel_0(B_175,'#skF_5')
      | ~ v7_waybel_0(B_175)
      | ~ v4_orders_2(B_175)
      | v2_struct_0(B_175)
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | r2_hidden(C_158,k2_pre_topc('#skF_5','#skF_8'))
      | ~ m1_subset_1(C_158,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_118,c_138])).

tff(c_146,plain,(
    ! [B_175,C_158] :
      ( r1_waybel_0('#skF_5',B_175,'#skF_1'('#skF_5','#skF_8',C_158))
      | ~ r2_hidden(C_158,k10_yellow_6('#skF_5',B_175))
      | ~ m1_subset_1(k10_yellow_6('#skF_5',B_175),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_waybel_0(B_175,'#skF_5')
      | ~ v7_waybel_0(B_175)
      | ~ v4_orders_2(B_175)
      | v2_struct_0(B_175)
      | v2_struct_0('#skF_5')
      | r2_hidden(C_158,k2_pre_topc('#skF_5','#skF_8'))
      | ~ m1_subset_1(C_158,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_142])).

tff(c_148,plain,(
    ! [B_178,C_179] :
      ( r1_waybel_0('#skF_5',B_178,'#skF_1'('#skF_5','#skF_8',C_179))
      | ~ r2_hidden(C_179,k10_yellow_6('#skF_5',B_178))
      | ~ m1_subset_1(k10_yellow_6('#skF_5',B_178),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_waybel_0(B_178,'#skF_5')
      | ~ v7_waybel_0(B_178)
      | ~ v4_orders_2(B_178)
      | v2_struct_0(B_178)
      | r2_hidden(C_179,k2_pre_topc('#skF_5','#skF_8'))
      | ~ m1_subset_1(C_179,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_146])).

tff(c_151,plain,(
    ! [B_109,C_179] :
      ( r1_waybel_0('#skF_5',B_109,'#skF_1'('#skF_5','#skF_8',C_179))
      | ~ r2_hidden(C_179,k10_yellow_6('#skF_5',B_109))
      | r2_hidden(C_179,k2_pre_topc('#skF_5','#skF_8'))
      | ~ m1_subset_1(C_179,u1_struct_0('#skF_5'))
      | ~ l1_waybel_0(B_109,'#skF_5')
      | ~ v7_waybel_0(B_109)
      | ~ v4_orders_2(B_109)
      | v2_struct_0(B_109)
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_30,c_148])).

tff(c_154,plain,(
    ! [B_109,C_179] :
      ( r1_waybel_0('#skF_5',B_109,'#skF_1'('#skF_5','#skF_8',C_179))
      | ~ r2_hidden(C_179,k10_yellow_6('#skF_5',B_109))
      | r2_hidden(C_179,k2_pre_topc('#skF_5','#skF_8'))
      | ~ m1_subset_1(C_179,u1_struct_0('#skF_5'))
      | ~ l1_waybel_0(B_109,'#skF_5')
      | ~ v7_waybel_0(B_109)
      | ~ v4_orders_2(B_109)
      | v2_struct_0(B_109)
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_151])).

tff(c_160,plain,(
    ! [B_183,C_184] :
      ( r1_waybel_0('#skF_5',B_183,'#skF_1'('#skF_5','#skF_8',C_184))
      | ~ r2_hidden(C_184,k10_yellow_6('#skF_5',B_183))
      | r2_hidden(C_184,k2_pre_topc('#skF_5','#skF_8'))
      | ~ m1_subset_1(C_184,u1_struct_0('#skF_5'))
      | ~ l1_waybel_0(B_183,'#skF_5')
      | ~ v7_waybel_0(B_183)
      | ~ v4_orders_2(B_183)
      | v2_struct_0(B_183) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_154])).

tff(c_84,plain,(
    ! [A_146,B_147,C_148] :
      ( r1_xboole_0('#skF_1'(A_146,B_147,C_148),B_147)
      | r2_hidden(C_148,k2_pre_topc(A_146,B_147))
      | ~ m1_subset_1(C_148,u1_struct_0(A_146))
      | ~ m1_subset_1(B_147,k1_zfmisc_1(u1_struct_0(A_146)))
      | ~ l1_pre_topc(A_146)
      | ~ v2_pre_topc(A_146)
      | v2_struct_0(A_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_88,plain,(
    ! [C_148] :
      ( r1_xboole_0('#skF_1'('#skF_5','#skF_8',C_148),'#skF_8')
      | r2_hidden(C_148,k2_pre_topc('#skF_5','#skF_8'))
      | ~ m1_subset_1(C_148,u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_40,c_84])).

tff(c_92,plain,(
    ! [C_148] :
      ( r1_xboole_0('#skF_1'('#skF_5','#skF_8',C_148),'#skF_8')
      | r2_hidden(C_148,k2_pre_topc('#skF_5','#skF_8'))
      | ~ m1_subset_1(C_148,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_88])).

tff(c_94,plain,(
    ! [C_149] :
      ( r1_xboole_0('#skF_1'('#skF_5','#skF_8',C_149),'#skF_8')
      | r2_hidden(C_149,k2_pre_topc('#skF_5','#skF_8'))
      | ~ m1_subset_1(C_149,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_92])).

tff(c_97,plain,
    ( r1_xboole_0('#skF_1'('#skF_5','#skF_8','#skF_6'),'#skF_8')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_94,c_36])).

tff(c_100,plain,(
    r1_xboole_0('#skF_1'('#skF_5','#skF_8','#skF_6'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_97])).

tff(c_32,plain,(
    ! [C_119,D_120,A_110,B_116] :
      ( ~ r1_xboole_0(C_119,D_120)
      | ~ r1_waybel_0(A_110,B_116,D_120)
      | ~ r1_waybel_0(A_110,B_116,C_119)
      | ~ l1_waybel_0(B_116,A_110)
      | ~ v7_waybel_0(B_116)
      | ~ v4_orders_2(B_116)
      | v2_struct_0(B_116)
      | ~ l1_struct_0(A_110)
      | v2_struct_0(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_103,plain,(
    ! [A_110,B_116] :
      ( ~ r1_waybel_0(A_110,B_116,'#skF_8')
      | ~ r1_waybel_0(A_110,B_116,'#skF_1'('#skF_5','#skF_8','#skF_6'))
      | ~ l1_waybel_0(B_116,A_110)
      | ~ v7_waybel_0(B_116)
      | ~ v4_orders_2(B_116)
      | v2_struct_0(B_116)
      | ~ l1_struct_0(A_110)
      | v2_struct_0(A_110) ) ),
    inference(resolution,[status(thm)],[c_100,c_32])).

tff(c_164,plain,(
    ! [B_183] :
      ( ~ r1_waybel_0('#skF_5',B_183,'#skF_8')
      | ~ l1_struct_0('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r2_hidden('#skF_6',k10_yellow_6('#skF_5',B_183))
      | r2_hidden('#skF_6',k2_pre_topc('#skF_5','#skF_8'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
      | ~ l1_waybel_0(B_183,'#skF_5')
      | ~ v7_waybel_0(B_183)
      | ~ v4_orders_2(B_183)
      | v2_struct_0(B_183) ) ),
    inference(resolution,[status(thm)],[c_160,c_103])).

tff(c_167,plain,(
    ! [B_183] :
      ( ~ r1_waybel_0('#skF_5',B_183,'#skF_8')
      | v2_struct_0('#skF_5')
      | ~ r2_hidden('#skF_6',k10_yellow_6('#skF_5',B_183))
      | r2_hidden('#skF_6',k2_pre_topc('#skF_5','#skF_8'))
      | ~ l1_waybel_0(B_183,'#skF_5')
      | ~ v7_waybel_0(B_183)
      | ~ v4_orders_2(B_183)
      | v2_struct_0(B_183) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_81,c_164])).

tff(c_169,plain,(
    ! [B_185] :
      ( ~ r1_waybel_0('#skF_5',B_185,'#skF_8')
      | ~ r2_hidden('#skF_6',k10_yellow_6('#skF_5',B_185))
      | ~ l1_waybel_0(B_185,'#skF_5')
      | ~ v7_waybel_0(B_185)
      | ~ v4_orders_2(B_185)
      | v2_struct_0(B_185) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_58,c_167])).

tff(c_172,plain,
    ( ~ r1_waybel_0('#skF_5','#skF_7','#skF_8')
    | ~ l1_waybel_0('#skF_7','#skF_5')
    | ~ v7_waybel_0('#skF_7')
    | ~ v4_orders_2('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_42,c_169])).

tff(c_175,plain,(
    v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_80,c_172])).

tff(c_177,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_175])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.31  % Computer   : n025.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % DateTime   : Tue Dec  1 17:24:35 EST 2020
% 0.12/0.31  % CPUTime    : 
% 0.16/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.32/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.32/1.26  
% 2.32/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.32/1.27  %$ r1_waybel_0 > m1_connsp_2 > r2_hidden > r1_xboole_0 > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k2_relset_1 > u1_waybel_0 > k2_pre_topc > k10_yellow_6 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_3
% 2.32/1.27  
% 2.32/1.27  %Foreground sorts:
% 2.32/1.27  
% 2.32/1.27  
% 2.32/1.27  %Background operators:
% 2.32/1.27  
% 2.32/1.27  
% 2.32/1.27  %Foreground operators:
% 2.32/1.27  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.32/1.27  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.32/1.27  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 2.32/1.27  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.32/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.32/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.32/1.27  tff(k10_yellow_6, type, k10_yellow_6: ($i * $i) > $i).
% 2.32/1.27  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.32/1.27  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 2.32/1.27  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.32/1.27  tff('#skF_7', type, '#skF_7': $i).
% 2.32/1.27  tff('#skF_5', type, '#skF_5': $i).
% 2.32/1.27  tff(r1_waybel_0, type, r1_waybel_0: ($i * $i * $i) > $o).
% 2.32/1.27  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.32/1.27  tff('#skF_6', type, '#skF_6': $i).
% 2.32/1.27  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.32/1.27  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.32/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.32/1.27  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.32/1.27  tff(u1_waybel_0, type, u1_waybel_0: ($i * $i) > $i).
% 2.32/1.27  tff('#skF_8', type, '#skF_8': $i).
% 2.32/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.32/1.27  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 2.32/1.27  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.32/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.32/1.27  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.32/1.27  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.32/1.27  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.32/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.32/1.27  
% 2.46/1.28  tff(f_166, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((((~v2_struct_0(C) & v4_orders_2(C)) & v7_waybel_0(C)) & l1_waybel_0(C, A)) => (r2_hidden(B, k10_yellow_6(A, C)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ((D = k2_relset_1(u1_struct_0(C), u1_struct_0(A), u1_waybel_0(A, C))) => r2_hidden(B, k2_pre_topc(A, D)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_waybel_9)).
% 2.46/1.28  tff(f_29, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.46/1.28  tff(f_136, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => r1_waybel_0(A, B, k2_relset_1(u1_struct_0(B), u1_struct_0(A), u1_waybel_0(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_waybel_9)).
% 2.46/1.28  tff(f_100, axiom, (![A, B]: (((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => m1_subset_1(k10_yellow_6(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k10_yellow_6)).
% 2.46/1.28  tff(f_50, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, k2_pre_topc(A, B)) <=> (![D]: (m1_connsp_2(D, A, C) => ~r1_xboole_0(D, B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_connsp_2)).
% 2.46/1.28  tff(f_82, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = k10_yellow_6(A, B)) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) <=> (![E]: (m1_connsp_2(E, A, D) => r1_waybel_0(A, B, E))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_yellow_6)).
% 2.46/1.28  tff(f_123, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C, D]: ~((r1_waybel_0(A, B, C) & r1_waybel_0(A, B, D)) & r1_xboole_0(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_yellow_6)).
% 2.46/1.28  tff(c_50, plain, (~v2_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_166])).
% 2.46/1.28  tff(c_48, plain, (v4_orders_2('#skF_7')), inference(cnfTransformation, [status(thm)], [f_166])).
% 2.46/1.28  tff(c_46, plain, (v7_waybel_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_166])).
% 2.46/1.28  tff(c_44, plain, (l1_waybel_0('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_166])).
% 2.46/1.28  tff(c_54, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_166])).
% 2.46/1.28  tff(c_2, plain, (![A_1]: (l1_struct_0(A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.46/1.28  tff(c_58, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_166])).
% 2.46/1.28  tff(c_38, plain, (k2_relset_1(u1_struct_0('#skF_7'), u1_struct_0('#skF_5'), u1_waybel_0('#skF_5', '#skF_7'))='#skF_8'), inference(cnfTransformation, [status(thm)], [f_166])).
% 2.46/1.28  tff(c_64, plain, (![A_136, B_137]: (r1_waybel_0(A_136, B_137, k2_relset_1(u1_struct_0(B_137), u1_struct_0(A_136), u1_waybel_0(A_136, B_137))) | ~l1_waybel_0(B_137, A_136) | v2_struct_0(B_137) | ~l1_struct_0(A_136) | v2_struct_0(A_136))), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.46/1.28  tff(c_67, plain, (r1_waybel_0('#skF_5', '#skF_7', '#skF_8') | ~l1_waybel_0('#skF_7', '#skF_5') | v2_struct_0('#skF_7') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_38, c_64])).
% 2.46/1.28  tff(c_69, plain, (r1_waybel_0('#skF_5', '#skF_7', '#skF_8') | v2_struct_0('#skF_7') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_67])).
% 2.46/1.28  tff(c_70, plain, (r1_waybel_0('#skF_5', '#skF_7', '#skF_8') | ~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_58, c_50, c_69])).
% 2.46/1.28  tff(c_71, plain, (~l1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_70])).
% 2.46/1.28  tff(c_75, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_2, c_71])).
% 2.46/1.28  tff(c_79, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_75])).
% 2.46/1.28  tff(c_80, plain, (r1_waybel_0('#skF_5', '#skF_7', '#skF_8')), inference(splitRight, [status(thm)], [c_70])).
% 2.46/1.28  tff(c_42, plain, (r2_hidden('#skF_6', k10_yellow_6('#skF_5', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_166])).
% 2.46/1.28  tff(c_36, plain, (~r2_hidden('#skF_6', k2_pre_topc('#skF_5', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_166])).
% 2.46/1.28  tff(c_52, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_166])).
% 2.46/1.28  tff(c_81, plain, (l1_struct_0('#skF_5')), inference(splitRight, [status(thm)], [c_70])).
% 2.46/1.28  tff(c_56, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_166])).
% 2.46/1.28  tff(c_30, plain, (![A_108, B_109]: (m1_subset_1(k10_yellow_6(A_108, B_109), k1_zfmisc_1(u1_struct_0(A_108))) | ~l1_waybel_0(B_109, A_108) | ~v7_waybel_0(B_109) | ~v4_orders_2(B_109) | v2_struct_0(B_109) | ~l1_pre_topc(A_108) | ~v2_pre_topc(A_108) | v2_struct_0(A_108))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.46/1.28  tff(c_40, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_166])).
% 2.46/1.28  tff(c_109, plain, (![A_156, B_157, C_158]: (m1_connsp_2('#skF_1'(A_156, B_157, C_158), A_156, C_158) | r2_hidden(C_158, k2_pre_topc(A_156, B_157)) | ~m1_subset_1(C_158, u1_struct_0(A_156)) | ~m1_subset_1(B_157, k1_zfmisc_1(u1_struct_0(A_156))) | ~l1_pre_topc(A_156) | ~v2_pre_topc(A_156) | v2_struct_0(A_156))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.46/1.28  tff(c_113, plain, (![C_158]: (m1_connsp_2('#skF_1'('#skF_5', '#skF_8', C_158), '#skF_5', C_158) | r2_hidden(C_158, k2_pre_topc('#skF_5', '#skF_8')) | ~m1_subset_1(C_158, u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_40, c_109])).
% 2.46/1.29  tff(c_117, plain, (![C_158]: (m1_connsp_2('#skF_1'('#skF_5', '#skF_8', C_158), '#skF_5', C_158) | r2_hidden(C_158, k2_pre_topc('#skF_5', '#skF_8')) | ~m1_subset_1(C_158, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_113])).
% 2.46/1.29  tff(c_118, plain, (![C_158]: (m1_connsp_2('#skF_1'('#skF_5', '#skF_8', C_158), '#skF_5', C_158) | r2_hidden(C_158, k2_pre_topc('#skF_5', '#skF_8')) | ~m1_subset_1(C_158, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_58, c_117])).
% 2.46/1.29  tff(c_138, plain, (![A_174, B_175, E_176, D_177]: (r1_waybel_0(A_174, B_175, E_176) | ~m1_connsp_2(E_176, A_174, D_177) | ~r2_hidden(D_177, k10_yellow_6(A_174, B_175)) | ~m1_subset_1(D_177, u1_struct_0(A_174)) | ~m1_subset_1(k10_yellow_6(A_174, B_175), k1_zfmisc_1(u1_struct_0(A_174))) | ~l1_waybel_0(B_175, A_174) | ~v7_waybel_0(B_175) | ~v4_orders_2(B_175) | v2_struct_0(B_175) | ~l1_pre_topc(A_174) | ~v2_pre_topc(A_174) | v2_struct_0(A_174))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.46/1.29  tff(c_142, plain, (![B_175, C_158]: (r1_waybel_0('#skF_5', B_175, '#skF_1'('#skF_5', '#skF_8', C_158)) | ~r2_hidden(C_158, k10_yellow_6('#skF_5', B_175)) | ~m1_subset_1(k10_yellow_6('#skF_5', B_175), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_waybel_0(B_175, '#skF_5') | ~v7_waybel_0(B_175) | ~v4_orders_2(B_175) | v2_struct_0(B_175) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | r2_hidden(C_158, k2_pre_topc('#skF_5', '#skF_8')) | ~m1_subset_1(C_158, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_118, c_138])).
% 2.46/1.29  tff(c_146, plain, (![B_175, C_158]: (r1_waybel_0('#skF_5', B_175, '#skF_1'('#skF_5', '#skF_8', C_158)) | ~r2_hidden(C_158, k10_yellow_6('#skF_5', B_175)) | ~m1_subset_1(k10_yellow_6('#skF_5', B_175), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_waybel_0(B_175, '#skF_5') | ~v7_waybel_0(B_175) | ~v4_orders_2(B_175) | v2_struct_0(B_175) | v2_struct_0('#skF_5') | r2_hidden(C_158, k2_pre_topc('#skF_5', '#skF_8')) | ~m1_subset_1(C_158, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_142])).
% 2.46/1.29  tff(c_148, plain, (![B_178, C_179]: (r1_waybel_0('#skF_5', B_178, '#skF_1'('#skF_5', '#skF_8', C_179)) | ~r2_hidden(C_179, k10_yellow_6('#skF_5', B_178)) | ~m1_subset_1(k10_yellow_6('#skF_5', B_178), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_waybel_0(B_178, '#skF_5') | ~v7_waybel_0(B_178) | ~v4_orders_2(B_178) | v2_struct_0(B_178) | r2_hidden(C_179, k2_pre_topc('#skF_5', '#skF_8')) | ~m1_subset_1(C_179, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_58, c_146])).
% 2.46/1.29  tff(c_151, plain, (![B_109, C_179]: (r1_waybel_0('#skF_5', B_109, '#skF_1'('#skF_5', '#skF_8', C_179)) | ~r2_hidden(C_179, k10_yellow_6('#skF_5', B_109)) | r2_hidden(C_179, k2_pre_topc('#skF_5', '#skF_8')) | ~m1_subset_1(C_179, u1_struct_0('#skF_5')) | ~l1_waybel_0(B_109, '#skF_5') | ~v7_waybel_0(B_109) | ~v4_orders_2(B_109) | v2_struct_0(B_109) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_30, c_148])).
% 2.46/1.29  tff(c_154, plain, (![B_109, C_179]: (r1_waybel_0('#skF_5', B_109, '#skF_1'('#skF_5', '#skF_8', C_179)) | ~r2_hidden(C_179, k10_yellow_6('#skF_5', B_109)) | r2_hidden(C_179, k2_pre_topc('#skF_5', '#skF_8')) | ~m1_subset_1(C_179, u1_struct_0('#skF_5')) | ~l1_waybel_0(B_109, '#skF_5') | ~v7_waybel_0(B_109) | ~v4_orders_2(B_109) | v2_struct_0(B_109) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_151])).
% 2.46/1.29  tff(c_160, plain, (![B_183, C_184]: (r1_waybel_0('#skF_5', B_183, '#skF_1'('#skF_5', '#skF_8', C_184)) | ~r2_hidden(C_184, k10_yellow_6('#skF_5', B_183)) | r2_hidden(C_184, k2_pre_topc('#skF_5', '#skF_8')) | ~m1_subset_1(C_184, u1_struct_0('#skF_5')) | ~l1_waybel_0(B_183, '#skF_5') | ~v7_waybel_0(B_183) | ~v4_orders_2(B_183) | v2_struct_0(B_183))), inference(negUnitSimplification, [status(thm)], [c_58, c_154])).
% 2.46/1.29  tff(c_84, plain, (![A_146, B_147, C_148]: (r1_xboole_0('#skF_1'(A_146, B_147, C_148), B_147) | r2_hidden(C_148, k2_pre_topc(A_146, B_147)) | ~m1_subset_1(C_148, u1_struct_0(A_146)) | ~m1_subset_1(B_147, k1_zfmisc_1(u1_struct_0(A_146))) | ~l1_pre_topc(A_146) | ~v2_pre_topc(A_146) | v2_struct_0(A_146))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.46/1.29  tff(c_88, plain, (![C_148]: (r1_xboole_0('#skF_1'('#skF_5', '#skF_8', C_148), '#skF_8') | r2_hidden(C_148, k2_pre_topc('#skF_5', '#skF_8')) | ~m1_subset_1(C_148, u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_40, c_84])).
% 2.46/1.29  tff(c_92, plain, (![C_148]: (r1_xboole_0('#skF_1'('#skF_5', '#skF_8', C_148), '#skF_8') | r2_hidden(C_148, k2_pre_topc('#skF_5', '#skF_8')) | ~m1_subset_1(C_148, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_88])).
% 2.46/1.29  tff(c_94, plain, (![C_149]: (r1_xboole_0('#skF_1'('#skF_5', '#skF_8', C_149), '#skF_8') | r2_hidden(C_149, k2_pre_topc('#skF_5', '#skF_8')) | ~m1_subset_1(C_149, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_58, c_92])).
% 2.46/1.29  tff(c_97, plain, (r1_xboole_0('#skF_1'('#skF_5', '#skF_8', '#skF_6'), '#skF_8') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_94, c_36])).
% 2.46/1.29  tff(c_100, plain, (r1_xboole_0('#skF_1'('#skF_5', '#skF_8', '#skF_6'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_97])).
% 2.46/1.29  tff(c_32, plain, (![C_119, D_120, A_110, B_116]: (~r1_xboole_0(C_119, D_120) | ~r1_waybel_0(A_110, B_116, D_120) | ~r1_waybel_0(A_110, B_116, C_119) | ~l1_waybel_0(B_116, A_110) | ~v7_waybel_0(B_116) | ~v4_orders_2(B_116) | v2_struct_0(B_116) | ~l1_struct_0(A_110) | v2_struct_0(A_110))), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.46/1.29  tff(c_103, plain, (![A_110, B_116]: (~r1_waybel_0(A_110, B_116, '#skF_8') | ~r1_waybel_0(A_110, B_116, '#skF_1'('#skF_5', '#skF_8', '#skF_6')) | ~l1_waybel_0(B_116, A_110) | ~v7_waybel_0(B_116) | ~v4_orders_2(B_116) | v2_struct_0(B_116) | ~l1_struct_0(A_110) | v2_struct_0(A_110))), inference(resolution, [status(thm)], [c_100, c_32])).
% 2.46/1.29  tff(c_164, plain, (![B_183]: (~r1_waybel_0('#skF_5', B_183, '#skF_8') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5') | ~r2_hidden('#skF_6', k10_yellow_6('#skF_5', B_183)) | r2_hidden('#skF_6', k2_pre_topc('#skF_5', '#skF_8')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l1_waybel_0(B_183, '#skF_5') | ~v7_waybel_0(B_183) | ~v4_orders_2(B_183) | v2_struct_0(B_183))), inference(resolution, [status(thm)], [c_160, c_103])).
% 2.46/1.29  tff(c_167, plain, (![B_183]: (~r1_waybel_0('#skF_5', B_183, '#skF_8') | v2_struct_0('#skF_5') | ~r2_hidden('#skF_6', k10_yellow_6('#skF_5', B_183)) | r2_hidden('#skF_6', k2_pre_topc('#skF_5', '#skF_8')) | ~l1_waybel_0(B_183, '#skF_5') | ~v7_waybel_0(B_183) | ~v4_orders_2(B_183) | v2_struct_0(B_183))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_81, c_164])).
% 2.46/1.29  tff(c_169, plain, (![B_185]: (~r1_waybel_0('#skF_5', B_185, '#skF_8') | ~r2_hidden('#skF_6', k10_yellow_6('#skF_5', B_185)) | ~l1_waybel_0(B_185, '#skF_5') | ~v7_waybel_0(B_185) | ~v4_orders_2(B_185) | v2_struct_0(B_185))), inference(negUnitSimplification, [status(thm)], [c_36, c_58, c_167])).
% 2.46/1.29  tff(c_172, plain, (~r1_waybel_0('#skF_5', '#skF_7', '#skF_8') | ~l1_waybel_0('#skF_7', '#skF_5') | ~v7_waybel_0('#skF_7') | ~v4_orders_2('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_42, c_169])).
% 2.46/1.29  tff(c_175, plain, (v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_80, c_172])).
% 2.46/1.29  tff(c_177, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_175])).
% 2.46/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.46/1.29  
% 2.46/1.29  Inference rules
% 2.46/1.29  ----------------------
% 2.46/1.29  #Ref     : 0
% 2.46/1.29  #Sup     : 20
% 2.46/1.29  #Fact    : 0
% 2.46/1.29  #Define  : 0
% 2.46/1.29  #Split   : 1
% 2.46/1.29  #Chain   : 0
% 2.46/1.29  #Close   : 0
% 2.46/1.29  
% 2.46/1.29  Ordering : KBO
% 2.46/1.29  
% 2.46/1.29  Simplification rules
% 2.46/1.29  ----------------------
% 2.46/1.29  #Subsume      : 2
% 2.46/1.29  #Demod        : 21
% 2.46/1.29  #Tautology    : 3
% 2.46/1.29  #SimpNegUnit  : 8
% 2.46/1.29  #BackRed      : 0
% 2.46/1.29  
% 2.46/1.29  #Partial instantiations: 0
% 2.46/1.29  #Strategies tried      : 1
% 2.46/1.29  
% 2.46/1.29  Timing (in seconds)
% 2.46/1.29  ----------------------
% 2.46/1.29  Preprocessing        : 0.33
% 2.46/1.29  Parsing              : 0.18
% 2.46/1.29  CNF conversion       : 0.03
% 2.46/1.29  Main loop            : 0.21
% 2.46/1.29  Inferencing          : 0.09
% 2.46/1.29  Reduction            : 0.06
% 2.46/1.29  Demodulation         : 0.04
% 2.46/1.29  BG Simplification    : 0.02
% 2.46/1.29  Subsumption          : 0.03
% 2.46/1.29  Abstraction          : 0.01
% 2.46/1.29  MUC search           : 0.00
% 2.46/1.29  Cooper               : 0.00
% 2.46/1.29  Total                : 0.58
% 2.46/1.29  Index Insertion      : 0.00
% 2.46/1.29  Index Deletion       : 0.00
% 2.46/1.29  Index Matching       : 0.00
% 2.46/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
