%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT2030+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:47 EST 2020

% Result     : Theorem 2.51s
% Output     : CNFRefutation 2.51s
% Verified   : 
% Statistics : Number of formulae       :   57 (  69 expanded)
%              Number of leaves         :   32 (  43 expanded)
%              Depth                    :    9
%              Number of atoms          :  172 ( 282 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_waybel_9 > r2_waybel_0 > r1_waybel_0 > m1_connsp_2 > r2_hidden > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k10_yellow_6 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff(r2_waybel_0,type,(
    r2_waybel_0: ( $i * $i * $i ) > $o )).

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

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_146,negated_conjecture,(
    ~ ! [A] :
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

tff(f_101,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_97,axiom,(
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
          ( ( ~ v2_struct_0(B)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r3_waybel_9(A,B,C)
              <=> ! [D] :
                    ( m1_connsp_2(D,A,C)
                   => r2_waybel_0(A,B,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_waybel_9)).

tff(f_56,axiom,(
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

tff(f_121,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v4_orders_2(B)
            & v7_waybel_0(B)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( r1_waybel_0(A,B,C)
             => r2_waybel_0(A,B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_yellow_6)).

tff(c_48,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_30,plain,(
    ! [A_109] :
      ( l1_struct_0(A_109)
      | ~ l1_pre_topc(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_34,plain,(
    ~ r3_waybel_9('#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_50,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_44,plain,(
    v4_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_42,plain,(
    v7_waybel_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_40,plain,(
    l1_waybel_0('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_38,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_36,plain,(
    r2_hidden('#skF_7',k10_yellow_6('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_28,plain,(
    ! [A_107,B_108] :
      ( m1_subset_1(k10_yellow_6(A_107,B_108),k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ l1_waybel_0(B_108,A_107)
      | ~ v7_waybel_0(B_108)
      | ~ v4_orders_2(B_108)
      | v2_struct_0(B_108)
      | ~ l1_pre_topc(A_107)
      | ~ v2_pre_topc(A_107)
      | v2_struct_0(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_26,plain,(
    ! [A_85,B_97,C_103] :
      ( m1_connsp_2('#skF_4'(A_85,B_97,C_103),A_85,C_103)
      | r3_waybel_9(A_85,B_97,C_103)
      | ~ m1_subset_1(C_103,u1_struct_0(A_85))
      | ~ l1_waybel_0(B_97,A_85)
      | v2_struct_0(B_97)
      | ~ l1_pre_topc(A_85)
      | ~ v2_pre_topc(A_85)
      | v2_struct_0(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_76,plain,(
    ! [A_150,B_151,E_152,D_153] :
      ( r1_waybel_0(A_150,B_151,E_152)
      | ~ m1_connsp_2(E_152,A_150,D_153)
      | ~ r2_hidden(D_153,k10_yellow_6(A_150,B_151))
      | ~ m1_subset_1(D_153,u1_struct_0(A_150))
      | ~ m1_subset_1(k10_yellow_6(A_150,B_151),k1_zfmisc_1(u1_struct_0(A_150)))
      | ~ l1_waybel_0(B_151,A_150)
      | ~ v7_waybel_0(B_151)
      | ~ v4_orders_2(B_151)
      | v2_struct_0(B_151)
      | ~ l1_pre_topc(A_150)
      | ~ v2_pre_topc(A_150)
      | v2_struct_0(A_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_125,plain,(
    ! [A_182,B_183,B_184,C_185] :
      ( r1_waybel_0(A_182,B_183,'#skF_4'(A_182,B_184,C_185))
      | ~ r2_hidden(C_185,k10_yellow_6(A_182,B_183))
      | ~ m1_subset_1(k10_yellow_6(A_182,B_183),k1_zfmisc_1(u1_struct_0(A_182)))
      | ~ l1_waybel_0(B_183,A_182)
      | ~ v7_waybel_0(B_183)
      | ~ v4_orders_2(B_183)
      | v2_struct_0(B_183)
      | r3_waybel_9(A_182,B_184,C_185)
      | ~ m1_subset_1(C_185,u1_struct_0(A_182))
      | ~ l1_waybel_0(B_184,A_182)
      | v2_struct_0(B_184)
      | ~ l1_pre_topc(A_182)
      | ~ v2_pre_topc(A_182)
      | v2_struct_0(A_182) ) ),
    inference(resolution,[status(thm)],[c_26,c_76])).

tff(c_129,plain,(
    ! [A_186,B_187,B_188,C_189] :
      ( r1_waybel_0(A_186,B_187,'#skF_4'(A_186,B_188,C_189))
      | ~ r2_hidden(C_189,k10_yellow_6(A_186,B_187))
      | r3_waybel_9(A_186,B_188,C_189)
      | ~ m1_subset_1(C_189,u1_struct_0(A_186))
      | ~ l1_waybel_0(B_188,A_186)
      | v2_struct_0(B_188)
      | ~ l1_waybel_0(B_187,A_186)
      | ~ v7_waybel_0(B_187)
      | ~ v4_orders_2(B_187)
      | v2_struct_0(B_187)
      | ~ l1_pre_topc(A_186)
      | ~ v2_pre_topc(A_186)
      | v2_struct_0(A_186) ) ),
    inference(resolution,[status(thm)],[c_28,c_125])).

tff(c_32,plain,(
    ! [A_110,B_114,C_116] :
      ( r2_waybel_0(A_110,B_114,C_116)
      | ~ r1_waybel_0(A_110,B_114,C_116)
      | ~ l1_waybel_0(B_114,A_110)
      | ~ v7_waybel_0(B_114)
      | ~ v4_orders_2(B_114)
      | v2_struct_0(B_114)
      | ~ l1_struct_0(A_110)
      | v2_struct_0(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_56,plain,(
    ! [A_127,B_128,C_129] :
      ( ~ r2_waybel_0(A_127,B_128,'#skF_4'(A_127,B_128,C_129))
      | r3_waybel_9(A_127,B_128,C_129)
      | ~ m1_subset_1(C_129,u1_struct_0(A_127))
      | ~ l1_waybel_0(B_128,A_127)
      | v2_struct_0(B_128)
      | ~ l1_pre_topc(A_127)
      | ~ v2_pre_topc(A_127)
      | v2_struct_0(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_61,plain,(
    ! [A_110,B_114,C_129] :
      ( r3_waybel_9(A_110,B_114,C_129)
      | ~ m1_subset_1(C_129,u1_struct_0(A_110))
      | ~ l1_pre_topc(A_110)
      | ~ v2_pre_topc(A_110)
      | ~ r1_waybel_0(A_110,B_114,'#skF_4'(A_110,B_114,C_129))
      | ~ l1_waybel_0(B_114,A_110)
      | ~ v7_waybel_0(B_114)
      | ~ v4_orders_2(B_114)
      | v2_struct_0(B_114)
      | ~ l1_struct_0(A_110)
      | v2_struct_0(A_110) ) ),
    inference(resolution,[status(thm)],[c_32,c_56])).

tff(c_135,plain,(
    ! [A_190,C_191,B_192] :
      ( ~ l1_struct_0(A_190)
      | ~ r2_hidden(C_191,k10_yellow_6(A_190,B_192))
      | r3_waybel_9(A_190,B_192,C_191)
      | ~ m1_subset_1(C_191,u1_struct_0(A_190))
      | ~ l1_waybel_0(B_192,A_190)
      | ~ v7_waybel_0(B_192)
      | ~ v4_orders_2(B_192)
      | v2_struct_0(B_192)
      | ~ l1_pre_topc(A_190)
      | ~ v2_pre_topc(A_190)
      | v2_struct_0(A_190) ) ),
    inference(resolution,[status(thm)],[c_129,c_61])).

tff(c_138,plain,
    ( ~ l1_struct_0('#skF_5')
    | r3_waybel_9('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ l1_waybel_0('#skF_6','#skF_5')
    | ~ v7_waybel_0('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | v2_struct_0('#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_135])).

tff(c_141,plain,
    ( ~ l1_struct_0('#skF_5')
    | r3_waybel_9('#skF_5','#skF_6','#skF_7')
    | v2_struct_0('#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_44,c_42,c_40,c_38,c_138])).

tff(c_142,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_46,c_34,c_141])).

tff(c_145,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_142])).

tff(c_149,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_145])).

%------------------------------------------------------------------------------
