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
% DateTime   : Thu Dec  3 10:31:12 EST 2020

% Result     : Theorem 20.60s
% Output     : CNFRefutation 20.81s
% Verified   : 
% Statistics : Number of formulae       :  193 (3159 expanded)
%              Number of leaves         :   43 (1091 expanded)
%              Depth                    :   22
%              Number of atoms          :  444 (8453 expanded)
%              Number of equality atoms :   26 ( 679 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_yellow_6 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k9_yellow_6,type,(
    k9_yellow_6: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_178,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(k9_yellow_6(A,B)))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(k9_yellow_6(A,B)))
                   => m1_subset_1(k3_xboole_0(C,D),u1_struct_0(k9_yellow_6(A,B))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_waybel_9)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_159,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(k9_yellow_6(A,B)))
             => m1_connsp_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_waybel_9)).

tff(f_125,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ! [C] :
          ( m1_connsp_2(C,A,B)
         => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_84,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_111,axiom,(
    ! [A,B,C] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & v3_pre_topc(B,A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & v3_pre_topc(C,A)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k3_xboole_0(B,C),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_tops_1)).

tff(f_144,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r2_hidden(C,u1_struct_0(k9_yellow_6(A,B)))
              <=> ( r2_hidden(B,C)
                  & v3_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_yellow_6)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_80,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_51,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_72,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_74,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_49,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_86,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_84,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_82,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_76,plain,(
    m1_subset_1('#skF_7',u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_177,plain,(
    ! [B_88,A_89] :
      ( v1_xboole_0(B_88)
      | ~ m1_subset_1(B_88,A_89)
      | ~ v1_xboole_0(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_199,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_76,c_177])).

tff(c_208,plain,(
    ~ v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_199])).

tff(c_10,plain,(
    ! [D_13,A_8,B_9] :
      ( r2_hidden(D_13,k3_xboole_0(A_8,B_9))
      | ~ r2_hidden(D_13,B_9)
      | ~ r2_hidden(D_13,A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_231,plain,(
    ! [D_97,B_98,A_99] :
      ( r2_hidden(D_97,B_98)
      | ~ r2_hidden(D_97,k3_xboole_0(A_99,B_98)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_54522,plain,(
    ! [A_1291,B_1292,B_1293] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_1291,B_1292),B_1293),B_1292)
      | r1_tarski(k3_xboole_0(A_1291,B_1292),B_1293) ) ),
    inference(resolution,[status(thm)],[c_8,c_231])).

tff(c_80,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_201,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_80,c_177])).

tff(c_206,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_201])).

tff(c_1125,plain,(
    ! [C_195,A_196,B_197] :
      ( m1_connsp_2(C_195,A_196,B_197)
      | ~ m1_subset_1(C_195,u1_struct_0(k9_yellow_6(A_196,B_197)))
      | ~ m1_subset_1(B_197,u1_struct_0(A_196))
      | ~ l1_pre_topc(A_196)
      | ~ v2_pre_topc(A_196)
      | v2_struct_0(A_196) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_1139,plain,
    ( m1_connsp_2('#skF_7','#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_1125])).

tff(c_1148,plain,
    ( m1_connsp_2('#skF_7','#skF_4','#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_1139])).

tff(c_1149,plain,(
    m1_connsp_2('#skF_7','#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_1148])).

tff(c_64,plain,(
    ! [C_43,A_40,B_41] :
      ( m1_subset_1(C_43,k1_zfmisc_1(u1_struct_0(A_40)))
      | ~ m1_connsp_2(C_43,A_40,B_41)
      | ~ m1_subset_1(B_41,u1_struct_0(A_40))
      | ~ l1_pre_topc(A_40)
      | ~ v2_pre_topc(A_40)
      | v2_struct_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1157,plain,
    ( m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1149,c_64])).

tff(c_1160,plain,
    ( m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_1157])).

tff(c_1161,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_1160])).

tff(c_58,plain,(
    ! [A_31,C_33,B_32] :
      ( m1_subset_1(A_31,C_33)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(C_33))
      | ~ r2_hidden(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1199,plain,(
    ! [A_31] :
      ( m1_subset_1(A_31,u1_struct_0('#skF_4'))
      | ~ r2_hidden(A_31,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_1161,c_58])).

tff(c_210,plain,(
    ! [B_93,A_94] :
      ( r2_hidden(B_93,A_94)
      | ~ m1_subset_1(B_93,A_94)
      | v1_xboole_0(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_50624,plain,(
    ! [A_1209,A_1210] :
      ( r1_tarski(A_1209,A_1210)
      | ~ m1_subset_1('#skF_1'(A_1209,A_1210),A_1210)
      | v1_xboole_0(A_1210) ) ),
    inference(resolution,[status(thm)],[c_210,c_6])).

tff(c_50632,plain,(
    ! [A_1209] :
      ( r1_tarski(A_1209,u1_struct_0('#skF_4'))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_1'(A_1209,u1_struct_0('#skF_4')),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_1199,c_50624])).

tff(c_50650,plain,(
    ! [A_1209] :
      ( r1_tarski(A_1209,u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_1'(A_1209,u1_struct_0('#skF_4')),'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_206,c_50632])).

tff(c_54596,plain,(
    ! [A_1291] : r1_tarski(k3_xboole_0(A_1291,'#skF_7'),u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_54522,c_50650])).

tff(c_56,plain,(
    ! [A_29,B_30] :
      ( m1_subset_1(A_29,k1_zfmisc_1(B_30))
      | ~ r1_tarski(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2435,plain,(
    ! [B_265,C_266,A_267] :
      ( v3_pre_topc(k3_xboole_0(B_265,C_266),A_267)
      | ~ m1_subset_1(C_266,k1_zfmisc_1(u1_struct_0(A_267)))
      | ~ v3_pre_topc(C_266,A_267)
      | ~ m1_subset_1(B_265,k1_zfmisc_1(u1_struct_0(A_267)))
      | ~ v3_pre_topc(B_265,A_267)
      | ~ l1_pre_topc(A_267)
      | ~ v2_pre_topc(A_267) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_2437,plain,(
    ! [B_265] :
      ( v3_pre_topc(k3_xboole_0(B_265,'#skF_7'),'#skF_4')
      | ~ v3_pre_topc('#skF_7','#skF_4')
      | ~ m1_subset_1(B_265,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v3_pre_topc(B_265,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1161,c_2435])).

tff(c_2454,plain,(
    ! [B_265] :
      ( v3_pre_topc(k3_xboole_0(B_265,'#skF_7'),'#skF_4')
      | ~ v3_pre_topc('#skF_7','#skF_4')
      | ~ m1_subset_1(B_265,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v3_pre_topc(B_265,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_2437])).

tff(c_26014,plain,(
    ~ v3_pre_topc('#skF_7','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2454])).

tff(c_40,plain,(
    ! [B_22,A_21] :
      ( r2_hidden(B_22,A_21)
      | ~ m1_subset_1(B_22,A_21)
      | v1_xboole_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1765,plain,(
    ! [C_234,A_235,B_236] :
      ( v3_pre_topc(C_234,A_235)
      | ~ r2_hidden(C_234,u1_struct_0(k9_yellow_6(A_235,B_236)))
      | ~ m1_subset_1(C_234,k1_zfmisc_1(u1_struct_0(A_235)))
      | ~ m1_subset_1(B_236,u1_struct_0(A_235))
      | ~ l1_pre_topc(A_235)
      | ~ v2_pre_topc(A_235)
      | v2_struct_0(A_235) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_49850,plain,(
    ! [B_1177,A_1178,B_1179] :
      ( v3_pre_topc(B_1177,A_1178)
      | ~ m1_subset_1(B_1177,k1_zfmisc_1(u1_struct_0(A_1178)))
      | ~ m1_subset_1(B_1179,u1_struct_0(A_1178))
      | ~ l1_pre_topc(A_1178)
      | ~ v2_pre_topc(A_1178)
      | v2_struct_0(A_1178)
      | ~ m1_subset_1(B_1177,u1_struct_0(k9_yellow_6(A_1178,B_1179)))
      | v1_xboole_0(u1_struct_0(k9_yellow_6(A_1178,B_1179))) ) ),
    inference(resolution,[status(thm)],[c_40,c_1765])).

tff(c_49891,plain,
    ( v3_pre_topc('#skF_7','#skF_4')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_76,c_49850])).

tff(c_49907,plain,
    ( v3_pre_topc('#skF_7','#skF_4')
    | v2_struct_0('#skF_4')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_1161,c_49891])).

tff(c_49909,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_208,c_86,c_26014,c_49907])).

tff(c_49911,plain,(
    v3_pre_topc('#skF_7','#skF_4') ),
    inference(splitRight,[status(thm)],[c_2454])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_78,plain,(
    m1_subset_1('#skF_6',u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_1136,plain,
    ( m1_connsp_2('#skF_6','#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_1125])).

tff(c_1144,plain,
    ( m1_connsp_2('#skF_6','#skF_4','#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_1136])).

tff(c_1145,plain,(
    m1_connsp_2('#skF_6','#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_1144])).

tff(c_1151,plain,
    ( m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1145,c_64])).

tff(c_1154,plain,
    ( m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_1151])).

tff(c_1155,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_1154])).

tff(c_2439,plain,(
    ! [B_265] :
      ( v3_pre_topc(k3_xboole_0(B_265,'#skF_6'),'#skF_4')
      | ~ v3_pre_topc('#skF_6','#skF_4')
      | ~ m1_subset_1(B_265,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v3_pre_topc(B_265,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1155,c_2435])).

tff(c_2457,plain,(
    ! [B_265] :
      ( v3_pre_topc(k3_xboole_0(B_265,'#skF_6'),'#skF_4')
      | ~ v3_pre_topc('#skF_6','#skF_4')
      | ~ m1_subset_1(B_265,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v3_pre_topc(B_265,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_2439])).

tff(c_2556,plain,(
    ~ v3_pre_topc('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2457])).

tff(c_25773,plain,(
    ! [B_717,A_718,B_719] :
      ( v3_pre_topc(B_717,A_718)
      | ~ m1_subset_1(B_717,k1_zfmisc_1(u1_struct_0(A_718)))
      | ~ m1_subset_1(B_719,u1_struct_0(A_718))
      | ~ l1_pre_topc(A_718)
      | ~ v2_pre_topc(A_718)
      | v2_struct_0(A_718)
      | ~ m1_subset_1(B_717,u1_struct_0(k9_yellow_6(A_718,B_719)))
      | v1_xboole_0(u1_struct_0(k9_yellow_6(A_718,B_719))) ) ),
    inference(resolution,[status(thm)],[c_40,c_1765])).

tff(c_25811,plain,
    ( v3_pre_topc('#skF_6','#skF_4')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_78,c_25773])).

tff(c_25826,plain,
    ( v3_pre_topc('#skF_6','#skF_4')
    | v2_struct_0('#skF_4')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_1155,c_25811])).

tff(c_25828,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_208,c_86,c_2556,c_25826])).

tff(c_50008,plain,(
    ! [B_1184] :
      ( v3_pre_topc(k3_xboole_0(B_1184,'#skF_6'),'#skF_4')
      | ~ m1_subset_1(B_1184,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v3_pre_topc(B_1184,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_2457])).

tff(c_50011,plain,
    ( v3_pre_topc(k3_xboole_0('#skF_7','#skF_6'),'#skF_4')
    | ~ v3_pre_topc('#skF_7','#skF_4') ),
    inference(resolution,[status(thm)],[c_1161,c_50008])).

tff(c_50033,plain,(
    v3_pre_topc(k3_xboole_0('#skF_6','#skF_7'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_49911,c_2,c_50011])).

tff(c_50045,plain,(
    ! [C_1185,A_1186,B_1187] :
      ( r2_hidden(C_1185,u1_struct_0(k9_yellow_6(A_1186,B_1187)))
      | ~ v3_pre_topc(C_1185,A_1186)
      | ~ r2_hidden(B_1187,C_1185)
      | ~ m1_subset_1(C_1185,k1_zfmisc_1(u1_struct_0(A_1186)))
      | ~ m1_subset_1(B_1187,u1_struct_0(A_1186))
      | ~ l1_pre_topc(A_1186)
      | ~ v2_pre_topc(A_1186)
      | v2_struct_0(A_1186) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_52,plain,(
    ! [A_27,B_28] :
      ( m1_subset_1(A_27,B_28)
      | ~ r2_hidden(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_69954,plain,(
    ! [C_1577,A_1578,B_1579] :
      ( m1_subset_1(C_1577,u1_struct_0(k9_yellow_6(A_1578,B_1579)))
      | ~ v3_pre_topc(C_1577,A_1578)
      | ~ r2_hidden(B_1579,C_1577)
      | ~ m1_subset_1(C_1577,k1_zfmisc_1(u1_struct_0(A_1578)))
      | ~ m1_subset_1(B_1579,u1_struct_0(A_1578))
      | ~ l1_pre_topc(A_1578)
      | ~ v2_pre_topc(A_1578)
      | v2_struct_0(A_1578) ) ),
    inference(resolution,[status(thm)],[c_50045,c_52])).

tff(c_74,plain,(
    ~ m1_subset_1(k3_xboole_0('#skF_6','#skF_7'),u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_69974,plain,
    ( ~ v3_pre_topc(k3_xboole_0('#skF_6','#skF_7'),'#skF_4')
    | ~ r2_hidden('#skF_5',k3_xboole_0('#skF_6','#skF_7'))
    | ~ m1_subset_1(k3_xboole_0('#skF_6','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_69954,c_74])).

tff(c_69986,plain,
    ( ~ r2_hidden('#skF_5',k3_xboole_0('#skF_6','#skF_7'))
    | ~ m1_subset_1(k3_xboole_0('#skF_6','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_50033,c_69974])).

tff(c_69987,plain,
    ( ~ r2_hidden('#skF_5',k3_xboole_0('#skF_6','#skF_7'))
    | ~ m1_subset_1(k3_xboole_0('#skF_6','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_69986])).

tff(c_70487,plain,(
    ~ m1_subset_1(k3_xboole_0('#skF_6','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_69987])).

tff(c_70493,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_6','#skF_7'),u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_56,c_70487])).

tff(c_70498,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54596,c_70493])).

tff(c_70499,plain,(
    ~ r2_hidden('#skF_5',k3_xboole_0('#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_69987])).

tff(c_70507,plain,
    ( ~ r2_hidden('#skF_5','#skF_7')
    | ~ r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_10,c_70499])).

tff(c_70509,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_70507])).

tff(c_1497,plain,(
    ! [B_217,C_218,A_219] :
      ( r2_hidden(B_217,C_218)
      | ~ r2_hidden(C_218,u1_struct_0(k9_yellow_6(A_219,B_217)))
      | ~ m1_subset_1(C_218,k1_zfmisc_1(u1_struct_0(A_219)))
      | ~ m1_subset_1(B_217,u1_struct_0(A_219))
      | ~ l1_pre_topc(A_219)
      | ~ v2_pre_topc(A_219)
      | v2_struct_0(A_219) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_70520,plain,(
    ! [B_1586,B_1587,A_1588] :
      ( r2_hidden(B_1586,B_1587)
      | ~ m1_subset_1(B_1587,k1_zfmisc_1(u1_struct_0(A_1588)))
      | ~ m1_subset_1(B_1586,u1_struct_0(A_1588))
      | ~ l1_pre_topc(A_1588)
      | ~ v2_pre_topc(A_1588)
      | v2_struct_0(A_1588)
      | ~ m1_subset_1(B_1587,u1_struct_0(k9_yellow_6(A_1588,B_1586)))
      | v1_xboole_0(u1_struct_0(k9_yellow_6(A_1588,B_1586))) ) ),
    inference(resolution,[status(thm)],[c_40,c_1497])).

tff(c_70558,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_78,c_70520])).

tff(c_70573,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | v2_struct_0('#skF_4')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_1155,c_70558])).

tff(c_70575,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_208,c_86,c_70509,c_70573])).

tff(c_70576,plain,(
    ~ r2_hidden('#skF_5','#skF_7') ),
    inference(splitRight,[status(thm)],[c_70507])).

tff(c_70820,plain,(
    ! [B_1591,B_1592,A_1593] :
      ( r2_hidden(B_1591,B_1592)
      | ~ m1_subset_1(B_1592,k1_zfmisc_1(u1_struct_0(A_1593)))
      | ~ m1_subset_1(B_1591,u1_struct_0(A_1593))
      | ~ l1_pre_topc(A_1593)
      | ~ v2_pre_topc(A_1593)
      | v2_struct_0(A_1593)
      | ~ m1_subset_1(B_1592,u1_struct_0(k9_yellow_6(A_1593,B_1591)))
      | v1_xboole_0(u1_struct_0(k9_yellow_6(A_1593,B_1591))) ) ),
    inference(resolution,[status(thm)],[c_40,c_1497])).

tff(c_70861,plain,
    ( r2_hidden('#skF_5','#skF_7')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_76,c_70820])).

tff(c_70877,plain,
    ( r2_hidden('#skF_5','#skF_7')
    | v2_struct_0('#skF_4')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_1161,c_70861])).

tff(c_70879,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_208,c_86,c_70576,c_70877])).

tff(c_70881,plain,(
    v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_199])).

tff(c_198,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_78,c_177])).

tff(c_70883,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70881,c_198])).

tff(c_34,plain,(
    ! [A_16,B_17] : r1_tarski(k3_xboole_0(A_16,B_17),A_16) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_46,plain,(
    ! [A_23] : k2_subset_1(A_23) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_48,plain,(
    ! [A_24] : m1_subset_1(k2_subset_1(A_24),k1_zfmisc_1(A_24)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_87,plain,(
    ! [A_24] : m1_subset_1(A_24,k1_zfmisc_1(A_24)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_48])).

tff(c_70974,plain,(
    ! [C_1617,B_1618,A_1619] :
      ( ~ v1_xboole_0(C_1617)
      | ~ m1_subset_1(B_1618,k1_zfmisc_1(C_1617))
      | ~ r2_hidden(A_1619,B_1618) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_70989,plain,(
    ! [A_1620,A_1621] :
      ( ~ v1_xboole_0(A_1620)
      | ~ r2_hidden(A_1621,A_1620) ) ),
    inference(resolution,[status(thm)],[c_87,c_70974])).

tff(c_70998,plain,(
    ! [A_1622,B_1623] :
      ( ~ v1_xboole_0(A_1622)
      | r1_tarski(A_1622,B_1623) ) ),
    inference(resolution,[status(thm)],[c_8,c_70989])).

tff(c_28,plain,(
    ! [B_15,A_14] :
      ( B_15 = A_14
      | ~ r1_tarski(B_15,A_14)
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_71015,plain,(
    ! [B_1627,A_1628] :
      ( B_1627 = A_1628
      | ~ r1_tarski(B_1627,A_1628)
      | ~ v1_xboole_0(A_1628) ) ),
    inference(resolution,[status(thm)],[c_70998,c_28])).

tff(c_71081,plain,(
    ! [A_1632,B_1633] :
      ( k3_xboole_0(A_1632,B_1633) = A_1632
      | ~ v1_xboole_0(A_1632) ) ),
    inference(resolution,[status(thm)],[c_34,c_71015])).

tff(c_71084,plain,(
    ! [B_1633] : k3_xboole_0('#skF_6',B_1633) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_70883,c_71081])).

tff(c_70880,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_199])).

tff(c_70996,plain,(
    ! [A_3,B_4] :
      ( ~ v1_xboole_0(A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(resolution,[status(thm)],[c_8,c_70989])).

tff(c_71033,plain,(
    ! [B_1629,A_1630] :
      ( B_1629 = A_1630
      | ~ v1_xboole_0(B_1629)
      | ~ v1_xboole_0(A_1630) ) ),
    inference(resolution,[status(thm)],[c_70996,c_71015])).

tff(c_71043,plain,(
    ! [A_1631] :
      ( A_1631 = '#skF_6'
      | ~ v1_xboole_0(A_1631) ) ),
    inference(resolution,[status(thm)],[c_70883,c_71033])).

tff(c_71056,plain,(
    '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_70880,c_71043])).

tff(c_42,plain,(
    ! [B_22,A_21] :
      ( m1_subset_1(B_22,A_21)
      | ~ v1_xboole_0(B_22)
      | ~ v1_xboole_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_205,plain,
    ( ~ v1_xboole_0(k3_xboole_0('#skF_6','#skF_7'))
    | ~ v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_42,c_74])).

tff(c_70885,plain,(
    ~ v1_xboole_0(k3_xboole_0('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70881,c_205])).

tff(c_71057,plain,(
    ~ v1_xboole_0(k3_xboole_0('#skF_6','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71056,c_70885])).

tff(c_71100,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_71084,c_71057])).

tff(c_71103,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70883,c_71100])).

tff(c_71105,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_201])).

tff(c_71104,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_201])).

tff(c_71189,plain,(
    ! [C_1658,B_1659,A_1660] :
      ( ~ v1_xboole_0(C_1658)
      | ~ m1_subset_1(B_1659,k1_zfmisc_1(C_1658))
      | ~ r2_hidden(A_1660,B_1659) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_71204,plain,(
    ! [A_1661,A_1662] :
      ( ~ v1_xboole_0(A_1661)
      | ~ r2_hidden(A_1662,A_1661) ) ),
    inference(resolution,[status(thm)],[c_87,c_71189])).

tff(c_71213,plain,(
    ! [A_1663,B_1664] :
      ( ~ v1_xboole_0(A_1663)
      | r1_tarski(A_1663,B_1664) ) ),
    inference(resolution,[status(thm)],[c_8,c_71204])).

tff(c_71217,plain,(
    ! [B_1665,A_1666] :
      ( B_1665 = A_1666
      | ~ r1_tarski(B_1665,A_1666)
      | ~ v1_xboole_0(A_1666) ) ),
    inference(resolution,[status(thm)],[c_71213,c_28])).

tff(c_71248,plain,(
    ! [A_1670,B_1671] :
      ( k3_xboole_0(A_1670,B_1671) = A_1670
      | ~ v1_xboole_0(A_1670) ) ),
    inference(resolution,[status(thm)],[c_34,c_71217])).

tff(c_71255,plain,(
    ! [B_1672] : k3_xboole_0('#skF_5',B_1672) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_71104,c_71248])).

tff(c_101,plain,(
    ! [B_74,A_75] : k3_xboole_0(B_74,A_75) = k3_xboole_0(A_75,B_74) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_116,plain,(
    ! [B_74,A_75] : r1_tarski(k3_xboole_0(B_74,A_75),A_75) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_34])).

tff(c_71289,plain,(
    ! [B_1673] : r1_tarski('#skF_5',B_1673) ),
    inference(superposition,[status(thm),theory(equality)],[c_71255,c_116])).

tff(c_71216,plain,(
    ! [B_1664,A_1663] :
      ( B_1664 = A_1663
      | ~ r1_tarski(B_1664,A_1663)
      | ~ v1_xboole_0(A_1663) ) ),
    inference(resolution,[status(thm)],[c_71213,c_28])).

tff(c_71357,plain,(
    ! [B_1678] :
      ( B_1678 = '#skF_5'
      | ~ v1_xboole_0(B_1678) ) ),
    inference(resolution,[status(thm)],[c_71289,c_71216])).

tff(c_71364,plain,(
    u1_struct_0('#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_71105,c_71357])).

tff(c_71368,plain,(
    m1_subset_1('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_71364,c_80])).

tff(c_72729,plain,(
    ! [C_1764,A_1765,B_1766] :
      ( m1_connsp_2(C_1764,A_1765,B_1766)
      | ~ m1_subset_1(C_1764,u1_struct_0(k9_yellow_6(A_1765,B_1766)))
      | ~ m1_subset_1(B_1766,u1_struct_0(A_1765))
      | ~ l1_pre_topc(A_1765)
      | ~ v2_pre_topc(A_1765)
      | v2_struct_0(A_1765) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_72740,plain,
    ( m1_connsp_2('#skF_6','#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_72729])).

tff(c_72748,plain,
    ( m1_connsp_2('#skF_6','#skF_4','#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_71368,c_71364,c_72740])).

tff(c_72749,plain,(
    m1_connsp_2('#skF_6','#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_72748])).

tff(c_72755,plain,
    ( m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_72749,c_64])).

tff(c_72758,plain,
    ( m1_subset_1('#skF_6',k1_zfmisc_1('#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_71368,c_71364,c_71364,c_72755])).

tff(c_72759,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_72758])).

tff(c_54,plain,(
    ! [A_29,B_30] :
      ( r1_tarski(A_29,B_30)
      | ~ m1_subset_1(A_29,k1_zfmisc_1(B_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_72781,plain,(
    r1_tarski('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_72759,c_54])).

tff(c_71299,plain,(
    ! [B_1673] :
      ( B_1673 = '#skF_5'
      | ~ r1_tarski(B_1673,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_71289,c_28])).

tff(c_72816,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_72781,c_71299])).

tff(c_72845,plain,(
    m1_subset_1('#skF_6',u1_struct_0(k9_yellow_6('#skF_4','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72816,c_78])).

tff(c_71254,plain,(
    ! [B_1671] : k3_xboole_0('#skF_5',B_1671) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_71104,c_71248])).

tff(c_72841,plain,(
    ! [B_1671] : k3_xboole_0('#skF_6',B_1671) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72816,c_72816,c_71254])).

tff(c_72843,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72816,c_71104])).

tff(c_72743,plain,
    ( m1_connsp_2('#skF_7','#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_72729])).

tff(c_72752,plain,
    ( m1_connsp_2('#skF_7','#skF_4','#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_71368,c_71364,c_72743])).

tff(c_72753,plain,(
    m1_connsp_2('#skF_7','#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_72752])).

tff(c_72761,plain,
    ( m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_72753,c_64])).

tff(c_72764,plain,
    ( m1_subset_1('#skF_7',k1_zfmisc_1('#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_71368,c_71364,c_71364,c_72761])).

tff(c_72765,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_72764])).

tff(c_72797,plain,(
    r1_tarski('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_72765,c_54])).

tff(c_72913,plain,(
    r1_tarski('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72816,c_72797])).

tff(c_72920,plain,
    ( '#skF_7' = '#skF_6'
    | ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_72913,c_71216])).

tff(c_72929,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72843,c_72920])).

tff(c_72844,plain,(
    ~ m1_subset_1(k3_xboole_0('#skF_6','#skF_7'),u1_struct_0(k9_yellow_6('#skF_4','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72816,c_74])).

tff(c_73264,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72845,c_72841,c_72929,c_72844])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:27:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 20.60/11.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 20.60/11.11  
% 20.60/11.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 20.60/11.11  %$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_yellow_6 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 20.60/11.11  
% 20.60/11.11  %Foreground sorts:
% 20.60/11.11  
% 20.60/11.11  
% 20.60/11.11  %Background operators:
% 20.60/11.11  
% 20.60/11.11  
% 20.60/11.11  %Foreground operators:
% 20.60/11.11  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 20.60/11.11  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 20.60/11.11  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 20.60/11.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 20.60/11.11  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 20.60/11.11  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 20.60/11.11  tff('#skF_7', type, '#skF_7': $i).
% 20.60/11.11  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 20.60/11.11  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 20.60/11.11  tff('#skF_5', type, '#skF_5': $i).
% 20.60/11.11  tff('#skF_6', type, '#skF_6': $i).
% 20.60/11.11  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 20.60/11.11  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 20.60/11.11  tff(k9_yellow_6, type, k9_yellow_6: ($i * $i) > $i).
% 20.60/11.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 20.60/11.11  tff('#skF_4', type, '#skF_4': $i).
% 20.60/11.11  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 20.60/11.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 20.60/11.11  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 20.60/11.11  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 20.60/11.11  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 20.60/11.11  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 20.60/11.11  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 20.60/11.11  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 20.60/11.11  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 20.60/11.11  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 20.60/11.11  
% 20.81/11.13  tff(f_178, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(k9_yellow_6(A, B))) => (![D]: (m1_subset_1(D, u1_struct_0(k9_yellow_6(A, B))) => m1_subset_1(k3_xboole_0(C, D), u1_struct_0(k9_yellow_6(A, B))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_waybel_9)).
% 20.81/11.13  tff(f_70, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 20.81/11.13  tff(f_43, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 20.81/11.13  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 20.81/11.13  tff(f_159, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(k9_yellow_6(A, B))) => m1_connsp_2(C, A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_waybel_9)).
% 20.81/11.13  tff(f_125, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (![C]: (m1_connsp_2(C, A, B) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 20.81/11.13  tff(f_90, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 20.81/11.13  tff(f_84, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 20.81/11.13  tff(f_111, axiom, (![A, B, C]: ((((((v2_pre_topc(A) & l1_pre_topc(A)) & v3_pre_topc(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & v3_pre_topc(C, A)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k3_xboole_0(B, C), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_tops_1)).
% 20.81/11.13  tff(f_144, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(C, u1_struct_0(k9_yellow_6(A, B))) <=> (r2_hidden(B, C) & v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_yellow_6)).
% 20.81/11.13  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 20.81/11.13  tff(f_80, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 20.81/11.13  tff(f_51, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 20.81/11.13  tff(f_72, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 20.81/11.13  tff(f_74, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 20.81/11.13  tff(f_97, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 20.81/11.13  tff(f_49, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 20.81/11.13  tff(c_86, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_178])).
% 20.81/11.13  tff(c_84, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_178])).
% 20.81/11.13  tff(c_82, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_178])).
% 20.81/11.13  tff(c_76, plain, (m1_subset_1('#skF_7', u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_178])).
% 20.81/11.13  tff(c_177, plain, (![B_88, A_89]: (v1_xboole_0(B_88) | ~m1_subset_1(B_88, A_89) | ~v1_xboole_0(A_89))), inference(cnfTransformation, [status(thm)], [f_70])).
% 20.81/11.13  tff(c_199, plain, (v1_xboole_0('#skF_7') | ~v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_76, c_177])).
% 20.81/11.13  tff(c_208, plain, (~v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(splitLeft, [status(thm)], [c_199])).
% 20.81/11.13  tff(c_10, plain, (![D_13, A_8, B_9]: (r2_hidden(D_13, k3_xboole_0(A_8, B_9)) | ~r2_hidden(D_13, B_9) | ~r2_hidden(D_13, A_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 20.81/11.13  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 20.81/11.13  tff(c_231, plain, (![D_97, B_98, A_99]: (r2_hidden(D_97, B_98) | ~r2_hidden(D_97, k3_xboole_0(A_99, B_98)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 20.81/11.13  tff(c_54522, plain, (![A_1291, B_1292, B_1293]: (r2_hidden('#skF_1'(k3_xboole_0(A_1291, B_1292), B_1293), B_1292) | r1_tarski(k3_xboole_0(A_1291, B_1292), B_1293))), inference(resolution, [status(thm)], [c_8, c_231])).
% 20.81/11.13  tff(c_80, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_178])).
% 20.81/11.13  tff(c_201, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_80, c_177])).
% 20.81/11.13  tff(c_206, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_201])).
% 20.81/11.13  tff(c_1125, plain, (![C_195, A_196, B_197]: (m1_connsp_2(C_195, A_196, B_197) | ~m1_subset_1(C_195, u1_struct_0(k9_yellow_6(A_196, B_197))) | ~m1_subset_1(B_197, u1_struct_0(A_196)) | ~l1_pre_topc(A_196) | ~v2_pre_topc(A_196) | v2_struct_0(A_196))), inference(cnfTransformation, [status(thm)], [f_159])).
% 20.81/11.13  tff(c_1139, plain, (m1_connsp_2('#skF_7', '#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_76, c_1125])).
% 20.81/11.13  tff(c_1148, plain, (m1_connsp_2('#skF_7', '#skF_4', '#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_80, c_1139])).
% 20.81/11.13  tff(c_1149, plain, (m1_connsp_2('#skF_7', '#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_86, c_1148])).
% 20.81/11.13  tff(c_64, plain, (![C_43, A_40, B_41]: (m1_subset_1(C_43, k1_zfmisc_1(u1_struct_0(A_40))) | ~m1_connsp_2(C_43, A_40, B_41) | ~m1_subset_1(B_41, u1_struct_0(A_40)) | ~l1_pre_topc(A_40) | ~v2_pre_topc(A_40) | v2_struct_0(A_40))), inference(cnfTransformation, [status(thm)], [f_125])).
% 20.81/11.13  tff(c_1157, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_1149, c_64])).
% 20.81/11.13  tff(c_1160, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_80, c_1157])).
% 20.81/11.13  tff(c_1161, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_86, c_1160])).
% 20.81/11.13  tff(c_58, plain, (![A_31, C_33, B_32]: (m1_subset_1(A_31, C_33) | ~m1_subset_1(B_32, k1_zfmisc_1(C_33)) | ~r2_hidden(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_90])).
% 20.81/11.13  tff(c_1199, plain, (![A_31]: (m1_subset_1(A_31, u1_struct_0('#skF_4')) | ~r2_hidden(A_31, '#skF_7'))), inference(resolution, [status(thm)], [c_1161, c_58])).
% 20.81/11.13  tff(c_210, plain, (![B_93, A_94]: (r2_hidden(B_93, A_94) | ~m1_subset_1(B_93, A_94) | v1_xboole_0(A_94))), inference(cnfTransformation, [status(thm)], [f_70])).
% 20.81/11.13  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 20.81/11.13  tff(c_50624, plain, (![A_1209, A_1210]: (r1_tarski(A_1209, A_1210) | ~m1_subset_1('#skF_1'(A_1209, A_1210), A_1210) | v1_xboole_0(A_1210))), inference(resolution, [status(thm)], [c_210, c_6])).
% 20.81/11.13  tff(c_50632, plain, (![A_1209]: (r1_tarski(A_1209, u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_4')) | ~r2_hidden('#skF_1'(A_1209, u1_struct_0('#skF_4')), '#skF_7'))), inference(resolution, [status(thm)], [c_1199, c_50624])).
% 20.81/11.13  tff(c_50650, plain, (![A_1209]: (r1_tarski(A_1209, u1_struct_0('#skF_4')) | ~r2_hidden('#skF_1'(A_1209, u1_struct_0('#skF_4')), '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_206, c_50632])).
% 20.81/11.13  tff(c_54596, plain, (![A_1291]: (r1_tarski(k3_xboole_0(A_1291, '#skF_7'), u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_54522, c_50650])).
% 20.81/11.13  tff(c_56, plain, (![A_29, B_30]: (m1_subset_1(A_29, k1_zfmisc_1(B_30)) | ~r1_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_84])).
% 20.81/11.13  tff(c_2435, plain, (![B_265, C_266, A_267]: (v3_pre_topc(k3_xboole_0(B_265, C_266), A_267) | ~m1_subset_1(C_266, k1_zfmisc_1(u1_struct_0(A_267))) | ~v3_pre_topc(C_266, A_267) | ~m1_subset_1(B_265, k1_zfmisc_1(u1_struct_0(A_267))) | ~v3_pre_topc(B_265, A_267) | ~l1_pre_topc(A_267) | ~v2_pre_topc(A_267))), inference(cnfTransformation, [status(thm)], [f_111])).
% 20.81/11.13  tff(c_2437, plain, (![B_265]: (v3_pre_topc(k3_xboole_0(B_265, '#skF_7'), '#skF_4') | ~v3_pre_topc('#skF_7', '#skF_4') | ~m1_subset_1(B_265, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v3_pre_topc(B_265, '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_1161, c_2435])).
% 20.81/11.13  tff(c_2454, plain, (![B_265]: (v3_pre_topc(k3_xboole_0(B_265, '#skF_7'), '#skF_4') | ~v3_pre_topc('#skF_7', '#skF_4') | ~m1_subset_1(B_265, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v3_pre_topc(B_265, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_2437])).
% 20.81/11.13  tff(c_26014, plain, (~v3_pre_topc('#skF_7', '#skF_4')), inference(splitLeft, [status(thm)], [c_2454])).
% 20.81/11.13  tff(c_40, plain, (![B_22, A_21]: (r2_hidden(B_22, A_21) | ~m1_subset_1(B_22, A_21) | v1_xboole_0(A_21))), inference(cnfTransformation, [status(thm)], [f_70])).
% 20.81/11.13  tff(c_1765, plain, (![C_234, A_235, B_236]: (v3_pre_topc(C_234, A_235) | ~r2_hidden(C_234, u1_struct_0(k9_yellow_6(A_235, B_236))) | ~m1_subset_1(C_234, k1_zfmisc_1(u1_struct_0(A_235))) | ~m1_subset_1(B_236, u1_struct_0(A_235)) | ~l1_pre_topc(A_235) | ~v2_pre_topc(A_235) | v2_struct_0(A_235))), inference(cnfTransformation, [status(thm)], [f_144])).
% 20.81/11.13  tff(c_49850, plain, (![B_1177, A_1178, B_1179]: (v3_pre_topc(B_1177, A_1178) | ~m1_subset_1(B_1177, k1_zfmisc_1(u1_struct_0(A_1178))) | ~m1_subset_1(B_1179, u1_struct_0(A_1178)) | ~l1_pre_topc(A_1178) | ~v2_pre_topc(A_1178) | v2_struct_0(A_1178) | ~m1_subset_1(B_1177, u1_struct_0(k9_yellow_6(A_1178, B_1179))) | v1_xboole_0(u1_struct_0(k9_yellow_6(A_1178, B_1179))))), inference(resolution, [status(thm)], [c_40, c_1765])).
% 20.81/11.13  tff(c_49891, plain, (v3_pre_topc('#skF_7', '#skF_4') | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_76, c_49850])).
% 20.81/11.13  tff(c_49907, plain, (v3_pre_topc('#skF_7', '#skF_4') | v2_struct_0('#skF_4') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_80, c_1161, c_49891])).
% 20.81/11.13  tff(c_49909, plain, $false, inference(negUnitSimplification, [status(thm)], [c_208, c_86, c_26014, c_49907])).
% 20.81/11.13  tff(c_49911, plain, (v3_pre_topc('#skF_7', '#skF_4')), inference(splitRight, [status(thm)], [c_2454])).
% 20.81/11.13  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 20.81/11.13  tff(c_78, plain, (m1_subset_1('#skF_6', u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_178])).
% 20.81/11.13  tff(c_1136, plain, (m1_connsp_2('#skF_6', '#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_78, c_1125])).
% 20.81/11.13  tff(c_1144, plain, (m1_connsp_2('#skF_6', '#skF_4', '#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_80, c_1136])).
% 20.81/11.13  tff(c_1145, plain, (m1_connsp_2('#skF_6', '#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_86, c_1144])).
% 20.81/11.13  tff(c_1151, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_1145, c_64])).
% 20.81/11.13  tff(c_1154, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_80, c_1151])).
% 20.81/11.13  tff(c_1155, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_86, c_1154])).
% 20.81/11.13  tff(c_2439, plain, (![B_265]: (v3_pre_topc(k3_xboole_0(B_265, '#skF_6'), '#skF_4') | ~v3_pre_topc('#skF_6', '#skF_4') | ~m1_subset_1(B_265, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v3_pre_topc(B_265, '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_1155, c_2435])).
% 20.81/11.13  tff(c_2457, plain, (![B_265]: (v3_pre_topc(k3_xboole_0(B_265, '#skF_6'), '#skF_4') | ~v3_pre_topc('#skF_6', '#skF_4') | ~m1_subset_1(B_265, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v3_pre_topc(B_265, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_2439])).
% 20.81/11.13  tff(c_2556, plain, (~v3_pre_topc('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_2457])).
% 20.81/11.13  tff(c_25773, plain, (![B_717, A_718, B_719]: (v3_pre_topc(B_717, A_718) | ~m1_subset_1(B_717, k1_zfmisc_1(u1_struct_0(A_718))) | ~m1_subset_1(B_719, u1_struct_0(A_718)) | ~l1_pre_topc(A_718) | ~v2_pre_topc(A_718) | v2_struct_0(A_718) | ~m1_subset_1(B_717, u1_struct_0(k9_yellow_6(A_718, B_719))) | v1_xboole_0(u1_struct_0(k9_yellow_6(A_718, B_719))))), inference(resolution, [status(thm)], [c_40, c_1765])).
% 20.81/11.13  tff(c_25811, plain, (v3_pre_topc('#skF_6', '#skF_4') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_78, c_25773])).
% 20.81/11.13  tff(c_25826, plain, (v3_pre_topc('#skF_6', '#skF_4') | v2_struct_0('#skF_4') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_80, c_1155, c_25811])).
% 20.81/11.13  tff(c_25828, plain, $false, inference(negUnitSimplification, [status(thm)], [c_208, c_86, c_2556, c_25826])).
% 20.81/11.13  tff(c_50008, plain, (![B_1184]: (v3_pre_topc(k3_xboole_0(B_1184, '#skF_6'), '#skF_4') | ~m1_subset_1(B_1184, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v3_pre_topc(B_1184, '#skF_4'))), inference(splitRight, [status(thm)], [c_2457])).
% 20.81/11.13  tff(c_50011, plain, (v3_pre_topc(k3_xboole_0('#skF_7', '#skF_6'), '#skF_4') | ~v3_pre_topc('#skF_7', '#skF_4')), inference(resolution, [status(thm)], [c_1161, c_50008])).
% 20.81/11.13  tff(c_50033, plain, (v3_pre_topc(k3_xboole_0('#skF_6', '#skF_7'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_49911, c_2, c_50011])).
% 20.81/11.13  tff(c_50045, plain, (![C_1185, A_1186, B_1187]: (r2_hidden(C_1185, u1_struct_0(k9_yellow_6(A_1186, B_1187))) | ~v3_pre_topc(C_1185, A_1186) | ~r2_hidden(B_1187, C_1185) | ~m1_subset_1(C_1185, k1_zfmisc_1(u1_struct_0(A_1186))) | ~m1_subset_1(B_1187, u1_struct_0(A_1186)) | ~l1_pre_topc(A_1186) | ~v2_pre_topc(A_1186) | v2_struct_0(A_1186))), inference(cnfTransformation, [status(thm)], [f_144])).
% 20.81/11.13  tff(c_52, plain, (![A_27, B_28]: (m1_subset_1(A_27, B_28) | ~r2_hidden(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_80])).
% 20.81/11.13  tff(c_69954, plain, (![C_1577, A_1578, B_1579]: (m1_subset_1(C_1577, u1_struct_0(k9_yellow_6(A_1578, B_1579))) | ~v3_pre_topc(C_1577, A_1578) | ~r2_hidden(B_1579, C_1577) | ~m1_subset_1(C_1577, k1_zfmisc_1(u1_struct_0(A_1578))) | ~m1_subset_1(B_1579, u1_struct_0(A_1578)) | ~l1_pre_topc(A_1578) | ~v2_pre_topc(A_1578) | v2_struct_0(A_1578))), inference(resolution, [status(thm)], [c_50045, c_52])).
% 20.81/11.13  tff(c_74, plain, (~m1_subset_1(k3_xboole_0('#skF_6', '#skF_7'), u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_178])).
% 20.81/11.13  tff(c_69974, plain, (~v3_pre_topc(k3_xboole_0('#skF_6', '#skF_7'), '#skF_4') | ~r2_hidden('#skF_5', k3_xboole_0('#skF_6', '#skF_7')) | ~m1_subset_1(k3_xboole_0('#skF_6', '#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_69954, c_74])).
% 20.81/11.13  tff(c_69986, plain, (~r2_hidden('#skF_5', k3_xboole_0('#skF_6', '#skF_7')) | ~m1_subset_1(k3_xboole_0('#skF_6', '#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_80, c_50033, c_69974])).
% 20.81/11.13  tff(c_69987, plain, (~r2_hidden('#skF_5', k3_xboole_0('#skF_6', '#skF_7')) | ~m1_subset_1(k3_xboole_0('#skF_6', '#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_86, c_69986])).
% 20.81/11.13  tff(c_70487, plain, (~m1_subset_1(k3_xboole_0('#skF_6', '#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_69987])).
% 20.81/11.13  tff(c_70493, plain, (~r1_tarski(k3_xboole_0('#skF_6', '#skF_7'), u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_56, c_70487])).
% 20.81/11.13  tff(c_70498, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54596, c_70493])).
% 20.81/11.13  tff(c_70499, plain, (~r2_hidden('#skF_5', k3_xboole_0('#skF_6', '#skF_7'))), inference(splitRight, [status(thm)], [c_69987])).
% 20.81/11.13  tff(c_70507, plain, (~r2_hidden('#skF_5', '#skF_7') | ~r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_10, c_70499])).
% 20.81/11.13  tff(c_70509, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_70507])).
% 20.81/11.13  tff(c_1497, plain, (![B_217, C_218, A_219]: (r2_hidden(B_217, C_218) | ~r2_hidden(C_218, u1_struct_0(k9_yellow_6(A_219, B_217))) | ~m1_subset_1(C_218, k1_zfmisc_1(u1_struct_0(A_219))) | ~m1_subset_1(B_217, u1_struct_0(A_219)) | ~l1_pre_topc(A_219) | ~v2_pre_topc(A_219) | v2_struct_0(A_219))), inference(cnfTransformation, [status(thm)], [f_144])).
% 20.81/11.13  tff(c_70520, plain, (![B_1586, B_1587, A_1588]: (r2_hidden(B_1586, B_1587) | ~m1_subset_1(B_1587, k1_zfmisc_1(u1_struct_0(A_1588))) | ~m1_subset_1(B_1586, u1_struct_0(A_1588)) | ~l1_pre_topc(A_1588) | ~v2_pre_topc(A_1588) | v2_struct_0(A_1588) | ~m1_subset_1(B_1587, u1_struct_0(k9_yellow_6(A_1588, B_1586))) | v1_xboole_0(u1_struct_0(k9_yellow_6(A_1588, B_1586))))), inference(resolution, [status(thm)], [c_40, c_1497])).
% 20.81/11.13  tff(c_70558, plain, (r2_hidden('#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_78, c_70520])).
% 20.81/11.13  tff(c_70573, plain, (r2_hidden('#skF_5', '#skF_6') | v2_struct_0('#skF_4') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_80, c_1155, c_70558])).
% 20.81/11.13  tff(c_70575, plain, $false, inference(negUnitSimplification, [status(thm)], [c_208, c_86, c_70509, c_70573])).
% 20.81/11.13  tff(c_70576, plain, (~r2_hidden('#skF_5', '#skF_7')), inference(splitRight, [status(thm)], [c_70507])).
% 20.81/11.13  tff(c_70820, plain, (![B_1591, B_1592, A_1593]: (r2_hidden(B_1591, B_1592) | ~m1_subset_1(B_1592, k1_zfmisc_1(u1_struct_0(A_1593))) | ~m1_subset_1(B_1591, u1_struct_0(A_1593)) | ~l1_pre_topc(A_1593) | ~v2_pre_topc(A_1593) | v2_struct_0(A_1593) | ~m1_subset_1(B_1592, u1_struct_0(k9_yellow_6(A_1593, B_1591))) | v1_xboole_0(u1_struct_0(k9_yellow_6(A_1593, B_1591))))), inference(resolution, [status(thm)], [c_40, c_1497])).
% 20.81/11.13  tff(c_70861, plain, (r2_hidden('#skF_5', '#skF_7') | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_76, c_70820])).
% 20.81/11.13  tff(c_70877, plain, (r2_hidden('#skF_5', '#skF_7') | v2_struct_0('#skF_4') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_80, c_1161, c_70861])).
% 20.81/11.13  tff(c_70879, plain, $false, inference(negUnitSimplification, [status(thm)], [c_208, c_86, c_70576, c_70877])).
% 20.81/11.13  tff(c_70881, plain, (v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(splitRight, [status(thm)], [c_199])).
% 20.81/11.13  tff(c_198, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_78, c_177])).
% 20.81/11.13  tff(c_70883, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_70881, c_198])).
% 20.81/11.13  tff(c_34, plain, (![A_16, B_17]: (r1_tarski(k3_xboole_0(A_16, B_17), A_16))), inference(cnfTransformation, [status(thm)], [f_51])).
% 20.81/11.13  tff(c_46, plain, (![A_23]: (k2_subset_1(A_23)=A_23)), inference(cnfTransformation, [status(thm)], [f_72])).
% 20.81/11.13  tff(c_48, plain, (![A_24]: (m1_subset_1(k2_subset_1(A_24), k1_zfmisc_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 20.81/11.13  tff(c_87, plain, (![A_24]: (m1_subset_1(A_24, k1_zfmisc_1(A_24)))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_48])).
% 20.81/11.13  tff(c_70974, plain, (![C_1617, B_1618, A_1619]: (~v1_xboole_0(C_1617) | ~m1_subset_1(B_1618, k1_zfmisc_1(C_1617)) | ~r2_hidden(A_1619, B_1618))), inference(cnfTransformation, [status(thm)], [f_97])).
% 20.81/11.13  tff(c_70989, plain, (![A_1620, A_1621]: (~v1_xboole_0(A_1620) | ~r2_hidden(A_1621, A_1620))), inference(resolution, [status(thm)], [c_87, c_70974])).
% 20.81/11.13  tff(c_70998, plain, (![A_1622, B_1623]: (~v1_xboole_0(A_1622) | r1_tarski(A_1622, B_1623))), inference(resolution, [status(thm)], [c_8, c_70989])).
% 20.81/11.13  tff(c_28, plain, (![B_15, A_14]: (B_15=A_14 | ~r1_tarski(B_15, A_14) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_49])).
% 20.81/11.13  tff(c_71015, plain, (![B_1627, A_1628]: (B_1627=A_1628 | ~r1_tarski(B_1627, A_1628) | ~v1_xboole_0(A_1628))), inference(resolution, [status(thm)], [c_70998, c_28])).
% 20.81/11.13  tff(c_71081, plain, (![A_1632, B_1633]: (k3_xboole_0(A_1632, B_1633)=A_1632 | ~v1_xboole_0(A_1632))), inference(resolution, [status(thm)], [c_34, c_71015])).
% 20.81/11.13  tff(c_71084, plain, (![B_1633]: (k3_xboole_0('#skF_6', B_1633)='#skF_6')), inference(resolution, [status(thm)], [c_70883, c_71081])).
% 20.81/11.13  tff(c_70880, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_199])).
% 20.81/11.13  tff(c_70996, plain, (![A_3, B_4]: (~v1_xboole_0(A_3) | r1_tarski(A_3, B_4))), inference(resolution, [status(thm)], [c_8, c_70989])).
% 20.81/11.13  tff(c_71033, plain, (![B_1629, A_1630]: (B_1629=A_1630 | ~v1_xboole_0(B_1629) | ~v1_xboole_0(A_1630))), inference(resolution, [status(thm)], [c_70996, c_71015])).
% 20.81/11.13  tff(c_71043, plain, (![A_1631]: (A_1631='#skF_6' | ~v1_xboole_0(A_1631))), inference(resolution, [status(thm)], [c_70883, c_71033])).
% 20.81/11.13  tff(c_71056, plain, ('#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_70880, c_71043])).
% 20.81/11.13  tff(c_42, plain, (![B_22, A_21]: (m1_subset_1(B_22, A_21) | ~v1_xboole_0(B_22) | ~v1_xboole_0(A_21))), inference(cnfTransformation, [status(thm)], [f_70])).
% 20.81/11.13  tff(c_205, plain, (~v1_xboole_0(k3_xboole_0('#skF_6', '#skF_7')) | ~v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_42, c_74])).
% 20.81/11.13  tff(c_70885, plain, (~v1_xboole_0(k3_xboole_0('#skF_6', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_70881, c_205])).
% 20.81/11.13  tff(c_71057, plain, (~v1_xboole_0(k3_xboole_0('#skF_6', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_71056, c_70885])).
% 20.81/11.13  tff(c_71100, plain, (~v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_71084, c_71057])).
% 20.81/11.13  tff(c_71103, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70883, c_71100])).
% 20.81/11.13  tff(c_71105, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_201])).
% 20.81/11.13  tff(c_71104, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_201])).
% 20.81/11.13  tff(c_71189, plain, (![C_1658, B_1659, A_1660]: (~v1_xboole_0(C_1658) | ~m1_subset_1(B_1659, k1_zfmisc_1(C_1658)) | ~r2_hidden(A_1660, B_1659))), inference(cnfTransformation, [status(thm)], [f_97])).
% 20.81/11.13  tff(c_71204, plain, (![A_1661, A_1662]: (~v1_xboole_0(A_1661) | ~r2_hidden(A_1662, A_1661))), inference(resolution, [status(thm)], [c_87, c_71189])).
% 20.81/11.13  tff(c_71213, plain, (![A_1663, B_1664]: (~v1_xboole_0(A_1663) | r1_tarski(A_1663, B_1664))), inference(resolution, [status(thm)], [c_8, c_71204])).
% 20.81/11.13  tff(c_71217, plain, (![B_1665, A_1666]: (B_1665=A_1666 | ~r1_tarski(B_1665, A_1666) | ~v1_xboole_0(A_1666))), inference(resolution, [status(thm)], [c_71213, c_28])).
% 20.81/11.13  tff(c_71248, plain, (![A_1670, B_1671]: (k3_xboole_0(A_1670, B_1671)=A_1670 | ~v1_xboole_0(A_1670))), inference(resolution, [status(thm)], [c_34, c_71217])).
% 20.81/11.13  tff(c_71255, plain, (![B_1672]: (k3_xboole_0('#skF_5', B_1672)='#skF_5')), inference(resolution, [status(thm)], [c_71104, c_71248])).
% 20.81/11.13  tff(c_101, plain, (![B_74, A_75]: (k3_xboole_0(B_74, A_75)=k3_xboole_0(A_75, B_74))), inference(cnfTransformation, [status(thm)], [f_27])).
% 20.81/11.13  tff(c_116, plain, (![B_74, A_75]: (r1_tarski(k3_xboole_0(B_74, A_75), A_75))), inference(superposition, [status(thm), theory('equality')], [c_101, c_34])).
% 20.81/11.13  tff(c_71289, plain, (![B_1673]: (r1_tarski('#skF_5', B_1673))), inference(superposition, [status(thm), theory('equality')], [c_71255, c_116])).
% 20.81/11.13  tff(c_71216, plain, (![B_1664, A_1663]: (B_1664=A_1663 | ~r1_tarski(B_1664, A_1663) | ~v1_xboole_0(A_1663))), inference(resolution, [status(thm)], [c_71213, c_28])).
% 20.81/11.13  tff(c_71357, plain, (![B_1678]: (B_1678='#skF_5' | ~v1_xboole_0(B_1678))), inference(resolution, [status(thm)], [c_71289, c_71216])).
% 20.81/11.13  tff(c_71364, plain, (u1_struct_0('#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_71105, c_71357])).
% 20.81/11.13  tff(c_71368, plain, (m1_subset_1('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_71364, c_80])).
% 20.81/11.13  tff(c_72729, plain, (![C_1764, A_1765, B_1766]: (m1_connsp_2(C_1764, A_1765, B_1766) | ~m1_subset_1(C_1764, u1_struct_0(k9_yellow_6(A_1765, B_1766))) | ~m1_subset_1(B_1766, u1_struct_0(A_1765)) | ~l1_pre_topc(A_1765) | ~v2_pre_topc(A_1765) | v2_struct_0(A_1765))), inference(cnfTransformation, [status(thm)], [f_159])).
% 20.81/11.13  tff(c_72740, plain, (m1_connsp_2('#skF_6', '#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_78, c_72729])).
% 20.81/11.13  tff(c_72748, plain, (m1_connsp_2('#skF_6', '#skF_4', '#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_71368, c_71364, c_72740])).
% 20.81/11.13  tff(c_72749, plain, (m1_connsp_2('#skF_6', '#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_86, c_72748])).
% 20.81/11.13  tff(c_72755, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_72749, c_64])).
% 20.81/11.13  tff(c_72758, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_5')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_71368, c_71364, c_71364, c_72755])).
% 20.81/11.13  tff(c_72759, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_86, c_72758])).
% 20.81/11.13  tff(c_54, plain, (![A_29, B_30]: (r1_tarski(A_29, B_30) | ~m1_subset_1(A_29, k1_zfmisc_1(B_30)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 20.81/11.13  tff(c_72781, plain, (r1_tarski('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_72759, c_54])).
% 20.81/11.13  tff(c_71299, plain, (![B_1673]: (B_1673='#skF_5' | ~r1_tarski(B_1673, '#skF_5'))), inference(resolution, [status(thm)], [c_71289, c_28])).
% 20.81/11.13  tff(c_72816, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_72781, c_71299])).
% 20.81/11.13  tff(c_72845, plain, (m1_subset_1('#skF_6', u1_struct_0(k9_yellow_6('#skF_4', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_72816, c_78])).
% 20.81/11.13  tff(c_71254, plain, (![B_1671]: (k3_xboole_0('#skF_5', B_1671)='#skF_5')), inference(resolution, [status(thm)], [c_71104, c_71248])).
% 20.81/11.13  tff(c_72841, plain, (![B_1671]: (k3_xboole_0('#skF_6', B_1671)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_72816, c_72816, c_71254])).
% 20.81/11.13  tff(c_72843, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_72816, c_71104])).
% 20.81/11.13  tff(c_72743, plain, (m1_connsp_2('#skF_7', '#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_76, c_72729])).
% 20.81/11.13  tff(c_72752, plain, (m1_connsp_2('#skF_7', '#skF_4', '#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_71368, c_71364, c_72743])).
% 20.81/11.13  tff(c_72753, plain, (m1_connsp_2('#skF_7', '#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_86, c_72752])).
% 20.81/11.13  tff(c_72761, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_72753, c_64])).
% 20.81/11.13  tff(c_72764, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_5')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_71368, c_71364, c_71364, c_72761])).
% 20.81/11.13  tff(c_72765, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_86, c_72764])).
% 20.81/11.13  tff(c_72797, plain, (r1_tarski('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_72765, c_54])).
% 20.81/11.13  tff(c_72913, plain, (r1_tarski('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_72816, c_72797])).
% 20.81/11.13  tff(c_72920, plain, ('#skF_7'='#skF_6' | ~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_72913, c_71216])).
% 20.81/11.13  tff(c_72929, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_72843, c_72920])).
% 20.81/11.13  tff(c_72844, plain, (~m1_subset_1(k3_xboole_0('#skF_6', '#skF_7'), u1_struct_0(k9_yellow_6('#skF_4', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_72816, c_74])).
% 20.81/11.13  tff(c_73264, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72845, c_72841, c_72929, c_72844])).
% 20.81/11.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 20.81/11.13  
% 20.81/11.13  Inference rules
% 20.81/11.13  ----------------------
% 20.81/11.13  #Ref     : 0
% 20.81/11.13  #Sup     : 20897
% 20.81/11.13  #Fact    : 0
% 20.81/11.13  #Define  : 0
% 20.81/11.13  #Split   : 41
% 20.81/11.13  #Chain   : 0
% 20.81/11.13  #Close   : 0
% 20.81/11.13  
% 20.81/11.13  Ordering : KBO
% 20.81/11.13  
% 20.81/11.13  Simplification rules
% 20.81/11.13  ----------------------
% 20.81/11.14  #Subsume      : 11425
% 20.81/11.14  #Demod        : 2779
% 20.81/11.14  #Tautology    : 2039
% 20.81/11.14  #SimpNegUnit  : 175
% 20.81/11.14  #BackRed      : 61
% 20.81/11.14  
% 20.81/11.14  #Partial instantiations: 0
% 20.81/11.14  #Strategies tried      : 1
% 20.81/11.14  
% 20.81/11.14  Timing (in seconds)
% 20.81/11.14  ----------------------
% 20.81/11.14  Preprocessing        : 0.35
% 20.81/11.14  Parsing              : 0.19
% 20.81/11.14  CNF conversion       : 0.03
% 20.81/11.14  Main loop            : 9.93
% 20.81/11.14  Inferencing          : 1.68
% 20.81/11.14  Reduction            : 3.38
% 20.81/11.14  Demodulation         : 2.71
% 20.81/11.14  BG Simplification    : 0.19
% 20.81/11.14  Subsumption          : 4.18
% 20.81/11.14  Abstraction          : 0.26
% 20.81/11.14  MUC search           : 0.00
% 20.81/11.14  Cooper               : 0.00
% 20.81/11.14  Total                : 10.34
% 20.81/11.14  Index Insertion      : 0.00
% 20.81/11.14  Index Deletion       : 0.00
% 20.81/11.14  Index Matching       : 0.00
% 20.81/11.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
