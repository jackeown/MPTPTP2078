%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:15 EST 2020

% Result     : Theorem 26.75s
% Output     : CNFRefutation 26.95s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 999 expanded)
%              Number of leaves         :   41 ( 394 expanded)
%              Depth                    :   21
%              Number of atoms          :  343 (3835 expanded)
%              Number of equality atoms :    5 (  13 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_connsp_2 > v3_pre_topc > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > l1_orders_2 > k4_subset_1 > k9_yellow_6 > k2_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k9_yellow_6,type,(
    k9_yellow_6: ( $i * $i ) > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_186,negated_conjecture,(
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
                   => m1_subset_1(k2_xboole_0(C,D),u1_struct_0(k9_yellow_6(A,B))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_waybel_9)).

tff(f_121,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => l1_orders_2(k9_yellow_6(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_yellow_6)).

tff(f_82,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_133,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ~ v2_struct_0(k9_yellow_6(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc20_yellow_6)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_167,axiom,(
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

tff(f_110,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ! [C] :
          ( m1_connsp_2(C,A,B)
         => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => m1_subset_1(k4_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_152,axiom,(
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

tff(f_78,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & v3_pre_topc(B,A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & v3_pre_topc(C,A)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k2_xboole_0(B,C),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_tops_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_66,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_64,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_62,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_163,plain,(
    ! [A_103,B_104] :
      ( l1_orders_2(k9_yellow_6(A_103,B_104))
      | ~ m1_subset_1(B_104,u1_struct_0(A_103))
      | ~ l1_pre_topc(A_103)
      | ~ v2_pre_topc(A_103)
      | v2_struct_0(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_180,plain,
    ( l1_orders_2(k9_yellow_6('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_163])).

tff(c_187,plain,
    ( l1_orders_2(k9_yellow_6('#skF_4','#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_180])).

tff(c_188,plain,(
    l1_orders_2(k9_yellow_6('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_187])).

tff(c_38,plain,(
    ! [A_27] :
      ( l1_struct_0(A_27)
      | ~ l1_orders_2(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_189,plain,(
    ! [A_105,B_106] :
      ( ~ v2_struct_0(k9_yellow_6(A_105,B_106))
      | ~ m1_subset_1(B_106,u1_struct_0(A_105))
      | ~ l1_pre_topc(A_105)
      | ~ v2_pre_topc(A_105)
      | v2_struct_0(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_206,plain,
    ( ~ v2_struct_0(k9_yellow_6('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_189])).

tff(c_213,plain,
    ( ~ v2_struct_0(k9_yellow_6('#skF_4','#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_206])).

tff(c_214,plain,(
    ~ v2_struct_0(k9_yellow_6('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_213])).

tff(c_10,plain,(
    ! [D_10,A_5,B_6] :
      ( ~ r2_hidden(D_10,A_5)
      | r2_hidden(D_10,k2_xboole_0(A_5,B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_60,plain,(
    m1_subset_1('#skF_6',u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_526,plain,(
    ! [C_149,A_150,B_151] :
      ( m1_connsp_2(C_149,A_150,B_151)
      | ~ m1_subset_1(C_149,u1_struct_0(k9_yellow_6(A_150,B_151)))
      | ~ m1_subset_1(B_151,u1_struct_0(A_150))
      | ~ l1_pre_topc(A_150)
      | ~ v2_pre_topc(A_150)
      | v2_struct_0(A_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_549,plain,
    ( m1_connsp_2('#skF_6','#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_526])).

tff(c_560,plain,
    ( m1_connsp_2('#skF_6','#skF_4','#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_549])).

tff(c_561,plain,(
    m1_connsp_2('#skF_6','#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_560])).

tff(c_42,plain,(
    ! [C_34,A_31,B_32] :
      ( m1_subset_1(C_34,k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ m1_connsp_2(C_34,A_31,B_32)
      | ~ m1_subset_1(B_32,u1_struct_0(A_31))
      | ~ l1_pre_topc(A_31)
      | ~ v2_pre_topc(A_31)
      | v2_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_567,plain,
    ( m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_561,c_42])).

tff(c_570,plain,
    ( m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_567])).

tff(c_571,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_570])).

tff(c_58,plain,(
    m1_subset_1('#skF_7',u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_552,plain,
    ( m1_connsp_2('#skF_7','#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_526])).

tff(c_564,plain,
    ( m1_connsp_2('#skF_7','#skF_4','#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_552])).

tff(c_565,plain,(
    m1_connsp_2('#skF_7','#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_564])).

tff(c_573,plain,
    ( m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_565,c_42])).

tff(c_576,plain,
    ( m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_573])).

tff(c_577,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_576])).

tff(c_28,plain,(
    ! [A_16,B_17,C_18] :
      ( k4_subset_1(A_16,B_17,C_18) = k2_xboole_0(B_17,C_18)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(A_16))
      | ~ m1_subset_1(B_17,k1_zfmisc_1(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_719,plain,(
    ! [B_161] :
      ( k4_subset_1(u1_struct_0('#skF_4'),B_161,'#skF_7') = k2_xboole_0(B_161,'#skF_7')
      | ~ m1_subset_1(B_161,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_577,c_28])).

tff(c_751,plain,(
    k4_subset_1(u1_struct_0('#skF_4'),'#skF_6','#skF_7') = k2_xboole_0('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_571,c_719])).

tff(c_26,plain,(
    ! [A_13,B_14,C_15] :
      ( m1_subset_1(k4_subset_1(A_13,B_14,C_15),k1_zfmisc_1(A_13))
      | ~ m1_subset_1(C_15,k1_zfmisc_1(A_13))
      | ~ m1_subset_1(B_14,k1_zfmisc_1(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_781,plain,
    ( m1_subset_1(k2_xboole_0('#skF_6','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_751,c_26])).

tff(c_785,plain,(
    m1_subset_1(k2_xboole_0('#skF_6','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_571,c_577,c_781])).

tff(c_32,plain,(
    ! [A_21,B_22] :
      ( r2_hidden(A_21,B_22)
      | v1_xboole_0(B_22)
      | ~ m1_subset_1(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_8274,plain,(
    ! [B_285,C_286,A_287] :
      ( r2_hidden(B_285,C_286)
      | ~ r2_hidden(C_286,u1_struct_0(k9_yellow_6(A_287,B_285)))
      | ~ m1_subset_1(C_286,k1_zfmisc_1(u1_struct_0(A_287)))
      | ~ m1_subset_1(B_285,u1_struct_0(A_287))
      | ~ l1_pre_topc(A_287)
      | ~ v2_pre_topc(A_287)
      | v2_struct_0(A_287) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_40863,plain,(
    ! [B_786,A_787,A_788] :
      ( r2_hidden(B_786,A_787)
      | ~ m1_subset_1(A_787,k1_zfmisc_1(u1_struct_0(A_788)))
      | ~ m1_subset_1(B_786,u1_struct_0(A_788))
      | ~ l1_pre_topc(A_788)
      | ~ v2_pre_topc(A_788)
      | v2_struct_0(A_788)
      | v1_xboole_0(u1_struct_0(k9_yellow_6(A_788,B_786)))
      | ~ m1_subset_1(A_787,u1_struct_0(k9_yellow_6(A_788,B_786))) ) ),
    inference(resolution,[status(thm)],[c_32,c_8274])).

tff(c_41000,plain,
    ( r2_hidden('#skF_5','#skF_7')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_58,c_40863])).

tff(c_41040,plain,
    ( r2_hidden('#skF_5','#skF_7')
    | v2_struct_0('#skF_4')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_577,c_41000])).

tff(c_41041,plain,
    ( r2_hidden('#skF_5','#skF_7')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_41040])).

tff(c_41043,plain,(
    v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_41041])).

tff(c_36,plain,(
    ! [A_26] :
      ( ~ v1_xboole_0(u1_struct_0(A_26))
      | ~ l1_struct_0(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_41086,plain,
    ( ~ l1_struct_0(k9_yellow_6('#skF_4','#skF_5'))
    | v2_struct_0(k9_yellow_6('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_41043,c_36])).

tff(c_41112,plain,(
    ~ l1_struct_0(k9_yellow_6('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_214,c_41086])).

tff(c_41435,plain,(
    ~ l1_orders_2(k9_yellow_6('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_38,c_41112])).

tff(c_41439,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_41435])).

tff(c_41441,plain,(
    ~ v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_41041])).

tff(c_8860,plain,(
    ! [B_296,C_297,A_298] :
      ( v3_pre_topc(k2_xboole_0(B_296,C_297),A_298)
      | ~ m1_subset_1(C_297,k1_zfmisc_1(u1_struct_0(A_298)))
      | ~ v3_pre_topc(C_297,A_298)
      | ~ m1_subset_1(B_296,k1_zfmisc_1(u1_struct_0(A_298)))
      | ~ v3_pre_topc(B_296,A_298)
      | ~ l1_pre_topc(A_298)
      | ~ v2_pre_topc(A_298) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_8872,plain,(
    ! [B_296] :
      ( v3_pre_topc(k2_xboole_0(B_296,'#skF_6'),'#skF_4')
      | ~ v3_pre_topc('#skF_6','#skF_4')
      | ~ m1_subset_1(B_296,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v3_pre_topc(B_296,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_571,c_8860])).

tff(c_8908,plain,(
    ! [B_296] :
      ( v3_pre_topc(k2_xboole_0(B_296,'#skF_6'),'#skF_4')
      | ~ v3_pre_topc('#skF_6','#skF_4')
      | ~ m1_subset_1(B_296,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v3_pre_topc(B_296,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_8872])).

tff(c_14199,plain,(
    ~ v3_pre_topc('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_8908])).

tff(c_8533,plain,(
    ! [C_290,A_291,B_292] :
      ( v3_pre_topc(C_290,A_291)
      | ~ r2_hidden(C_290,u1_struct_0(k9_yellow_6(A_291,B_292)))
      | ~ m1_subset_1(C_290,k1_zfmisc_1(u1_struct_0(A_291)))
      | ~ m1_subset_1(B_292,u1_struct_0(A_291))
      | ~ l1_pre_topc(A_291)
      | ~ v2_pre_topc(A_291)
      | v2_struct_0(A_291) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_41752,plain,(
    ! [A_791,A_792,B_793] :
      ( v3_pre_topc(A_791,A_792)
      | ~ m1_subset_1(A_791,k1_zfmisc_1(u1_struct_0(A_792)))
      | ~ m1_subset_1(B_793,u1_struct_0(A_792))
      | ~ l1_pre_topc(A_792)
      | ~ v2_pre_topc(A_792)
      | v2_struct_0(A_792)
      | v1_xboole_0(u1_struct_0(k9_yellow_6(A_792,B_793)))
      | ~ m1_subset_1(A_791,u1_struct_0(k9_yellow_6(A_792,B_793))) ) ),
    inference(resolution,[status(thm)],[c_32,c_8533])).

tff(c_41886,plain,
    ( v3_pre_topc('#skF_6','#skF_4')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_60,c_41752])).

tff(c_41925,plain,
    ( v3_pre_topc('#skF_6','#skF_4')
    | v2_struct_0('#skF_4')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_571,c_41886])).

tff(c_41927,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_41441,c_68,c_14199,c_41925])).

tff(c_66068,plain,(
    ! [B_1141] :
      ( v3_pre_topc(k2_xboole_0(B_1141,'#skF_6'),'#skF_4')
      | ~ m1_subset_1(B_1141,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v3_pre_topc(B_1141,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_8908])).

tff(c_66133,plain,
    ( v3_pre_topc(k2_xboole_0(k2_xboole_0('#skF_6','#skF_7'),'#skF_6'),'#skF_4')
    | ~ v3_pre_topc(k2_xboole_0('#skF_6','#skF_7'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_785,c_66068])).

tff(c_66175,plain,(
    ~ v3_pre_topc(k2_xboole_0('#skF_6','#skF_7'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_66133])).

tff(c_41929,plain,(
    v3_pre_topc('#skF_6','#skF_4') ),
    inference(splitRight,[status(thm)],[c_8908])).

tff(c_8870,plain,(
    ! [B_296] :
      ( v3_pre_topc(k2_xboole_0(B_296,'#skF_7'),'#skF_4')
      | ~ v3_pre_topc('#skF_7','#skF_4')
      | ~ m1_subset_1(B_296,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v3_pre_topc(B_296,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_577,c_8860])).

tff(c_8905,plain,(
    ! [B_296] :
      ( v3_pre_topc(k2_xboole_0(B_296,'#skF_7'),'#skF_4')
      | ~ v3_pre_topc('#skF_7','#skF_4')
      | ~ m1_subset_1(B_296,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v3_pre_topc(B_296,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_8870])).

tff(c_41963,plain,(
    ~ v3_pre_topc('#skF_7','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_8905])).

tff(c_65801,plain,(
    ! [A_1135,A_1136,B_1137] :
      ( v3_pre_topc(A_1135,A_1136)
      | ~ m1_subset_1(A_1135,k1_zfmisc_1(u1_struct_0(A_1136)))
      | ~ m1_subset_1(B_1137,u1_struct_0(A_1136))
      | ~ l1_pre_topc(A_1136)
      | ~ v2_pre_topc(A_1136)
      | v2_struct_0(A_1136)
      | v1_xboole_0(u1_struct_0(k9_yellow_6(A_1136,B_1137)))
      | ~ m1_subset_1(A_1135,u1_struct_0(k9_yellow_6(A_1136,B_1137))) ) ),
    inference(resolution,[status(thm)],[c_32,c_8533])).

tff(c_65914,plain,
    ( v3_pre_topc('#skF_7','#skF_4')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_58,c_65801])).

tff(c_65948,plain,
    ( v3_pre_topc('#skF_7','#skF_4')
    | v2_struct_0('#skF_4')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_577,c_65914])).

tff(c_65949,plain,(
    v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_41963,c_65948])).

tff(c_66000,plain,
    ( ~ l1_struct_0(k9_yellow_6('#skF_4','#skF_5'))
    | v2_struct_0(k9_yellow_6('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_65949,c_36])).

tff(c_66026,plain,(
    ~ l1_struct_0(k9_yellow_6('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_214,c_66000])).

tff(c_66029,plain,(
    ~ l1_orders_2(k9_yellow_6('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_38,c_66026])).

tff(c_66033,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_66029])).

tff(c_66220,plain,(
    ! [B_1144] :
      ( v3_pre_topc(k2_xboole_0(B_1144,'#skF_7'),'#skF_4')
      | ~ m1_subset_1(B_1144,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v3_pre_topc(B_1144,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_8905])).

tff(c_66259,plain,
    ( v3_pre_topc(k2_xboole_0('#skF_6','#skF_7'),'#skF_4')
    | ~ v3_pre_topc('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_571,c_66220])).

tff(c_66299,plain,(
    v3_pre_topc(k2_xboole_0('#skF_6','#skF_7'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_41929,c_66259])).

tff(c_66301,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66175,c_66299])).

tff(c_66303,plain,(
    v3_pre_topc(k2_xboole_0('#skF_6','#skF_7'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_66133])).

tff(c_11659,plain,(
    ! [C_351,A_352,B_353] :
      ( r2_hidden(C_351,u1_struct_0(k9_yellow_6(A_352,B_353)))
      | ~ v3_pre_topc(C_351,A_352)
      | ~ r2_hidden(B_353,C_351)
      | ~ m1_subset_1(C_351,k1_zfmisc_1(u1_struct_0(A_352)))
      | ~ m1_subset_1(B_353,u1_struct_0(A_352))
      | ~ l1_pre_topc(A_352)
      | ~ v2_pre_topc(A_352)
      | v2_struct_0(A_352) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_30,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(A_19,B_20)
      | ~ r2_hidden(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_88670,plain,(
    ! [C_1469,A_1470,B_1471] :
      ( m1_subset_1(C_1469,u1_struct_0(k9_yellow_6(A_1470,B_1471)))
      | ~ v3_pre_topc(C_1469,A_1470)
      | ~ r2_hidden(B_1471,C_1469)
      | ~ m1_subset_1(C_1469,k1_zfmisc_1(u1_struct_0(A_1470)))
      | ~ m1_subset_1(B_1471,u1_struct_0(A_1470))
      | ~ l1_pre_topc(A_1470)
      | ~ v2_pre_topc(A_1470)
      | v2_struct_0(A_1470) ) ),
    inference(resolution,[status(thm)],[c_11659,c_30])).

tff(c_56,plain,(
    ~ m1_subset_1(k2_xboole_0('#skF_6','#skF_7'),u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_88690,plain,
    ( ~ v3_pre_topc(k2_xboole_0('#skF_6','#skF_7'),'#skF_4')
    | ~ r2_hidden('#skF_5',k2_xboole_0('#skF_6','#skF_7'))
    | ~ m1_subset_1(k2_xboole_0('#skF_6','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_88670,c_56])).

tff(c_88698,plain,
    ( ~ r2_hidden('#skF_5',k2_xboole_0('#skF_6','#skF_7'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_785,c_66303,c_88690])).

tff(c_88699,plain,(
    ~ r2_hidden('#skF_5',k2_xboole_0('#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_88698])).

tff(c_88710,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_10,c_88699])).

tff(c_89719,plain,(
    ! [B_1477,A_1478,A_1479] :
      ( r2_hidden(B_1477,A_1478)
      | ~ m1_subset_1(A_1478,k1_zfmisc_1(u1_struct_0(A_1479)))
      | ~ m1_subset_1(B_1477,u1_struct_0(A_1479))
      | ~ l1_pre_topc(A_1479)
      | ~ v2_pre_topc(A_1479)
      | v2_struct_0(A_1479)
      | v1_xboole_0(u1_struct_0(k9_yellow_6(A_1479,B_1477)))
      | ~ m1_subset_1(A_1478,u1_struct_0(k9_yellow_6(A_1479,B_1477))) ) ),
    inference(resolution,[status(thm)],[c_32,c_8274])).

tff(c_89837,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_60,c_89719])).

tff(c_89872,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | v2_struct_0('#skF_4')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_571,c_89837])).

tff(c_89873,plain,(
    v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_88710,c_89872])).

tff(c_89920,plain,
    ( ~ l1_struct_0(k9_yellow_6('#skF_4','#skF_5'))
    | v2_struct_0(k9_yellow_6('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_89873,c_36])).

tff(c_89946,plain,(
    ~ l1_struct_0(k9_yellow_6('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_214,c_89920])).

tff(c_89949,plain,(
    ~ l1_orders_2(k9_yellow_6('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_38,c_89946])).

tff(c_89953,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_89949])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:40:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 26.75/16.82  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 26.80/16.84  
% 26.80/16.84  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 26.80/16.84  %$ m1_connsp_2 > v3_pre_topc > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > l1_orders_2 > k4_subset_1 > k9_yellow_6 > k2_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 26.80/16.84  
% 26.80/16.84  %Foreground sorts:
% 26.80/16.84  
% 26.80/16.84  
% 26.80/16.84  %Background operators:
% 26.80/16.84  
% 26.80/16.84  
% 26.80/16.84  %Foreground operators:
% 26.80/16.84  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 26.80/16.84  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 26.80/16.84  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 26.80/16.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 26.80/16.84  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 26.80/16.84  tff('#skF_1', type, '#skF_1': $i > $i).
% 26.80/16.84  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 26.80/16.84  tff('#skF_7', type, '#skF_7': $i).
% 26.80/16.84  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 26.80/16.84  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 26.80/16.84  tff('#skF_5', type, '#skF_5': $i).
% 26.80/16.84  tff('#skF_6', type, '#skF_6': $i).
% 26.80/16.84  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 26.80/16.84  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 26.80/16.84  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 26.80/16.84  tff(k9_yellow_6, type, k9_yellow_6: ($i * $i) > $i).
% 26.80/16.84  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 26.80/16.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 26.80/16.84  tff(k3_tarski, type, k3_tarski: $i > $i).
% 26.80/16.84  tff('#skF_4', type, '#skF_4': $i).
% 26.80/16.84  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 26.80/16.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 26.80/16.84  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 26.80/16.84  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 26.80/16.84  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 26.80/16.84  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 26.80/16.84  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 26.80/16.84  
% 26.95/16.86  tff(f_186, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(k9_yellow_6(A, B))) => (![D]: (m1_subset_1(D, u1_struct_0(k9_yellow_6(A, B))) => m1_subset_1(k2_xboole_0(C, D), u1_struct_0(k9_yellow_6(A, B))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_waybel_9)).
% 26.95/16.86  tff(f_121, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => l1_orders_2(k9_yellow_6(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_yellow_6)).
% 26.95/16.86  tff(f_82, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 26.95/16.86  tff(f_133, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ~v2_struct_0(k9_yellow_6(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc20_yellow_6)).
% 26.95/16.86  tff(f_40, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 26.95/16.86  tff(f_167, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(k9_yellow_6(A, B))) => m1_connsp_2(C, A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_waybel_9)).
% 26.95/16.86  tff(f_110, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (![C]: (m1_connsp_2(C, A, B) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 26.95/16.86  tff(f_54, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 26.95/16.86  tff(f_48, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => m1_subset_1(k4_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 26.95/16.86  tff(f_64, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 26.95/16.86  tff(f_152, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(C, u1_struct_0(k9_yellow_6(A, B))) <=> (r2_hidden(B, C) & v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_yellow_6)).
% 26.95/16.86  tff(f_78, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 26.95/16.86  tff(f_96, axiom, (![A, B, C]: ((((((v2_pre_topc(A) & l1_pre_topc(A)) & v3_pre_topc(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & v3_pre_topc(C, A)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k2_xboole_0(B, C), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_tops_1)).
% 26.95/16.86  tff(f_58, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 26.95/16.86  tff(c_68, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_186])).
% 26.95/16.86  tff(c_66, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_186])).
% 26.95/16.86  tff(c_64, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_186])).
% 26.95/16.86  tff(c_62, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_186])).
% 26.95/16.86  tff(c_163, plain, (![A_103, B_104]: (l1_orders_2(k9_yellow_6(A_103, B_104)) | ~m1_subset_1(B_104, u1_struct_0(A_103)) | ~l1_pre_topc(A_103) | ~v2_pre_topc(A_103) | v2_struct_0(A_103))), inference(cnfTransformation, [status(thm)], [f_121])).
% 26.95/16.86  tff(c_180, plain, (l1_orders_2(k9_yellow_6('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_62, c_163])).
% 26.95/16.86  tff(c_187, plain, (l1_orders_2(k9_yellow_6('#skF_4', '#skF_5')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_180])).
% 26.95/16.86  tff(c_188, plain, (l1_orders_2(k9_yellow_6('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_68, c_187])).
% 26.95/16.86  tff(c_38, plain, (![A_27]: (l1_struct_0(A_27) | ~l1_orders_2(A_27))), inference(cnfTransformation, [status(thm)], [f_82])).
% 26.95/16.86  tff(c_189, plain, (![A_105, B_106]: (~v2_struct_0(k9_yellow_6(A_105, B_106)) | ~m1_subset_1(B_106, u1_struct_0(A_105)) | ~l1_pre_topc(A_105) | ~v2_pre_topc(A_105) | v2_struct_0(A_105))), inference(cnfTransformation, [status(thm)], [f_133])).
% 26.95/16.86  tff(c_206, plain, (~v2_struct_0(k9_yellow_6('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_62, c_189])).
% 26.95/16.86  tff(c_213, plain, (~v2_struct_0(k9_yellow_6('#skF_4', '#skF_5')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_206])).
% 26.95/16.86  tff(c_214, plain, (~v2_struct_0(k9_yellow_6('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_68, c_213])).
% 26.95/16.86  tff(c_10, plain, (![D_10, A_5, B_6]: (~r2_hidden(D_10, A_5) | r2_hidden(D_10, k2_xboole_0(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 26.95/16.86  tff(c_60, plain, (m1_subset_1('#skF_6', u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_186])).
% 26.95/16.86  tff(c_526, plain, (![C_149, A_150, B_151]: (m1_connsp_2(C_149, A_150, B_151) | ~m1_subset_1(C_149, u1_struct_0(k9_yellow_6(A_150, B_151))) | ~m1_subset_1(B_151, u1_struct_0(A_150)) | ~l1_pre_topc(A_150) | ~v2_pre_topc(A_150) | v2_struct_0(A_150))), inference(cnfTransformation, [status(thm)], [f_167])).
% 26.95/16.86  tff(c_549, plain, (m1_connsp_2('#skF_6', '#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_60, c_526])).
% 26.95/16.86  tff(c_560, plain, (m1_connsp_2('#skF_6', '#skF_4', '#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_549])).
% 26.95/16.86  tff(c_561, plain, (m1_connsp_2('#skF_6', '#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_68, c_560])).
% 26.95/16.86  tff(c_42, plain, (![C_34, A_31, B_32]: (m1_subset_1(C_34, k1_zfmisc_1(u1_struct_0(A_31))) | ~m1_connsp_2(C_34, A_31, B_32) | ~m1_subset_1(B_32, u1_struct_0(A_31)) | ~l1_pre_topc(A_31) | ~v2_pre_topc(A_31) | v2_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_110])).
% 26.95/16.86  tff(c_567, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_561, c_42])).
% 26.95/16.86  tff(c_570, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_567])).
% 26.95/16.86  tff(c_571, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_68, c_570])).
% 26.95/16.86  tff(c_58, plain, (m1_subset_1('#skF_7', u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_186])).
% 26.95/16.86  tff(c_552, plain, (m1_connsp_2('#skF_7', '#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_58, c_526])).
% 26.95/16.86  tff(c_564, plain, (m1_connsp_2('#skF_7', '#skF_4', '#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_552])).
% 26.95/16.86  tff(c_565, plain, (m1_connsp_2('#skF_7', '#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_68, c_564])).
% 26.95/16.86  tff(c_573, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_565, c_42])).
% 26.95/16.86  tff(c_576, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_573])).
% 26.95/16.86  tff(c_577, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_68, c_576])).
% 26.95/16.86  tff(c_28, plain, (![A_16, B_17, C_18]: (k4_subset_1(A_16, B_17, C_18)=k2_xboole_0(B_17, C_18) | ~m1_subset_1(C_18, k1_zfmisc_1(A_16)) | ~m1_subset_1(B_17, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 26.95/16.86  tff(c_719, plain, (![B_161]: (k4_subset_1(u1_struct_0('#skF_4'), B_161, '#skF_7')=k2_xboole_0(B_161, '#skF_7') | ~m1_subset_1(B_161, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_577, c_28])).
% 26.95/16.86  tff(c_751, plain, (k4_subset_1(u1_struct_0('#skF_4'), '#skF_6', '#skF_7')=k2_xboole_0('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_571, c_719])).
% 26.95/16.86  tff(c_26, plain, (![A_13, B_14, C_15]: (m1_subset_1(k4_subset_1(A_13, B_14, C_15), k1_zfmisc_1(A_13)) | ~m1_subset_1(C_15, k1_zfmisc_1(A_13)) | ~m1_subset_1(B_14, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 26.95/16.86  tff(c_781, plain, (m1_subset_1(k2_xboole_0('#skF_6', '#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_751, c_26])).
% 26.95/16.86  tff(c_785, plain, (m1_subset_1(k2_xboole_0('#skF_6', '#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_571, c_577, c_781])).
% 26.95/16.86  tff(c_32, plain, (![A_21, B_22]: (r2_hidden(A_21, B_22) | v1_xboole_0(B_22) | ~m1_subset_1(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_64])).
% 26.95/16.86  tff(c_8274, plain, (![B_285, C_286, A_287]: (r2_hidden(B_285, C_286) | ~r2_hidden(C_286, u1_struct_0(k9_yellow_6(A_287, B_285))) | ~m1_subset_1(C_286, k1_zfmisc_1(u1_struct_0(A_287))) | ~m1_subset_1(B_285, u1_struct_0(A_287)) | ~l1_pre_topc(A_287) | ~v2_pre_topc(A_287) | v2_struct_0(A_287))), inference(cnfTransformation, [status(thm)], [f_152])).
% 26.95/16.86  tff(c_40863, plain, (![B_786, A_787, A_788]: (r2_hidden(B_786, A_787) | ~m1_subset_1(A_787, k1_zfmisc_1(u1_struct_0(A_788))) | ~m1_subset_1(B_786, u1_struct_0(A_788)) | ~l1_pre_topc(A_788) | ~v2_pre_topc(A_788) | v2_struct_0(A_788) | v1_xboole_0(u1_struct_0(k9_yellow_6(A_788, B_786))) | ~m1_subset_1(A_787, u1_struct_0(k9_yellow_6(A_788, B_786))))), inference(resolution, [status(thm)], [c_32, c_8274])).
% 26.95/16.86  tff(c_41000, plain, (r2_hidden('#skF_5', '#skF_7') | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_58, c_40863])).
% 26.95/16.86  tff(c_41040, plain, (r2_hidden('#skF_5', '#skF_7') | v2_struct_0('#skF_4') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_577, c_41000])).
% 26.95/16.86  tff(c_41041, plain, (r2_hidden('#skF_5', '#skF_7') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_68, c_41040])).
% 26.95/16.86  tff(c_41043, plain, (v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(splitLeft, [status(thm)], [c_41041])).
% 26.95/16.86  tff(c_36, plain, (![A_26]: (~v1_xboole_0(u1_struct_0(A_26)) | ~l1_struct_0(A_26) | v2_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_78])).
% 26.95/16.86  tff(c_41086, plain, (~l1_struct_0(k9_yellow_6('#skF_4', '#skF_5')) | v2_struct_0(k9_yellow_6('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_41043, c_36])).
% 26.95/16.86  tff(c_41112, plain, (~l1_struct_0(k9_yellow_6('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_214, c_41086])).
% 26.95/16.86  tff(c_41435, plain, (~l1_orders_2(k9_yellow_6('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_38, c_41112])).
% 26.95/16.86  tff(c_41439, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_188, c_41435])).
% 26.95/16.86  tff(c_41441, plain, (~v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(splitRight, [status(thm)], [c_41041])).
% 26.95/16.86  tff(c_8860, plain, (![B_296, C_297, A_298]: (v3_pre_topc(k2_xboole_0(B_296, C_297), A_298) | ~m1_subset_1(C_297, k1_zfmisc_1(u1_struct_0(A_298))) | ~v3_pre_topc(C_297, A_298) | ~m1_subset_1(B_296, k1_zfmisc_1(u1_struct_0(A_298))) | ~v3_pre_topc(B_296, A_298) | ~l1_pre_topc(A_298) | ~v2_pre_topc(A_298))), inference(cnfTransformation, [status(thm)], [f_96])).
% 26.95/16.86  tff(c_8872, plain, (![B_296]: (v3_pre_topc(k2_xboole_0(B_296, '#skF_6'), '#skF_4') | ~v3_pre_topc('#skF_6', '#skF_4') | ~m1_subset_1(B_296, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v3_pre_topc(B_296, '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_571, c_8860])).
% 26.95/16.86  tff(c_8908, plain, (![B_296]: (v3_pre_topc(k2_xboole_0(B_296, '#skF_6'), '#skF_4') | ~v3_pre_topc('#skF_6', '#skF_4') | ~m1_subset_1(B_296, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v3_pre_topc(B_296, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_8872])).
% 26.95/16.86  tff(c_14199, plain, (~v3_pre_topc('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_8908])).
% 26.95/16.86  tff(c_8533, plain, (![C_290, A_291, B_292]: (v3_pre_topc(C_290, A_291) | ~r2_hidden(C_290, u1_struct_0(k9_yellow_6(A_291, B_292))) | ~m1_subset_1(C_290, k1_zfmisc_1(u1_struct_0(A_291))) | ~m1_subset_1(B_292, u1_struct_0(A_291)) | ~l1_pre_topc(A_291) | ~v2_pre_topc(A_291) | v2_struct_0(A_291))), inference(cnfTransformation, [status(thm)], [f_152])).
% 26.95/16.86  tff(c_41752, plain, (![A_791, A_792, B_793]: (v3_pre_topc(A_791, A_792) | ~m1_subset_1(A_791, k1_zfmisc_1(u1_struct_0(A_792))) | ~m1_subset_1(B_793, u1_struct_0(A_792)) | ~l1_pre_topc(A_792) | ~v2_pre_topc(A_792) | v2_struct_0(A_792) | v1_xboole_0(u1_struct_0(k9_yellow_6(A_792, B_793))) | ~m1_subset_1(A_791, u1_struct_0(k9_yellow_6(A_792, B_793))))), inference(resolution, [status(thm)], [c_32, c_8533])).
% 26.95/16.86  tff(c_41886, plain, (v3_pre_topc('#skF_6', '#skF_4') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_60, c_41752])).
% 26.95/16.86  tff(c_41925, plain, (v3_pre_topc('#skF_6', '#skF_4') | v2_struct_0('#skF_4') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_571, c_41886])).
% 26.95/16.86  tff(c_41927, plain, $false, inference(negUnitSimplification, [status(thm)], [c_41441, c_68, c_14199, c_41925])).
% 26.95/16.86  tff(c_66068, plain, (![B_1141]: (v3_pre_topc(k2_xboole_0(B_1141, '#skF_6'), '#skF_4') | ~m1_subset_1(B_1141, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v3_pre_topc(B_1141, '#skF_4'))), inference(splitRight, [status(thm)], [c_8908])).
% 26.95/16.86  tff(c_66133, plain, (v3_pre_topc(k2_xboole_0(k2_xboole_0('#skF_6', '#skF_7'), '#skF_6'), '#skF_4') | ~v3_pre_topc(k2_xboole_0('#skF_6', '#skF_7'), '#skF_4')), inference(resolution, [status(thm)], [c_785, c_66068])).
% 26.95/16.86  tff(c_66175, plain, (~v3_pre_topc(k2_xboole_0('#skF_6', '#skF_7'), '#skF_4')), inference(splitLeft, [status(thm)], [c_66133])).
% 26.95/16.86  tff(c_41929, plain, (v3_pre_topc('#skF_6', '#skF_4')), inference(splitRight, [status(thm)], [c_8908])).
% 26.95/16.86  tff(c_8870, plain, (![B_296]: (v3_pre_topc(k2_xboole_0(B_296, '#skF_7'), '#skF_4') | ~v3_pre_topc('#skF_7', '#skF_4') | ~m1_subset_1(B_296, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v3_pre_topc(B_296, '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_577, c_8860])).
% 26.95/16.86  tff(c_8905, plain, (![B_296]: (v3_pre_topc(k2_xboole_0(B_296, '#skF_7'), '#skF_4') | ~v3_pre_topc('#skF_7', '#skF_4') | ~m1_subset_1(B_296, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v3_pre_topc(B_296, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_8870])).
% 26.95/16.86  tff(c_41963, plain, (~v3_pre_topc('#skF_7', '#skF_4')), inference(splitLeft, [status(thm)], [c_8905])).
% 26.95/16.86  tff(c_65801, plain, (![A_1135, A_1136, B_1137]: (v3_pre_topc(A_1135, A_1136) | ~m1_subset_1(A_1135, k1_zfmisc_1(u1_struct_0(A_1136))) | ~m1_subset_1(B_1137, u1_struct_0(A_1136)) | ~l1_pre_topc(A_1136) | ~v2_pre_topc(A_1136) | v2_struct_0(A_1136) | v1_xboole_0(u1_struct_0(k9_yellow_6(A_1136, B_1137))) | ~m1_subset_1(A_1135, u1_struct_0(k9_yellow_6(A_1136, B_1137))))), inference(resolution, [status(thm)], [c_32, c_8533])).
% 26.95/16.86  tff(c_65914, plain, (v3_pre_topc('#skF_7', '#skF_4') | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_58, c_65801])).
% 26.95/16.86  tff(c_65948, plain, (v3_pre_topc('#skF_7', '#skF_4') | v2_struct_0('#skF_4') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_577, c_65914])).
% 26.95/16.86  tff(c_65949, plain, (v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_68, c_41963, c_65948])).
% 26.95/16.86  tff(c_66000, plain, (~l1_struct_0(k9_yellow_6('#skF_4', '#skF_5')) | v2_struct_0(k9_yellow_6('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_65949, c_36])).
% 26.95/16.86  tff(c_66026, plain, (~l1_struct_0(k9_yellow_6('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_214, c_66000])).
% 26.95/16.86  tff(c_66029, plain, (~l1_orders_2(k9_yellow_6('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_38, c_66026])).
% 26.95/16.86  tff(c_66033, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_188, c_66029])).
% 26.95/16.86  tff(c_66220, plain, (![B_1144]: (v3_pre_topc(k2_xboole_0(B_1144, '#skF_7'), '#skF_4') | ~m1_subset_1(B_1144, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v3_pre_topc(B_1144, '#skF_4'))), inference(splitRight, [status(thm)], [c_8905])).
% 26.95/16.86  tff(c_66259, plain, (v3_pre_topc(k2_xboole_0('#skF_6', '#skF_7'), '#skF_4') | ~v3_pre_topc('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_571, c_66220])).
% 26.95/16.86  tff(c_66299, plain, (v3_pre_topc(k2_xboole_0('#skF_6', '#skF_7'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_41929, c_66259])).
% 26.95/16.86  tff(c_66301, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66175, c_66299])).
% 26.95/16.86  tff(c_66303, plain, (v3_pre_topc(k2_xboole_0('#skF_6', '#skF_7'), '#skF_4')), inference(splitRight, [status(thm)], [c_66133])).
% 26.95/16.86  tff(c_11659, plain, (![C_351, A_352, B_353]: (r2_hidden(C_351, u1_struct_0(k9_yellow_6(A_352, B_353))) | ~v3_pre_topc(C_351, A_352) | ~r2_hidden(B_353, C_351) | ~m1_subset_1(C_351, k1_zfmisc_1(u1_struct_0(A_352))) | ~m1_subset_1(B_353, u1_struct_0(A_352)) | ~l1_pre_topc(A_352) | ~v2_pre_topc(A_352) | v2_struct_0(A_352))), inference(cnfTransformation, [status(thm)], [f_152])).
% 26.95/16.86  tff(c_30, plain, (![A_19, B_20]: (m1_subset_1(A_19, B_20) | ~r2_hidden(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_58])).
% 26.95/16.86  tff(c_88670, plain, (![C_1469, A_1470, B_1471]: (m1_subset_1(C_1469, u1_struct_0(k9_yellow_6(A_1470, B_1471))) | ~v3_pre_topc(C_1469, A_1470) | ~r2_hidden(B_1471, C_1469) | ~m1_subset_1(C_1469, k1_zfmisc_1(u1_struct_0(A_1470))) | ~m1_subset_1(B_1471, u1_struct_0(A_1470)) | ~l1_pre_topc(A_1470) | ~v2_pre_topc(A_1470) | v2_struct_0(A_1470))), inference(resolution, [status(thm)], [c_11659, c_30])).
% 26.95/16.86  tff(c_56, plain, (~m1_subset_1(k2_xboole_0('#skF_6', '#skF_7'), u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_186])).
% 26.95/16.86  tff(c_88690, plain, (~v3_pre_topc(k2_xboole_0('#skF_6', '#skF_7'), '#skF_4') | ~r2_hidden('#skF_5', k2_xboole_0('#skF_6', '#skF_7')) | ~m1_subset_1(k2_xboole_0('#skF_6', '#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_88670, c_56])).
% 26.95/16.86  tff(c_88698, plain, (~r2_hidden('#skF_5', k2_xboole_0('#skF_6', '#skF_7')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_785, c_66303, c_88690])).
% 26.95/16.86  tff(c_88699, plain, (~r2_hidden('#skF_5', k2_xboole_0('#skF_6', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_68, c_88698])).
% 26.95/16.86  tff(c_88710, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_10, c_88699])).
% 26.95/16.86  tff(c_89719, plain, (![B_1477, A_1478, A_1479]: (r2_hidden(B_1477, A_1478) | ~m1_subset_1(A_1478, k1_zfmisc_1(u1_struct_0(A_1479))) | ~m1_subset_1(B_1477, u1_struct_0(A_1479)) | ~l1_pre_topc(A_1479) | ~v2_pre_topc(A_1479) | v2_struct_0(A_1479) | v1_xboole_0(u1_struct_0(k9_yellow_6(A_1479, B_1477))) | ~m1_subset_1(A_1478, u1_struct_0(k9_yellow_6(A_1479, B_1477))))), inference(resolution, [status(thm)], [c_32, c_8274])).
% 26.95/16.86  tff(c_89837, plain, (r2_hidden('#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_60, c_89719])).
% 26.95/16.86  tff(c_89872, plain, (r2_hidden('#skF_5', '#skF_6') | v2_struct_0('#skF_4') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_571, c_89837])).
% 26.95/16.86  tff(c_89873, plain, (v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_68, c_88710, c_89872])).
% 26.95/16.86  tff(c_89920, plain, (~l1_struct_0(k9_yellow_6('#skF_4', '#skF_5')) | v2_struct_0(k9_yellow_6('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_89873, c_36])).
% 26.95/16.86  tff(c_89946, plain, (~l1_struct_0(k9_yellow_6('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_214, c_89920])).
% 26.95/16.86  tff(c_89949, plain, (~l1_orders_2(k9_yellow_6('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_38, c_89946])).
% 26.95/16.86  tff(c_89953, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_188, c_89949])).
% 26.95/16.86  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 26.95/16.86  
% 26.95/16.86  Inference rules
% 26.95/16.86  ----------------------
% 26.95/16.86  #Ref     : 0
% 26.95/16.86  #Sup     : 19927
% 26.95/16.86  #Fact    : 24
% 26.95/16.86  #Define  : 0
% 26.95/16.86  #Split   : 60
% 26.95/16.86  #Chain   : 0
% 26.95/16.86  #Close   : 0
% 26.95/16.86  
% 26.95/16.86  Ordering : KBO
% 26.95/16.86  
% 26.95/16.86  Simplification rules
% 26.95/16.86  ----------------------
% 26.95/16.86  #Subsume      : 6262
% 26.95/16.86  #Demod        : 6430
% 26.95/16.86  #Tautology    : 1643
% 26.95/16.86  #SimpNegUnit  : 690
% 26.95/16.86  #BackRed      : 197
% 26.95/16.86  
% 26.95/16.86  #Partial instantiations: 0
% 26.95/16.86  #Strategies tried      : 1
% 26.95/16.86  
% 26.95/16.86  Timing (in seconds)
% 26.95/16.86  ----------------------
% 26.95/16.86  Preprocessing        : 0.37
% 26.95/16.86  Parsing              : 0.19
% 26.95/16.86  CNF conversion       : 0.03
% 26.95/16.86  Main loop            : 15.71
% 26.95/16.86  Inferencing          : 2.52
% 26.95/16.86  Reduction            : 4.93
% 26.95/16.86  Demodulation         : 3.81
% 26.95/16.86  BG Simplification    : 0.31
% 26.95/16.86  Subsumption          : 6.99
% 26.95/16.86  Abstraction          : 0.51
% 26.95/16.86  MUC search           : 0.00
% 26.95/16.86  Cooper               : 0.00
% 26.95/16.86  Total                : 16.13
% 26.95/16.86  Index Insertion      : 0.00
% 26.95/16.86  Index Deletion       : 0.00
% 26.95/16.86  Index Matching       : 0.00
% 26.95/16.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
