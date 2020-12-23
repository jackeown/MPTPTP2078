%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT2022+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:47 EST 2020

% Result     : Theorem 1.74s
% Output     : CNFRefutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 125 expanded)
%              Number of leaves         :   20 (  59 expanded)
%              Depth                    :   10
%              Number of atoms          :  115 ( 421 expanded)
%              Number of equality atoms :    5 (  18 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_connsp_2 > v3_pre_topc > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k9_yellow_6 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k9_yellow_6,type,(
    k9_yellow_6: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_81,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(k9_yellow_6(A,B)))
               => m1_connsp_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_waybel_9)).

tff(f_46,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(k9_yellow_6(A,B)))
             => ? [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                  & D = C
                  & r2_hidden(B,D)
                  & v3_pre_topc(D,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_yellow_6)).

tff(f_65,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_connsp_2)).

tff(c_12,plain,(
    ~ m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_22,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_20,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_18,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_16,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_14,plain,(
    m1_subset_1('#skF_4',u1_struct_0(k9_yellow_6('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_23,plain,(
    ! [A_26,B_27,C_28] :
      ( '#skF_1'(A_26,B_27,C_28) = C_28
      | ~ m1_subset_1(C_28,u1_struct_0(k9_yellow_6(A_26,B_27)))
      | ~ m1_subset_1(B_27,u1_struct_0(A_26))
      | ~ l1_pre_topc(A_26)
      | ~ v2_pre_topc(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_26,plain,
    ( '#skF_1'('#skF_2','#skF_3','#skF_4') = '#skF_4'
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_23])).

tff(c_29,plain,
    ( '#skF_1'('#skF_2','#skF_3','#skF_4') = '#skF_4'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_16,c_26])).

tff(c_30,plain,(
    '#skF_1'('#skF_2','#skF_3','#skF_4') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_29])).

tff(c_42,plain,(
    ! [A_32,B_33,C_34] :
      ( v3_pre_topc('#skF_1'(A_32,B_33,C_34),A_32)
      | ~ m1_subset_1(C_34,u1_struct_0(k9_yellow_6(A_32,B_33)))
      | ~ m1_subset_1(B_33,u1_struct_0(A_32))
      | ~ l1_pre_topc(A_32)
      | ~ v2_pre_topc(A_32)
      | v2_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_44,plain,
    ( v3_pre_topc('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_2')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_42])).

tff(c_47,plain,
    ( v3_pre_topc('#skF_4','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_16,c_30,c_44])).

tff(c_48,plain,(
    v3_pre_topc('#skF_4','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_47])).

tff(c_35,plain,(
    ! [B_29,A_30,C_31] :
      ( r2_hidden(B_29,'#skF_1'(A_30,B_29,C_31))
      | ~ m1_subset_1(C_31,u1_struct_0(k9_yellow_6(A_30,B_29)))
      | ~ m1_subset_1(B_29,u1_struct_0(A_30))
      | ~ l1_pre_topc(A_30)
      | ~ v2_pre_topc(A_30)
      | v2_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_37,plain,
    ( r2_hidden('#skF_3','#skF_1'('#skF_2','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_35])).

tff(c_40,plain,
    ( r2_hidden('#skF_3','#skF_4')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_16,c_30,c_37])).

tff(c_41,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_40])).

tff(c_49,plain,(
    ! [A_35,B_36,C_37] :
      ( m1_subset_1('#skF_1'(A_35,B_36,C_37),k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ m1_subset_1(C_37,u1_struct_0(k9_yellow_6(A_35,B_36)))
      | ~ m1_subset_1(B_36,u1_struct_0(A_35))
      | ~ l1_pre_topc(A_35)
      | ~ v2_pre_topc(A_35)
      | v2_struct_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_52,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_4',u1_struct_0(k9_yellow_6('#skF_2','#skF_3')))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_49])).

tff(c_54,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_16,c_14,c_52])).

tff(c_55,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_54])).

tff(c_56,plain,(
    ! [B_38,A_39,C_40] :
      ( m1_connsp_2(B_38,A_39,C_40)
      | ~ r2_hidden(C_40,B_38)
      | ~ v3_pre_topc(B_38,A_39)
      | ~ m1_subset_1(C_40,u1_struct_0(A_39))
      | ~ m1_subset_1(B_38,k1_zfmisc_1(u1_struct_0(A_39)))
      | ~ l1_pre_topc(A_39)
      | ~ v2_pre_topc(A_39)
      | v2_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_60,plain,(
    ! [B_38] :
      ( m1_connsp_2(B_38,'#skF_2','#skF_3')
      | ~ r2_hidden('#skF_3',B_38)
      | ~ v3_pre_topc(B_38,'#skF_2')
      | ~ m1_subset_1(B_38,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_16,c_56])).

tff(c_64,plain,(
    ! [B_38] :
      ( m1_connsp_2(B_38,'#skF_2','#skF_3')
      | ~ r2_hidden('#skF_3',B_38)
      | ~ v3_pre_topc(B_38,'#skF_2')
      | ~ m1_subset_1(B_38,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_60])).

tff(c_66,plain,(
    ! [B_41] :
      ( m1_connsp_2(B_41,'#skF_2','#skF_3')
      | ~ r2_hidden('#skF_3',B_41)
      | ~ v3_pre_topc(B_41,'#skF_2')
      | ~ m1_subset_1(B_41,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_64])).

tff(c_69,plain,
    ( m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ r2_hidden('#skF_3','#skF_4')
    | ~ v3_pre_topc('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_55,c_66])).

tff(c_76,plain,(
    m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_41,c_69])).

tff(c_78,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_76])).

%------------------------------------------------------------------------------
