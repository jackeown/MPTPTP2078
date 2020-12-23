%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:36 EST 2020

% Result     : Theorem 3.64s
% Output     : CNFRefutation 3.64s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 200 expanded)
%              Number of leaves         :   22 (  96 expanded)
%              Depth                    :   10
%              Number of atoms          :  262 (1274 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   33 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tex_2 > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k4_subset_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_113,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( v3_pre_topc(B,A)
                    & v3_pre_topc(C,A)
                    & v2_tex_2(B,A)
                    & v2_tex_2(C,A) )
                 => v2_tex_2(k4_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_tex_2)).

tff(f_89,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( v3_pre_topc(B,A)
                    & v3_pre_topc(C,A) )
                 => ( v3_pre_topc(k9_subset_1(u1_struct_0(A),B,C),A)
                    & v3_pre_topc(k4_subset_1(u1_struct_0(A),B,C),A) ) ) ) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( v3_pre_topc(B,A)
                    & v3_pre_topc(C,A)
                    & v2_tex_2(B,A)
                    & v2_tex_2(C,A) )
                 => v2_tex_2(k4_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_tex_2)).

tff(f_41,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v3_pre_topc(B,A)
                  & v3_pre_topc(C,A) )
               => v3_pre_topc(k4_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_tops_1)).

tff(f_57,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v3_pre_topc(B,A)
                  & v3_pre_topc(C,A) )
               => v3_pre_topc(k9_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_tops_1)).

tff(c_28,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_26,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_24,plain,(
    v3_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_22,plain,(
    v3_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_20,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_18,plain,(
    v2_tex_2('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_30,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_32,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_44,plain,(
    ! [A_39,B_40,C_41] :
      ( v3_pre_topc('#skF_1'(A_39),A_39)
      | v2_tex_2(k4_subset_1(u1_struct_0(A_39),B_40,C_41),A_39)
      | ~ v2_tex_2(C_41,A_39)
      | ~ v2_tex_2(B_40,A_39)
      | ~ v3_pre_topc(C_41,A_39)
      | ~ v3_pre_topc(B_40,A_39)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(u1_struct_0(A_39)))
      | ~ m1_subset_1(B_40,k1_zfmisc_1(u1_struct_0(A_39)))
      | ~ l1_pre_topc(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_16,plain,(
    ~ v2_tex_2(k4_subset_1(u1_struct_0('#skF_3'),'#skF_4','#skF_5'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_47,plain,
    ( v3_pre_topc('#skF_1'('#skF_3'),'#skF_3')
    | ~ v2_tex_2('#skF_5','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ v3_pre_topc('#skF_5','#skF_3')
    | ~ v3_pre_topc('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_16])).

tff(c_50,plain,(
    v3_pre_topc('#skF_1'('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_24,c_22,c_20,c_18,c_47])).

tff(c_37,plain,(
    ! [A_36,B_37,C_38] :
      ( v3_pre_topc('#skF_2'(A_36),A_36)
      | v2_tex_2(k4_subset_1(u1_struct_0(A_36),B_37,C_38),A_36)
      | ~ v2_tex_2(C_38,A_36)
      | ~ v2_tex_2(B_37,A_36)
      | ~ v3_pre_topc(C_38,A_36)
      | ~ v3_pre_topc(B_37,A_36)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(u1_struct_0(A_36)))
      | ~ m1_subset_1(B_37,k1_zfmisc_1(u1_struct_0(A_36)))
      | ~ l1_pre_topc(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_40,plain,
    ( v3_pre_topc('#skF_2'('#skF_3'),'#skF_3')
    | ~ v2_tex_2('#skF_5','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ v3_pre_topc('#skF_5','#skF_3')
    | ~ v3_pre_topc('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_37,c_16])).

tff(c_43,plain,(
    v3_pre_topc('#skF_2'('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_24,c_22,c_20,c_18,c_40])).

tff(c_14,plain,(
    ! [A_15,B_23,C_25] :
      ( m1_subset_1('#skF_1'(A_15),k1_zfmisc_1(u1_struct_0(A_15)))
      | v2_tex_2(k4_subset_1(u1_struct_0(A_15),B_23,C_25),A_15)
      | ~ v2_tex_2(C_25,A_15)
      | ~ v2_tex_2(B_23,A_15)
      | ~ v3_pre_topc(C_25,A_15)
      | ~ v3_pre_topc(B_23,A_15)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ m1_subset_1(B_23,k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_12,plain,(
    ! [A_15,B_23,C_25] :
      ( m1_subset_1('#skF_2'(A_15),k1_zfmisc_1(u1_struct_0(A_15)))
      | v2_tex_2(k4_subset_1(u1_struct_0(A_15),B_23,C_25),A_15)
      | ~ v2_tex_2(C_25,A_15)
      | ~ v2_tex_2(B_23,A_15)
      | ~ v3_pre_topc(C_25,A_15)
      | ~ v3_pre_topc(B_23,A_15)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ m1_subset_1(B_23,k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2,plain,(
    ! [A_1,B_5,C_7] :
      ( v3_pre_topc(k4_subset_1(u1_struct_0(A_1),B_5,C_7),A_1)
      | ~ v3_pre_topc(C_7,A_1)
      | ~ v3_pre_topc(B_5,A_1)
      | ~ m1_subset_1(C_7,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ m1_subset_1(B_5,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4,plain,(
    ! [A_8,B_12,C_14] :
      ( v3_pre_topc(k9_subset_1(u1_struct_0(A_8),B_12,C_14),A_8)
      | ~ v3_pre_topc(C_14,A_8)
      | ~ v3_pre_topc(B_12,A_8)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ m1_subset_1(B_12,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ l1_pre_topc(A_8)
      | ~ v2_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_55,plain,(
    ! [A_48,B_49,C_50] :
      ( ~ v3_pre_topc(k4_subset_1(u1_struct_0(A_48),'#skF_1'(A_48),'#skF_2'(A_48)),A_48)
      | ~ v3_pre_topc(k9_subset_1(u1_struct_0(A_48),'#skF_1'(A_48),'#skF_2'(A_48)),A_48)
      | v2_tex_2(k4_subset_1(u1_struct_0(A_48),B_49,C_50),A_48)
      | ~ v2_tex_2(C_50,A_48)
      | ~ v2_tex_2(B_49,A_48)
      | ~ v3_pre_topc(C_50,A_48)
      | ~ v3_pre_topc(B_49,A_48)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ m1_subset_1(B_49,k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ l1_pre_topc(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_60,plain,(
    ! [A_51,B_52,C_53] :
      ( ~ v3_pre_topc(k4_subset_1(u1_struct_0(A_51),'#skF_1'(A_51),'#skF_2'(A_51)),A_51)
      | v2_tex_2(k4_subset_1(u1_struct_0(A_51),B_52,C_53),A_51)
      | ~ v2_tex_2(C_53,A_51)
      | ~ v2_tex_2(B_52,A_51)
      | ~ v3_pre_topc(C_53,A_51)
      | ~ v3_pre_topc(B_52,A_51)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ m1_subset_1(B_52,k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ v3_pre_topc('#skF_2'(A_51),A_51)
      | ~ v3_pre_topc('#skF_1'(A_51),A_51)
      | ~ m1_subset_1('#skF_2'(A_51),k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ m1_subset_1('#skF_1'(A_51),k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ l1_pre_topc(A_51)
      | ~ v2_pre_topc(A_51) ) ),
    inference(resolution,[status(thm)],[c_4,c_55])).

tff(c_65,plain,(
    ! [A_54,B_55,C_56] :
      ( v2_tex_2(k4_subset_1(u1_struct_0(A_54),B_55,C_56),A_54)
      | ~ v2_tex_2(C_56,A_54)
      | ~ v2_tex_2(B_55,A_54)
      | ~ v3_pre_topc(C_56,A_54)
      | ~ v3_pre_topc(B_55,A_54)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ m1_subset_1(B_55,k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ v3_pre_topc('#skF_2'(A_54),A_54)
      | ~ v3_pre_topc('#skF_1'(A_54),A_54)
      | ~ m1_subset_1('#skF_2'(A_54),k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ m1_subset_1('#skF_1'(A_54),k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ l1_pre_topc(A_54)
      | ~ v2_pre_topc(A_54) ) ),
    inference(resolution,[status(thm)],[c_2,c_60])).

tff(c_69,plain,(
    ! [B_59,A_60,C_57,B_61,C_58] :
      ( v2_tex_2(k4_subset_1(u1_struct_0(A_60),B_59,C_58),A_60)
      | ~ v2_tex_2(C_58,A_60)
      | ~ v2_tex_2(B_59,A_60)
      | ~ v3_pre_topc(C_58,A_60)
      | ~ v3_pre_topc(B_59,A_60)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ v3_pre_topc('#skF_2'(A_60),A_60)
      | ~ v3_pre_topc('#skF_1'(A_60),A_60)
      | ~ m1_subset_1('#skF_1'(A_60),k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ v2_pre_topc(A_60)
      | v2_tex_2(k4_subset_1(u1_struct_0(A_60),B_61,C_57),A_60)
      | ~ v2_tex_2(C_57,A_60)
      | ~ v2_tex_2(B_61,A_60)
      | ~ v3_pre_topc(C_57,A_60)
      | ~ v3_pre_topc(B_61,A_60)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ m1_subset_1(B_61,k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ l1_pre_topc(A_60) ) ),
    inference(resolution,[status(thm)],[c_12,c_65])).

tff(c_115,plain,(
    ! [B_62,C_67,A_66,B_68,C_63,C_64,B_65] :
      ( v2_tex_2(k4_subset_1(u1_struct_0(A_66),B_62,C_64),A_66)
      | ~ v2_tex_2(C_64,A_66)
      | ~ v2_tex_2(B_62,A_66)
      | ~ v3_pre_topc(C_64,A_66)
      | ~ v3_pre_topc(B_62,A_66)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ v3_pre_topc('#skF_2'(A_66),A_66)
      | ~ v3_pre_topc('#skF_1'(A_66),A_66)
      | ~ v2_pre_topc(A_66)
      | v2_tex_2(k4_subset_1(u1_struct_0(A_66),B_65,C_67),A_66)
      | ~ v2_tex_2(C_67,A_66)
      | ~ v2_tex_2(B_65,A_66)
      | ~ v3_pre_topc(C_67,A_66)
      | ~ v3_pre_topc(B_65,A_66)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0(A_66)))
      | v2_tex_2(k4_subset_1(u1_struct_0(A_66),B_68,C_63),A_66)
      | ~ v2_tex_2(C_63,A_66)
      | ~ v2_tex_2(B_68,A_66)
      | ~ v3_pre_topc(C_63,A_66)
      | ~ v3_pre_topc(B_68,A_66)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ m1_subset_1(B_68,k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ l1_pre_topc(A_66) ) ),
    inference(resolution,[status(thm)],[c_14,c_69])).

tff(c_118,plain,(
    ! [B_65,C_67,B_68,C_63] :
      ( ~ v2_tex_2('#skF_5','#skF_3')
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ v3_pre_topc('#skF_5','#skF_3')
      | ~ v3_pre_topc('#skF_4','#skF_3')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v3_pre_topc('#skF_2'('#skF_3'),'#skF_3')
      | ~ v3_pre_topc('#skF_1'('#skF_3'),'#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_tex_2(k4_subset_1(u1_struct_0('#skF_3'),B_65,C_67),'#skF_3')
      | ~ v2_tex_2(C_67,'#skF_3')
      | ~ v2_tex_2(B_65,'#skF_3')
      | ~ v3_pre_topc(C_67,'#skF_3')
      | ~ v3_pre_topc(B_65,'#skF_3')
      | ~ m1_subset_1(C_67,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_tex_2(k4_subset_1(u1_struct_0('#skF_3'),B_68,C_63),'#skF_3')
      | ~ v2_tex_2(C_63,'#skF_3')
      | ~ v2_tex_2(B_68,'#skF_3')
      | ~ v3_pre_topc(C_63,'#skF_3')
      | ~ v3_pre_topc(B_68,'#skF_3')
      | ~ m1_subset_1(C_63,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_68,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_115,c_16])).

tff(c_127,plain,(
    ! [B_65,C_67,B_68,C_63] :
      ( v2_tex_2(k4_subset_1(u1_struct_0('#skF_3'),B_65,C_67),'#skF_3')
      | ~ v2_tex_2(C_67,'#skF_3')
      | ~ v2_tex_2(B_65,'#skF_3')
      | ~ v3_pre_topc(C_67,'#skF_3')
      | ~ v3_pre_topc(B_65,'#skF_3')
      | ~ m1_subset_1(C_67,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_tex_2(k4_subset_1(u1_struct_0('#skF_3'),B_68,C_63),'#skF_3')
      | ~ v2_tex_2(C_63,'#skF_3')
      | ~ v2_tex_2(B_68,'#skF_3')
      | ~ v3_pre_topc(C_63,'#skF_3')
      | ~ v3_pre_topc(B_68,'#skF_3')
      | ~ m1_subset_1(C_63,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_68,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_32,c_50,c_43,c_28,c_26,c_24,c_22,c_20,c_18,c_118])).

tff(c_135,plain,(
    ! [B_69,C_70] :
      ( v2_tex_2(k4_subset_1(u1_struct_0('#skF_3'),B_69,C_70),'#skF_3')
      | ~ v2_tex_2(C_70,'#skF_3')
      | ~ v2_tex_2(B_69,'#skF_3')
      | ~ v3_pre_topc(C_70,'#skF_3')
      | ~ v3_pre_topc(B_69,'#skF_3')
      | ~ m1_subset_1(C_70,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(splitLeft,[status(thm)],[c_127])).

tff(c_138,plain,
    ( ~ v2_tex_2('#skF_5','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ v3_pre_topc('#skF_5','#skF_3')
    | ~ v3_pre_topc('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_135,c_16])).

tff(c_142,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_22,c_20,c_18,c_138])).

tff(c_144,plain,(
    ! [B_71,C_72] :
      ( v2_tex_2(k4_subset_1(u1_struct_0('#skF_3'),B_71,C_72),'#skF_3')
      | ~ v2_tex_2(C_72,'#skF_3')
      | ~ v2_tex_2(B_71,'#skF_3')
      | ~ v3_pre_topc(C_72,'#skF_3')
      | ~ v3_pre_topc(B_71,'#skF_3')
      | ~ m1_subset_1(C_72,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_71,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(splitRight,[status(thm)],[c_127])).

tff(c_147,plain,
    ( ~ v2_tex_2('#skF_5','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ v3_pre_topc('#skF_5','#skF_3')
    | ~ v3_pre_topc('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_144,c_16])).

tff(c_151,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_22,c_20,c_18,c_147])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.16/0.36  % Computer   : n007.cluster.edu
% 0.16/0.36  % Model      : x86_64 x86_64
% 0.16/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.36  % Memory     : 8042.1875MB
% 0.16/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.36  % CPULimit   : 60
% 0.16/0.36  % DateTime   : Tue Dec  1 09:57:51 EST 2020
% 0.16/0.36  % CPUTime    : 
% 0.16/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.64/1.63  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.64/1.64  
% 3.64/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.64/1.65  %$ v3_pre_topc > v2_tex_2 > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k4_subset_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4
% 3.64/1.65  
% 3.64/1.65  %Foreground sorts:
% 3.64/1.65  
% 3.64/1.65  
% 3.64/1.65  %Background operators:
% 3.64/1.65  
% 3.64/1.65  
% 3.64/1.65  %Foreground operators:
% 3.64/1.65  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.64/1.65  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.64/1.65  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.64/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.64/1.65  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.64/1.65  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.64/1.65  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 3.64/1.65  tff('#skF_5', type, '#skF_5': $i).
% 3.64/1.65  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.64/1.65  tff('#skF_3', type, '#skF_3': $i).
% 3.64/1.65  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.64/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.64/1.65  tff('#skF_4', type, '#skF_4': $i).
% 3.64/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.64/1.65  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.64/1.65  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.64/1.65  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.64/1.65  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.64/1.65  
% 3.64/1.68  tff(f_113, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((((v3_pre_topc(B, A) & v3_pre_topc(C, A)) & v2_tex_2(B, A)) & v2_tex_2(C, A)) => v2_tex_2(k4_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_tex_2)).
% 3.64/1.68  tff(f_89, axiom, (![A]: (l1_pre_topc(A) => ((![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & v3_pre_topc(C, A)) => (v3_pre_topc(k9_subset_1(u1_struct_0(A), B, C), A) & v3_pre_topc(k4_subset_1(u1_struct_0(A), B, C), A))))))) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((((v3_pre_topc(B, A) & v3_pre_topc(C, A)) & v2_tex_2(B, A)) & v2_tex_2(C, A)) => v2_tex_2(k4_subset_1(u1_struct_0(A), B, C), A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_tex_2)).
% 3.64/1.68  tff(f_41, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & v3_pre_topc(C, A)) => v3_pre_topc(k4_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_tops_1)).
% 3.64/1.68  tff(f_57, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & v3_pre_topc(C, A)) => v3_pre_topc(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_tops_1)).
% 3.64/1.68  tff(c_28, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.64/1.68  tff(c_26, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.64/1.68  tff(c_24, plain, (v3_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.64/1.68  tff(c_22, plain, (v3_pre_topc('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.64/1.68  tff(c_20, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.64/1.68  tff(c_18, plain, (v2_tex_2('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.64/1.68  tff(c_30, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.64/1.68  tff(c_32, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.64/1.68  tff(c_44, plain, (![A_39, B_40, C_41]: (v3_pre_topc('#skF_1'(A_39), A_39) | v2_tex_2(k4_subset_1(u1_struct_0(A_39), B_40, C_41), A_39) | ~v2_tex_2(C_41, A_39) | ~v2_tex_2(B_40, A_39) | ~v3_pre_topc(C_41, A_39) | ~v3_pre_topc(B_40, A_39) | ~m1_subset_1(C_41, k1_zfmisc_1(u1_struct_0(A_39))) | ~m1_subset_1(B_40, k1_zfmisc_1(u1_struct_0(A_39))) | ~l1_pre_topc(A_39))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.64/1.68  tff(c_16, plain, (~v2_tex_2(k4_subset_1(u1_struct_0('#skF_3'), '#skF_4', '#skF_5'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.64/1.68  tff(c_47, plain, (v3_pre_topc('#skF_1'('#skF_3'), '#skF_3') | ~v2_tex_2('#skF_5', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~v3_pre_topc('#skF_5', '#skF_3') | ~v3_pre_topc('#skF_4', '#skF_3') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_44, c_16])).
% 3.64/1.68  tff(c_50, plain, (v3_pre_topc('#skF_1'('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_24, c_22, c_20, c_18, c_47])).
% 3.64/1.68  tff(c_37, plain, (![A_36, B_37, C_38]: (v3_pre_topc('#skF_2'(A_36), A_36) | v2_tex_2(k4_subset_1(u1_struct_0(A_36), B_37, C_38), A_36) | ~v2_tex_2(C_38, A_36) | ~v2_tex_2(B_37, A_36) | ~v3_pre_topc(C_38, A_36) | ~v3_pre_topc(B_37, A_36) | ~m1_subset_1(C_38, k1_zfmisc_1(u1_struct_0(A_36))) | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0(A_36))) | ~l1_pre_topc(A_36))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.64/1.68  tff(c_40, plain, (v3_pre_topc('#skF_2'('#skF_3'), '#skF_3') | ~v2_tex_2('#skF_5', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~v3_pre_topc('#skF_5', '#skF_3') | ~v3_pre_topc('#skF_4', '#skF_3') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_37, c_16])).
% 3.64/1.68  tff(c_43, plain, (v3_pre_topc('#skF_2'('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_24, c_22, c_20, c_18, c_40])).
% 3.64/1.68  tff(c_14, plain, (![A_15, B_23, C_25]: (m1_subset_1('#skF_1'(A_15), k1_zfmisc_1(u1_struct_0(A_15))) | v2_tex_2(k4_subset_1(u1_struct_0(A_15), B_23, C_25), A_15) | ~v2_tex_2(C_25, A_15) | ~v2_tex_2(B_23, A_15) | ~v3_pre_topc(C_25, A_15) | ~v3_pre_topc(B_23, A_15) | ~m1_subset_1(C_25, k1_zfmisc_1(u1_struct_0(A_15))) | ~m1_subset_1(B_23, k1_zfmisc_1(u1_struct_0(A_15))) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.64/1.68  tff(c_12, plain, (![A_15, B_23, C_25]: (m1_subset_1('#skF_2'(A_15), k1_zfmisc_1(u1_struct_0(A_15))) | v2_tex_2(k4_subset_1(u1_struct_0(A_15), B_23, C_25), A_15) | ~v2_tex_2(C_25, A_15) | ~v2_tex_2(B_23, A_15) | ~v3_pre_topc(C_25, A_15) | ~v3_pre_topc(B_23, A_15) | ~m1_subset_1(C_25, k1_zfmisc_1(u1_struct_0(A_15))) | ~m1_subset_1(B_23, k1_zfmisc_1(u1_struct_0(A_15))) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.64/1.68  tff(c_2, plain, (![A_1, B_5, C_7]: (v3_pre_topc(k4_subset_1(u1_struct_0(A_1), B_5, C_7), A_1) | ~v3_pre_topc(C_7, A_1) | ~v3_pre_topc(B_5, A_1) | ~m1_subset_1(C_7, k1_zfmisc_1(u1_struct_0(A_1))) | ~m1_subset_1(B_5, k1_zfmisc_1(u1_struct_0(A_1))) | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.64/1.68  tff(c_4, plain, (![A_8, B_12, C_14]: (v3_pre_topc(k9_subset_1(u1_struct_0(A_8), B_12, C_14), A_8) | ~v3_pre_topc(C_14, A_8) | ~v3_pre_topc(B_12, A_8) | ~m1_subset_1(C_14, k1_zfmisc_1(u1_struct_0(A_8))) | ~m1_subset_1(B_12, k1_zfmisc_1(u1_struct_0(A_8))) | ~l1_pre_topc(A_8) | ~v2_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.64/1.68  tff(c_55, plain, (![A_48, B_49, C_50]: (~v3_pre_topc(k4_subset_1(u1_struct_0(A_48), '#skF_1'(A_48), '#skF_2'(A_48)), A_48) | ~v3_pre_topc(k9_subset_1(u1_struct_0(A_48), '#skF_1'(A_48), '#skF_2'(A_48)), A_48) | v2_tex_2(k4_subset_1(u1_struct_0(A_48), B_49, C_50), A_48) | ~v2_tex_2(C_50, A_48) | ~v2_tex_2(B_49, A_48) | ~v3_pre_topc(C_50, A_48) | ~v3_pre_topc(B_49, A_48) | ~m1_subset_1(C_50, k1_zfmisc_1(u1_struct_0(A_48))) | ~m1_subset_1(B_49, k1_zfmisc_1(u1_struct_0(A_48))) | ~l1_pre_topc(A_48))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.64/1.68  tff(c_60, plain, (![A_51, B_52, C_53]: (~v3_pre_topc(k4_subset_1(u1_struct_0(A_51), '#skF_1'(A_51), '#skF_2'(A_51)), A_51) | v2_tex_2(k4_subset_1(u1_struct_0(A_51), B_52, C_53), A_51) | ~v2_tex_2(C_53, A_51) | ~v2_tex_2(B_52, A_51) | ~v3_pre_topc(C_53, A_51) | ~v3_pre_topc(B_52, A_51) | ~m1_subset_1(C_53, k1_zfmisc_1(u1_struct_0(A_51))) | ~m1_subset_1(B_52, k1_zfmisc_1(u1_struct_0(A_51))) | ~v3_pre_topc('#skF_2'(A_51), A_51) | ~v3_pre_topc('#skF_1'(A_51), A_51) | ~m1_subset_1('#skF_2'(A_51), k1_zfmisc_1(u1_struct_0(A_51))) | ~m1_subset_1('#skF_1'(A_51), k1_zfmisc_1(u1_struct_0(A_51))) | ~l1_pre_topc(A_51) | ~v2_pre_topc(A_51))), inference(resolution, [status(thm)], [c_4, c_55])).
% 3.64/1.68  tff(c_65, plain, (![A_54, B_55, C_56]: (v2_tex_2(k4_subset_1(u1_struct_0(A_54), B_55, C_56), A_54) | ~v2_tex_2(C_56, A_54) | ~v2_tex_2(B_55, A_54) | ~v3_pre_topc(C_56, A_54) | ~v3_pre_topc(B_55, A_54) | ~m1_subset_1(C_56, k1_zfmisc_1(u1_struct_0(A_54))) | ~m1_subset_1(B_55, k1_zfmisc_1(u1_struct_0(A_54))) | ~v3_pre_topc('#skF_2'(A_54), A_54) | ~v3_pre_topc('#skF_1'(A_54), A_54) | ~m1_subset_1('#skF_2'(A_54), k1_zfmisc_1(u1_struct_0(A_54))) | ~m1_subset_1('#skF_1'(A_54), k1_zfmisc_1(u1_struct_0(A_54))) | ~l1_pre_topc(A_54) | ~v2_pre_topc(A_54))), inference(resolution, [status(thm)], [c_2, c_60])).
% 3.64/1.68  tff(c_69, plain, (![B_59, A_60, C_57, B_61, C_58]: (v2_tex_2(k4_subset_1(u1_struct_0(A_60), B_59, C_58), A_60) | ~v2_tex_2(C_58, A_60) | ~v2_tex_2(B_59, A_60) | ~v3_pre_topc(C_58, A_60) | ~v3_pre_topc(B_59, A_60) | ~m1_subset_1(C_58, k1_zfmisc_1(u1_struct_0(A_60))) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(A_60))) | ~v3_pre_topc('#skF_2'(A_60), A_60) | ~v3_pre_topc('#skF_1'(A_60), A_60) | ~m1_subset_1('#skF_1'(A_60), k1_zfmisc_1(u1_struct_0(A_60))) | ~v2_pre_topc(A_60) | v2_tex_2(k4_subset_1(u1_struct_0(A_60), B_61, C_57), A_60) | ~v2_tex_2(C_57, A_60) | ~v2_tex_2(B_61, A_60) | ~v3_pre_topc(C_57, A_60) | ~v3_pre_topc(B_61, A_60) | ~m1_subset_1(C_57, k1_zfmisc_1(u1_struct_0(A_60))) | ~m1_subset_1(B_61, k1_zfmisc_1(u1_struct_0(A_60))) | ~l1_pre_topc(A_60))), inference(resolution, [status(thm)], [c_12, c_65])).
% 3.64/1.68  tff(c_115, plain, (![B_62, C_67, A_66, B_68, C_63, C_64, B_65]: (v2_tex_2(k4_subset_1(u1_struct_0(A_66), B_62, C_64), A_66) | ~v2_tex_2(C_64, A_66) | ~v2_tex_2(B_62, A_66) | ~v3_pre_topc(C_64, A_66) | ~v3_pre_topc(B_62, A_66) | ~m1_subset_1(C_64, k1_zfmisc_1(u1_struct_0(A_66))) | ~m1_subset_1(B_62, k1_zfmisc_1(u1_struct_0(A_66))) | ~v3_pre_topc('#skF_2'(A_66), A_66) | ~v3_pre_topc('#skF_1'(A_66), A_66) | ~v2_pre_topc(A_66) | v2_tex_2(k4_subset_1(u1_struct_0(A_66), B_65, C_67), A_66) | ~v2_tex_2(C_67, A_66) | ~v2_tex_2(B_65, A_66) | ~v3_pre_topc(C_67, A_66) | ~v3_pre_topc(B_65, A_66) | ~m1_subset_1(C_67, k1_zfmisc_1(u1_struct_0(A_66))) | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0(A_66))) | v2_tex_2(k4_subset_1(u1_struct_0(A_66), B_68, C_63), A_66) | ~v2_tex_2(C_63, A_66) | ~v2_tex_2(B_68, A_66) | ~v3_pre_topc(C_63, A_66) | ~v3_pre_topc(B_68, A_66) | ~m1_subset_1(C_63, k1_zfmisc_1(u1_struct_0(A_66))) | ~m1_subset_1(B_68, k1_zfmisc_1(u1_struct_0(A_66))) | ~l1_pre_topc(A_66))), inference(resolution, [status(thm)], [c_14, c_69])).
% 3.64/1.68  tff(c_118, plain, (![B_65, C_67, B_68, C_63]: (~v2_tex_2('#skF_5', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~v3_pre_topc('#skF_5', '#skF_3') | ~v3_pre_topc('#skF_4', '#skF_3') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v3_pre_topc('#skF_2'('#skF_3'), '#skF_3') | ~v3_pre_topc('#skF_1'('#skF_3'), '#skF_3') | ~v2_pre_topc('#skF_3') | v2_tex_2(k4_subset_1(u1_struct_0('#skF_3'), B_65, C_67), '#skF_3') | ~v2_tex_2(C_67, '#skF_3') | ~v2_tex_2(B_65, '#skF_3') | ~v3_pre_topc(C_67, '#skF_3') | ~v3_pre_topc(B_65, '#skF_3') | ~m1_subset_1(C_67, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_tex_2(k4_subset_1(u1_struct_0('#skF_3'), B_68, C_63), '#skF_3') | ~v2_tex_2(C_63, '#skF_3') | ~v2_tex_2(B_68, '#skF_3') | ~v3_pre_topc(C_63, '#skF_3') | ~v3_pre_topc(B_68, '#skF_3') | ~m1_subset_1(C_63, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_68, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_115, c_16])).
% 3.64/1.68  tff(c_127, plain, (![B_65, C_67, B_68, C_63]: (v2_tex_2(k4_subset_1(u1_struct_0('#skF_3'), B_65, C_67), '#skF_3') | ~v2_tex_2(C_67, '#skF_3') | ~v2_tex_2(B_65, '#skF_3') | ~v3_pre_topc(C_67, '#skF_3') | ~v3_pre_topc(B_65, '#skF_3') | ~m1_subset_1(C_67, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_tex_2(k4_subset_1(u1_struct_0('#skF_3'), B_68, C_63), '#skF_3') | ~v2_tex_2(C_63, '#skF_3') | ~v2_tex_2(B_68, '#skF_3') | ~v3_pre_topc(C_63, '#skF_3') | ~v3_pre_topc(B_68, '#skF_3') | ~m1_subset_1(C_63, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_68, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_32, c_50, c_43, c_28, c_26, c_24, c_22, c_20, c_18, c_118])).
% 3.64/1.68  tff(c_135, plain, (![B_69, C_70]: (v2_tex_2(k4_subset_1(u1_struct_0('#skF_3'), B_69, C_70), '#skF_3') | ~v2_tex_2(C_70, '#skF_3') | ~v2_tex_2(B_69, '#skF_3') | ~v3_pre_topc(C_70, '#skF_3') | ~v3_pre_topc(B_69, '#skF_3') | ~m1_subset_1(C_70, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_69, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(splitLeft, [status(thm)], [c_127])).
% 3.64/1.68  tff(c_138, plain, (~v2_tex_2('#skF_5', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~v3_pre_topc('#skF_5', '#skF_3') | ~v3_pre_topc('#skF_4', '#skF_3') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_135, c_16])).
% 3.64/1.68  tff(c_142, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_24, c_22, c_20, c_18, c_138])).
% 3.64/1.68  tff(c_144, plain, (![B_71, C_72]: (v2_tex_2(k4_subset_1(u1_struct_0('#skF_3'), B_71, C_72), '#skF_3') | ~v2_tex_2(C_72, '#skF_3') | ~v2_tex_2(B_71, '#skF_3') | ~v3_pre_topc(C_72, '#skF_3') | ~v3_pre_topc(B_71, '#skF_3') | ~m1_subset_1(C_72, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_71, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(splitRight, [status(thm)], [c_127])).
% 3.64/1.68  tff(c_147, plain, (~v2_tex_2('#skF_5', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~v3_pre_topc('#skF_5', '#skF_3') | ~v3_pre_topc('#skF_4', '#skF_3') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_144, c_16])).
% 3.64/1.68  tff(c_151, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_24, c_22, c_20, c_18, c_147])).
% 3.64/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.64/1.68  
% 3.64/1.68  Inference rules
% 3.64/1.68  ----------------------
% 3.64/1.68  #Ref     : 0
% 3.64/1.68  #Sup     : 11
% 3.64/1.68  #Fact    : 6
% 3.64/1.68  #Define  : 0
% 3.64/1.68  #Split   : 1
% 3.64/1.68  #Chain   : 0
% 3.64/1.68  #Close   : 0
% 3.64/1.68  
% 3.64/1.68  Ordering : KBO
% 3.64/1.68  
% 3.64/1.68  Simplification rules
% 3.64/1.68  ----------------------
% 3.64/1.68  #Subsume      : 1
% 3.64/1.68  #Demod        : 56
% 3.64/1.68  #Tautology    : 0
% 3.64/1.68  #SimpNegUnit  : 0
% 3.64/1.68  #BackRed      : 0
% 3.64/1.68  
% 3.64/1.68  #Partial instantiations: 0
% 3.64/1.68  #Strategies tried      : 1
% 3.64/1.68  
% 3.64/1.68  Timing (in seconds)
% 3.64/1.68  ----------------------
% 3.64/1.69  Preprocessing        : 0.32
% 3.64/1.69  Parsing              : 0.18
% 3.64/1.69  CNF conversion       : 0.03
% 3.64/1.69  Main loop            : 0.48
% 3.64/1.69  Inferencing          : 0.11
% 3.83/1.69  Reduction            : 0.06
% 3.83/1.69  Demodulation         : 0.05
% 3.83/1.69  BG Simplification    : 0.02
% 3.83/1.69  Subsumption          : 0.27
% 3.83/1.69  Abstraction          : 0.01
% 3.83/1.69  MUC search           : 0.00
% 3.83/1.69  Cooper               : 0.00
% 3.83/1.69  Total                : 0.86
% 3.83/1.69  Index Insertion      : 0.00
% 3.83/1.69  Index Deletion       : 0.00
% 3.83/1.69  Index Matching       : 0.00
% 3.83/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
