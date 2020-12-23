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
% DateTime   : Thu Dec  3 10:29:37 EST 2020

% Result     : Theorem 3.21s
% Output     : CNFRefutation 3.36s
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
%$ v4_pre_topc > v2_tex_2 > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k4_subset_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

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

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

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
               => ( ( v4_pre_topc(B,A)
                    & v4_pre_topc(C,A)
                    & v2_tex_2(B,A)
                    & v2_tex_2(C,A) )
                 => v2_tex_2(k4_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_tex_2)).

tff(f_89,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( v4_pre_topc(B,A)
                    & v4_pre_topc(C,A) )
                 => ( v4_pre_topc(k9_subset_1(u1_struct_0(A),B,C),A)
                    & v4_pre_topc(k4_subset_1(u1_struct_0(A),B,C),A) ) ) ) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( v4_pre_topc(B,A)
                    & v4_pre_topc(C,A)
                    & v2_tex_2(B,A)
                    & v2_tex_2(C,A) )
                 => v2_tex_2(k4_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_tex_2)).

tff(f_57,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v4_pre_topc(B,A)
                  & v4_pre_topc(C,A) )
               => v4_pre_topc(k4_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tops_1)).

tff(f_41,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v4_pre_topc(B,A)
                  & v4_pre_topc(C,A) )
               => v4_pre_topc(k9_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tops_1)).

tff(c_28,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_26,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_24,plain,(
    v4_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_22,plain,(
    v4_pre_topc('#skF_5','#skF_3') ),
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
      ( v4_pre_topc('#skF_1'(A_39),A_39)
      | v2_tex_2(k4_subset_1(u1_struct_0(A_39),B_40,C_41),A_39)
      | ~ v2_tex_2(C_41,A_39)
      | ~ v2_tex_2(B_40,A_39)
      | ~ v4_pre_topc(C_41,A_39)
      | ~ v4_pre_topc(B_40,A_39)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(u1_struct_0(A_39)))
      | ~ m1_subset_1(B_40,k1_zfmisc_1(u1_struct_0(A_39)))
      | ~ l1_pre_topc(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_16,plain,(
    ~ v2_tex_2(k4_subset_1(u1_struct_0('#skF_3'),'#skF_4','#skF_5'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_47,plain,
    ( v4_pre_topc('#skF_1'('#skF_3'),'#skF_3')
    | ~ v2_tex_2('#skF_5','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ v4_pre_topc('#skF_5','#skF_3')
    | ~ v4_pre_topc('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_16])).

tff(c_50,plain,(
    v4_pre_topc('#skF_1'('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_24,c_22,c_20,c_18,c_47])).

tff(c_37,plain,(
    ! [A_36,B_37,C_38] :
      ( v4_pre_topc('#skF_2'(A_36),A_36)
      | v2_tex_2(k4_subset_1(u1_struct_0(A_36),B_37,C_38),A_36)
      | ~ v2_tex_2(C_38,A_36)
      | ~ v2_tex_2(B_37,A_36)
      | ~ v4_pre_topc(C_38,A_36)
      | ~ v4_pre_topc(B_37,A_36)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(u1_struct_0(A_36)))
      | ~ m1_subset_1(B_37,k1_zfmisc_1(u1_struct_0(A_36)))
      | ~ l1_pre_topc(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_40,plain,
    ( v4_pre_topc('#skF_2'('#skF_3'),'#skF_3')
    | ~ v2_tex_2('#skF_5','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ v4_pre_topc('#skF_5','#skF_3')
    | ~ v4_pre_topc('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_37,c_16])).

tff(c_43,plain,(
    v4_pre_topc('#skF_2'('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_24,c_22,c_20,c_18,c_40])).

tff(c_14,plain,(
    ! [A_15,B_23,C_25] :
      ( m1_subset_1('#skF_1'(A_15),k1_zfmisc_1(u1_struct_0(A_15)))
      | v2_tex_2(k4_subset_1(u1_struct_0(A_15),B_23,C_25),A_15)
      | ~ v2_tex_2(C_25,A_15)
      | ~ v2_tex_2(B_23,A_15)
      | ~ v4_pre_topc(C_25,A_15)
      | ~ v4_pre_topc(B_23,A_15)
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
      | ~ v4_pre_topc(C_25,A_15)
      | ~ v4_pre_topc(B_23,A_15)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ m1_subset_1(B_23,k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_4,plain,(
    ! [A_8,B_12,C_14] :
      ( v4_pre_topc(k4_subset_1(u1_struct_0(A_8),B_12,C_14),A_8)
      | ~ v4_pre_topc(C_14,A_8)
      | ~ v4_pre_topc(B_12,A_8)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ m1_subset_1(B_12,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ l1_pre_topc(A_8)
      | ~ v2_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2,plain,(
    ! [A_1,B_5,C_7] :
      ( v4_pre_topc(k9_subset_1(u1_struct_0(A_1),B_5,C_7),A_1)
      | ~ v4_pre_topc(C_7,A_1)
      | ~ v4_pre_topc(B_5,A_1)
      | ~ m1_subset_1(C_7,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ m1_subset_1(B_5,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_55,plain,(
    ! [A_48,B_49,C_50] :
      ( ~ v4_pre_topc(k4_subset_1(u1_struct_0(A_48),'#skF_1'(A_48),'#skF_2'(A_48)),A_48)
      | ~ v4_pre_topc(k9_subset_1(u1_struct_0(A_48),'#skF_1'(A_48),'#skF_2'(A_48)),A_48)
      | v2_tex_2(k4_subset_1(u1_struct_0(A_48),B_49,C_50),A_48)
      | ~ v2_tex_2(C_50,A_48)
      | ~ v2_tex_2(B_49,A_48)
      | ~ v4_pre_topc(C_50,A_48)
      | ~ v4_pre_topc(B_49,A_48)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ m1_subset_1(B_49,k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ l1_pre_topc(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_60,plain,(
    ! [A_51,B_52,C_53] :
      ( ~ v4_pre_topc(k4_subset_1(u1_struct_0(A_51),'#skF_1'(A_51),'#skF_2'(A_51)),A_51)
      | v2_tex_2(k4_subset_1(u1_struct_0(A_51),B_52,C_53),A_51)
      | ~ v2_tex_2(C_53,A_51)
      | ~ v2_tex_2(B_52,A_51)
      | ~ v4_pre_topc(C_53,A_51)
      | ~ v4_pre_topc(B_52,A_51)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ m1_subset_1(B_52,k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ v4_pre_topc('#skF_2'(A_51),A_51)
      | ~ v4_pre_topc('#skF_1'(A_51),A_51)
      | ~ m1_subset_1('#skF_2'(A_51),k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ m1_subset_1('#skF_1'(A_51),k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ l1_pre_topc(A_51)
      | ~ v2_pre_topc(A_51) ) ),
    inference(resolution,[status(thm)],[c_2,c_55])).

tff(c_65,plain,(
    ! [A_54,B_55,C_56] :
      ( v2_tex_2(k4_subset_1(u1_struct_0(A_54),B_55,C_56),A_54)
      | ~ v2_tex_2(C_56,A_54)
      | ~ v2_tex_2(B_55,A_54)
      | ~ v4_pre_topc(C_56,A_54)
      | ~ v4_pre_topc(B_55,A_54)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ m1_subset_1(B_55,k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ v4_pre_topc('#skF_2'(A_54),A_54)
      | ~ v4_pre_topc('#skF_1'(A_54),A_54)
      | ~ m1_subset_1('#skF_2'(A_54),k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ m1_subset_1('#skF_1'(A_54),k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ l1_pre_topc(A_54)
      | ~ v2_pre_topc(A_54) ) ),
    inference(resolution,[status(thm)],[c_4,c_60])).

tff(c_69,plain,(
    ! [B_59,A_60,C_57,B_61,C_58] :
      ( v2_tex_2(k4_subset_1(u1_struct_0(A_60),B_59,C_58),A_60)
      | ~ v2_tex_2(C_58,A_60)
      | ~ v2_tex_2(B_59,A_60)
      | ~ v4_pre_topc(C_58,A_60)
      | ~ v4_pre_topc(B_59,A_60)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ v4_pre_topc('#skF_2'(A_60),A_60)
      | ~ v4_pre_topc('#skF_1'(A_60),A_60)
      | ~ m1_subset_1('#skF_1'(A_60),k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ v2_pre_topc(A_60)
      | v2_tex_2(k4_subset_1(u1_struct_0(A_60),B_61,C_57),A_60)
      | ~ v2_tex_2(C_57,A_60)
      | ~ v2_tex_2(B_61,A_60)
      | ~ v4_pre_topc(C_57,A_60)
      | ~ v4_pre_topc(B_61,A_60)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ m1_subset_1(B_61,k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ l1_pre_topc(A_60) ) ),
    inference(resolution,[status(thm)],[c_12,c_65])).

tff(c_115,plain,(
    ! [B_62,C_67,A_66,B_68,C_63,C_64,B_65] :
      ( v2_tex_2(k4_subset_1(u1_struct_0(A_66),B_62,C_64),A_66)
      | ~ v2_tex_2(C_64,A_66)
      | ~ v2_tex_2(B_62,A_66)
      | ~ v4_pre_topc(C_64,A_66)
      | ~ v4_pre_topc(B_62,A_66)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ v4_pre_topc('#skF_2'(A_66),A_66)
      | ~ v4_pre_topc('#skF_1'(A_66),A_66)
      | ~ v2_pre_topc(A_66)
      | v2_tex_2(k4_subset_1(u1_struct_0(A_66),B_65,C_67),A_66)
      | ~ v2_tex_2(C_67,A_66)
      | ~ v2_tex_2(B_65,A_66)
      | ~ v4_pre_topc(C_67,A_66)
      | ~ v4_pre_topc(B_65,A_66)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0(A_66)))
      | v2_tex_2(k4_subset_1(u1_struct_0(A_66),B_68,C_63),A_66)
      | ~ v2_tex_2(C_63,A_66)
      | ~ v2_tex_2(B_68,A_66)
      | ~ v4_pre_topc(C_63,A_66)
      | ~ v4_pre_topc(B_68,A_66)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ m1_subset_1(B_68,k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ l1_pre_topc(A_66) ) ),
    inference(resolution,[status(thm)],[c_14,c_69])).

tff(c_118,plain,(
    ! [B_65,C_67,B_68,C_63] :
      ( ~ v2_tex_2('#skF_5','#skF_3')
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ v4_pre_topc('#skF_5','#skF_3')
      | ~ v4_pre_topc('#skF_4','#skF_3')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v4_pre_topc('#skF_2'('#skF_3'),'#skF_3')
      | ~ v4_pre_topc('#skF_1'('#skF_3'),'#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_tex_2(k4_subset_1(u1_struct_0('#skF_3'),B_65,C_67),'#skF_3')
      | ~ v2_tex_2(C_67,'#skF_3')
      | ~ v2_tex_2(B_65,'#skF_3')
      | ~ v4_pre_topc(C_67,'#skF_3')
      | ~ v4_pre_topc(B_65,'#skF_3')
      | ~ m1_subset_1(C_67,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_tex_2(k4_subset_1(u1_struct_0('#skF_3'),B_68,C_63),'#skF_3')
      | ~ v2_tex_2(C_63,'#skF_3')
      | ~ v2_tex_2(B_68,'#skF_3')
      | ~ v4_pre_topc(C_63,'#skF_3')
      | ~ v4_pre_topc(B_68,'#skF_3')
      | ~ m1_subset_1(C_63,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_68,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_115,c_16])).

tff(c_127,plain,(
    ! [B_65,C_67,B_68,C_63] :
      ( v2_tex_2(k4_subset_1(u1_struct_0('#skF_3'),B_65,C_67),'#skF_3')
      | ~ v2_tex_2(C_67,'#skF_3')
      | ~ v2_tex_2(B_65,'#skF_3')
      | ~ v4_pre_topc(C_67,'#skF_3')
      | ~ v4_pre_topc(B_65,'#skF_3')
      | ~ m1_subset_1(C_67,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_tex_2(k4_subset_1(u1_struct_0('#skF_3'),B_68,C_63),'#skF_3')
      | ~ v2_tex_2(C_63,'#skF_3')
      | ~ v2_tex_2(B_68,'#skF_3')
      | ~ v4_pre_topc(C_63,'#skF_3')
      | ~ v4_pre_topc(B_68,'#skF_3')
      | ~ m1_subset_1(C_63,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_68,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_32,c_50,c_43,c_28,c_26,c_24,c_22,c_20,c_18,c_118])).

tff(c_135,plain,(
    ! [B_69,C_70] :
      ( v2_tex_2(k4_subset_1(u1_struct_0('#skF_3'),B_69,C_70),'#skF_3')
      | ~ v2_tex_2(C_70,'#skF_3')
      | ~ v2_tex_2(B_69,'#skF_3')
      | ~ v4_pre_topc(C_70,'#skF_3')
      | ~ v4_pre_topc(B_69,'#skF_3')
      | ~ m1_subset_1(C_70,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(splitLeft,[status(thm)],[c_127])).

tff(c_138,plain,
    ( ~ v2_tex_2('#skF_5','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ v4_pre_topc('#skF_5','#skF_3')
    | ~ v4_pre_topc('#skF_4','#skF_3')
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
      | ~ v4_pre_topc(C_72,'#skF_3')
      | ~ v4_pre_topc(B_71,'#skF_3')
      | ~ m1_subset_1(C_72,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_71,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(splitRight,[status(thm)],[c_127])).

tff(c_147,plain,
    ( ~ v2_tex_2('#skF_5','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ v4_pre_topc('#skF_5','#skF_3')
    | ~ v4_pre_topc('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_144,c_16])).

tff(c_151,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_22,c_20,c_18,c_147])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:46:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.21/1.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.21/1.47  
% 3.21/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.36/1.47  %$ v4_pre_topc > v2_tex_2 > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k4_subset_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4
% 3.36/1.47  
% 3.36/1.47  %Foreground sorts:
% 3.36/1.47  
% 3.36/1.47  
% 3.36/1.47  %Background operators:
% 3.36/1.47  
% 3.36/1.47  
% 3.36/1.47  %Foreground operators:
% 3.36/1.47  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.36/1.47  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.36/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.36/1.47  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.36/1.47  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.36/1.47  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 3.36/1.47  tff('#skF_5', type, '#skF_5': $i).
% 3.36/1.47  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.36/1.47  tff('#skF_3', type, '#skF_3': $i).
% 3.36/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.36/1.47  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.36/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.36/1.47  tff('#skF_4', type, '#skF_4': $i).
% 3.36/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.36/1.47  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.36/1.47  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.36/1.47  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.36/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.36/1.47  
% 3.36/1.49  tff(f_113, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((((v4_pre_topc(B, A) & v4_pre_topc(C, A)) & v2_tex_2(B, A)) & v2_tex_2(C, A)) => v2_tex_2(k4_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_tex_2)).
% 3.36/1.49  tff(f_89, axiom, (![A]: (l1_pre_topc(A) => ((![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) & v4_pre_topc(C, A)) => (v4_pre_topc(k9_subset_1(u1_struct_0(A), B, C), A) & v4_pre_topc(k4_subset_1(u1_struct_0(A), B, C), A))))))) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((((v4_pre_topc(B, A) & v4_pre_topc(C, A)) & v2_tex_2(B, A)) & v2_tex_2(C, A)) => v2_tex_2(k4_subset_1(u1_struct_0(A), B, C), A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_tex_2)).
% 3.36/1.49  tff(f_57, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) & v4_pre_topc(C, A)) => v4_pre_topc(k4_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_tops_1)).
% 3.36/1.49  tff(f_41, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) & v4_pre_topc(C, A)) => v4_pre_topc(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_tops_1)).
% 3.36/1.49  tff(c_28, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.36/1.49  tff(c_26, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.36/1.49  tff(c_24, plain, (v4_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.36/1.49  tff(c_22, plain, (v4_pre_topc('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.36/1.49  tff(c_20, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.36/1.49  tff(c_18, plain, (v2_tex_2('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.36/1.49  tff(c_30, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.36/1.49  tff(c_32, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.36/1.49  tff(c_44, plain, (![A_39, B_40, C_41]: (v4_pre_topc('#skF_1'(A_39), A_39) | v2_tex_2(k4_subset_1(u1_struct_0(A_39), B_40, C_41), A_39) | ~v2_tex_2(C_41, A_39) | ~v2_tex_2(B_40, A_39) | ~v4_pre_topc(C_41, A_39) | ~v4_pre_topc(B_40, A_39) | ~m1_subset_1(C_41, k1_zfmisc_1(u1_struct_0(A_39))) | ~m1_subset_1(B_40, k1_zfmisc_1(u1_struct_0(A_39))) | ~l1_pre_topc(A_39))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.36/1.49  tff(c_16, plain, (~v2_tex_2(k4_subset_1(u1_struct_0('#skF_3'), '#skF_4', '#skF_5'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.36/1.49  tff(c_47, plain, (v4_pre_topc('#skF_1'('#skF_3'), '#skF_3') | ~v2_tex_2('#skF_5', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~v4_pre_topc('#skF_5', '#skF_3') | ~v4_pre_topc('#skF_4', '#skF_3') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_44, c_16])).
% 3.36/1.49  tff(c_50, plain, (v4_pre_topc('#skF_1'('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_24, c_22, c_20, c_18, c_47])).
% 3.36/1.49  tff(c_37, plain, (![A_36, B_37, C_38]: (v4_pre_topc('#skF_2'(A_36), A_36) | v2_tex_2(k4_subset_1(u1_struct_0(A_36), B_37, C_38), A_36) | ~v2_tex_2(C_38, A_36) | ~v2_tex_2(B_37, A_36) | ~v4_pre_topc(C_38, A_36) | ~v4_pre_topc(B_37, A_36) | ~m1_subset_1(C_38, k1_zfmisc_1(u1_struct_0(A_36))) | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0(A_36))) | ~l1_pre_topc(A_36))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.36/1.49  tff(c_40, plain, (v4_pre_topc('#skF_2'('#skF_3'), '#skF_3') | ~v2_tex_2('#skF_5', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~v4_pre_topc('#skF_5', '#skF_3') | ~v4_pre_topc('#skF_4', '#skF_3') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_37, c_16])).
% 3.36/1.49  tff(c_43, plain, (v4_pre_topc('#skF_2'('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_24, c_22, c_20, c_18, c_40])).
% 3.36/1.49  tff(c_14, plain, (![A_15, B_23, C_25]: (m1_subset_1('#skF_1'(A_15), k1_zfmisc_1(u1_struct_0(A_15))) | v2_tex_2(k4_subset_1(u1_struct_0(A_15), B_23, C_25), A_15) | ~v2_tex_2(C_25, A_15) | ~v2_tex_2(B_23, A_15) | ~v4_pre_topc(C_25, A_15) | ~v4_pre_topc(B_23, A_15) | ~m1_subset_1(C_25, k1_zfmisc_1(u1_struct_0(A_15))) | ~m1_subset_1(B_23, k1_zfmisc_1(u1_struct_0(A_15))) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.36/1.49  tff(c_12, plain, (![A_15, B_23, C_25]: (m1_subset_1('#skF_2'(A_15), k1_zfmisc_1(u1_struct_0(A_15))) | v2_tex_2(k4_subset_1(u1_struct_0(A_15), B_23, C_25), A_15) | ~v2_tex_2(C_25, A_15) | ~v2_tex_2(B_23, A_15) | ~v4_pre_topc(C_25, A_15) | ~v4_pre_topc(B_23, A_15) | ~m1_subset_1(C_25, k1_zfmisc_1(u1_struct_0(A_15))) | ~m1_subset_1(B_23, k1_zfmisc_1(u1_struct_0(A_15))) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.36/1.49  tff(c_4, plain, (![A_8, B_12, C_14]: (v4_pre_topc(k4_subset_1(u1_struct_0(A_8), B_12, C_14), A_8) | ~v4_pre_topc(C_14, A_8) | ~v4_pre_topc(B_12, A_8) | ~m1_subset_1(C_14, k1_zfmisc_1(u1_struct_0(A_8))) | ~m1_subset_1(B_12, k1_zfmisc_1(u1_struct_0(A_8))) | ~l1_pre_topc(A_8) | ~v2_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.36/1.49  tff(c_2, plain, (![A_1, B_5, C_7]: (v4_pre_topc(k9_subset_1(u1_struct_0(A_1), B_5, C_7), A_1) | ~v4_pre_topc(C_7, A_1) | ~v4_pre_topc(B_5, A_1) | ~m1_subset_1(C_7, k1_zfmisc_1(u1_struct_0(A_1))) | ~m1_subset_1(B_5, k1_zfmisc_1(u1_struct_0(A_1))) | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.36/1.49  tff(c_55, plain, (![A_48, B_49, C_50]: (~v4_pre_topc(k4_subset_1(u1_struct_0(A_48), '#skF_1'(A_48), '#skF_2'(A_48)), A_48) | ~v4_pre_topc(k9_subset_1(u1_struct_0(A_48), '#skF_1'(A_48), '#skF_2'(A_48)), A_48) | v2_tex_2(k4_subset_1(u1_struct_0(A_48), B_49, C_50), A_48) | ~v2_tex_2(C_50, A_48) | ~v2_tex_2(B_49, A_48) | ~v4_pre_topc(C_50, A_48) | ~v4_pre_topc(B_49, A_48) | ~m1_subset_1(C_50, k1_zfmisc_1(u1_struct_0(A_48))) | ~m1_subset_1(B_49, k1_zfmisc_1(u1_struct_0(A_48))) | ~l1_pre_topc(A_48))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.36/1.49  tff(c_60, plain, (![A_51, B_52, C_53]: (~v4_pre_topc(k4_subset_1(u1_struct_0(A_51), '#skF_1'(A_51), '#skF_2'(A_51)), A_51) | v2_tex_2(k4_subset_1(u1_struct_0(A_51), B_52, C_53), A_51) | ~v2_tex_2(C_53, A_51) | ~v2_tex_2(B_52, A_51) | ~v4_pre_topc(C_53, A_51) | ~v4_pre_topc(B_52, A_51) | ~m1_subset_1(C_53, k1_zfmisc_1(u1_struct_0(A_51))) | ~m1_subset_1(B_52, k1_zfmisc_1(u1_struct_0(A_51))) | ~v4_pre_topc('#skF_2'(A_51), A_51) | ~v4_pre_topc('#skF_1'(A_51), A_51) | ~m1_subset_1('#skF_2'(A_51), k1_zfmisc_1(u1_struct_0(A_51))) | ~m1_subset_1('#skF_1'(A_51), k1_zfmisc_1(u1_struct_0(A_51))) | ~l1_pre_topc(A_51) | ~v2_pre_topc(A_51))), inference(resolution, [status(thm)], [c_2, c_55])).
% 3.36/1.49  tff(c_65, plain, (![A_54, B_55, C_56]: (v2_tex_2(k4_subset_1(u1_struct_0(A_54), B_55, C_56), A_54) | ~v2_tex_2(C_56, A_54) | ~v2_tex_2(B_55, A_54) | ~v4_pre_topc(C_56, A_54) | ~v4_pre_topc(B_55, A_54) | ~m1_subset_1(C_56, k1_zfmisc_1(u1_struct_0(A_54))) | ~m1_subset_1(B_55, k1_zfmisc_1(u1_struct_0(A_54))) | ~v4_pre_topc('#skF_2'(A_54), A_54) | ~v4_pre_topc('#skF_1'(A_54), A_54) | ~m1_subset_1('#skF_2'(A_54), k1_zfmisc_1(u1_struct_0(A_54))) | ~m1_subset_1('#skF_1'(A_54), k1_zfmisc_1(u1_struct_0(A_54))) | ~l1_pre_topc(A_54) | ~v2_pre_topc(A_54))), inference(resolution, [status(thm)], [c_4, c_60])).
% 3.36/1.49  tff(c_69, plain, (![B_59, A_60, C_57, B_61, C_58]: (v2_tex_2(k4_subset_1(u1_struct_0(A_60), B_59, C_58), A_60) | ~v2_tex_2(C_58, A_60) | ~v2_tex_2(B_59, A_60) | ~v4_pre_topc(C_58, A_60) | ~v4_pre_topc(B_59, A_60) | ~m1_subset_1(C_58, k1_zfmisc_1(u1_struct_0(A_60))) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(A_60))) | ~v4_pre_topc('#skF_2'(A_60), A_60) | ~v4_pre_topc('#skF_1'(A_60), A_60) | ~m1_subset_1('#skF_1'(A_60), k1_zfmisc_1(u1_struct_0(A_60))) | ~v2_pre_topc(A_60) | v2_tex_2(k4_subset_1(u1_struct_0(A_60), B_61, C_57), A_60) | ~v2_tex_2(C_57, A_60) | ~v2_tex_2(B_61, A_60) | ~v4_pre_topc(C_57, A_60) | ~v4_pre_topc(B_61, A_60) | ~m1_subset_1(C_57, k1_zfmisc_1(u1_struct_0(A_60))) | ~m1_subset_1(B_61, k1_zfmisc_1(u1_struct_0(A_60))) | ~l1_pre_topc(A_60))), inference(resolution, [status(thm)], [c_12, c_65])).
% 3.36/1.49  tff(c_115, plain, (![B_62, C_67, A_66, B_68, C_63, C_64, B_65]: (v2_tex_2(k4_subset_1(u1_struct_0(A_66), B_62, C_64), A_66) | ~v2_tex_2(C_64, A_66) | ~v2_tex_2(B_62, A_66) | ~v4_pre_topc(C_64, A_66) | ~v4_pre_topc(B_62, A_66) | ~m1_subset_1(C_64, k1_zfmisc_1(u1_struct_0(A_66))) | ~m1_subset_1(B_62, k1_zfmisc_1(u1_struct_0(A_66))) | ~v4_pre_topc('#skF_2'(A_66), A_66) | ~v4_pre_topc('#skF_1'(A_66), A_66) | ~v2_pre_topc(A_66) | v2_tex_2(k4_subset_1(u1_struct_0(A_66), B_65, C_67), A_66) | ~v2_tex_2(C_67, A_66) | ~v2_tex_2(B_65, A_66) | ~v4_pre_topc(C_67, A_66) | ~v4_pre_topc(B_65, A_66) | ~m1_subset_1(C_67, k1_zfmisc_1(u1_struct_0(A_66))) | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0(A_66))) | v2_tex_2(k4_subset_1(u1_struct_0(A_66), B_68, C_63), A_66) | ~v2_tex_2(C_63, A_66) | ~v2_tex_2(B_68, A_66) | ~v4_pre_topc(C_63, A_66) | ~v4_pre_topc(B_68, A_66) | ~m1_subset_1(C_63, k1_zfmisc_1(u1_struct_0(A_66))) | ~m1_subset_1(B_68, k1_zfmisc_1(u1_struct_0(A_66))) | ~l1_pre_topc(A_66))), inference(resolution, [status(thm)], [c_14, c_69])).
% 3.36/1.49  tff(c_118, plain, (![B_65, C_67, B_68, C_63]: (~v2_tex_2('#skF_5', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~v4_pre_topc('#skF_5', '#skF_3') | ~v4_pre_topc('#skF_4', '#skF_3') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v4_pre_topc('#skF_2'('#skF_3'), '#skF_3') | ~v4_pre_topc('#skF_1'('#skF_3'), '#skF_3') | ~v2_pre_topc('#skF_3') | v2_tex_2(k4_subset_1(u1_struct_0('#skF_3'), B_65, C_67), '#skF_3') | ~v2_tex_2(C_67, '#skF_3') | ~v2_tex_2(B_65, '#skF_3') | ~v4_pre_topc(C_67, '#skF_3') | ~v4_pre_topc(B_65, '#skF_3') | ~m1_subset_1(C_67, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_tex_2(k4_subset_1(u1_struct_0('#skF_3'), B_68, C_63), '#skF_3') | ~v2_tex_2(C_63, '#skF_3') | ~v2_tex_2(B_68, '#skF_3') | ~v4_pre_topc(C_63, '#skF_3') | ~v4_pre_topc(B_68, '#skF_3') | ~m1_subset_1(C_63, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_68, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_115, c_16])).
% 3.36/1.49  tff(c_127, plain, (![B_65, C_67, B_68, C_63]: (v2_tex_2(k4_subset_1(u1_struct_0('#skF_3'), B_65, C_67), '#skF_3') | ~v2_tex_2(C_67, '#skF_3') | ~v2_tex_2(B_65, '#skF_3') | ~v4_pre_topc(C_67, '#skF_3') | ~v4_pre_topc(B_65, '#skF_3') | ~m1_subset_1(C_67, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_tex_2(k4_subset_1(u1_struct_0('#skF_3'), B_68, C_63), '#skF_3') | ~v2_tex_2(C_63, '#skF_3') | ~v2_tex_2(B_68, '#skF_3') | ~v4_pre_topc(C_63, '#skF_3') | ~v4_pre_topc(B_68, '#skF_3') | ~m1_subset_1(C_63, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_68, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_32, c_50, c_43, c_28, c_26, c_24, c_22, c_20, c_18, c_118])).
% 3.36/1.49  tff(c_135, plain, (![B_69, C_70]: (v2_tex_2(k4_subset_1(u1_struct_0('#skF_3'), B_69, C_70), '#skF_3') | ~v2_tex_2(C_70, '#skF_3') | ~v2_tex_2(B_69, '#skF_3') | ~v4_pre_topc(C_70, '#skF_3') | ~v4_pre_topc(B_69, '#skF_3') | ~m1_subset_1(C_70, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_69, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(splitLeft, [status(thm)], [c_127])).
% 3.36/1.49  tff(c_138, plain, (~v2_tex_2('#skF_5', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~v4_pre_topc('#skF_5', '#skF_3') | ~v4_pre_topc('#skF_4', '#skF_3') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_135, c_16])).
% 3.36/1.49  tff(c_142, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_24, c_22, c_20, c_18, c_138])).
% 3.36/1.49  tff(c_144, plain, (![B_71, C_72]: (v2_tex_2(k4_subset_1(u1_struct_0('#skF_3'), B_71, C_72), '#skF_3') | ~v2_tex_2(C_72, '#skF_3') | ~v2_tex_2(B_71, '#skF_3') | ~v4_pre_topc(C_72, '#skF_3') | ~v4_pre_topc(B_71, '#skF_3') | ~m1_subset_1(C_72, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_71, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(splitRight, [status(thm)], [c_127])).
% 3.36/1.49  tff(c_147, plain, (~v2_tex_2('#skF_5', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~v4_pre_topc('#skF_5', '#skF_3') | ~v4_pre_topc('#skF_4', '#skF_3') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_144, c_16])).
% 3.36/1.49  tff(c_151, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_24, c_22, c_20, c_18, c_147])).
% 3.36/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.36/1.49  
% 3.36/1.49  Inference rules
% 3.36/1.49  ----------------------
% 3.36/1.49  #Ref     : 0
% 3.36/1.49  #Sup     : 11
% 3.36/1.49  #Fact    : 6
% 3.36/1.49  #Define  : 0
% 3.36/1.49  #Split   : 1
% 3.36/1.49  #Chain   : 0
% 3.36/1.49  #Close   : 0
% 3.36/1.49  
% 3.36/1.49  Ordering : KBO
% 3.36/1.49  
% 3.36/1.49  Simplification rules
% 3.36/1.49  ----------------------
% 3.36/1.49  #Subsume      : 1
% 3.36/1.49  #Demod        : 56
% 3.36/1.49  #Tautology    : 0
% 3.36/1.49  #SimpNegUnit  : 0
% 3.36/1.49  #BackRed      : 0
% 3.36/1.49  
% 3.36/1.49  #Partial instantiations: 0
% 3.36/1.49  #Strategies tried      : 1
% 3.36/1.49  
% 3.36/1.49  Timing (in seconds)
% 3.36/1.49  ----------------------
% 3.36/1.50  Preprocessing        : 0.30
% 3.36/1.50  Parsing              : 0.17
% 3.36/1.50  CNF conversion       : 0.02
% 3.36/1.50  Main loop            : 0.43
% 3.36/1.50  Inferencing          : 0.10
% 3.36/1.50  Reduction            : 0.06
% 3.36/1.50  Demodulation         : 0.04
% 3.36/1.50  BG Simplification    : 0.01
% 3.36/1.50  Subsumption          : 0.25
% 3.36/1.50  Abstraction          : 0.01
% 3.36/1.50  MUC search           : 0.00
% 3.36/1.50  Cooper               : 0.00
% 3.36/1.50  Total                : 0.76
% 3.36/1.50  Index Insertion      : 0.00
% 3.36/1.50  Index Deletion       : 0.00
% 3.36/1.50  Index Matching       : 0.00
% 3.36/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
