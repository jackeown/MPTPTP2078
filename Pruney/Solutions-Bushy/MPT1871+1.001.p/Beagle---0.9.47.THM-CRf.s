%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1871+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:35 EST 2020

% Result     : Theorem 4.08s
% Output     : CNFRefutation 4.37s
% Verified   : 
% Statistics : Number of formulae       :  106 (1085 expanded)
%              Number of leaves         :   26 ( 418 expanded)
%              Depth                    :   22
%              Number of atoms          :  388 (5587 expanded)
%              Number of equality atoms :   16 ( 244 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_tex_2 > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k4_subset_1 > k3_xboole_0 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_118,negated_conjecture,(
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

tff(f_58,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_94,axiom,(
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

tff(f_52,axiom,(
    ! [A,B,C] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & v4_pre_topc(B,A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & v4_pre_topc(C,A)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_xboole_0(B,C),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_tops_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & v4_pre_topc(B,A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & v4_pre_topc(C,A)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k3_xboole_0(B,C),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_tops_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(c_32,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_30,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_64,plain,(
    ! [A_33,B_34,C_35] :
      ( k4_subset_1(A_33,B_34,C_35) = k2_xboole_0(B_34,C_35)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(A_33))
      | ~ m1_subset_1(B_34,k1_zfmisc_1(A_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_112,plain,(
    ! [B_41] :
      ( k4_subset_1(u1_struct_0('#skF_3'),B_41,'#skF_5') = k2_xboole_0(B_41,'#skF_5')
      | ~ m1_subset_1(B_41,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_30,c_64])).

tff(c_119,plain,(
    k4_subset_1(u1_struct_0('#skF_3'),'#skF_4','#skF_5') = k2_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_112])).

tff(c_20,plain,(
    ~ v2_tex_2(k4_subset_1(u1_struct_0('#skF_3'),'#skF_4','#skF_5'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_125,plain,(
    ~ v2_tex_2(k2_xboole_0('#skF_4','#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_20])).

tff(c_28,plain,(
    v4_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_26,plain,(
    v4_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_24,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_22,plain,(
    v2_tex_2('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_34,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_18,plain,(
    ! [A_13,B_21,C_23] :
      ( m1_subset_1('#skF_1'(A_13),k1_zfmisc_1(u1_struct_0(A_13)))
      | v2_tex_2(k4_subset_1(u1_struct_0(A_13),B_21,C_23),A_13)
      | ~ v2_tex_2(C_23,A_13)
      | ~ v2_tex_2(B_21,A_13)
      | ~ v4_pre_topc(C_23,A_13)
      | ~ v4_pre_topc(B_21,A_13)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ m1_subset_1(B_21,k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_205,plain,(
    ! [A_51,B_52,C_53] :
      ( v4_pre_topc('#skF_1'(A_51),A_51)
      | v2_tex_2(k4_subset_1(u1_struct_0(A_51),B_52,C_53),A_51)
      | ~ v2_tex_2(C_53,A_51)
      | ~ v2_tex_2(B_52,A_51)
      | ~ v4_pre_topc(C_53,A_51)
      | ~ v4_pre_topc(B_52,A_51)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ m1_subset_1(B_52,k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ l1_pre_topc(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_208,plain,
    ( v4_pre_topc('#skF_1'('#skF_3'),'#skF_3')
    | v2_tex_2(k2_xboole_0('#skF_4','#skF_5'),'#skF_3')
    | ~ v2_tex_2('#skF_5','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ v4_pre_topc('#skF_5','#skF_3')
    | ~ v4_pre_topc('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_205])).

tff(c_219,plain,
    ( v4_pre_topc('#skF_1'('#skF_3'),'#skF_3')
    | v2_tex_2(k2_xboole_0('#skF_4','#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_28,c_26,c_24,c_22,c_208])).

tff(c_220,plain,(
    v4_pre_topc('#skF_1'('#skF_3'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_125,c_219])).

tff(c_36,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_180,plain,(
    ! [A_48,B_49,C_50] :
      ( v4_pre_topc('#skF_2'(A_48),A_48)
      | v2_tex_2(k4_subset_1(u1_struct_0(A_48),B_49,C_50),A_48)
      | ~ v2_tex_2(C_50,A_48)
      | ~ v2_tex_2(B_49,A_48)
      | ~ v4_pre_topc(C_50,A_48)
      | ~ v4_pre_topc(B_49,A_48)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ m1_subset_1(B_49,k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ l1_pre_topc(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_183,plain,
    ( v4_pre_topc('#skF_2'('#skF_3'),'#skF_3')
    | v2_tex_2(k2_xboole_0('#skF_4','#skF_5'),'#skF_3')
    | ~ v2_tex_2('#skF_5','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ v4_pre_topc('#skF_5','#skF_3')
    | ~ v4_pre_topc('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_180])).

tff(c_194,plain,
    ( v4_pre_topc('#skF_2'('#skF_3'),'#skF_3')
    | v2_tex_2(k2_xboole_0('#skF_4','#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_28,c_26,c_24,c_22,c_183])).

tff(c_195,plain,(
    v4_pre_topc('#skF_2'('#skF_3'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_125,c_194])).

tff(c_16,plain,(
    ! [A_13,B_21,C_23] :
      ( m1_subset_1('#skF_2'(A_13),k1_zfmisc_1(u1_struct_0(A_13)))
      | v2_tex_2(k4_subset_1(u1_struct_0(A_13),B_21,C_23),A_13)
      | ~ v2_tex_2(C_23,A_13)
      | ~ v2_tex_2(B_21,A_13)
      | ~ v4_pre_topc(C_23,A_13)
      | ~ v4_pre_topc(B_21,A_13)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ m1_subset_1(B_21,k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_230,plain,(
    ! [A_54,B_55,C_56] :
      ( m1_subset_1('#skF_2'(A_54),k1_zfmisc_1(u1_struct_0(A_54)))
      | v2_tex_2(k4_subset_1(u1_struct_0(A_54),B_55,C_56),A_54)
      | ~ v2_tex_2(C_56,A_54)
      | ~ v2_tex_2(B_55,A_54)
      | ~ v4_pre_topc(C_56,A_54)
      | ~ v4_pre_topc(B_55,A_54)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ m1_subset_1(B_55,k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ l1_pre_topc(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_69,plain,(
    ! [B_34] :
      ( k4_subset_1(u1_struct_0('#skF_3'),B_34,'#skF_4') = k2_xboole_0(B_34,'#skF_4')
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_32,c_64])).

tff(c_258,plain,(
    ! [B_55,C_56] :
      ( k4_subset_1(u1_struct_0('#skF_3'),'#skF_2'('#skF_3'),'#skF_4') = k2_xboole_0('#skF_2'('#skF_3'),'#skF_4')
      | v2_tex_2(k4_subset_1(u1_struct_0('#skF_3'),B_55,C_56),'#skF_3')
      | ~ v2_tex_2(C_56,'#skF_3')
      | ~ v2_tex_2(B_55,'#skF_3')
      | ~ v4_pre_topc(C_56,'#skF_3')
      | ~ v4_pre_topc(B_55,'#skF_3')
      | ~ m1_subset_1(C_56,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_55,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_230,c_69])).

tff(c_286,plain,(
    ! [B_55,C_56] :
      ( k4_subset_1(u1_struct_0('#skF_3'),'#skF_2'('#skF_3'),'#skF_4') = k2_xboole_0('#skF_2'('#skF_3'),'#skF_4')
      | v2_tex_2(k4_subset_1(u1_struct_0('#skF_3'),B_55,C_56),'#skF_3')
      | ~ v2_tex_2(C_56,'#skF_3')
      | ~ v2_tex_2(B_55,'#skF_3')
      | ~ v4_pre_topc(C_56,'#skF_3')
      | ~ v4_pre_topc(B_55,'#skF_3')
      | ~ m1_subset_1(C_56,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_55,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_258])).

tff(c_291,plain,(
    k4_subset_1(u1_struct_0('#skF_3'),'#skF_2'('#skF_3'),'#skF_4') = k2_xboole_0('#skF_2'('#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_286])).

tff(c_313,plain,(
    ! [A_57,B_58,C_59] :
      ( m1_subset_1('#skF_1'(A_57),k1_zfmisc_1(u1_struct_0(A_57)))
      | v2_tex_2(k4_subset_1(u1_struct_0(A_57),B_58,C_59),A_57)
      | ~ v2_tex_2(C_59,A_57)
      | ~ v2_tex_2(B_58,A_57)
      | ~ v4_pre_topc(C_59,A_57)
      | ~ v4_pre_topc(B_58,A_57)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(u1_struct_0(A_57)))
      | ~ m1_subset_1(B_58,k1_zfmisc_1(u1_struct_0(A_57)))
      | ~ l1_pre_topc(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_348,plain,
    ( m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v2_tex_2(k2_xboole_0('#skF_2'('#skF_3'),'#skF_4'),'#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_2'('#skF_3'),'#skF_3')
    | ~ v4_pre_topc('#skF_4','#skF_3')
    | ~ v4_pre_topc('#skF_2'('#skF_3'),'#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_2'('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_291,c_313])).

tff(c_376,plain,
    ( m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v2_tex_2(k2_xboole_0('#skF_2'('#skF_3'),'#skF_4'),'#skF_3')
    | ~ v2_tex_2('#skF_2'('#skF_3'),'#skF_3')
    | ~ m1_subset_1('#skF_2'('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_195,c_28,c_24,c_348])).

tff(c_377,plain,(
    ~ m1_subset_1('#skF_2'('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_376])).

tff(c_380,plain,(
    ! [B_21,C_23] :
      ( v2_tex_2(k4_subset_1(u1_struct_0('#skF_3'),B_21,C_23),'#skF_3')
      | ~ v2_tex_2(C_23,'#skF_3')
      | ~ v2_tex_2(B_21,'#skF_3')
      | ~ v4_pre_topc(C_23,'#skF_3')
      | ~ v4_pre_topc(B_21,'#skF_3')
      | ~ m1_subset_1(C_23,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_21,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_16,c_377])).

tff(c_410,plain,(
    ! [B_60,C_61] :
      ( v2_tex_2(k4_subset_1(u1_struct_0('#skF_3'),B_60,C_61),'#skF_3')
      | ~ v2_tex_2(C_61,'#skF_3')
      | ~ v2_tex_2(B_60,'#skF_3')
      | ~ v4_pre_topc(C_61,'#skF_3')
      | ~ v4_pre_topc(B_60,'#skF_3')
      | ~ m1_subset_1(C_61,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_380])).

tff(c_419,plain,
    ( v2_tex_2(k2_xboole_0('#skF_4','#skF_5'),'#skF_3')
    | ~ v2_tex_2('#skF_5','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ v4_pre_topc('#skF_5','#skF_3')
    | ~ v4_pre_topc('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_410])).

tff(c_434,plain,(
    v2_tex_2(k2_xboole_0('#skF_4','#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_26,c_24,c_22,c_419])).

tff(c_436,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_125,c_434])).

tff(c_438,plain,(
    m1_subset_1('#skF_2'('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_376])).

tff(c_4,plain,(
    ! [B_5,C_6,A_4] :
      ( v4_pre_topc(k2_xboole_0(B_5,C_6),A_4)
      | ~ m1_subset_1(C_6,k1_zfmisc_1(u1_struct_0(A_4)))
      | ~ v4_pre_topc(C_6,A_4)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(u1_struct_0(A_4)))
      | ~ v4_pre_topc(B_5,A_4)
      | ~ l1_pre_topc(A_4)
      | ~ v2_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_449,plain,(
    ! [B_5] :
      ( v4_pre_topc(k2_xboole_0(B_5,'#skF_2'('#skF_3')),'#skF_3')
      | ~ v4_pre_topc('#skF_2'('#skF_3'),'#skF_3')
      | ~ m1_subset_1(B_5,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v4_pre_topc(B_5,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_438,c_4])).

tff(c_476,plain,(
    ! [B_5] :
      ( v4_pre_topc(k2_xboole_0(B_5,'#skF_2'('#skF_3')),'#skF_3')
      | ~ m1_subset_1(B_5,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v4_pre_topc(B_5,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_195,c_449])).

tff(c_2,plain,(
    ! [B_2,C_3,A_1] :
      ( v4_pre_topc(k3_xboole_0(B_2,C_3),A_1)
      | ~ m1_subset_1(C_3,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ v4_pre_topc(C_3,A_1)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ v4_pre_topc(B_2,A_1)
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_457,plain,(
    ! [B_2] :
      ( v4_pre_topc(k3_xboole_0(B_2,'#skF_2'('#skF_3')),'#skF_3')
      | ~ v4_pre_topc('#skF_2'('#skF_3'),'#skF_3')
      | ~ m1_subset_1(B_2,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v4_pre_topc(B_2,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_438,c_2])).

tff(c_483,plain,(
    ! [B_2] :
      ( v4_pre_topc(k3_xboole_0(B_2,'#skF_2'('#skF_3')),'#skF_3')
      | ~ m1_subset_1(B_2,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v4_pre_topc(B_2,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_195,c_457])).

tff(c_6,plain,(
    ! [A_7,B_8,C_9] :
      ( k4_subset_1(A_7,B_8,C_9) = k2_xboole_0(B_8,C_9)
      | ~ m1_subset_1(C_9,k1_zfmisc_1(A_7))
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_529,plain,(
    ! [B_68] :
      ( k4_subset_1(u1_struct_0('#skF_3'),B_68,'#skF_2'('#skF_3')) = k2_xboole_0(B_68,'#skF_2'('#skF_3'))
      | ~ m1_subset_1(B_68,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_438,c_6])).

tff(c_536,plain,(
    ! [B_21,C_23] :
      ( k4_subset_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3'),'#skF_2'('#skF_3')) = k2_xboole_0('#skF_1'('#skF_3'),'#skF_2'('#skF_3'))
      | v2_tex_2(k4_subset_1(u1_struct_0('#skF_3'),B_21,C_23),'#skF_3')
      | ~ v2_tex_2(C_23,'#skF_3')
      | ~ v2_tex_2(B_21,'#skF_3')
      | ~ v4_pre_topc(C_23,'#skF_3')
      | ~ v4_pre_topc(B_21,'#skF_3')
      | ~ m1_subset_1(C_23,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_21,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_18,c_529])).

tff(c_550,plain,(
    ! [B_21,C_23] :
      ( k4_subset_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3'),'#skF_2'('#skF_3')) = k2_xboole_0('#skF_1'('#skF_3'),'#skF_2'('#skF_3'))
      | v2_tex_2(k4_subset_1(u1_struct_0('#skF_3'),B_21,C_23),'#skF_3')
      | ~ v2_tex_2(C_23,'#skF_3')
      | ~ v2_tex_2(B_21,'#skF_3')
      | ~ v4_pre_topc(C_23,'#skF_3')
      | ~ v4_pre_topc(B_21,'#skF_3')
      | ~ m1_subset_1(C_23,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_21,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_536])).

tff(c_1005,plain,(
    k4_subset_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3'),'#skF_2'('#skF_3')) = k2_xboole_0('#skF_1'('#skF_3'),'#skF_2'('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_550])).

tff(c_8,plain,(
    ! [A_10,B_11,C_12] :
      ( k9_subset_1(A_10,B_11,C_12) = k3_xboole_0(B_11,C_12)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_487,plain,(
    ! [B_11] : k9_subset_1(u1_struct_0('#skF_3'),B_11,'#skF_2'('#skF_3')) = k3_xboole_0(B_11,'#skF_2'('#skF_3')) ),
    inference(resolution,[status(thm)],[c_438,c_8])).

tff(c_521,plain,(
    ! [A_63,B_64,C_65] :
      ( ~ v4_pre_topc(k4_subset_1(u1_struct_0(A_63),'#skF_1'(A_63),'#skF_2'(A_63)),A_63)
      | ~ v4_pre_topc(k9_subset_1(u1_struct_0(A_63),'#skF_1'(A_63),'#skF_2'(A_63)),A_63)
      | v2_tex_2(k4_subset_1(u1_struct_0(A_63),B_64,C_65),A_63)
      | ~ v2_tex_2(C_65,A_63)
      | ~ v2_tex_2(B_64,A_63)
      | ~ v4_pre_topc(C_65,A_63)
      | ~ v4_pre_topc(B_64,A_63)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ l1_pre_topc(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_524,plain,(
    ! [B_64,C_65] :
      ( ~ v4_pre_topc(k4_subset_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3'),'#skF_2'('#skF_3')),'#skF_3')
      | ~ v4_pre_topc(k3_xboole_0('#skF_1'('#skF_3'),'#skF_2'('#skF_3')),'#skF_3')
      | v2_tex_2(k4_subset_1(u1_struct_0('#skF_3'),B_64,C_65),'#skF_3')
      | ~ v2_tex_2(C_65,'#skF_3')
      | ~ v2_tex_2(B_64,'#skF_3')
      | ~ v4_pre_topc(C_65,'#skF_3')
      | ~ v4_pre_topc(B_64,'#skF_3')
      | ~ m1_subset_1(C_65,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_487,c_521])).

tff(c_526,plain,(
    ! [B_64,C_65] :
      ( ~ v4_pre_topc(k4_subset_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3'),'#skF_2'('#skF_3')),'#skF_3')
      | ~ v4_pre_topc(k3_xboole_0('#skF_1'('#skF_3'),'#skF_2'('#skF_3')),'#skF_3')
      | v2_tex_2(k4_subset_1(u1_struct_0('#skF_3'),B_64,C_65),'#skF_3')
      | ~ v2_tex_2(C_65,'#skF_3')
      | ~ v2_tex_2(B_64,'#skF_3')
      | ~ v4_pre_topc(C_65,'#skF_3')
      | ~ v4_pre_topc(B_64,'#skF_3')
      | ~ m1_subset_1(C_65,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_524])).

tff(c_1040,plain,(
    ! [B_64,C_65] :
      ( ~ v4_pre_topc(k2_xboole_0('#skF_1'('#skF_3'),'#skF_2'('#skF_3')),'#skF_3')
      | ~ v4_pre_topc(k3_xboole_0('#skF_1'('#skF_3'),'#skF_2'('#skF_3')),'#skF_3')
      | v2_tex_2(k4_subset_1(u1_struct_0('#skF_3'),B_64,C_65),'#skF_3')
      | ~ v2_tex_2(C_65,'#skF_3')
      | ~ v2_tex_2(B_64,'#skF_3')
      | ~ v4_pre_topc(C_65,'#skF_3')
      | ~ v4_pre_topc(B_64,'#skF_3')
      | ~ m1_subset_1(C_65,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1005,c_526])).

tff(c_1041,plain,(
    ~ v4_pre_topc(k3_xboole_0('#skF_1'('#skF_3'),'#skF_2'('#skF_3')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1040])).

tff(c_1044,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ v4_pre_topc('#skF_1'('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_483,c_1041])).

tff(c_1047,plain,(
    ~ m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_1044])).

tff(c_1050,plain,(
    ! [B_21,C_23] :
      ( v2_tex_2(k4_subset_1(u1_struct_0('#skF_3'),B_21,C_23),'#skF_3')
      | ~ v2_tex_2(C_23,'#skF_3')
      | ~ v2_tex_2(B_21,'#skF_3')
      | ~ v4_pre_topc(C_23,'#skF_3')
      | ~ v4_pre_topc(B_21,'#skF_3')
      | ~ m1_subset_1(C_23,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_21,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_18,c_1047])).

tff(c_1054,plain,(
    ! [B_86,C_87] :
      ( v2_tex_2(k4_subset_1(u1_struct_0('#skF_3'),B_86,C_87),'#skF_3')
      | ~ v2_tex_2(C_87,'#skF_3')
      | ~ v2_tex_2(B_86,'#skF_3')
      | ~ v4_pre_topc(C_87,'#skF_3')
      | ~ v4_pre_topc(B_86,'#skF_3')
      | ~ m1_subset_1(C_87,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1050])).

tff(c_1090,plain,
    ( v2_tex_2(k2_xboole_0('#skF_4','#skF_5'),'#skF_3')
    | ~ v2_tex_2('#skF_5','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ v4_pre_topc('#skF_5','#skF_3')
    | ~ v4_pre_topc('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_1054])).

tff(c_1123,plain,(
    v2_tex_2(k2_xboole_0('#skF_4','#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_26,c_24,c_22,c_1090])).

tff(c_1125,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_125,c_1123])).

tff(c_1126,plain,(
    ! [B_64,C_65] :
      ( ~ v4_pre_topc(k2_xboole_0('#skF_1'('#skF_3'),'#skF_2'('#skF_3')),'#skF_3')
      | v2_tex_2(k4_subset_1(u1_struct_0('#skF_3'),B_64,C_65),'#skF_3')
      | ~ v2_tex_2(C_65,'#skF_3')
      | ~ v2_tex_2(B_64,'#skF_3')
      | ~ v4_pre_topc(C_65,'#skF_3')
      | ~ v4_pre_topc(B_64,'#skF_3')
      | ~ m1_subset_1(C_65,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(splitRight,[status(thm)],[c_1040])).

tff(c_1128,plain,(
    ~ v4_pre_topc(k2_xboole_0('#skF_1'('#skF_3'),'#skF_2'('#skF_3')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1126])).

tff(c_1131,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ v4_pre_topc('#skF_1'('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_476,c_1128])).

tff(c_1134,plain,(
    ~ m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_1131])).

tff(c_1197,plain,(
    ! [B_21,C_23] :
      ( v2_tex_2(k4_subset_1(u1_struct_0('#skF_3'),B_21,C_23),'#skF_3')
      | ~ v2_tex_2(C_23,'#skF_3')
      | ~ v2_tex_2(B_21,'#skF_3')
      | ~ v4_pre_topc(C_23,'#skF_3')
      | ~ v4_pre_topc(B_21,'#skF_3')
      | ~ m1_subset_1(C_23,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_21,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_18,c_1134])).

tff(c_1201,plain,(
    ! [B_92,C_93] :
      ( v2_tex_2(k4_subset_1(u1_struct_0('#skF_3'),B_92,C_93),'#skF_3')
      | ~ v2_tex_2(C_93,'#skF_3')
      | ~ v2_tex_2(B_92,'#skF_3')
      | ~ v4_pre_topc(C_93,'#skF_3')
      | ~ v4_pre_topc(B_92,'#skF_3')
      | ~ m1_subset_1(C_93,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_92,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1197])).

tff(c_1237,plain,
    ( v2_tex_2(k2_xboole_0('#skF_4','#skF_5'),'#skF_3')
    | ~ v2_tex_2('#skF_5','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ v4_pre_topc('#skF_5','#skF_3')
    | ~ v4_pre_topc('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_1201])).

tff(c_1270,plain,(
    v2_tex_2(k2_xboole_0('#skF_4','#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_26,c_24,c_22,c_1237])).

tff(c_1272,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_125,c_1270])).

tff(c_1275,plain,(
    ! [B_94,C_95] :
      ( v2_tex_2(k4_subset_1(u1_struct_0('#skF_3'),B_94,C_95),'#skF_3')
      | ~ v2_tex_2(C_95,'#skF_3')
      | ~ v2_tex_2(B_94,'#skF_3')
      | ~ v4_pre_topc(C_95,'#skF_3')
      | ~ v4_pre_topc(B_94,'#skF_3')
      | ~ m1_subset_1(C_95,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(splitRight,[status(thm)],[c_1126])).

tff(c_1311,plain,
    ( v2_tex_2(k2_xboole_0('#skF_4','#skF_5'),'#skF_3')
    | ~ v2_tex_2('#skF_5','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ v4_pre_topc('#skF_5','#skF_3')
    | ~ v4_pre_topc('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_1275])).

tff(c_1344,plain,(
    v2_tex_2(k2_xboole_0('#skF_4','#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_26,c_24,c_22,c_1311])).

tff(c_1346,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_125,c_1344])).

tff(c_1349,plain,(
    ! [B_96,C_97] :
      ( v2_tex_2(k4_subset_1(u1_struct_0('#skF_3'),B_96,C_97),'#skF_3')
      | ~ v2_tex_2(C_97,'#skF_3')
      | ~ v2_tex_2(B_96,'#skF_3')
      | ~ v4_pre_topc(C_97,'#skF_3')
      | ~ v4_pre_topc(B_96,'#skF_3')
      | ~ m1_subset_1(C_97,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(splitRight,[status(thm)],[c_550])).

tff(c_1382,plain,
    ( v2_tex_2(k2_xboole_0('#skF_4','#skF_5'),'#skF_3')
    | ~ v2_tex_2('#skF_5','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ v4_pre_topc('#skF_5','#skF_3')
    | ~ v4_pre_topc('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_1349])).

tff(c_1413,plain,(
    v2_tex_2(k2_xboole_0('#skF_4','#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_26,c_24,c_22,c_1382])).

tff(c_1415,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_125,c_1413])).

%------------------------------------------------------------------------------
