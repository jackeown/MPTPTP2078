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
% DateTime   : Thu Dec  3 10:30:04 EST 2020

% Result     : Theorem 3.96s
% Output     : CNFRefutation 3.96s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 173 expanded)
%              Number of leaves         :   25 (  77 expanded)
%              Depth                    :   21
%              Number of atoms          :  244 ( 685 expanded)
%              Number of equality atoms :   29 (  40 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > v1_tops_1 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_108,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( ( v1_tops_1(B,A)
                & v2_tex_2(B,A) )
             => v3_tex_2(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tex_2)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tex_2(B,A)
          <=> ( v2_tex_2(B,A)
              & ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( v2_tex_2(C,A)
                      & r1_tarski(B,C) )
                   => B = C ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_45,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v1_tops_1(B,A)
                  & r1_tarski(B,C) )
               => v1_tops_1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_tops_1)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = u1_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_3)).

tff(f_91,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( r1_tarski(C,B)
                 => k9_subset_1(u1_struct_0(A),B,k2_pre_topc(A,C)) = C ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_tex_2)).

tff(c_34,plain,(
    ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_36,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_42,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_101,plain,(
    ! [A_47,B_48] :
      ( v2_tex_2('#skF_1'(A_47,B_48),A_47)
      | v3_tex_2(B_48,A_47)
      | ~ v2_tex_2(B_48,A_47)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ l1_pre_topc(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_103,plain,
    ( v2_tex_2('#skF_1'('#skF_3','#skF_4'),'#skF_3')
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_101])).

tff(c_106,plain,
    ( v2_tex_2('#skF_1'('#skF_3','#skF_4'),'#skF_3')
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_36,c_103])).

tff(c_107,plain,(
    v2_tex_2('#skF_1'('#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_106])).

tff(c_89,plain,(
    ! [B_45,A_46] :
      ( r1_tarski(B_45,'#skF_1'(A_46,B_45))
      | v3_tex_2(B_45,A_46)
      | ~ v2_tex_2(B_45,A_46)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(u1_struct_0(A_46)))
      | ~ l1_pre_topc(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_91,plain,
    ( r1_tarski('#skF_4','#skF_1'('#skF_3','#skF_4'))
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_89])).

tff(c_94,plain,
    ( r1_tarski('#skF_4','#skF_1'('#skF_3','#skF_4'))
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_36,c_91])).

tff(c_95,plain,(
    r1_tarski('#skF_4','#skF_1'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_94])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_81,plain,(
    ! [A_43,B_44] :
      ( '#skF_1'(A_43,B_44) != B_44
      | v3_tex_2(B_44,A_43)
      | ~ v2_tex_2(B_44,A_43)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ l1_pre_topc(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_84,plain,
    ( '#skF_1'('#skF_3','#skF_4') != '#skF_4'
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_81])).

tff(c_87,plain,
    ( '#skF_1'('#skF_3','#skF_4') != '#skF_4'
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_36,c_84])).

tff(c_88,plain,(
    '#skF_1'('#skF_3','#skF_4') != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_87])).

tff(c_20,plain,(
    ! [A_13,B_19] :
      ( m1_subset_1('#skF_1'(A_13,B_19),k1_zfmisc_1(u1_struct_0(A_13)))
      | v3_tex_2(B_19,A_13)
      | ~ v2_tex_2(B_19,A_13)
      | ~ m1_subset_1(B_19,k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_44,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_38,plain,(
    v1_tops_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_167,plain,(
    ! [C_55,A_56,B_57] :
      ( v1_tops_1(C_55,A_56)
      | ~ r1_tarski(B_57,C_55)
      | ~ v1_tops_1(B_57,A_56)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ l1_pre_topc(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_174,plain,(
    ! [A_58] :
      ( v1_tops_1('#skF_1'('#skF_3','#skF_4'),A_58)
      | ~ v1_tops_1('#skF_4',A_58)
      | ~ m1_subset_1('#skF_1'('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ l1_pre_topc(A_58) ) ),
    inference(resolution,[status(thm)],[c_95,c_167])).

tff(c_178,plain,
    ( v1_tops_1('#skF_1'('#skF_3','#skF_4'),'#skF_3')
    | ~ v1_tops_1('#skF_4','#skF_3')
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_174])).

tff(c_181,plain,
    ( v1_tops_1('#skF_1'('#skF_3','#skF_4'),'#skF_3')
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_36,c_38,c_178])).

tff(c_182,plain,(
    v1_tops_1('#skF_1'('#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_181])).

tff(c_115,plain,(
    ! [A_51,B_52] :
      ( m1_subset_1('#skF_1'(A_51,B_52),k1_zfmisc_1(u1_struct_0(A_51)))
      | v3_tex_2(B_52,A_51)
      | ~ v2_tex_2(B_52,A_51)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ l1_pre_topc(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_12,plain,(
    ! [A_10,B_12] :
      ( k2_pre_topc(A_10,B_12) = u1_struct_0(A_10)
      | ~ v1_tops_1(B_12,A_10)
      | ~ m1_subset_1(B_12,k1_zfmisc_1(u1_struct_0(A_10)))
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_217,plain,(
    ! [A_69,B_70] :
      ( k2_pre_topc(A_69,'#skF_1'(A_69,B_70)) = u1_struct_0(A_69)
      | ~ v1_tops_1('#skF_1'(A_69,B_70),A_69)
      | v3_tex_2(B_70,A_69)
      | ~ v2_tex_2(B_70,A_69)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ l1_pre_topc(A_69) ) ),
    inference(resolution,[status(thm)],[c_115,c_12])).

tff(c_219,plain,
    ( k2_pre_topc('#skF_3','#skF_1'('#skF_3','#skF_4')) = u1_struct_0('#skF_3')
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_182,c_217])).

tff(c_222,plain,
    ( k2_pre_topc('#skF_3','#skF_1'('#skF_3','#skF_4')) = u1_struct_0('#skF_3')
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_36,c_219])).

tff(c_223,plain,(
    k2_pre_topc('#skF_3','#skF_1'('#skF_3','#skF_4')) = u1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_222])).

tff(c_242,plain,(
    ! [A_75,B_76,C_77] :
      ( k9_subset_1(u1_struct_0(A_75),B_76,k2_pre_topc(A_75,C_77)) = C_77
      | ~ r1_tarski(C_77,B_76)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ v2_tex_2(B_76,A_75)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ l1_pre_topc(A_75)
      | ~ v2_pre_topc(A_75)
      | v2_struct_0(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_386,plain,(
    ! [A_108,B_109,B_110] :
      ( k9_subset_1(u1_struct_0(A_108),B_109,k2_pre_topc(A_108,'#skF_1'(A_108,B_110))) = '#skF_1'(A_108,B_110)
      | ~ r1_tarski('#skF_1'(A_108,B_110),B_109)
      | ~ v2_tex_2(B_109,A_108)
      | ~ m1_subset_1(B_109,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ v2_pre_topc(A_108)
      | v2_struct_0(A_108)
      | v3_tex_2(B_110,A_108)
      | ~ v2_tex_2(B_110,A_108)
      | ~ m1_subset_1(B_110,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ l1_pre_topc(A_108) ) ),
    inference(resolution,[status(thm)],[c_20,c_242])).

tff(c_395,plain,(
    ! [B_109] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_109,u1_struct_0('#skF_3')) = '#skF_1'('#skF_3','#skF_4')
      | ~ r1_tarski('#skF_1'('#skF_3','#skF_4'),B_109)
      | ~ v2_tex_2(B_109,'#skF_3')
      | ~ m1_subset_1(B_109,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | v3_tex_2('#skF_4','#skF_3')
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_223,c_386])).

tff(c_399,plain,(
    ! [B_109] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_109,u1_struct_0('#skF_3')) = '#skF_1'('#skF_3','#skF_4')
      | ~ r1_tarski('#skF_1'('#skF_3','#skF_4'),B_109)
      | ~ v2_tex_2(B_109,'#skF_3')
      | ~ m1_subset_1(B_109,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3')
      | v3_tex_2('#skF_4','#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_36,c_44,c_395])).

tff(c_401,plain,(
    ! [B_111] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_111,u1_struct_0('#skF_3')) = '#skF_1'('#skF_3','#skF_4')
      | ~ r1_tarski('#skF_1'('#skF_3','#skF_4'),B_111)
      | ~ v2_tex_2(B_111,'#skF_3')
      | ~ m1_subset_1(B_111,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_46,c_399])).

tff(c_409,plain,(
    ! [B_19] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3',B_19),u1_struct_0('#skF_3')) = '#skF_1'('#skF_3','#skF_4')
      | ~ r1_tarski('#skF_1'('#skF_3','#skF_4'),'#skF_1'('#skF_3',B_19))
      | ~ v2_tex_2('#skF_1'('#skF_3',B_19),'#skF_3')
      | v3_tex_2(B_19,'#skF_3')
      | ~ v2_tex_2(B_19,'#skF_3')
      | ~ m1_subset_1(B_19,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_20,c_401])).

tff(c_441,plain,(
    ! [B_113] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3',B_113),u1_struct_0('#skF_3')) = '#skF_1'('#skF_3','#skF_4')
      | ~ r1_tarski('#skF_1'('#skF_3','#skF_4'),'#skF_1'('#skF_3',B_113))
      | ~ v2_tex_2('#skF_1'('#skF_3',B_113),'#skF_3')
      | v3_tex_2(B_113,'#skF_3')
      | ~ v2_tex_2(B_113,'#skF_3')
      | ~ m1_subset_1(B_113,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_409])).

tff(c_63,plain,(
    ! [A_39,B_40] :
      ( k2_pre_topc(A_39,B_40) = u1_struct_0(A_39)
      | ~ v1_tops_1(B_40,A_39)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(u1_struct_0(A_39)))
      | ~ l1_pre_topc(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_66,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = u1_struct_0('#skF_3')
    | ~ v1_tops_1('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_63])).

tff(c_69,plain,(
    k2_pre_topc('#skF_3','#skF_4') = u1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_66])).

tff(c_248,plain,(
    ! [B_76] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_76,k2_pre_topc('#skF_3','#skF_4')) = '#skF_4'
      | ~ r1_tarski('#skF_4',B_76)
      | ~ v2_tex_2(B_76,'#skF_3')
      | ~ m1_subset_1(B_76,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_40,c_242])).

tff(c_253,plain,(
    ! [B_76] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_76,u1_struct_0('#skF_3')) = '#skF_4'
      | ~ r1_tarski('#skF_4',B_76)
      | ~ v2_tex_2(B_76,'#skF_3')
      | ~ m1_subset_1(B_76,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_69,c_248])).

tff(c_255,plain,(
    ! [B_78] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_78,u1_struct_0('#skF_3')) = '#skF_4'
      | ~ r1_tarski('#skF_4',B_78)
      | ~ v2_tex_2(B_78,'#skF_3')
      | ~ m1_subset_1(B_78,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_253])).

tff(c_263,plain,(
    ! [B_19] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3',B_19),u1_struct_0('#skF_3')) = '#skF_4'
      | ~ r1_tarski('#skF_4','#skF_1'('#skF_3',B_19))
      | ~ v2_tex_2('#skF_1'('#skF_3',B_19),'#skF_3')
      | v3_tex_2(B_19,'#skF_3')
      | ~ v2_tex_2(B_19,'#skF_3')
      | ~ m1_subset_1(B_19,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_20,c_255])).

tff(c_273,plain,(
    ! [B_19] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3',B_19),u1_struct_0('#skF_3')) = '#skF_4'
      | ~ r1_tarski('#skF_4','#skF_1'('#skF_3',B_19))
      | ~ v2_tex_2('#skF_1'('#skF_3',B_19),'#skF_3')
      | v3_tex_2(B_19,'#skF_3')
      | ~ v2_tex_2(B_19,'#skF_3')
      | ~ m1_subset_1(B_19,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_263])).

tff(c_447,plain,(
    ! [B_113] :
      ( '#skF_1'('#skF_3','#skF_4') = '#skF_4'
      | ~ r1_tarski('#skF_4','#skF_1'('#skF_3',B_113))
      | ~ v2_tex_2('#skF_1'('#skF_3',B_113),'#skF_3')
      | v3_tex_2(B_113,'#skF_3')
      | ~ v2_tex_2(B_113,'#skF_3')
      | ~ m1_subset_1(B_113,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski('#skF_1'('#skF_3','#skF_4'),'#skF_1'('#skF_3',B_113))
      | ~ v2_tex_2('#skF_1'('#skF_3',B_113),'#skF_3')
      | v3_tex_2(B_113,'#skF_3')
      | ~ v2_tex_2(B_113,'#skF_3')
      | ~ m1_subset_1(B_113,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_441,c_273])).

tff(c_460,plain,(
    ! [B_117] :
      ( ~ r1_tarski('#skF_4','#skF_1'('#skF_3',B_117))
      | ~ v2_tex_2('#skF_1'('#skF_3',B_117),'#skF_3')
      | v3_tex_2(B_117,'#skF_3')
      | ~ v2_tex_2(B_117,'#skF_3')
      | ~ m1_subset_1(B_117,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski('#skF_1'('#skF_3','#skF_4'),'#skF_1'('#skF_3',B_117))
      | ~ v2_tex_2('#skF_1'('#skF_3',B_117),'#skF_3')
      | v3_tex_2(B_117,'#skF_3')
      | ~ v2_tex_2(B_117,'#skF_3')
      | ~ m1_subset_1(B_117,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_447])).

tff(c_468,plain,
    ( ~ r1_tarski('#skF_4','#skF_1'('#skF_3','#skF_4'))
    | ~ v2_tex_2('#skF_1'('#skF_3','#skF_4'),'#skF_3')
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_6,c_460])).

tff(c_475,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_107,c_95,c_468])).

tff(c_477,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_475])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:34:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.96/2.02  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.96/2.03  
% 3.96/2.03  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.96/2.03  %$ v3_tex_2 > v2_tex_2 > v1_tops_1 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.96/2.03  
% 3.96/2.03  %Foreground sorts:
% 3.96/2.03  
% 3.96/2.03  
% 3.96/2.03  %Background operators:
% 3.96/2.03  
% 3.96/2.03  
% 3.96/2.03  %Foreground operators:
% 3.96/2.03  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.96/2.03  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.96/2.03  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.96/2.03  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.96/2.03  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 3.96/2.03  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 3.96/2.03  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.96/2.03  tff('#skF_3', type, '#skF_3': $i).
% 3.96/2.03  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.96/2.03  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.96/2.03  tff('#skF_4', type, '#skF_4': $i).
% 3.96/2.03  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.96/2.03  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.96/2.03  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.96/2.03  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.96/2.03  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.96/2.03  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.96/2.03  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.96/2.03  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.96/2.03  
% 3.96/2.06  tff(f_108, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v1_tops_1(B, A) & v2_tex_2(B, A)) => v3_tex_2(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tex_2)).
% 3.96/2.06  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 3.96/2.06  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.96/2.06  tff(f_45, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v1_tops_1(B, A) & r1_tarski(B, C)) => v1_tops_1(C, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_tops_1)).
% 3.96/2.06  tff(f_54, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tops_3)).
% 3.96/2.06  tff(f_91, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C)) = C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_tex_2)).
% 3.96/2.06  tff(c_34, plain, (~v3_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.96/2.06  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.96/2.06  tff(c_36, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.96/2.06  tff(c_42, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.96/2.06  tff(c_101, plain, (![A_47, B_48]: (v2_tex_2('#skF_1'(A_47, B_48), A_47) | v3_tex_2(B_48, A_47) | ~v2_tex_2(B_48, A_47) | ~m1_subset_1(B_48, k1_zfmisc_1(u1_struct_0(A_47))) | ~l1_pre_topc(A_47))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.96/2.06  tff(c_103, plain, (v2_tex_2('#skF_1'('#skF_3', '#skF_4'), '#skF_3') | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_40, c_101])).
% 3.96/2.06  tff(c_106, plain, (v2_tex_2('#skF_1'('#skF_3', '#skF_4'), '#skF_3') | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_36, c_103])).
% 3.96/2.06  tff(c_107, plain, (v2_tex_2('#skF_1'('#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_34, c_106])).
% 3.96/2.06  tff(c_89, plain, (![B_45, A_46]: (r1_tarski(B_45, '#skF_1'(A_46, B_45)) | v3_tex_2(B_45, A_46) | ~v2_tex_2(B_45, A_46) | ~m1_subset_1(B_45, k1_zfmisc_1(u1_struct_0(A_46))) | ~l1_pre_topc(A_46))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.96/2.06  tff(c_91, plain, (r1_tarski('#skF_4', '#skF_1'('#skF_3', '#skF_4')) | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_40, c_89])).
% 3.96/2.06  tff(c_94, plain, (r1_tarski('#skF_4', '#skF_1'('#skF_3', '#skF_4')) | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_36, c_91])).
% 3.96/2.06  tff(c_95, plain, (r1_tarski('#skF_4', '#skF_1'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_34, c_94])).
% 3.96/2.06  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.96/2.06  tff(c_81, plain, (![A_43, B_44]: ('#skF_1'(A_43, B_44)!=B_44 | v3_tex_2(B_44, A_43) | ~v2_tex_2(B_44, A_43) | ~m1_subset_1(B_44, k1_zfmisc_1(u1_struct_0(A_43))) | ~l1_pre_topc(A_43))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.96/2.06  tff(c_84, plain, ('#skF_1'('#skF_3', '#skF_4')!='#skF_4' | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_40, c_81])).
% 3.96/2.06  tff(c_87, plain, ('#skF_1'('#skF_3', '#skF_4')!='#skF_4' | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_36, c_84])).
% 3.96/2.06  tff(c_88, plain, ('#skF_1'('#skF_3', '#skF_4')!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_34, c_87])).
% 3.96/2.06  tff(c_20, plain, (![A_13, B_19]: (m1_subset_1('#skF_1'(A_13, B_19), k1_zfmisc_1(u1_struct_0(A_13))) | v3_tex_2(B_19, A_13) | ~v2_tex_2(B_19, A_13) | ~m1_subset_1(B_19, k1_zfmisc_1(u1_struct_0(A_13))) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.96/2.06  tff(c_46, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.96/2.06  tff(c_44, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.96/2.06  tff(c_38, plain, (v1_tops_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.96/2.06  tff(c_167, plain, (![C_55, A_56, B_57]: (v1_tops_1(C_55, A_56) | ~r1_tarski(B_57, C_55) | ~v1_tops_1(B_57, A_56) | ~m1_subset_1(C_55, k1_zfmisc_1(u1_struct_0(A_56))) | ~m1_subset_1(B_57, k1_zfmisc_1(u1_struct_0(A_56))) | ~l1_pre_topc(A_56))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.96/2.06  tff(c_174, plain, (![A_58]: (v1_tops_1('#skF_1'('#skF_3', '#skF_4'), A_58) | ~v1_tops_1('#skF_4', A_58) | ~m1_subset_1('#skF_1'('#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0(A_58))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_58))) | ~l1_pre_topc(A_58))), inference(resolution, [status(thm)], [c_95, c_167])).
% 3.96/2.06  tff(c_178, plain, (v1_tops_1('#skF_1'('#skF_3', '#skF_4'), '#skF_3') | ~v1_tops_1('#skF_4', '#skF_3') | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_20, c_174])).
% 3.96/2.06  tff(c_181, plain, (v1_tops_1('#skF_1'('#skF_3', '#skF_4'), '#skF_3') | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_36, c_38, c_178])).
% 3.96/2.06  tff(c_182, plain, (v1_tops_1('#skF_1'('#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_34, c_181])).
% 3.96/2.06  tff(c_115, plain, (![A_51, B_52]: (m1_subset_1('#skF_1'(A_51, B_52), k1_zfmisc_1(u1_struct_0(A_51))) | v3_tex_2(B_52, A_51) | ~v2_tex_2(B_52, A_51) | ~m1_subset_1(B_52, k1_zfmisc_1(u1_struct_0(A_51))) | ~l1_pre_topc(A_51))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.96/2.06  tff(c_12, plain, (![A_10, B_12]: (k2_pre_topc(A_10, B_12)=u1_struct_0(A_10) | ~v1_tops_1(B_12, A_10) | ~m1_subset_1(B_12, k1_zfmisc_1(u1_struct_0(A_10))) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.96/2.06  tff(c_217, plain, (![A_69, B_70]: (k2_pre_topc(A_69, '#skF_1'(A_69, B_70))=u1_struct_0(A_69) | ~v1_tops_1('#skF_1'(A_69, B_70), A_69) | v3_tex_2(B_70, A_69) | ~v2_tex_2(B_70, A_69) | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0(A_69))) | ~l1_pre_topc(A_69))), inference(resolution, [status(thm)], [c_115, c_12])).
% 3.96/2.06  tff(c_219, plain, (k2_pre_topc('#skF_3', '#skF_1'('#skF_3', '#skF_4'))=u1_struct_0('#skF_3') | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_182, c_217])).
% 3.96/2.06  tff(c_222, plain, (k2_pre_topc('#skF_3', '#skF_1'('#skF_3', '#skF_4'))=u1_struct_0('#skF_3') | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_36, c_219])).
% 3.96/2.06  tff(c_223, plain, (k2_pre_topc('#skF_3', '#skF_1'('#skF_3', '#skF_4'))=u1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_34, c_222])).
% 3.96/2.06  tff(c_242, plain, (![A_75, B_76, C_77]: (k9_subset_1(u1_struct_0(A_75), B_76, k2_pre_topc(A_75, C_77))=C_77 | ~r1_tarski(C_77, B_76) | ~m1_subset_1(C_77, k1_zfmisc_1(u1_struct_0(A_75))) | ~v2_tex_2(B_76, A_75) | ~m1_subset_1(B_76, k1_zfmisc_1(u1_struct_0(A_75))) | ~l1_pre_topc(A_75) | ~v2_pre_topc(A_75) | v2_struct_0(A_75))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.96/2.06  tff(c_386, plain, (![A_108, B_109, B_110]: (k9_subset_1(u1_struct_0(A_108), B_109, k2_pre_topc(A_108, '#skF_1'(A_108, B_110)))='#skF_1'(A_108, B_110) | ~r1_tarski('#skF_1'(A_108, B_110), B_109) | ~v2_tex_2(B_109, A_108) | ~m1_subset_1(B_109, k1_zfmisc_1(u1_struct_0(A_108))) | ~v2_pre_topc(A_108) | v2_struct_0(A_108) | v3_tex_2(B_110, A_108) | ~v2_tex_2(B_110, A_108) | ~m1_subset_1(B_110, k1_zfmisc_1(u1_struct_0(A_108))) | ~l1_pre_topc(A_108))), inference(resolution, [status(thm)], [c_20, c_242])).
% 3.96/2.06  tff(c_395, plain, (![B_109]: (k9_subset_1(u1_struct_0('#skF_3'), B_109, u1_struct_0('#skF_3'))='#skF_1'('#skF_3', '#skF_4') | ~r1_tarski('#skF_1'('#skF_3', '#skF_4'), B_109) | ~v2_tex_2(B_109, '#skF_3') | ~m1_subset_1(B_109, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_223, c_386])).
% 3.96/2.06  tff(c_399, plain, (![B_109]: (k9_subset_1(u1_struct_0('#skF_3'), B_109, u1_struct_0('#skF_3'))='#skF_1'('#skF_3', '#skF_4') | ~r1_tarski('#skF_1'('#skF_3', '#skF_4'), B_109) | ~v2_tex_2(B_109, '#skF_3') | ~m1_subset_1(B_109, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3') | v3_tex_2('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_36, c_44, c_395])).
% 3.96/2.06  tff(c_401, plain, (![B_111]: (k9_subset_1(u1_struct_0('#skF_3'), B_111, u1_struct_0('#skF_3'))='#skF_1'('#skF_3', '#skF_4') | ~r1_tarski('#skF_1'('#skF_3', '#skF_4'), B_111) | ~v2_tex_2(B_111, '#skF_3') | ~m1_subset_1(B_111, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_34, c_46, c_399])).
% 3.96/2.06  tff(c_409, plain, (![B_19]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_3', B_19), u1_struct_0('#skF_3'))='#skF_1'('#skF_3', '#skF_4') | ~r1_tarski('#skF_1'('#skF_3', '#skF_4'), '#skF_1'('#skF_3', B_19)) | ~v2_tex_2('#skF_1'('#skF_3', B_19), '#skF_3') | v3_tex_2(B_19, '#skF_3') | ~v2_tex_2(B_19, '#skF_3') | ~m1_subset_1(B_19, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_20, c_401])).
% 3.96/2.06  tff(c_441, plain, (![B_113]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_3', B_113), u1_struct_0('#skF_3'))='#skF_1'('#skF_3', '#skF_4') | ~r1_tarski('#skF_1'('#skF_3', '#skF_4'), '#skF_1'('#skF_3', B_113)) | ~v2_tex_2('#skF_1'('#skF_3', B_113), '#skF_3') | v3_tex_2(B_113, '#skF_3') | ~v2_tex_2(B_113, '#skF_3') | ~m1_subset_1(B_113, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_409])).
% 3.96/2.06  tff(c_63, plain, (![A_39, B_40]: (k2_pre_topc(A_39, B_40)=u1_struct_0(A_39) | ~v1_tops_1(B_40, A_39) | ~m1_subset_1(B_40, k1_zfmisc_1(u1_struct_0(A_39))) | ~l1_pre_topc(A_39))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.96/2.06  tff(c_66, plain, (k2_pre_topc('#skF_3', '#skF_4')=u1_struct_0('#skF_3') | ~v1_tops_1('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_40, c_63])).
% 3.96/2.06  tff(c_69, plain, (k2_pre_topc('#skF_3', '#skF_4')=u1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_66])).
% 3.96/2.06  tff(c_248, plain, (![B_76]: (k9_subset_1(u1_struct_0('#skF_3'), B_76, k2_pre_topc('#skF_3', '#skF_4'))='#skF_4' | ~r1_tarski('#skF_4', B_76) | ~v2_tex_2(B_76, '#skF_3') | ~m1_subset_1(B_76, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_40, c_242])).
% 3.96/2.06  tff(c_253, plain, (![B_76]: (k9_subset_1(u1_struct_0('#skF_3'), B_76, u1_struct_0('#skF_3'))='#skF_4' | ~r1_tarski('#skF_4', B_76) | ~v2_tex_2(B_76, '#skF_3') | ~m1_subset_1(B_76, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_69, c_248])).
% 3.96/2.06  tff(c_255, plain, (![B_78]: (k9_subset_1(u1_struct_0('#skF_3'), B_78, u1_struct_0('#skF_3'))='#skF_4' | ~r1_tarski('#skF_4', B_78) | ~v2_tex_2(B_78, '#skF_3') | ~m1_subset_1(B_78, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_46, c_253])).
% 3.96/2.06  tff(c_263, plain, (![B_19]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_3', B_19), u1_struct_0('#skF_3'))='#skF_4' | ~r1_tarski('#skF_4', '#skF_1'('#skF_3', B_19)) | ~v2_tex_2('#skF_1'('#skF_3', B_19), '#skF_3') | v3_tex_2(B_19, '#skF_3') | ~v2_tex_2(B_19, '#skF_3') | ~m1_subset_1(B_19, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_20, c_255])).
% 3.96/2.06  tff(c_273, plain, (![B_19]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_3', B_19), u1_struct_0('#skF_3'))='#skF_4' | ~r1_tarski('#skF_4', '#skF_1'('#skF_3', B_19)) | ~v2_tex_2('#skF_1'('#skF_3', B_19), '#skF_3') | v3_tex_2(B_19, '#skF_3') | ~v2_tex_2(B_19, '#skF_3') | ~m1_subset_1(B_19, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_263])).
% 3.96/2.06  tff(c_447, plain, (![B_113]: ('#skF_1'('#skF_3', '#skF_4')='#skF_4' | ~r1_tarski('#skF_4', '#skF_1'('#skF_3', B_113)) | ~v2_tex_2('#skF_1'('#skF_3', B_113), '#skF_3') | v3_tex_2(B_113, '#skF_3') | ~v2_tex_2(B_113, '#skF_3') | ~m1_subset_1(B_113, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r1_tarski('#skF_1'('#skF_3', '#skF_4'), '#skF_1'('#skF_3', B_113)) | ~v2_tex_2('#skF_1'('#skF_3', B_113), '#skF_3') | v3_tex_2(B_113, '#skF_3') | ~v2_tex_2(B_113, '#skF_3') | ~m1_subset_1(B_113, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_441, c_273])).
% 3.96/2.06  tff(c_460, plain, (![B_117]: (~r1_tarski('#skF_4', '#skF_1'('#skF_3', B_117)) | ~v2_tex_2('#skF_1'('#skF_3', B_117), '#skF_3') | v3_tex_2(B_117, '#skF_3') | ~v2_tex_2(B_117, '#skF_3') | ~m1_subset_1(B_117, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r1_tarski('#skF_1'('#skF_3', '#skF_4'), '#skF_1'('#skF_3', B_117)) | ~v2_tex_2('#skF_1'('#skF_3', B_117), '#skF_3') | v3_tex_2(B_117, '#skF_3') | ~v2_tex_2(B_117, '#skF_3') | ~m1_subset_1(B_117, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_88, c_447])).
% 3.96/2.06  tff(c_468, plain, (~r1_tarski('#skF_4', '#skF_1'('#skF_3', '#skF_4')) | ~v2_tex_2('#skF_1'('#skF_3', '#skF_4'), '#skF_3') | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_6, c_460])).
% 3.96/2.06  tff(c_475, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_107, c_95, c_468])).
% 3.96/2.06  tff(c_477, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_475])).
% 3.96/2.06  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.96/2.06  
% 3.96/2.06  Inference rules
% 3.96/2.06  ----------------------
% 3.96/2.06  #Ref     : 0
% 3.96/2.06  #Sup     : 89
% 3.96/2.06  #Fact    : 0
% 3.96/2.06  #Define  : 0
% 3.96/2.06  #Split   : 1
% 3.96/2.06  #Chain   : 0
% 3.96/2.06  #Close   : 0
% 3.96/2.06  
% 3.96/2.06  Ordering : KBO
% 3.96/2.06  
% 3.96/2.06  Simplification rules
% 3.96/2.06  ----------------------
% 3.96/2.06  #Subsume      : 8
% 3.96/2.06  #Demod        : 66
% 3.96/2.06  #Tautology    : 31
% 3.96/2.06  #SimpNegUnit  : 24
% 3.96/2.06  #BackRed      : 0
% 3.96/2.06  
% 3.96/2.06  #Partial instantiations: 0
% 3.96/2.06  #Strategies tried      : 1
% 3.96/2.06  
% 3.96/2.06  Timing (in seconds)
% 3.96/2.06  ----------------------
% 3.96/2.07  Preprocessing        : 0.51
% 3.96/2.07  Parsing              : 0.25
% 3.96/2.07  CNF conversion       : 0.04
% 3.96/2.07  Main loop            : 0.62
% 3.96/2.07  Inferencing          : 0.23
% 3.96/2.07  Reduction            : 0.18
% 3.96/2.07  Demodulation         : 0.12
% 3.96/2.07  BG Simplification    : 0.03
% 3.96/2.07  Subsumption          : 0.15
% 3.96/2.07  Abstraction          : 0.03
% 3.96/2.07  MUC search           : 0.00
% 3.96/2.07  Cooper               : 0.00
% 3.96/2.07  Total                : 1.20
% 3.96/2.07  Index Insertion      : 0.00
% 3.96/2.07  Index Deletion       : 0.00
% 3.96/2.07  Index Matching       : 0.00
% 3.96/2.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
