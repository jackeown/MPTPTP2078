%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:04 EST 2020

% Result     : Theorem 4.35s
% Output     : CNFRefutation 4.59s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 174 expanded)
%              Number of leaves         :   26 (  78 expanded)
%              Depth                    :   21
%              Number of atoms          :  244 ( 685 expanded)
%              Number of equality atoms :   29 (  40 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > v1_tops_1 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

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

tff(f_54,axiom,(
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

tff(f_40,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

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

tff(c_89,plain,(
    ! [A_45,B_46] :
      ( v2_tex_2('#skF_1'(A_45,B_46),A_45)
      | v3_tex_2(B_46,A_45)
      | ~ v2_tex_2(B_46,A_45)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ l1_pre_topc(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_91,plain,
    ( v2_tex_2('#skF_1'('#skF_3','#skF_4'),'#skF_3')
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_89])).

tff(c_94,plain,
    ( v2_tex_2('#skF_1'('#skF_3','#skF_4'),'#skF_3')
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_36,c_91])).

tff(c_95,plain,(
    v2_tex_2('#skF_1'('#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_94])).

tff(c_96,plain,(
    ! [B_47,A_48] :
      ( r1_tarski(B_47,'#skF_1'(A_48,B_47))
      | v3_tex_2(B_47,A_48)
      | ~ v2_tex_2(B_47,A_48)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ l1_pre_topc(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_98,plain,
    ( r1_tarski('#skF_4','#skF_1'('#skF_3','#skF_4'))
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_96])).

tff(c_101,plain,
    ( r1_tarski('#skF_4','#skF_1'('#skF_3','#skF_4'))
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_36,c_98])).

tff(c_102,plain,(
    r1_tarski('#skF_4','#skF_1'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_101])).

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

tff(c_141,plain,(
    ! [C_53,A_54,B_55] :
      ( v1_tops_1(C_53,A_54)
      | ~ r1_tarski(B_55,C_53)
      | ~ v1_tops_1(B_55,A_54)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ m1_subset_1(B_55,k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ l1_pre_topc(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_174,plain,(
    ! [A_58] :
      ( v1_tops_1('#skF_1'('#skF_3','#skF_4'),A_58)
      | ~ v1_tops_1('#skF_4',A_58)
      | ~ m1_subset_1('#skF_1'('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ l1_pre_topc(A_58) ) ),
    inference(resolution,[status(thm)],[c_102,c_141])).

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

tff(c_10,plain,(
    ! [A_3,B_5] :
      ( k2_pre_topc(A_3,B_5) = k2_struct_0(A_3)
      | ~ v1_tops_1(B_5,A_3)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(u1_struct_0(A_3)))
      | ~ l1_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_204,plain,(
    ! [A_67,B_68] :
      ( k2_pre_topc(A_67,'#skF_1'(A_67,B_68)) = k2_struct_0(A_67)
      | ~ v1_tops_1('#skF_1'(A_67,B_68),A_67)
      | v3_tex_2(B_68,A_67)
      | ~ v2_tex_2(B_68,A_67)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ l1_pre_topc(A_67) ) ),
    inference(resolution,[status(thm)],[c_115,c_10])).

tff(c_206,plain,
    ( k2_pre_topc('#skF_3','#skF_1'('#skF_3','#skF_4')) = k2_struct_0('#skF_3')
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_182,c_204])).

tff(c_209,plain,
    ( k2_pre_topc('#skF_3','#skF_1'('#skF_3','#skF_4')) = k2_struct_0('#skF_3')
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_36,c_206])).

tff(c_210,plain,(
    k2_pre_topc('#skF_3','#skF_1'('#skF_3','#skF_4')) = k2_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_209])).

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
      ( k9_subset_1(u1_struct_0('#skF_3'),B_109,k2_struct_0('#skF_3')) = '#skF_1'('#skF_3','#skF_4')
      | ~ r1_tarski('#skF_1'('#skF_3','#skF_4'),B_109)
      | ~ v2_tex_2(B_109,'#skF_3')
      | ~ m1_subset_1(B_109,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | v3_tex_2('#skF_4','#skF_3')
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_210,c_386])).

tff(c_399,plain,(
    ! [B_109] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_109,k2_struct_0('#skF_3')) = '#skF_1'('#skF_3','#skF_4')
      | ~ r1_tarski('#skF_1'('#skF_3','#skF_4'),B_109)
      | ~ v2_tex_2(B_109,'#skF_3')
      | ~ m1_subset_1(B_109,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3')
      | v3_tex_2('#skF_4','#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_36,c_44,c_395])).

tff(c_401,plain,(
    ! [B_111] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_111,k2_struct_0('#skF_3')) = '#skF_1'('#skF_3','#skF_4')
      | ~ r1_tarski('#skF_1'('#skF_3','#skF_4'),B_111)
      | ~ v2_tex_2(B_111,'#skF_3')
      | ~ m1_subset_1(B_111,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_46,c_399])).

tff(c_409,plain,(
    ! [B_19] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3',B_19),k2_struct_0('#skF_3')) = '#skF_1'('#skF_3','#skF_4')
      | ~ r1_tarski('#skF_1'('#skF_3','#skF_4'),'#skF_1'('#skF_3',B_19))
      | ~ v2_tex_2('#skF_1'('#skF_3',B_19),'#skF_3')
      | v3_tex_2(B_19,'#skF_3')
      | ~ v2_tex_2(B_19,'#skF_3')
      | ~ m1_subset_1(B_19,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_20,c_401])).

tff(c_441,plain,(
    ! [B_113] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3',B_113),k2_struct_0('#skF_3')) = '#skF_1'('#skF_3','#skF_4')
      | ~ r1_tarski('#skF_1'('#skF_3','#skF_4'),'#skF_1'('#skF_3',B_113))
      | ~ v2_tex_2('#skF_1'('#skF_3',B_113),'#skF_3')
      | v3_tex_2(B_113,'#skF_3')
      | ~ v2_tex_2(B_113,'#skF_3')
      | ~ m1_subset_1(B_113,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_409])).

tff(c_70,plain,(
    ! [A_41,B_42] :
      ( k2_pre_topc(A_41,B_42) = k2_struct_0(A_41)
      | ~ v1_tops_1(B_42,A_41)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(u1_struct_0(A_41)))
      | ~ l1_pre_topc(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_73,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = k2_struct_0('#skF_3')
    | ~ v1_tops_1('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_70])).

tff(c_76,plain,(
    k2_pre_topc('#skF_3','#skF_4') = k2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_73])).

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
      ( k9_subset_1(u1_struct_0('#skF_3'),B_76,k2_struct_0('#skF_3')) = '#skF_4'
      | ~ r1_tarski('#skF_4',B_76)
      | ~ v2_tex_2(B_76,'#skF_3')
      | ~ m1_subset_1(B_76,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_76,c_248])).

tff(c_255,plain,(
    ! [B_78] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_78,k2_struct_0('#skF_3')) = '#skF_4'
      | ~ r1_tarski('#skF_4',B_78)
      | ~ v2_tex_2(B_78,'#skF_3')
      | ~ m1_subset_1(B_78,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_253])).

tff(c_263,plain,(
    ! [B_19] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3',B_19),k2_struct_0('#skF_3')) = '#skF_4'
      | ~ r1_tarski('#skF_4','#skF_1'('#skF_3',B_19))
      | ~ v2_tex_2('#skF_1'('#skF_3',B_19),'#skF_3')
      | v3_tex_2(B_19,'#skF_3')
      | ~ v2_tex_2(B_19,'#skF_3')
      | ~ m1_subset_1(B_19,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_20,c_255])).

tff(c_273,plain,(
    ! [B_19] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3',B_19),k2_struct_0('#skF_3')) = '#skF_4'
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
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_95,c_102,c_468])).

tff(c_477,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_475])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:23:23 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.35/2.76  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.35/2.77  
% 4.35/2.77  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.35/2.78  %$ v3_tex_2 > v2_tex_2 > v1_tops_1 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 4.35/2.78  
% 4.35/2.78  %Foreground sorts:
% 4.35/2.78  
% 4.35/2.78  
% 4.35/2.78  %Background operators:
% 4.35/2.78  
% 4.35/2.78  
% 4.35/2.78  %Foreground operators:
% 4.35/2.78  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.35/2.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.35/2.78  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.35/2.78  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.35/2.78  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 4.35/2.78  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 4.35/2.78  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 4.35/2.78  tff('#skF_3', type, '#skF_3': $i).
% 4.35/2.78  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.35/2.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.35/2.78  tff('#skF_4', type, '#skF_4': $i).
% 4.35/2.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.35/2.78  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.35/2.78  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.35/2.78  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.35/2.78  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.35/2.78  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.35/2.78  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.35/2.78  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 4.35/2.78  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.35/2.78  
% 4.59/2.83  tff(f_108, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v1_tops_1(B, A) & v2_tex_2(B, A)) => v3_tex_2(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tex_2)).
% 4.59/2.83  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 4.59/2.83  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.59/2.83  tff(f_54, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v1_tops_1(B, A) & r1_tarski(B, C)) => v1_tops_1(C, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_tops_1)).
% 4.59/2.83  tff(f_40, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tops_1)).
% 4.59/2.83  tff(f_91, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C)) = C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_tex_2)).
% 4.59/2.83  tff(c_34, plain, (~v3_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.59/2.83  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.59/2.83  tff(c_36, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.59/2.83  tff(c_42, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.59/2.83  tff(c_89, plain, (![A_45, B_46]: (v2_tex_2('#skF_1'(A_45, B_46), A_45) | v3_tex_2(B_46, A_45) | ~v2_tex_2(B_46, A_45) | ~m1_subset_1(B_46, k1_zfmisc_1(u1_struct_0(A_45))) | ~l1_pre_topc(A_45))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.59/2.83  tff(c_91, plain, (v2_tex_2('#skF_1'('#skF_3', '#skF_4'), '#skF_3') | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_40, c_89])).
% 4.59/2.83  tff(c_94, plain, (v2_tex_2('#skF_1'('#skF_3', '#skF_4'), '#skF_3') | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_36, c_91])).
% 4.59/2.83  tff(c_95, plain, (v2_tex_2('#skF_1'('#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_34, c_94])).
% 4.59/2.83  tff(c_96, plain, (![B_47, A_48]: (r1_tarski(B_47, '#skF_1'(A_48, B_47)) | v3_tex_2(B_47, A_48) | ~v2_tex_2(B_47, A_48) | ~m1_subset_1(B_47, k1_zfmisc_1(u1_struct_0(A_48))) | ~l1_pre_topc(A_48))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.59/2.83  tff(c_98, plain, (r1_tarski('#skF_4', '#skF_1'('#skF_3', '#skF_4')) | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_40, c_96])).
% 4.59/2.83  tff(c_101, plain, (r1_tarski('#skF_4', '#skF_1'('#skF_3', '#skF_4')) | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_36, c_98])).
% 4.59/2.83  tff(c_102, plain, (r1_tarski('#skF_4', '#skF_1'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_34, c_101])).
% 4.59/2.83  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.59/2.83  tff(c_81, plain, (![A_43, B_44]: ('#skF_1'(A_43, B_44)!=B_44 | v3_tex_2(B_44, A_43) | ~v2_tex_2(B_44, A_43) | ~m1_subset_1(B_44, k1_zfmisc_1(u1_struct_0(A_43))) | ~l1_pre_topc(A_43))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.59/2.83  tff(c_84, plain, ('#skF_1'('#skF_3', '#skF_4')!='#skF_4' | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_40, c_81])).
% 4.59/2.83  tff(c_87, plain, ('#skF_1'('#skF_3', '#skF_4')!='#skF_4' | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_36, c_84])).
% 4.59/2.83  tff(c_88, plain, ('#skF_1'('#skF_3', '#skF_4')!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_34, c_87])).
% 4.59/2.83  tff(c_20, plain, (![A_13, B_19]: (m1_subset_1('#skF_1'(A_13, B_19), k1_zfmisc_1(u1_struct_0(A_13))) | v3_tex_2(B_19, A_13) | ~v2_tex_2(B_19, A_13) | ~m1_subset_1(B_19, k1_zfmisc_1(u1_struct_0(A_13))) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.59/2.83  tff(c_46, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.59/2.83  tff(c_44, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.59/2.83  tff(c_38, plain, (v1_tops_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.59/2.83  tff(c_141, plain, (![C_53, A_54, B_55]: (v1_tops_1(C_53, A_54) | ~r1_tarski(B_55, C_53) | ~v1_tops_1(B_55, A_54) | ~m1_subset_1(C_53, k1_zfmisc_1(u1_struct_0(A_54))) | ~m1_subset_1(B_55, k1_zfmisc_1(u1_struct_0(A_54))) | ~l1_pre_topc(A_54))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.59/2.83  tff(c_174, plain, (![A_58]: (v1_tops_1('#skF_1'('#skF_3', '#skF_4'), A_58) | ~v1_tops_1('#skF_4', A_58) | ~m1_subset_1('#skF_1'('#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0(A_58))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_58))) | ~l1_pre_topc(A_58))), inference(resolution, [status(thm)], [c_102, c_141])).
% 4.59/2.83  tff(c_178, plain, (v1_tops_1('#skF_1'('#skF_3', '#skF_4'), '#skF_3') | ~v1_tops_1('#skF_4', '#skF_3') | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_20, c_174])).
% 4.59/2.83  tff(c_181, plain, (v1_tops_1('#skF_1'('#skF_3', '#skF_4'), '#skF_3') | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_36, c_38, c_178])).
% 4.59/2.83  tff(c_182, plain, (v1_tops_1('#skF_1'('#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_34, c_181])).
% 4.59/2.83  tff(c_115, plain, (![A_51, B_52]: (m1_subset_1('#skF_1'(A_51, B_52), k1_zfmisc_1(u1_struct_0(A_51))) | v3_tex_2(B_52, A_51) | ~v2_tex_2(B_52, A_51) | ~m1_subset_1(B_52, k1_zfmisc_1(u1_struct_0(A_51))) | ~l1_pre_topc(A_51))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.59/2.83  tff(c_10, plain, (![A_3, B_5]: (k2_pre_topc(A_3, B_5)=k2_struct_0(A_3) | ~v1_tops_1(B_5, A_3) | ~m1_subset_1(B_5, k1_zfmisc_1(u1_struct_0(A_3))) | ~l1_pre_topc(A_3))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.59/2.83  tff(c_204, plain, (![A_67, B_68]: (k2_pre_topc(A_67, '#skF_1'(A_67, B_68))=k2_struct_0(A_67) | ~v1_tops_1('#skF_1'(A_67, B_68), A_67) | v3_tex_2(B_68, A_67) | ~v2_tex_2(B_68, A_67) | ~m1_subset_1(B_68, k1_zfmisc_1(u1_struct_0(A_67))) | ~l1_pre_topc(A_67))), inference(resolution, [status(thm)], [c_115, c_10])).
% 4.59/2.83  tff(c_206, plain, (k2_pre_topc('#skF_3', '#skF_1'('#skF_3', '#skF_4'))=k2_struct_0('#skF_3') | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_182, c_204])).
% 4.59/2.83  tff(c_209, plain, (k2_pre_topc('#skF_3', '#skF_1'('#skF_3', '#skF_4'))=k2_struct_0('#skF_3') | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_36, c_206])).
% 4.59/2.83  tff(c_210, plain, (k2_pre_topc('#skF_3', '#skF_1'('#skF_3', '#skF_4'))=k2_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_34, c_209])).
% 4.59/2.83  tff(c_242, plain, (![A_75, B_76, C_77]: (k9_subset_1(u1_struct_0(A_75), B_76, k2_pre_topc(A_75, C_77))=C_77 | ~r1_tarski(C_77, B_76) | ~m1_subset_1(C_77, k1_zfmisc_1(u1_struct_0(A_75))) | ~v2_tex_2(B_76, A_75) | ~m1_subset_1(B_76, k1_zfmisc_1(u1_struct_0(A_75))) | ~l1_pre_topc(A_75) | ~v2_pre_topc(A_75) | v2_struct_0(A_75))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.59/2.83  tff(c_386, plain, (![A_108, B_109, B_110]: (k9_subset_1(u1_struct_0(A_108), B_109, k2_pre_topc(A_108, '#skF_1'(A_108, B_110)))='#skF_1'(A_108, B_110) | ~r1_tarski('#skF_1'(A_108, B_110), B_109) | ~v2_tex_2(B_109, A_108) | ~m1_subset_1(B_109, k1_zfmisc_1(u1_struct_0(A_108))) | ~v2_pre_topc(A_108) | v2_struct_0(A_108) | v3_tex_2(B_110, A_108) | ~v2_tex_2(B_110, A_108) | ~m1_subset_1(B_110, k1_zfmisc_1(u1_struct_0(A_108))) | ~l1_pre_topc(A_108))), inference(resolution, [status(thm)], [c_20, c_242])).
% 4.59/2.83  tff(c_395, plain, (![B_109]: (k9_subset_1(u1_struct_0('#skF_3'), B_109, k2_struct_0('#skF_3'))='#skF_1'('#skF_3', '#skF_4') | ~r1_tarski('#skF_1'('#skF_3', '#skF_4'), B_109) | ~v2_tex_2(B_109, '#skF_3') | ~m1_subset_1(B_109, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_210, c_386])).
% 4.59/2.83  tff(c_399, plain, (![B_109]: (k9_subset_1(u1_struct_0('#skF_3'), B_109, k2_struct_0('#skF_3'))='#skF_1'('#skF_3', '#skF_4') | ~r1_tarski('#skF_1'('#skF_3', '#skF_4'), B_109) | ~v2_tex_2(B_109, '#skF_3') | ~m1_subset_1(B_109, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3') | v3_tex_2('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_36, c_44, c_395])).
% 4.59/2.83  tff(c_401, plain, (![B_111]: (k9_subset_1(u1_struct_0('#skF_3'), B_111, k2_struct_0('#skF_3'))='#skF_1'('#skF_3', '#skF_4') | ~r1_tarski('#skF_1'('#skF_3', '#skF_4'), B_111) | ~v2_tex_2(B_111, '#skF_3') | ~m1_subset_1(B_111, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_34, c_46, c_399])).
% 4.59/2.83  tff(c_409, plain, (![B_19]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_3', B_19), k2_struct_0('#skF_3'))='#skF_1'('#skF_3', '#skF_4') | ~r1_tarski('#skF_1'('#skF_3', '#skF_4'), '#skF_1'('#skF_3', B_19)) | ~v2_tex_2('#skF_1'('#skF_3', B_19), '#skF_3') | v3_tex_2(B_19, '#skF_3') | ~v2_tex_2(B_19, '#skF_3') | ~m1_subset_1(B_19, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_20, c_401])).
% 4.59/2.83  tff(c_441, plain, (![B_113]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_3', B_113), k2_struct_0('#skF_3'))='#skF_1'('#skF_3', '#skF_4') | ~r1_tarski('#skF_1'('#skF_3', '#skF_4'), '#skF_1'('#skF_3', B_113)) | ~v2_tex_2('#skF_1'('#skF_3', B_113), '#skF_3') | v3_tex_2(B_113, '#skF_3') | ~v2_tex_2(B_113, '#skF_3') | ~m1_subset_1(B_113, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_409])).
% 4.59/2.83  tff(c_70, plain, (![A_41, B_42]: (k2_pre_topc(A_41, B_42)=k2_struct_0(A_41) | ~v1_tops_1(B_42, A_41) | ~m1_subset_1(B_42, k1_zfmisc_1(u1_struct_0(A_41))) | ~l1_pre_topc(A_41))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.59/2.83  tff(c_73, plain, (k2_pre_topc('#skF_3', '#skF_4')=k2_struct_0('#skF_3') | ~v1_tops_1('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_40, c_70])).
% 4.59/2.83  tff(c_76, plain, (k2_pre_topc('#skF_3', '#skF_4')=k2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_73])).
% 4.59/2.83  tff(c_248, plain, (![B_76]: (k9_subset_1(u1_struct_0('#skF_3'), B_76, k2_pre_topc('#skF_3', '#skF_4'))='#skF_4' | ~r1_tarski('#skF_4', B_76) | ~v2_tex_2(B_76, '#skF_3') | ~m1_subset_1(B_76, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_40, c_242])).
% 4.59/2.83  tff(c_253, plain, (![B_76]: (k9_subset_1(u1_struct_0('#skF_3'), B_76, k2_struct_0('#skF_3'))='#skF_4' | ~r1_tarski('#skF_4', B_76) | ~v2_tex_2(B_76, '#skF_3') | ~m1_subset_1(B_76, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_76, c_248])).
% 4.59/2.83  tff(c_255, plain, (![B_78]: (k9_subset_1(u1_struct_0('#skF_3'), B_78, k2_struct_0('#skF_3'))='#skF_4' | ~r1_tarski('#skF_4', B_78) | ~v2_tex_2(B_78, '#skF_3') | ~m1_subset_1(B_78, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_46, c_253])).
% 4.59/2.83  tff(c_263, plain, (![B_19]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_3', B_19), k2_struct_0('#skF_3'))='#skF_4' | ~r1_tarski('#skF_4', '#skF_1'('#skF_3', B_19)) | ~v2_tex_2('#skF_1'('#skF_3', B_19), '#skF_3') | v3_tex_2(B_19, '#skF_3') | ~v2_tex_2(B_19, '#skF_3') | ~m1_subset_1(B_19, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_20, c_255])).
% 4.59/2.83  tff(c_273, plain, (![B_19]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_3', B_19), k2_struct_0('#skF_3'))='#skF_4' | ~r1_tarski('#skF_4', '#skF_1'('#skF_3', B_19)) | ~v2_tex_2('#skF_1'('#skF_3', B_19), '#skF_3') | v3_tex_2(B_19, '#skF_3') | ~v2_tex_2(B_19, '#skF_3') | ~m1_subset_1(B_19, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_263])).
% 4.59/2.83  tff(c_447, plain, (![B_113]: ('#skF_1'('#skF_3', '#skF_4')='#skF_4' | ~r1_tarski('#skF_4', '#skF_1'('#skF_3', B_113)) | ~v2_tex_2('#skF_1'('#skF_3', B_113), '#skF_3') | v3_tex_2(B_113, '#skF_3') | ~v2_tex_2(B_113, '#skF_3') | ~m1_subset_1(B_113, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r1_tarski('#skF_1'('#skF_3', '#skF_4'), '#skF_1'('#skF_3', B_113)) | ~v2_tex_2('#skF_1'('#skF_3', B_113), '#skF_3') | v3_tex_2(B_113, '#skF_3') | ~v2_tex_2(B_113, '#skF_3') | ~m1_subset_1(B_113, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_441, c_273])).
% 4.59/2.83  tff(c_460, plain, (![B_117]: (~r1_tarski('#skF_4', '#skF_1'('#skF_3', B_117)) | ~v2_tex_2('#skF_1'('#skF_3', B_117), '#skF_3') | v3_tex_2(B_117, '#skF_3') | ~v2_tex_2(B_117, '#skF_3') | ~m1_subset_1(B_117, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r1_tarski('#skF_1'('#skF_3', '#skF_4'), '#skF_1'('#skF_3', B_117)) | ~v2_tex_2('#skF_1'('#skF_3', B_117), '#skF_3') | v3_tex_2(B_117, '#skF_3') | ~v2_tex_2(B_117, '#skF_3') | ~m1_subset_1(B_117, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_88, c_447])).
% 4.59/2.83  tff(c_468, plain, (~r1_tarski('#skF_4', '#skF_1'('#skF_3', '#skF_4')) | ~v2_tex_2('#skF_1'('#skF_3', '#skF_4'), '#skF_3') | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_6, c_460])).
% 4.59/2.83  tff(c_475, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_95, c_102, c_468])).
% 4.59/2.83  tff(c_477, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_475])).
% 4.59/2.83  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.59/2.83  
% 4.59/2.83  Inference rules
% 4.59/2.83  ----------------------
% 4.59/2.83  #Ref     : 0
% 4.59/2.83  #Sup     : 89
% 4.59/2.83  #Fact    : 0
% 4.59/2.83  #Define  : 0
% 4.59/2.83  #Split   : 1
% 4.59/2.83  #Chain   : 0
% 4.59/2.83  #Close   : 0
% 4.59/2.83  
% 4.59/2.83  Ordering : KBO
% 4.59/2.83  
% 4.59/2.83  Simplification rules
% 4.59/2.83  ----------------------
% 4.59/2.83  #Subsume      : 8
% 4.59/2.83  #Demod        : 66
% 4.59/2.83  #Tautology    : 31
% 4.59/2.83  #SimpNegUnit  : 24
% 4.59/2.83  #BackRed      : 0
% 4.59/2.83  
% 4.59/2.83  #Partial instantiations: 0
% 4.59/2.83  #Strategies tried      : 1
% 4.59/2.83  
% 4.59/2.83  Timing (in seconds)
% 4.59/2.83  ----------------------
% 4.59/2.84  Preprocessing        : 0.70
% 4.59/2.84  Parsing              : 0.37
% 4.59/2.84  CNF conversion       : 0.07
% 4.59/2.84  Main loop            : 1.02
% 4.59/2.84  Inferencing          : 0.34
% 4.59/2.84  Reduction            : 0.33
% 4.59/2.84  Demodulation         : 0.24
% 4.59/2.84  BG Simplification    : 0.06
% 4.59/2.84  Subsumption          : 0.23
% 4.59/2.84  Abstraction          : 0.05
% 4.59/2.84  MUC search           : 0.00
% 4.59/2.84  Cooper               : 0.00
% 4.59/2.84  Total                : 1.81
% 4.59/2.84  Index Insertion      : 0.00
% 4.59/2.84  Index Deletion       : 0.00
% 4.59/2.84  Index Matching       : 0.00
% 4.59/2.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
