%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:05 EST 2020

% Result     : Theorem 3.74s
% Output     : CNFRefutation 3.85s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 125 expanded)
%              Number of leaves         :   30 (  60 expanded)
%              Depth                    :   10
%              Number of atoms          :  168 ( 402 expanded)
%              Number of equality atoms :   29 (  33 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > v1_tops_1 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_104,negated_conjecture,(
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

tff(f_68,axiom,(
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

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_31,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_33,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_50,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = u1_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_3)).

tff(f_87,axiom,(
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

tff(c_38,plain,(
    ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_46,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_40,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_222,plain,(
    ! [A_66,B_67] :
      ( '#skF_1'(A_66,B_67) != B_67
      | v3_tex_2(B_67,A_66)
      | ~ v2_tex_2(B_67,A_66)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ l1_pre_topc(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_229,plain,
    ( '#skF_1'('#skF_3','#skF_4') != '#skF_4'
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_222])).

tff(c_237,plain,
    ( '#skF_1'('#skF_3','#skF_4') != '#skF_4'
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_40,c_229])).

tff(c_238,plain,(
    '#skF_1'('#skF_3','#skF_4') != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_237])).

tff(c_270,plain,(
    ! [A_73,B_74] :
      ( v2_tex_2('#skF_1'(A_73,B_74),A_73)
      | v3_tex_2(B_74,A_73)
      | ~ v2_tex_2(B_74,A_73)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ l1_pre_topc(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_275,plain,
    ( v2_tex_2('#skF_1'('#skF_3','#skF_4'),'#skF_3')
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_270])).

tff(c_282,plain,
    ( v2_tex_2('#skF_1'('#skF_3','#skF_4'),'#skF_3')
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_40,c_275])).

tff(c_283,plain,(
    v2_tex_2('#skF_1'('#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_282])).

tff(c_287,plain,(
    ! [B_78,A_79] :
      ( r1_tarski(B_78,'#skF_1'(A_79,B_78))
      | v3_tex_2(B_78,A_79)
      | ~ v2_tex_2(B_78,A_79)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ l1_pre_topc(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_292,plain,
    ( r1_tarski('#skF_4','#skF_1'('#skF_3','#skF_4'))
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_287])).

tff(c_299,plain,
    ( r1_tarski('#skF_4','#skF_1'('#skF_3','#skF_4'))
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_40,c_292])).

tff(c_300,plain,(
    r1_tarski('#skF_4','#skF_1'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_299])).

tff(c_424,plain,(
    ! [A_90,B_91] :
      ( m1_subset_1('#skF_1'(A_90,B_91),k1_zfmisc_1(u1_struct_0(A_90)))
      | v3_tex_2(B_91,A_90)
      | ~ v2_tex_2(B_91,A_90)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(u1_struct_0(A_90)))
      | ~ l1_pre_topc(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(A_8,B_9)
      | ~ m1_subset_1(A_8,k1_zfmisc_1(B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_457,plain,(
    ! [A_92,B_93] :
      ( r1_tarski('#skF_1'(A_92,B_93),u1_struct_0(A_92))
      | v3_tex_2(B_93,A_92)
      | ~ v2_tex_2(B_93,A_92)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ l1_pre_topc(A_92) ) ),
    inference(resolution,[status(thm)],[c_424,c_10])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_606,plain,(
    ! [A_105,B_106] :
      ( k3_xboole_0('#skF_1'(A_105,B_106),u1_struct_0(A_105)) = '#skF_1'(A_105,B_106)
      | v3_tex_2(B_106,A_105)
      | ~ v2_tex_2(B_106,A_105)
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ l1_pre_topc(A_105) ) ),
    inference(resolution,[status(thm)],[c_457,c_2])).

tff(c_615,plain,
    ( k3_xboole_0('#skF_1'('#skF_3','#skF_4'),u1_struct_0('#skF_3')) = '#skF_1'('#skF_3','#skF_4')
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_606])).

tff(c_624,plain,
    ( k3_xboole_0('#skF_1'('#skF_3','#skF_4'),u1_struct_0('#skF_3')) = '#skF_1'('#skF_3','#skF_4')
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_40,c_615])).

tff(c_625,plain,(
    k3_xboole_0('#skF_1'('#skF_3','#skF_4'),u1_struct_0('#skF_3')) = '#skF_1'('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_624])).

tff(c_24,plain,(
    ! [A_13,B_19] :
      ( m1_subset_1('#skF_1'(A_13,B_19),k1_zfmisc_1(u1_struct_0(A_13)))
      | v3_tex_2(B_19,A_13)
      | ~ v2_tex_2(B_19,A_13)
      | ~ m1_subset_1(B_19,k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_48,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_4,plain,(
    ! [A_3] : k2_subset_1(A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,(
    ! [A_4] : m1_subset_1(k2_subset_1(A_4),k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_51,plain,(
    ! [A_4] : m1_subset_1(A_4,k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6])).

tff(c_95,plain,(
    ! [A_44,B_45,C_46] :
      ( k9_subset_1(A_44,B_45,C_46) = k3_xboole_0(B_45,C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(A_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_104,plain,(
    ! [A_4,B_45] : k9_subset_1(A_4,B_45,A_4) = k3_xboole_0(B_45,A_4) ),
    inference(resolution,[status(thm)],[c_51,c_95])).

tff(c_42,plain,(
    v1_tops_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_166,plain,(
    ! [A_58,B_59] :
      ( k2_pre_topc(A_58,B_59) = u1_struct_0(A_58)
      | ~ v1_tops_1(B_59,A_58)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ l1_pre_topc(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_173,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = u1_struct_0('#skF_3')
    | ~ v1_tops_1('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_166])).

tff(c_181,plain,(
    k2_pre_topc('#skF_3','#skF_4') = u1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_173])).

tff(c_798,plain,(
    ! [A_128,B_129,C_130] :
      ( k9_subset_1(u1_struct_0(A_128),B_129,k2_pre_topc(A_128,C_130)) = C_130
      | ~ r1_tarski(C_130,B_129)
      | ~ m1_subset_1(C_130,k1_zfmisc_1(u1_struct_0(A_128)))
      | ~ v2_tex_2(B_129,A_128)
      | ~ m1_subset_1(B_129,k1_zfmisc_1(u1_struct_0(A_128)))
      | ~ l1_pre_topc(A_128)
      | ~ v2_pre_topc(A_128)
      | v2_struct_0(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_807,plain,(
    ! [B_129] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_129,k2_pre_topc('#skF_3','#skF_4')) = '#skF_4'
      | ~ r1_tarski('#skF_4',B_129)
      | ~ v2_tex_2(B_129,'#skF_3')
      | ~ m1_subset_1(B_129,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_44,c_798])).

tff(c_816,plain,(
    ! [B_129] :
      ( k3_xboole_0(B_129,u1_struct_0('#skF_3')) = '#skF_4'
      | ~ r1_tarski('#skF_4',B_129)
      | ~ v2_tex_2(B_129,'#skF_3')
      | ~ m1_subset_1(B_129,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_104,c_181,c_807])).

tff(c_819,plain,(
    ! [B_131] :
      ( k3_xboole_0(B_131,u1_struct_0('#skF_3')) = '#skF_4'
      | ~ r1_tarski('#skF_4',B_131)
      | ~ v2_tex_2(B_131,'#skF_3')
      | ~ m1_subset_1(B_131,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_816])).

tff(c_827,plain,(
    ! [B_19] :
      ( k3_xboole_0('#skF_1'('#skF_3',B_19),u1_struct_0('#skF_3')) = '#skF_4'
      | ~ r1_tarski('#skF_4','#skF_1'('#skF_3',B_19))
      | ~ v2_tex_2('#skF_1'('#skF_3',B_19),'#skF_3')
      | v3_tex_2(B_19,'#skF_3')
      | ~ v2_tex_2(B_19,'#skF_3')
      | ~ m1_subset_1(B_19,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_24,c_819])).

tff(c_1200,plain,(
    ! [B_168] :
      ( k3_xboole_0('#skF_1'('#skF_3',B_168),u1_struct_0('#skF_3')) = '#skF_4'
      | ~ r1_tarski('#skF_4','#skF_1'('#skF_3',B_168))
      | ~ v2_tex_2('#skF_1'('#skF_3',B_168),'#skF_3')
      | v3_tex_2(B_168,'#skF_3')
      | ~ v2_tex_2(B_168,'#skF_3')
      | ~ m1_subset_1(B_168,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_827])).

tff(c_1215,plain,
    ( k3_xboole_0('#skF_1'('#skF_3','#skF_4'),u1_struct_0('#skF_3')) = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_1'('#skF_3','#skF_4'))
    | ~ v2_tex_2('#skF_1'('#skF_3','#skF_4'),'#skF_3')
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_1200])).

tff(c_1230,plain,
    ( '#skF_1'('#skF_3','#skF_4') = '#skF_4'
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_283,c_300,c_625,c_1215])).

tff(c_1232,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_238,c_1230])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:57:39 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.74/1.67  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.74/1.68  
% 3.74/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.74/1.68  %$ v3_tex_2 > v2_tex_2 > v1_tops_1 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.74/1.68  
% 3.74/1.68  %Foreground sorts:
% 3.74/1.68  
% 3.74/1.68  
% 3.74/1.68  %Background operators:
% 3.74/1.68  
% 3.74/1.68  
% 3.74/1.68  %Foreground operators:
% 3.74/1.68  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.74/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.74/1.68  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.74/1.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.74/1.68  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 3.74/1.68  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 3.74/1.68  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.74/1.68  tff('#skF_3', type, '#skF_3': $i).
% 3.74/1.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.74/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.74/1.68  tff('#skF_4', type, '#skF_4': $i).
% 3.74/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.74/1.68  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.74/1.68  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.74/1.68  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.74/1.68  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.74/1.68  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.74/1.68  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.74/1.68  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.74/1.68  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.74/1.68  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.74/1.68  
% 3.85/1.70  tff(f_104, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v1_tops_1(B, A) & v2_tex_2(B, A)) => v3_tex_2(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tex_2)).
% 3.85/1.70  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 3.85/1.70  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.85/1.70  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.85/1.70  tff(f_31, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 3.85/1.70  tff(f_33, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.85/1.70  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 3.85/1.70  tff(f_50, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tops_3)).
% 3.85/1.70  tff(f_87, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C)) = C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_tex_2)).
% 3.85/1.70  tff(c_38, plain, (~v3_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.85/1.70  tff(c_46, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.85/1.70  tff(c_40, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.85/1.70  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.85/1.70  tff(c_222, plain, (![A_66, B_67]: ('#skF_1'(A_66, B_67)!=B_67 | v3_tex_2(B_67, A_66) | ~v2_tex_2(B_67, A_66) | ~m1_subset_1(B_67, k1_zfmisc_1(u1_struct_0(A_66))) | ~l1_pre_topc(A_66))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.85/1.70  tff(c_229, plain, ('#skF_1'('#skF_3', '#skF_4')!='#skF_4' | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_44, c_222])).
% 3.85/1.70  tff(c_237, plain, ('#skF_1'('#skF_3', '#skF_4')!='#skF_4' | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_40, c_229])).
% 3.85/1.70  tff(c_238, plain, ('#skF_1'('#skF_3', '#skF_4')!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_38, c_237])).
% 3.85/1.70  tff(c_270, plain, (![A_73, B_74]: (v2_tex_2('#skF_1'(A_73, B_74), A_73) | v3_tex_2(B_74, A_73) | ~v2_tex_2(B_74, A_73) | ~m1_subset_1(B_74, k1_zfmisc_1(u1_struct_0(A_73))) | ~l1_pre_topc(A_73))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.85/1.70  tff(c_275, plain, (v2_tex_2('#skF_1'('#skF_3', '#skF_4'), '#skF_3') | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_44, c_270])).
% 3.85/1.70  tff(c_282, plain, (v2_tex_2('#skF_1'('#skF_3', '#skF_4'), '#skF_3') | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_40, c_275])).
% 3.85/1.70  tff(c_283, plain, (v2_tex_2('#skF_1'('#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_38, c_282])).
% 3.85/1.70  tff(c_287, plain, (![B_78, A_79]: (r1_tarski(B_78, '#skF_1'(A_79, B_78)) | v3_tex_2(B_78, A_79) | ~v2_tex_2(B_78, A_79) | ~m1_subset_1(B_78, k1_zfmisc_1(u1_struct_0(A_79))) | ~l1_pre_topc(A_79))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.85/1.70  tff(c_292, plain, (r1_tarski('#skF_4', '#skF_1'('#skF_3', '#skF_4')) | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_44, c_287])).
% 3.85/1.70  tff(c_299, plain, (r1_tarski('#skF_4', '#skF_1'('#skF_3', '#skF_4')) | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_40, c_292])).
% 3.85/1.70  tff(c_300, plain, (r1_tarski('#skF_4', '#skF_1'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_38, c_299])).
% 3.85/1.70  tff(c_424, plain, (![A_90, B_91]: (m1_subset_1('#skF_1'(A_90, B_91), k1_zfmisc_1(u1_struct_0(A_90))) | v3_tex_2(B_91, A_90) | ~v2_tex_2(B_91, A_90) | ~m1_subset_1(B_91, k1_zfmisc_1(u1_struct_0(A_90))) | ~l1_pre_topc(A_90))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.85/1.70  tff(c_10, plain, (![A_8, B_9]: (r1_tarski(A_8, B_9) | ~m1_subset_1(A_8, k1_zfmisc_1(B_9)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.85/1.70  tff(c_457, plain, (![A_92, B_93]: (r1_tarski('#skF_1'(A_92, B_93), u1_struct_0(A_92)) | v3_tex_2(B_93, A_92) | ~v2_tex_2(B_93, A_92) | ~m1_subset_1(B_93, k1_zfmisc_1(u1_struct_0(A_92))) | ~l1_pre_topc(A_92))), inference(resolution, [status(thm)], [c_424, c_10])).
% 3.85/1.70  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.85/1.70  tff(c_606, plain, (![A_105, B_106]: (k3_xboole_0('#skF_1'(A_105, B_106), u1_struct_0(A_105))='#skF_1'(A_105, B_106) | v3_tex_2(B_106, A_105) | ~v2_tex_2(B_106, A_105) | ~m1_subset_1(B_106, k1_zfmisc_1(u1_struct_0(A_105))) | ~l1_pre_topc(A_105))), inference(resolution, [status(thm)], [c_457, c_2])).
% 3.85/1.70  tff(c_615, plain, (k3_xboole_0('#skF_1'('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))='#skF_1'('#skF_3', '#skF_4') | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_44, c_606])).
% 3.85/1.70  tff(c_624, plain, (k3_xboole_0('#skF_1'('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))='#skF_1'('#skF_3', '#skF_4') | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_40, c_615])).
% 3.85/1.70  tff(c_625, plain, (k3_xboole_0('#skF_1'('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))='#skF_1'('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_38, c_624])).
% 3.85/1.70  tff(c_24, plain, (![A_13, B_19]: (m1_subset_1('#skF_1'(A_13, B_19), k1_zfmisc_1(u1_struct_0(A_13))) | v3_tex_2(B_19, A_13) | ~v2_tex_2(B_19, A_13) | ~m1_subset_1(B_19, k1_zfmisc_1(u1_struct_0(A_13))) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.85/1.70  tff(c_50, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.85/1.70  tff(c_48, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.85/1.70  tff(c_4, plain, (![A_3]: (k2_subset_1(A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.85/1.70  tff(c_6, plain, (![A_4]: (m1_subset_1(k2_subset_1(A_4), k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.85/1.70  tff(c_51, plain, (![A_4]: (m1_subset_1(A_4, k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6])).
% 3.85/1.70  tff(c_95, plain, (![A_44, B_45, C_46]: (k9_subset_1(A_44, B_45, C_46)=k3_xboole_0(B_45, C_46) | ~m1_subset_1(C_46, k1_zfmisc_1(A_44)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.85/1.70  tff(c_104, plain, (![A_4, B_45]: (k9_subset_1(A_4, B_45, A_4)=k3_xboole_0(B_45, A_4))), inference(resolution, [status(thm)], [c_51, c_95])).
% 3.85/1.70  tff(c_42, plain, (v1_tops_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.85/1.70  tff(c_166, plain, (![A_58, B_59]: (k2_pre_topc(A_58, B_59)=u1_struct_0(A_58) | ~v1_tops_1(B_59, A_58) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(A_58))) | ~l1_pre_topc(A_58))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.85/1.70  tff(c_173, plain, (k2_pre_topc('#skF_3', '#skF_4')=u1_struct_0('#skF_3') | ~v1_tops_1('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_44, c_166])).
% 3.85/1.70  tff(c_181, plain, (k2_pre_topc('#skF_3', '#skF_4')=u1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_42, c_173])).
% 3.85/1.70  tff(c_798, plain, (![A_128, B_129, C_130]: (k9_subset_1(u1_struct_0(A_128), B_129, k2_pre_topc(A_128, C_130))=C_130 | ~r1_tarski(C_130, B_129) | ~m1_subset_1(C_130, k1_zfmisc_1(u1_struct_0(A_128))) | ~v2_tex_2(B_129, A_128) | ~m1_subset_1(B_129, k1_zfmisc_1(u1_struct_0(A_128))) | ~l1_pre_topc(A_128) | ~v2_pre_topc(A_128) | v2_struct_0(A_128))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.85/1.70  tff(c_807, plain, (![B_129]: (k9_subset_1(u1_struct_0('#skF_3'), B_129, k2_pre_topc('#skF_3', '#skF_4'))='#skF_4' | ~r1_tarski('#skF_4', B_129) | ~v2_tex_2(B_129, '#skF_3') | ~m1_subset_1(B_129, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_44, c_798])).
% 3.85/1.70  tff(c_816, plain, (![B_129]: (k3_xboole_0(B_129, u1_struct_0('#skF_3'))='#skF_4' | ~r1_tarski('#skF_4', B_129) | ~v2_tex_2(B_129, '#skF_3') | ~m1_subset_1(B_129, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_104, c_181, c_807])).
% 3.85/1.70  tff(c_819, plain, (![B_131]: (k3_xboole_0(B_131, u1_struct_0('#skF_3'))='#skF_4' | ~r1_tarski('#skF_4', B_131) | ~v2_tex_2(B_131, '#skF_3') | ~m1_subset_1(B_131, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_816])).
% 3.85/1.70  tff(c_827, plain, (![B_19]: (k3_xboole_0('#skF_1'('#skF_3', B_19), u1_struct_0('#skF_3'))='#skF_4' | ~r1_tarski('#skF_4', '#skF_1'('#skF_3', B_19)) | ~v2_tex_2('#skF_1'('#skF_3', B_19), '#skF_3') | v3_tex_2(B_19, '#skF_3') | ~v2_tex_2(B_19, '#skF_3') | ~m1_subset_1(B_19, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_24, c_819])).
% 3.85/1.70  tff(c_1200, plain, (![B_168]: (k3_xboole_0('#skF_1'('#skF_3', B_168), u1_struct_0('#skF_3'))='#skF_4' | ~r1_tarski('#skF_4', '#skF_1'('#skF_3', B_168)) | ~v2_tex_2('#skF_1'('#skF_3', B_168), '#skF_3') | v3_tex_2(B_168, '#skF_3') | ~v2_tex_2(B_168, '#skF_3') | ~m1_subset_1(B_168, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_827])).
% 3.85/1.70  tff(c_1215, plain, (k3_xboole_0('#skF_1'('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))='#skF_4' | ~r1_tarski('#skF_4', '#skF_1'('#skF_3', '#skF_4')) | ~v2_tex_2('#skF_1'('#skF_3', '#skF_4'), '#skF_3') | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_1200])).
% 3.85/1.70  tff(c_1230, plain, ('#skF_1'('#skF_3', '#skF_4')='#skF_4' | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_283, c_300, c_625, c_1215])).
% 3.85/1.70  tff(c_1232, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_238, c_1230])).
% 3.85/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.85/1.70  
% 3.85/1.70  Inference rules
% 3.85/1.70  ----------------------
% 3.85/1.70  #Ref     : 0
% 3.85/1.70  #Sup     : 245
% 3.85/1.70  #Fact    : 0
% 3.85/1.70  #Define  : 0
% 3.85/1.70  #Split   : 4
% 3.85/1.70  #Chain   : 0
% 3.85/1.70  #Close   : 0
% 3.85/1.70  
% 3.85/1.70  Ordering : KBO
% 3.85/1.70  
% 3.85/1.70  Simplification rules
% 3.85/1.70  ----------------------
% 3.85/1.70  #Subsume      : 37
% 3.85/1.70  #Demod        : 135
% 3.85/1.70  #Tautology    : 83
% 3.85/1.70  #SimpNegUnit  : 35
% 3.85/1.70  #BackRed      : 0
% 3.85/1.70  
% 3.85/1.70  #Partial instantiations: 0
% 3.85/1.70  #Strategies tried      : 1
% 3.85/1.70  
% 3.85/1.70  Timing (in seconds)
% 3.85/1.70  ----------------------
% 3.85/1.70  Preprocessing        : 0.34
% 3.85/1.70  Parsing              : 0.18
% 3.85/1.70  CNF conversion       : 0.02
% 3.85/1.70  Main loop            : 0.53
% 3.85/1.70  Inferencing          : 0.20
% 3.85/1.70  Reduction            : 0.16
% 3.85/1.70  Demodulation         : 0.11
% 3.85/1.70  BG Simplification    : 0.03
% 3.85/1.70  Subsumption          : 0.12
% 3.85/1.70  Abstraction          : 0.03
% 3.85/1.70  MUC search           : 0.00
% 3.85/1.70  Cooper               : 0.00
% 3.85/1.70  Total                : 0.91
% 3.85/1.70  Index Insertion      : 0.00
% 3.85/1.70  Index Deletion       : 0.00
% 3.85/1.70  Index Matching       : 0.00
% 3.85/1.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
