%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:04 EST 2020

% Result     : Theorem 3.41s
% Output     : CNFRefutation 3.70s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 124 expanded)
%              Number of leaves         :   28 (  59 expanded)
%              Depth                    :   10
%              Number of atoms          :  171 ( 407 expanded)
%              Number of equality atoms :   29 (  33 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > v1_tops_1 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_106,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( ( v1_tops_1(B,A)
                & v2_tex_2(B,A) )
             => v3_tex_2(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tex_2)).

tff(f_70,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = u1_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_3)).

tff(f_89,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tex_2)).

tff(c_40,plain,(
    ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_48,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_42,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_197,plain,(
    ! [A_65,B_66] :
      ( '#skF_1'(A_65,B_66) != B_66
      | v3_tex_2(B_66,A_65)
      | ~ v2_tex_2(B_66,A_65)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ l1_pre_topc(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_204,plain,
    ( '#skF_1'('#skF_3','#skF_4') != '#skF_4'
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_197])).

tff(c_208,plain,
    ( '#skF_1'('#skF_3','#skF_4') != '#skF_4'
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_42,c_204])).

tff(c_209,plain,(
    '#skF_1'('#skF_3','#skF_4') != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_208])).

tff(c_245,plain,(
    ! [A_73,B_74] :
      ( v2_tex_2('#skF_1'(A_73,B_74),A_73)
      | v3_tex_2(B_74,A_73)
      | ~ v2_tex_2(B_74,A_73)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ l1_pre_topc(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_250,plain,
    ( v2_tex_2('#skF_1'('#skF_3','#skF_4'),'#skF_3')
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_245])).

tff(c_254,plain,
    ( v2_tex_2('#skF_1'('#skF_3','#skF_4'),'#skF_3')
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_42,c_250])).

tff(c_255,plain,(
    v2_tex_2('#skF_1'('#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_254])).

tff(c_257,plain,(
    ! [B_77,A_78] :
      ( r1_tarski(B_77,'#skF_1'(A_78,B_77))
      | v3_tex_2(B_77,A_78)
      | ~ v2_tex_2(B_77,A_78)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ l1_pre_topc(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_262,plain,
    ( r1_tarski('#skF_4','#skF_1'('#skF_3','#skF_4'))
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_257])).

tff(c_266,plain,
    ( r1_tarski('#skF_4','#skF_1'('#skF_3','#skF_4'))
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_42,c_262])).

tff(c_267,plain,(
    r1_tarski('#skF_4','#skF_1'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_266])).

tff(c_370,plain,(
    ! [A_88,B_89] :
      ( m1_subset_1('#skF_1'(A_88,B_89),k1_zfmisc_1(u1_struct_0(A_88)))
      | v3_tex_2(B_89,A_88)
      | ~ v2_tex_2(B_89,A_88)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ l1_pre_topc(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(A_8,B_9)
      | ~ m1_subset_1(A_8,k1_zfmisc_1(B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_436,plain,(
    ! [A_92,B_93] :
      ( r1_tarski('#skF_1'(A_92,B_93),u1_struct_0(A_92))
      | v3_tex_2(B_93,A_92)
      | ~ v2_tex_2(B_93,A_92)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ l1_pre_topc(A_92) ) ),
    inference(resolution,[status(thm)],[c_370,c_12])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = A_3
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_526,plain,(
    ! [A_99,B_100] :
      ( k3_xboole_0('#skF_1'(A_99,B_100),u1_struct_0(A_99)) = '#skF_1'(A_99,B_100)
      | v3_tex_2(B_100,A_99)
      | ~ v2_tex_2(B_100,A_99)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ l1_pre_topc(A_99) ) ),
    inference(resolution,[status(thm)],[c_436,c_8])).

tff(c_535,plain,
    ( k3_xboole_0('#skF_1'('#skF_3','#skF_4'),u1_struct_0('#skF_3')) = '#skF_1'('#skF_3','#skF_4')
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_526])).

tff(c_541,plain,
    ( k3_xboole_0('#skF_1'('#skF_3','#skF_4'),u1_struct_0('#skF_3')) = '#skF_1'('#skF_3','#skF_4')
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_42,c_535])).

tff(c_542,plain,(
    k3_xboole_0('#skF_1'('#skF_3','#skF_4'),u1_struct_0('#skF_3')) = '#skF_1'('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_541])).

tff(c_26,plain,(
    ! [A_13,B_19] :
      ( m1_subset_1('#skF_1'(A_13,B_19),k1_zfmisc_1(u1_struct_0(A_13)))
      | v3_tex_2(B_19,A_13)
      | ~ v2_tex_2(B_19,A_13)
      | ~ m1_subset_1(B_19,k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_50,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_97,plain,(
    ! [A_44,B_45,C_46] :
      ( k9_subset_1(A_44,B_45,C_46) = k3_xboole_0(B_45,C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(A_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_126,plain,(
    ! [B_50,B_51,A_52] :
      ( k9_subset_1(B_50,B_51,A_52) = k3_xboole_0(B_51,A_52)
      | ~ r1_tarski(A_52,B_50) ) ),
    inference(resolution,[status(thm)],[c_14,c_97])).

tff(c_133,plain,(
    ! [B_2,B_51] : k9_subset_1(B_2,B_51,B_2) = k3_xboole_0(B_51,B_2) ),
    inference(resolution,[status(thm)],[c_6,c_126])).

tff(c_44,plain,(
    v1_tops_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_156,plain,(
    ! [A_58,B_59] :
      ( k2_pre_topc(A_58,B_59) = u1_struct_0(A_58)
      | ~ v1_tops_1(B_59,A_58)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ l1_pre_topc(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_163,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = u1_struct_0('#skF_3')
    | ~ v1_tops_1('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_156])).

tff(c_167,plain,(
    k2_pre_topc('#skF_3','#skF_4') = u1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_163])).

tff(c_687,plain,(
    ! [A_121,B_122,C_123] :
      ( k9_subset_1(u1_struct_0(A_121),B_122,k2_pre_topc(A_121,C_123)) = C_123
      | ~ r1_tarski(C_123,B_122)
      | ~ m1_subset_1(C_123,k1_zfmisc_1(u1_struct_0(A_121)))
      | ~ v2_tex_2(B_122,A_121)
      | ~ m1_subset_1(B_122,k1_zfmisc_1(u1_struct_0(A_121)))
      | ~ l1_pre_topc(A_121)
      | ~ v2_pre_topc(A_121)
      | v2_struct_0(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_696,plain,(
    ! [B_122] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_122,k2_pre_topc('#skF_3','#skF_4')) = '#skF_4'
      | ~ r1_tarski('#skF_4',B_122)
      | ~ v2_tex_2(B_122,'#skF_3')
      | ~ m1_subset_1(B_122,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_46,c_687])).

tff(c_702,plain,(
    ! [B_122] :
      ( k3_xboole_0(B_122,u1_struct_0('#skF_3')) = '#skF_4'
      | ~ r1_tarski('#skF_4',B_122)
      | ~ v2_tex_2(B_122,'#skF_3')
      | ~ m1_subset_1(B_122,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_133,c_167,c_696])).

tff(c_704,plain,(
    ! [B_124] :
      ( k3_xboole_0(B_124,u1_struct_0('#skF_3')) = '#skF_4'
      | ~ r1_tarski('#skF_4',B_124)
      | ~ v2_tex_2(B_124,'#skF_3')
      | ~ m1_subset_1(B_124,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_702])).

tff(c_712,plain,(
    ! [B_19] :
      ( k3_xboole_0('#skF_1'('#skF_3',B_19),u1_struct_0('#skF_3')) = '#skF_4'
      | ~ r1_tarski('#skF_4','#skF_1'('#skF_3',B_19))
      | ~ v2_tex_2('#skF_1'('#skF_3',B_19),'#skF_3')
      | v3_tex_2(B_19,'#skF_3')
      | ~ v2_tex_2(B_19,'#skF_3')
      | ~ m1_subset_1(B_19,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_26,c_704])).

tff(c_1056,plain,(
    ! [B_170] :
      ( k3_xboole_0('#skF_1'('#skF_3',B_170),u1_struct_0('#skF_3')) = '#skF_4'
      | ~ r1_tarski('#skF_4','#skF_1'('#skF_3',B_170))
      | ~ v2_tex_2('#skF_1'('#skF_3',B_170),'#skF_3')
      | v3_tex_2(B_170,'#skF_3')
      | ~ v2_tex_2(B_170,'#skF_3')
      | ~ m1_subset_1(B_170,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_712])).

tff(c_1071,plain,
    ( k3_xboole_0('#skF_1'('#skF_3','#skF_4'),u1_struct_0('#skF_3')) = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_1'('#skF_3','#skF_4'))
    | ~ v2_tex_2('#skF_1'('#skF_3','#skF_4'),'#skF_3')
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_1056])).

tff(c_1082,plain,
    ( '#skF_1'('#skF_3','#skF_4') = '#skF_4'
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_255,c_267,c_542,c_1071])).

tff(c_1084,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_209,c_1082])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:19:15 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.41/1.62  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.41/1.62  
% 3.41/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.70/1.62  %$ v3_tex_2 > v2_tex_2 > v1_tops_1 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.70/1.62  
% 3.70/1.62  %Foreground sorts:
% 3.70/1.62  
% 3.70/1.62  
% 3.70/1.62  %Background operators:
% 3.70/1.62  
% 3.70/1.62  
% 3.70/1.62  %Foreground operators:
% 3.70/1.62  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.70/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.70/1.62  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.70/1.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.70/1.62  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 3.70/1.62  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 3.70/1.62  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.70/1.62  tff('#skF_3', type, '#skF_3': $i).
% 3.70/1.62  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.70/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.70/1.62  tff('#skF_4', type, '#skF_4': $i).
% 3.70/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.70/1.62  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.70/1.62  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.70/1.62  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.70/1.62  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.70/1.62  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.70/1.62  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.70/1.62  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.70/1.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.70/1.62  
% 3.70/1.64  tff(f_106, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v1_tops_1(B, A) & v2_tex_2(B, A)) => v3_tex_2(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_tex_2)).
% 3.70/1.64  tff(f_70, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_tex_2)).
% 3.70/1.64  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.70/1.64  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.70/1.64  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.70/1.64  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 3.70/1.64  tff(f_52, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tops_3)).
% 3.70/1.64  tff(f_89, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C)) = C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_tex_2)).
% 3.70/1.64  tff(c_40, plain, (~v3_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.70/1.64  tff(c_48, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.70/1.64  tff(c_42, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.70/1.64  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.70/1.64  tff(c_197, plain, (![A_65, B_66]: ('#skF_1'(A_65, B_66)!=B_66 | v3_tex_2(B_66, A_65) | ~v2_tex_2(B_66, A_65) | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0(A_65))) | ~l1_pre_topc(A_65))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.70/1.64  tff(c_204, plain, ('#skF_1'('#skF_3', '#skF_4')!='#skF_4' | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_46, c_197])).
% 3.70/1.64  tff(c_208, plain, ('#skF_1'('#skF_3', '#skF_4')!='#skF_4' | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_42, c_204])).
% 3.70/1.64  tff(c_209, plain, ('#skF_1'('#skF_3', '#skF_4')!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_40, c_208])).
% 3.70/1.64  tff(c_245, plain, (![A_73, B_74]: (v2_tex_2('#skF_1'(A_73, B_74), A_73) | v3_tex_2(B_74, A_73) | ~v2_tex_2(B_74, A_73) | ~m1_subset_1(B_74, k1_zfmisc_1(u1_struct_0(A_73))) | ~l1_pre_topc(A_73))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.70/1.64  tff(c_250, plain, (v2_tex_2('#skF_1'('#skF_3', '#skF_4'), '#skF_3') | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_46, c_245])).
% 3.70/1.64  tff(c_254, plain, (v2_tex_2('#skF_1'('#skF_3', '#skF_4'), '#skF_3') | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_42, c_250])).
% 3.70/1.64  tff(c_255, plain, (v2_tex_2('#skF_1'('#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_40, c_254])).
% 3.70/1.64  tff(c_257, plain, (![B_77, A_78]: (r1_tarski(B_77, '#skF_1'(A_78, B_77)) | v3_tex_2(B_77, A_78) | ~v2_tex_2(B_77, A_78) | ~m1_subset_1(B_77, k1_zfmisc_1(u1_struct_0(A_78))) | ~l1_pre_topc(A_78))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.70/1.64  tff(c_262, plain, (r1_tarski('#skF_4', '#skF_1'('#skF_3', '#skF_4')) | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_46, c_257])).
% 3.70/1.64  tff(c_266, plain, (r1_tarski('#skF_4', '#skF_1'('#skF_3', '#skF_4')) | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_42, c_262])).
% 3.70/1.64  tff(c_267, plain, (r1_tarski('#skF_4', '#skF_1'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_40, c_266])).
% 3.70/1.64  tff(c_370, plain, (![A_88, B_89]: (m1_subset_1('#skF_1'(A_88, B_89), k1_zfmisc_1(u1_struct_0(A_88))) | v3_tex_2(B_89, A_88) | ~v2_tex_2(B_89, A_88) | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0(A_88))) | ~l1_pre_topc(A_88))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.70/1.64  tff(c_12, plain, (![A_8, B_9]: (r1_tarski(A_8, B_9) | ~m1_subset_1(A_8, k1_zfmisc_1(B_9)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.70/1.64  tff(c_436, plain, (![A_92, B_93]: (r1_tarski('#skF_1'(A_92, B_93), u1_struct_0(A_92)) | v3_tex_2(B_93, A_92) | ~v2_tex_2(B_93, A_92) | ~m1_subset_1(B_93, k1_zfmisc_1(u1_struct_0(A_92))) | ~l1_pre_topc(A_92))), inference(resolution, [status(thm)], [c_370, c_12])).
% 3.70/1.64  tff(c_8, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=A_3 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.70/1.64  tff(c_526, plain, (![A_99, B_100]: (k3_xboole_0('#skF_1'(A_99, B_100), u1_struct_0(A_99))='#skF_1'(A_99, B_100) | v3_tex_2(B_100, A_99) | ~v2_tex_2(B_100, A_99) | ~m1_subset_1(B_100, k1_zfmisc_1(u1_struct_0(A_99))) | ~l1_pre_topc(A_99))), inference(resolution, [status(thm)], [c_436, c_8])).
% 3.70/1.64  tff(c_535, plain, (k3_xboole_0('#skF_1'('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))='#skF_1'('#skF_3', '#skF_4') | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_46, c_526])).
% 3.70/1.64  tff(c_541, plain, (k3_xboole_0('#skF_1'('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))='#skF_1'('#skF_3', '#skF_4') | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_42, c_535])).
% 3.70/1.64  tff(c_542, plain, (k3_xboole_0('#skF_1'('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))='#skF_1'('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_40, c_541])).
% 3.70/1.64  tff(c_26, plain, (![A_13, B_19]: (m1_subset_1('#skF_1'(A_13, B_19), k1_zfmisc_1(u1_struct_0(A_13))) | v3_tex_2(B_19, A_13) | ~v2_tex_2(B_19, A_13) | ~m1_subset_1(B_19, k1_zfmisc_1(u1_struct_0(A_13))) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.70/1.64  tff(c_52, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.70/1.64  tff(c_50, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.70/1.64  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.70/1.64  tff(c_14, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.70/1.64  tff(c_97, plain, (![A_44, B_45, C_46]: (k9_subset_1(A_44, B_45, C_46)=k3_xboole_0(B_45, C_46) | ~m1_subset_1(C_46, k1_zfmisc_1(A_44)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.70/1.64  tff(c_126, plain, (![B_50, B_51, A_52]: (k9_subset_1(B_50, B_51, A_52)=k3_xboole_0(B_51, A_52) | ~r1_tarski(A_52, B_50))), inference(resolution, [status(thm)], [c_14, c_97])).
% 3.70/1.64  tff(c_133, plain, (![B_2, B_51]: (k9_subset_1(B_2, B_51, B_2)=k3_xboole_0(B_51, B_2))), inference(resolution, [status(thm)], [c_6, c_126])).
% 3.70/1.64  tff(c_44, plain, (v1_tops_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.70/1.64  tff(c_156, plain, (![A_58, B_59]: (k2_pre_topc(A_58, B_59)=u1_struct_0(A_58) | ~v1_tops_1(B_59, A_58) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(A_58))) | ~l1_pre_topc(A_58))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.70/1.64  tff(c_163, plain, (k2_pre_topc('#skF_3', '#skF_4')=u1_struct_0('#skF_3') | ~v1_tops_1('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_46, c_156])).
% 3.70/1.64  tff(c_167, plain, (k2_pre_topc('#skF_3', '#skF_4')=u1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_163])).
% 3.70/1.64  tff(c_687, plain, (![A_121, B_122, C_123]: (k9_subset_1(u1_struct_0(A_121), B_122, k2_pre_topc(A_121, C_123))=C_123 | ~r1_tarski(C_123, B_122) | ~m1_subset_1(C_123, k1_zfmisc_1(u1_struct_0(A_121))) | ~v2_tex_2(B_122, A_121) | ~m1_subset_1(B_122, k1_zfmisc_1(u1_struct_0(A_121))) | ~l1_pre_topc(A_121) | ~v2_pre_topc(A_121) | v2_struct_0(A_121))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.70/1.64  tff(c_696, plain, (![B_122]: (k9_subset_1(u1_struct_0('#skF_3'), B_122, k2_pre_topc('#skF_3', '#skF_4'))='#skF_4' | ~r1_tarski('#skF_4', B_122) | ~v2_tex_2(B_122, '#skF_3') | ~m1_subset_1(B_122, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_46, c_687])).
% 3.70/1.64  tff(c_702, plain, (![B_122]: (k3_xboole_0(B_122, u1_struct_0('#skF_3'))='#skF_4' | ~r1_tarski('#skF_4', B_122) | ~v2_tex_2(B_122, '#skF_3') | ~m1_subset_1(B_122, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_133, c_167, c_696])).
% 3.70/1.64  tff(c_704, plain, (![B_124]: (k3_xboole_0(B_124, u1_struct_0('#skF_3'))='#skF_4' | ~r1_tarski('#skF_4', B_124) | ~v2_tex_2(B_124, '#skF_3') | ~m1_subset_1(B_124, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_52, c_702])).
% 3.70/1.64  tff(c_712, plain, (![B_19]: (k3_xboole_0('#skF_1'('#skF_3', B_19), u1_struct_0('#skF_3'))='#skF_4' | ~r1_tarski('#skF_4', '#skF_1'('#skF_3', B_19)) | ~v2_tex_2('#skF_1'('#skF_3', B_19), '#skF_3') | v3_tex_2(B_19, '#skF_3') | ~v2_tex_2(B_19, '#skF_3') | ~m1_subset_1(B_19, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_26, c_704])).
% 3.70/1.64  tff(c_1056, plain, (![B_170]: (k3_xboole_0('#skF_1'('#skF_3', B_170), u1_struct_0('#skF_3'))='#skF_4' | ~r1_tarski('#skF_4', '#skF_1'('#skF_3', B_170)) | ~v2_tex_2('#skF_1'('#skF_3', B_170), '#skF_3') | v3_tex_2(B_170, '#skF_3') | ~v2_tex_2(B_170, '#skF_3') | ~m1_subset_1(B_170, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_712])).
% 3.70/1.64  tff(c_1071, plain, (k3_xboole_0('#skF_1'('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))='#skF_4' | ~r1_tarski('#skF_4', '#skF_1'('#skF_3', '#skF_4')) | ~v2_tex_2('#skF_1'('#skF_3', '#skF_4'), '#skF_3') | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_1056])).
% 3.70/1.64  tff(c_1082, plain, ('#skF_1'('#skF_3', '#skF_4')='#skF_4' | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_255, c_267, c_542, c_1071])).
% 3.70/1.64  tff(c_1084, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_209, c_1082])).
% 3.70/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.70/1.64  
% 3.70/1.64  Inference rules
% 3.70/1.64  ----------------------
% 3.70/1.64  #Ref     : 0
% 3.70/1.64  #Sup     : 215
% 3.70/1.64  #Fact    : 0
% 3.70/1.64  #Define  : 0
% 3.70/1.64  #Split   : 5
% 3.70/1.64  #Chain   : 0
% 3.70/1.64  #Close   : 0
% 3.70/1.64  
% 3.70/1.64  Ordering : KBO
% 3.70/1.64  
% 3.70/1.64  Simplification rules
% 3.70/1.64  ----------------------
% 3.70/1.64  #Subsume      : 29
% 3.70/1.64  #Demod        : 122
% 3.70/1.64  #Tautology    : 71
% 3.70/1.64  #SimpNegUnit  : 34
% 3.70/1.64  #BackRed      : 0
% 3.70/1.64  
% 3.70/1.64  #Partial instantiations: 0
% 3.70/1.64  #Strategies tried      : 1
% 3.70/1.64  
% 3.70/1.64  Timing (in seconds)
% 3.70/1.64  ----------------------
% 3.70/1.64  Preprocessing        : 0.32
% 3.70/1.64  Parsing              : 0.16
% 3.70/1.64  CNF conversion       : 0.02
% 3.70/1.64  Main loop            : 0.50
% 3.70/1.64  Inferencing          : 0.18
% 3.70/1.64  Reduction            : 0.14
% 3.70/1.64  Demodulation         : 0.09
% 3.70/1.64  BG Simplification    : 0.03
% 3.70/1.64  Subsumption          : 0.12
% 3.70/1.64  Abstraction          : 0.03
% 3.70/1.65  MUC search           : 0.00
% 3.70/1.65  Cooper               : 0.00
% 3.70/1.65  Total                : 0.84
% 3.70/1.65  Index Insertion      : 0.00
% 3.70/1.65  Index Deletion       : 0.00
% 3.70/1.65  Index Matching       : 0.00
% 3.70/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
