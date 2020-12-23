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
% DateTime   : Thu Dec  3 10:29:12 EST 2020

% Result     : Theorem 27.15s
% Output     : CNFRefutation 27.15s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 148 expanded)
%              Number of leaves         :   21 (  62 expanded)
%              Depth                    :   10
%              Number of atoms          :  129 ( 390 expanded)
%              Number of equality atoms :   16 (  37 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_pre_topc,type,(
    k1_pre_topc: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_83,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( v2_tex_2(B,A)
                    | v2_tex_2(C,A) )
                 => v2_tex_2(k9_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tex_2)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(f_44,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => u1_struct_0(k1_pre_topc(A,B)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_pre_topc)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => m1_subset_1(k9_subset_1(u1_struct_0(A),B,C),k1_zfmisc_1(u1_struct_0(k1_pre_topc(A,C)))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_tops_2)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( r1_tarski(C,B)
                  & v2_tex_2(B,A) )
               => v2_tex_2(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_tex_2)).

tff(c_22,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_37132,plain,(
    ! [A_482,C_483,B_484] :
      ( k9_subset_1(A_482,C_483,B_484) = k9_subset_1(A_482,B_484,C_483)
      | ~ m1_subset_1(C_483,k1_zfmisc_1(A_482)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_37144,plain,(
    ! [B_484] : k9_subset_1(u1_struct_0('#skF_1'),B_484,'#skF_2') = k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',B_484) ),
    inference(resolution,[status(thm)],[c_22,c_37132])).

tff(c_16,plain,(
    ~ v2_tex_2(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_37146,plain,(
    ~ v2_tex_2(k9_subset_1(u1_struct_0('#skF_1'),'#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_37144,c_16])).

tff(c_24,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_20,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_37247,plain,(
    ! [A_494,B_495] :
      ( u1_struct_0(k1_pre_topc(A_494,B_495)) = B_495
      | ~ m1_subset_1(B_495,k1_zfmisc_1(u1_struct_0(A_494)))
      | ~ l1_pre_topc(A_494) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_37258,plain,
    ( u1_struct_0(k1_pre_topc('#skF_1','#skF_3')) = '#skF_3'
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_37247])).

tff(c_37266,plain,(
    u1_struct_0(k1_pre_topc('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_37258])).

tff(c_93,plain,(
    ! [A_44,B_45] :
      ( u1_struct_0(k1_pre_topc(A_44,B_45)) = B_45
      | ~ m1_subset_1(B_45,k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ l1_pre_topc(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_107,plain,
    ( u1_struct_0(k1_pre_topc('#skF_1','#skF_2')) = '#skF_2'
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_93])).

tff(c_115,plain,(
    u1_struct_0(k1_pre_topc('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_107])).

tff(c_18,plain,
    ( v2_tex_2('#skF_3','#skF_1')
    | v2_tex_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_25,plain,(
    v2_tex_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_46,plain,(
    ! [A_40,C_41,B_42] :
      ( k9_subset_1(A_40,C_41,B_42) = k9_subset_1(A_40,B_42,C_41)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(A_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_58,plain,(
    ! [B_42] : k9_subset_1(u1_struct_0('#skF_1'),B_42,'#skF_2') = k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',B_42) ),
    inference(resolution,[status(thm)],[c_22,c_46])).

tff(c_133,plain,(
    ! [B_47] : k9_subset_1(u1_struct_0('#skF_1'),B_47,'#skF_2') = k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',B_47) ),
    inference(resolution,[status(thm)],[c_22,c_46])).

tff(c_4,plain,(
    ! [A_4,B_5,C_6] :
      ( m1_subset_1(k9_subset_1(A_4,B_5,C_6),k1_zfmisc_1(A_4))
      | ~ m1_subset_1(C_6,k1_zfmisc_1(A_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_155,plain,(
    ! [B_47] :
      ( m1_subset_1(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',B_47),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_4])).

tff(c_197,plain,(
    ! [B_51] : m1_subset_1(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',B_51),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_155])).

tff(c_207,plain,(
    ! [B_42] : m1_subset_1(k9_subset_1(u1_struct_0('#skF_1'),B_42,'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_197])).

tff(c_390,plain,(
    ! [A_64,B_65,C_66] :
      ( m1_subset_1(k9_subset_1(u1_struct_0(A_64),B_65,C_66),k1_zfmisc_1(u1_struct_0(k1_pre_topc(A_64,C_66))))
      | ~ m1_subset_1(C_66,k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ l1_pre_topc(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_6,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | ~ m1_subset_1(A_7,k1_zfmisc_1(B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1294,plain,(
    ! [A_97,B_98,C_99] :
      ( r1_tarski(k9_subset_1(u1_struct_0(A_97),B_98,C_99),u1_struct_0(k1_pre_topc(A_97,C_99)))
      | ~ m1_subset_1(C_99,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ m1_subset_1(B_98,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ l1_pre_topc(A_97) ) ),
    inference(resolution,[status(thm)],[c_390,c_6])).

tff(c_14,plain,(
    ! [C_25,A_19,B_23] :
      ( v2_tex_2(C_25,A_19)
      | ~ v2_tex_2(B_23,A_19)
      | ~ r1_tarski(C_25,B_23)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ m1_subset_1(B_23,k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_36619,plain,(
    ! [A_470,B_471,C_472,A_473] :
      ( v2_tex_2(k9_subset_1(u1_struct_0(A_470),B_471,C_472),A_473)
      | ~ v2_tex_2(u1_struct_0(k1_pre_topc(A_470,C_472)),A_473)
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(A_470),B_471,C_472),k1_zfmisc_1(u1_struct_0(A_473)))
      | ~ m1_subset_1(u1_struct_0(k1_pre_topc(A_470,C_472)),k1_zfmisc_1(u1_struct_0(A_473)))
      | ~ l1_pre_topc(A_473)
      | ~ m1_subset_1(C_472,k1_zfmisc_1(u1_struct_0(A_470)))
      | ~ m1_subset_1(B_471,k1_zfmisc_1(u1_struct_0(A_470)))
      | ~ l1_pre_topc(A_470) ) ),
    inference(resolution,[status(thm)],[c_1294,c_14])).

tff(c_36876,plain,(
    ! [B_42] :
      ( v2_tex_2(k9_subset_1(u1_struct_0('#skF_1'),B_42,'#skF_2'),'#skF_1')
      | ~ v2_tex_2(u1_struct_0(k1_pre_topc('#skF_1','#skF_2')),'#skF_1')
      | ~ m1_subset_1(u1_struct_0(k1_pre_topc('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_42,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_207,c_36619])).

tff(c_37044,plain,(
    ! [B_474] :
      ( v2_tex_2(k9_subset_1(u1_struct_0('#skF_1'),B_474,'#skF_2'),'#skF_1')
      | ~ m1_subset_1(B_474,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_22,c_115,c_25,c_115,c_36876])).

tff(c_57,plain,(
    ! [B_42] : k9_subset_1(u1_struct_0('#skF_1'),B_42,'#skF_3') = k9_subset_1(u1_struct_0('#skF_1'),'#skF_3',B_42) ),
    inference(resolution,[status(thm)],[c_20,c_46])).

tff(c_59,plain,(
    ~ v2_tex_2(k9_subset_1(u1_struct_0('#skF_1'),'#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_16])).

tff(c_37047,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_37044,c_59])).

tff(c_37110,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_37047])).

tff(c_37111,plain,(
    v2_tex_2('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_37143,plain,(
    ! [B_484] : k9_subset_1(u1_struct_0('#skF_1'),B_484,'#skF_3') = k9_subset_1(u1_struct_0('#skF_1'),'#skF_3',B_484) ),
    inference(resolution,[status(thm)],[c_20,c_37132])).

tff(c_37180,plain,(
    ! [B_489] : k9_subset_1(u1_struct_0('#skF_1'),B_489,'#skF_3') = k9_subset_1(u1_struct_0('#skF_1'),'#skF_3',B_489) ),
    inference(resolution,[status(thm)],[c_20,c_37132])).

tff(c_37202,plain,(
    ! [B_489] :
      ( m1_subset_1(k9_subset_1(u1_struct_0('#skF_1'),'#skF_3',B_489),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_37180,c_4])).

tff(c_37284,plain,(
    ! [B_496] : m1_subset_1(k9_subset_1(u1_struct_0('#skF_1'),'#skF_3',B_496),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_37202])).

tff(c_37294,plain,(
    ! [B_484] : m1_subset_1(k9_subset_1(u1_struct_0('#skF_1'),B_484,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_37143,c_37284])).

tff(c_37628,plain,(
    ! [A_513,B_514,C_515] :
      ( m1_subset_1(k9_subset_1(u1_struct_0(A_513),B_514,C_515),k1_zfmisc_1(u1_struct_0(k1_pre_topc(A_513,C_515))))
      | ~ m1_subset_1(C_515,k1_zfmisc_1(u1_struct_0(A_513)))
      | ~ m1_subset_1(B_514,k1_zfmisc_1(u1_struct_0(A_513)))
      | ~ l1_pre_topc(A_513) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_38673,plain,(
    ! [A_547,B_548,C_549] :
      ( r1_tarski(k9_subset_1(u1_struct_0(A_547),B_548,C_549),u1_struct_0(k1_pre_topc(A_547,C_549)))
      | ~ m1_subset_1(C_549,k1_zfmisc_1(u1_struct_0(A_547)))
      | ~ m1_subset_1(B_548,k1_zfmisc_1(u1_struct_0(A_547)))
      | ~ l1_pre_topc(A_547) ) ),
    inference(resolution,[status(thm)],[c_37628,c_6])).

tff(c_74200,plain,(
    ! [A_899,B_900,C_901,A_902] :
      ( v2_tex_2(k9_subset_1(u1_struct_0(A_899),B_900,C_901),A_902)
      | ~ v2_tex_2(u1_struct_0(k1_pre_topc(A_899,C_901)),A_902)
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(A_899),B_900,C_901),k1_zfmisc_1(u1_struct_0(A_902)))
      | ~ m1_subset_1(u1_struct_0(k1_pre_topc(A_899,C_901)),k1_zfmisc_1(u1_struct_0(A_902)))
      | ~ l1_pre_topc(A_902)
      | ~ m1_subset_1(C_901,k1_zfmisc_1(u1_struct_0(A_899)))
      | ~ m1_subset_1(B_900,k1_zfmisc_1(u1_struct_0(A_899)))
      | ~ l1_pre_topc(A_899) ) ),
    inference(resolution,[status(thm)],[c_38673,c_14])).

tff(c_74460,plain,(
    ! [B_484] :
      ( v2_tex_2(k9_subset_1(u1_struct_0('#skF_1'),B_484,'#skF_3'),'#skF_1')
      | ~ v2_tex_2(u1_struct_0(k1_pre_topc('#skF_1','#skF_3')),'#skF_1')
      | ~ m1_subset_1(u1_struct_0(k1_pre_topc('#skF_1','#skF_3')),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_484,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_37294,c_74200])).

tff(c_74625,plain,(
    ! [B_903] :
      ( v2_tex_2(k9_subset_1(u1_struct_0('#skF_1'),B_903,'#skF_3'),'#skF_1')
      | ~ m1_subset_1(B_903,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_20,c_20,c_37266,c_37111,c_37266,c_74460])).

tff(c_74688,plain,
    ( v2_tex_2(k9_subset_1(u1_struct_0('#skF_1'),'#skF_3','#skF_2'),'#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_37144,c_74625])).

tff(c_74714,plain,(
    v2_tex_2(k9_subset_1(u1_struct_0('#skF_1'),'#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_74688])).

tff(c_74716,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_37146,c_74714])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:23:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 27.15/17.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.15/17.26  
% 27.15/17.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.15/17.26  %$ v2_tex_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 27.15/17.26  
% 27.15/17.26  %Foreground sorts:
% 27.15/17.26  
% 27.15/17.26  
% 27.15/17.26  %Background operators:
% 27.15/17.26  
% 27.15/17.26  
% 27.15/17.26  %Foreground operators:
% 27.15/17.26  tff(k1_pre_topc, type, k1_pre_topc: ($i * $i) > $i).
% 27.15/17.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 27.15/17.26  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 27.15/17.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 27.15/17.26  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 27.15/17.26  tff('#skF_2', type, '#skF_2': $i).
% 27.15/17.26  tff('#skF_3', type, '#skF_3': $i).
% 27.15/17.26  tff('#skF_1', type, '#skF_1': $i).
% 27.15/17.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 27.15/17.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 27.15/17.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 27.15/17.26  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 27.15/17.26  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 27.15/17.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 27.15/17.26  
% 27.15/17.28  tff(f_83, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(B, A) | v2_tex_2(C, A)) => v2_tex_2(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_tex_2)).
% 27.15/17.28  tff(f_29, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k9_subset_1(A, C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 27.15/17.28  tff(f_44, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (u1_struct_0(k1_pre_topc(A, B)) = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_pre_topc)).
% 27.15/17.28  tff(f_33, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 27.15/17.28  tff(f_54, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => m1_subset_1(k9_subset_1(u1_struct_0(A), B, C), k1_zfmisc_1(u1_struct_0(k1_pre_topc(A, C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_tops_2)).
% 27.15/17.28  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 27.15/17.28  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v2_tex_2(B, A)) => v2_tex_2(C, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_tex_2)).
% 27.15/17.28  tff(c_22, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_83])).
% 27.15/17.28  tff(c_37132, plain, (![A_482, C_483, B_484]: (k9_subset_1(A_482, C_483, B_484)=k9_subset_1(A_482, B_484, C_483) | ~m1_subset_1(C_483, k1_zfmisc_1(A_482)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 27.15/17.28  tff(c_37144, plain, (![B_484]: (k9_subset_1(u1_struct_0('#skF_1'), B_484, '#skF_2')=k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', B_484))), inference(resolution, [status(thm)], [c_22, c_37132])).
% 27.15/17.28  tff(c_16, plain, (~v2_tex_2(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_83])).
% 27.15/17.28  tff(c_37146, plain, (~v2_tex_2(k9_subset_1(u1_struct_0('#skF_1'), '#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_37144, c_16])).
% 27.15/17.28  tff(c_24, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_83])).
% 27.15/17.28  tff(c_20, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_83])).
% 27.15/17.28  tff(c_37247, plain, (![A_494, B_495]: (u1_struct_0(k1_pre_topc(A_494, B_495))=B_495 | ~m1_subset_1(B_495, k1_zfmisc_1(u1_struct_0(A_494))) | ~l1_pre_topc(A_494))), inference(cnfTransformation, [status(thm)], [f_44])).
% 27.15/17.28  tff(c_37258, plain, (u1_struct_0(k1_pre_topc('#skF_1', '#skF_3'))='#skF_3' | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_37247])).
% 27.15/17.28  tff(c_37266, plain, (u1_struct_0(k1_pre_topc('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_37258])).
% 27.15/17.28  tff(c_93, plain, (![A_44, B_45]: (u1_struct_0(k1_pre_topc(A_44, B_45))=B_45 | ~m1_subset_1(B_45, k1_zfmisc_1(u1_struct_0(A_44))) | ~l1_pre_topc(A_44))), inference(cnfTransformation, [status(thm)], [f_44])).
% 27.15/17.28  tff(c_107, plain, (u1_struct_0(k1_pre_topc('#skF_1', '#skF_2'))='#skF_2' | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_93])).
% 27.15/17.28  tff(c_115, plain, (u1_struct_0(k1_pre_topc('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_107])).
% 27.15/17.28  tff(c_18, plain, (v2_tex_2('#skF_3', '#skF_1') | v2_tex_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_83])).
% 27.15/17.28  tff(c_25, plain, (v2_tex_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_18])).
% 27.15/17.28  tff(c_46, plain, (![A_40, C_41, B_42]: (k9_subset_1(A_40, C_41, B_42)=k9_subset_1(A_40, B_42, C_41) | ~m1_subset_1(C_41, k1_zfmisc_1(A_40)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 27.15/17.28  tff(c_58, plain, (![B_42]: (k9_subset_1(u1_struct_0('#skF_1'), B_42, '#skF_2')=k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', B_42))), inference(resolution, [status(thm)], [c_22, c_46])).
% 27.15/17.28  tff(c_133, plain, (![B_47]: (k9_subset_1(u1_struct_0('#skF_1'), B_47, '#skF_2')=k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', B_47))), inference(resolution, [status(thm)], [c_22, c_46])).
% 27.15/17.28  tff(c_4, plain, (![A_4, B_5, C_6]: (m1_subset_1(k9_subset_1(A_4, B_5, C_6), k1_zfmisc_1(A_4)) | ~m1_subset_1(C_6, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 27.15/17.28  tff(c_155, plain, (![B_47]: (m1_subset_1(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', B_47), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_133, c_4])).
% 27.15/17.28  tff(c_197, plain, (![B_51]: (m1_subset_1(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', B_51), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_155])).
% 27.15/17.28  tff(c_207, plain, (![B_42]: (m1_subset_1(k9_subset_1(u1_struct_0('#skF_1'), B_42, '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_58, c_197])).
% 27.15/17.28  tff(c_390, plain, (![A_64, B_65, C_66]: (m1_subset_1(k9_subset_1(u1_struct_0(A_64), B_65, C_66), k1_zfmisc_1(u1_struct_0(k1_pre_topc(A_64, C_66)))) | ~m1_subset_1(C_66, k1_zfmisc_1(u1_struct_0(A_64))) | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0(A_64))) | ~l1_pre_topc(A_64))), inference(cnfTransformation, [status(thm)], [f_54])).
% 27.15/17.28  tff(c_6, plain, (![A_7, B_8]: (r1_tarski(A_7, B_8) | ~m1_subset_1(A_7, k1_zfmisc_1(B_8)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 27.15/17.28  tff(c_1294, plain, (![A_97, B_98, C_99]: (r1_tarski(k9_subset_1(u1_struct_0(A_97), B_98, C_99), u1_struct_0(k1_pre_topc(A_97, C_99))) | ~m1_subset_1(C_99, k1_zfmisc_1(u1_struct_0(A_97))) | ~m1_subset_1(B_98, k1_zfmisc_1(u1_struct_0(A_97))) | ~l1_pre_topc(A_97))), inference(resolution, [status(thm)], [c_390, c_6])).
% 27.15/17.28  tff(c_14, plain, (![C_25, A_19, B_23]: (v2_tex_2(C_25, A_19) | ~v2_tex_2(B_23, A_19) | ~r1_tarski(C_25, B_23) | ~m1_subset_1(C_25, k1_zfmisc_1(u1_struct_0(A_19))) | ~m1_subset_1(B_23, k1_zfmisc_1(u1_struct_0(A_19))) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_68])).
% 27.15/17.28  tff(c_36619, plain, (![A_470, B_471, C_472, A_473]: (v2_tex_2(k9_subset_1(u1_struct_0(A_470), B_471, C_472), A_473) | ~v2_tex_2(u1_struct_0(k1_pre_topc(A_470, C_472)), A_473) | ~m1_subset_1(k9_subset_1(u1_struct_0(A_470), B_471, C_472), k1_zfmisc_1(u1_struct_0(A_473))) | ~m1_subset_1(u1_struct_0(k1_pre_topc(A_470, C_472)), k1_zfmisc_1(u1_struct_0(A_473))) | ~l1_pre_topc(A_473) | ~m1_subset_1(C_472, k1_zfmisc_1(u1_struct_0(A_470))) | ~m1_subset_1(B_471, k1_zfmisc_1(u1_struct_0(A_470))) | ~l1_pre_topc(A_470))), inference(resolution, [status(thm)], [c_1294, c_14])).
% 27.15/17.28  tff(c_36876, plain, (![B_42]: (v2_tex_2(k9_subset_1(u1_struct_0('#skF_1'), B_42, '#skF_2'), '#skF_1') | ~v2_tex_2(u1_struct_0(k1_pre_topc('#skF_1', '#skF_2')), '#skF_1') | ~m1_subset_1(u1_struct_0(k1_pre_topc('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_42, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_207, c_36619])).
% 27.15/17.28  tff(c_37044, plain, (![B_474]: (v2_tex_2(k9_subset_1(u1_struct_0('#skF_1'), B_474, '#skF_2'), '#skF_1') | ~m1_subset_1(B_474, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_22, c_115, c_25, c_115, c_36876])).
% 27.15/17.28  tff(c_57, plain, (![B_42]: (k9_subset_1(u1_struct_0('#skF_1'), B_42, '#skF_3')=k9_subset_1(u1_struct_0('#skF_1'), '#skF_3', B_42))), inference(resolution, [status(thm)], [c_20, c_46])).
% 27.15/17.28  tff(c_59, plain, (~v2_tex_2(k9_subset_1(u1_struct_0('#skF_1'), '#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_57, c_16])).
% 27.15/17.28  tff(c_37047, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_37044, c_59])).
% 27.15/17.28  tff(c_37110, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_37047])).
% 27.15/17.28  tff(c_37111, plain, (v2_tex_2('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_18])).
% 27.15/17.28  tff(c_37143, plain, (![B_484]: (k9_subset_1(u1_struct_0('#skF_1'), B_484, '#skF_3')=k9_subset_1(u1_struct_0('#skF_1'), '#skF_3', B_484))), inference(resolution, [status(thm)], [c_20, c_37132])).
% 27.15/17.28  tff(c_37180, plain, (![B_489]: (k9_subset_1(u1_struct_0('#skF_1'), B_489, '#skF_3')=k9_subset_1(u1_struct_0('#skF_1'), '#skF_3', B_489))), inference(resolution, [status(thm)], [c_20, c_37132])).
% 27.15/17.28  tff(c_37202, plain, (![B_489]: (m1_subset_1(k9_subset_1(u1_struct_0('#skF_1'), '#skF_3', B_489), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_37180, c_4])).
% 27.15/17.28  tff(c_37284, plain, (![B_496]: (m1_subset_1(k9_subset_1(u1_struct_0('#skF_1'), '#skF_3', B_496), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_37202])).
% 27.15/17.28  tff(c_37294, plain, (![B_484]: (m1_subset_1(k9_subset_1(u1_struct_0('#skF_1'), B_484, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_37143, c_37284])).
% 27.15/17.28  tff(c_37628, plain, (![A_513, B_514, C_515]: (m1_subset_1(k9_subset_1(u1_struct_0(A_513), B_514, C_515), k1_zfmisc_1(u1_struct_0(k1_pre_topc(A_513, C_515)))) | ~m1_subset_1(C_515, k1_zfmisc_1(u1_struct_0(A_513))) | ~m1_subset_1(B_514, k1_zfmisc_1(u1_struct_0(A_513))) | ~l1_pre_topc(A_513))), inference(cnfTransformation, [status(thm)], [f_54])).
% 27.15/17.28  tff(c_38673, plain, (![A_547, B_548, C_549]: (r1_tarski(k9_subset_1(u1_struct_0(A_547), B_548, C_549), u1_struct_0(k1_pre_topc(A_547, C_549))) | ~m1_subset_1(C_549, k1_zfmisc_1(u1_struct_0(A_547))) | ~m1_subset_1(B_548, k1_zfmisc_1(u1_struct_0(A_547))) | ~l1_pre_topc(A_547))), inference(resolution, [status(thm)], [c_37628, c_6])).
% 27.15/17.28  tff(c_74200, plain, (![A_899, B_900, C_901, A_902]: (v2_tex_2(k9_subset_1(u1_struct_0(A_899), B_900, C_901), A_902) | ~v2_tex_2(u1_struct_0(k1_pre_topc(A_899, C_901)), A_902) | ~m1_subset_1(k9_subset_1(u1_struct_0(A_899), B_900, C_901), k1_zfmisc_1(u1_struct_0(A_902))) | ~m1_subset_1(u1_struct_0(k1_pre_topc(A_899, C_901)), k1_zfmisc_1(u1_struct_0(A_902))) | ~l1_pre_topc(A_902) | ~m1_subset_1(C_901, k1_zfmisc_1(u1_struct_0(A_899))) | ~m1_subset_1(B_900, k1_zfmisc_1(u1_struct_0(A_899))) | ~l1_pre_topc(A_899))), inference(resolution, [status(thm)], [c_38673, c_14])).
% 27.15/17.28  tff(c_74460, plain, (![B_484]: (v2_tex_2(k9_subset_1(u1_struct_0('#skF_1'), B_484, '#skF_3'), '#skF_1') | ~v2_tex_2(u1_struct_0(k1_pre_topc('#skF_1', '#skF_3')), '#skF_1') | ~m1_subset_1(u1_struct_0(k1_pre_topc('#skF_1', '#skF_3')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_484, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_37294, c_74200])).
% 27.15/17.28  tff(c_74625, plain, (![B_903]: (v2_tex_2(k9_subset_1(u1_struct_0('#skF_1'), B_903, '#skF_3'), '#skF_1') | ~m1_subset_1(B_903, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_20, c_20, c_37266, c_37111, c_37266, c_74460])).
% 27.15/17.28  tff(c_74688, plain, (v2_tex_2(k9_subset_1(u1_struct_0('#skF_1'), '#skF_3', '#skF_2'), '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_37144, c_74625])).
% 27.15/17.28  tff(c_74714, plain, (v2_tex_2(k9_subset_1(u1_struct_0('#skF_1'), '#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_74688])).
% 27.15/17.28  tff(c_74716, plain, $false, inference(negUnitSimplification, [status(thm)], [c_37146, c_74714])).
% 27.15/17.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.15/17.28  
% 27.15/17.28  Inference rules
% 27.15/17.28  ----------------------
% 27.15/17.28  #Ref     : 0
% 27.15/17.28  #Sup     : 16682
% 27.15/17.28  #Fact    : 0
% 27.15/17.28  #Define  : 0
% 27.15/17.28  #Split   : 7
% 27.15/17.28  #Chain   : 0
% 27.15/17.28  #Close   : 0
% 27.15/17.28  
% 27.15/17.28  Ordering : KBO
% 27.15/17.28  
% 27.15/17.28  Simplification rules
% 27.15/17.28  ----------------------
% 27.15/17.28  #Subsume      : 1422
% 27.15/17.28  #Demod        : 17517
% 27.15/17.28  #Tautology    : 6766
% 27.15/17.28  #SimpNegUnit  : 1
% 27.15/17.28  #BackRed      : 2
% 27.15/17.28  
% 27.15/17.28  #Partial instantiations: 0
% 27.15/17.28  #Strategies tried      : 1
% 27.15/17.28  
% 27.15/17.28  Timing (in seconds)
% 27.15/17.28  ----------------------
% 27.15/17.28  Preprocessing        : 0.28
% 27.15/17.28  Parsing              : 0.16
% 27.15/17.28  CNF conversion       : 0.02
% 27.15/17.28  Main loop            : 16.13
% 27.15/17.28  Inferencing          : 2.43
% 27.15/17.28  Reduction            : 10.62
% 27.15/17.28  Demodulation         : 9.85
% 27.15/17.28  BG Simplification    : 0.32
% 27.15/17.28  Subsumption          : 2.29
% 27.15/17.28  Abstraction          : 0.53
% 27.15/17.28  MUC search           : 0.00
% 27.15/17.28  Cooper               : 0.00
% 27.15/17.28  Total                : 16.45
% 27.15/17.28  Index Insertion      : 0.00
% 27.15/17.28  Index Deletion       : 0.00
% 27.15/17.28  Index Matching       : 0.00
% 27.15/17.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
