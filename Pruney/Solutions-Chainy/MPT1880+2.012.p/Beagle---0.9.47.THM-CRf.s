%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:05 EST 2020

% Result     : Theorem 5.15s
% Output     : CNFRefutation 5.43s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 333 expanded)
%              Number of leaves         :   32 ( 129 expanded)
%              Depth                    :   12
%              Number of atoms          :  229 ( 899 expanded)
%              Number of equality atoms :   36 ( 120 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > v1_tops_1 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

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

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_112,negated_conjecture,(
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

tff(f_49,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_76,axiom,(
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

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_45,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_95,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_42,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_48,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_14,plain,(
    ! [A_10] :
      ( l1_struct_0(A_10)
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_54,plain,(
    ! [A_36] :
      ( u1_struct_0(A_36) = k2_struct_0(A_36)
      | ~ l1_struct_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_60,plain,(
    ! [A_39] :
      ( u1_struct_0(A_39) = k2_struct_0(A_39)
      | ~ l1_pre_topc(A_39) ) ),
    inference(resolution,[status(thm)],[c_14,c_54])).

tff(c_64,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_60])).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_65,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_46])).

tff(c_379,plain,(
    ! [A_78,B_79] :
      ( '#skF_1'(A_78,B_79) != B_79
      | v3_tex_2(B_79,A_78)
      | ~ v2_tex_2(B_79,A_78)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ l1_pre_topc(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_385,plain,(
    ! [B_79] :
      ( '#skF_1'('#skF_3',B_79) != B_79
      | v3_tex_2(B_79,'#skF_3')
      | ~ v2_tex_2(B_79,'#skF_3')
      | ~ m1_subset_1(B_79,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_379])).

tff(c_406,plain,(
    ! [B_82] :
      ( '#skF_1'('#skF_3',B_82) != B_82
      | v3_tex_2(B_82,'#skF_3')
      | ~ v2_tex_2(B_82,'#skF_3')
      | ~ m1_subset_1(B_82,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_385])).

tff(c_412,plain,
    ( '#skF_1'('#skF_3','#skF_4') != '#skF_4'
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_65,c_406])).

tff(c_422,plain,
    ( '#skF_1'('#skF_3','#skF_4') != '#skF_4'
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_412])).

tff(c_423,plain,(
    '#skF_1'('#skF_3','#skF_4') != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_422])).

tff(c_394,plain,(
    ! [A_80,B_81] :
      ( v2_tex_2('#skF_1'(A_80,B_81),A_80)
      | v3_tex_2(B_81,A_80)
      | ~ v2_tex_2(B_81,A_80)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(u1_struct_0(A_80)))
      | ~ l1_pre_topc(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_398,plain,(
    ! [B_81] :
      ( v2_tex_2('#skF_1'('#skF_3',B_81),'#skF_3')
      | v3_tex_2(B_81,'#skF_3')
      | ~ v2_tex_2(B_81,'#skF_3')
      | ~ m1_subset_1(B_81,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_394])).

tff(c_426,plain,(
    ! [B_83] :
      ( v2_tex_2('#skF_1'('#skF_3',B_83),'#skF_3')
      | v3_tex_2(B_83,'#skF_3')
      | ~ v2_tex_2(B_83,'#skF_3')
      | ~ m1_subset_1(B_83,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_398])).

tff(c_432,plain,
    ( v2_tex_2('#skF_1'('#skF_3','#skF_4'),'#skF_3')
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_65,c_426])).

tff(c_442,plain,
    ( v2_tex_2('#skF_1'('#skF_3','#skF_4'),'#skF_3')
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_432])).

tff(c_443,plain,(
    v2_tex_2('#skF_1'('#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_442])).

tff(c_459,plain,(
    ! [B_86,A_87] :
      ( r1_tarski(B_86,'#skF_1'(A_87,B_86))
      | v3_tex_2(B_86,A_87)
      | ~ v2_tex_2(B_86,A_87)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ l1_pre_topc(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_463,plain,(
    ! [B_86] :
      ( r1_tarski(B_86,'#skF_1'('#skF_3',B_86))
      | v3_tex_2(B_86,'#skF_3')
      | ~ v2_tex_2(B_86,'#skF_3')
      | ~ m1_subset_1(B_86,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_459])).

tff(c_481,plain,(
    ! [B_90] :
      ( r1_tarski(B_90,'#skF_1'('#skF_3',B_90))
      | v3_tex_2(B_90,'#skF_3')
      | ~ v2_tex_2(B_90,'#skF_3')
      | ~ m1_subset_1(B_90,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_463])).

tff(c_485,plain,
    ( r1_tarski('#skF_4','#skF_1'('#skF_3','#skF_4'))
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_65,c_481])).

tff(c_493,plain,
    ( r1_tarski('#skF_4','#skF_1'('#skF_3','#skF_4'))
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_485])).

tff(c_494,plain,(
    r1_tarski('#skF_4','#skF_1'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_493])).

tff(c_667,plain,(
    ! [A_102,B_103] :
      ( m1_subset_1('#skF_1'(A_102,B_103),k1_zfmisc_1(u1_struct_0(A_102)))
      | v3_tex_2(B_103,A_102)
      | ~ v2_tex_2(B_103,A_102)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ l1_pre_topc(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_693,plain,(
    ! [B_103] :
      ( m1_subset_1('#skF_1'('#skF_3',B_103),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | v3_tex_2(B_103,'#skF_3')
      | ~ v2_tex_2(B_103,'#skF_3')
      | ~ m1_subset_1(B_103,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_667])).

tff(c_808,plain,(
    ! [B_109] :
      ( m1_subset_1('#skF_1'('#skF_3',B_109),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | v3_tex_2(B_109,'#skF_3')
      | ~ v2_tex_2(B_109,'#skF_3')
      | ~ m1_subset_1(B_109,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_64,c_693])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_945,plain,(
    ! [B_114] :
      ( r1_tarski('#skF_1'('#skF_3',B_114),k2_struct_0('#skF_3'))
      | v3_tex_2(B_114,'#skF_3')
      | ~ v2_tex_2(B_114,'#skF_3')
      | ~ m1_subset_1(B_114,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_808,c_6])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1393,plain,(
    ! [B_144] :
      ( k3_xboole_0('#skF_1'('#skF_3',B_144),k2_struct_0('#skF_3')) = '#skF_1'('#skF_3',B_144)
      | v3_tex_2(B_144,'#skF_3')
      | ~ v2_tex_2(B_144,'#skF_3')
      | ~ m1_subset_1(B_144,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_945,c_2])).

tff(c_1405,plain,
    ( k3_xboole_0('#skF_1'('#skF_3','#skF_4'),k2_struct_0('#skF_3')) = '#skF_1'('#skF_3','#skF_4')
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_65,c_1393])).

tff(c_1416,plain,
    ( k3_xboole_0('#skF_1'('#skF_3','#skF_4'),k2_struct_0('#skF_3')) = '#skF_1'('#skF_3','#skF_4')
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1405])).

tff(c_1417,plain,(
    k3_xboole_0('#skF_1'('#skF_3','#skF_4'),k2_struct_0('#skF_3')) = '#skF_1'('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_1416])).

tff(c_704,plain,(
    ! [B_103] :
      ( m1_subset_1('#skF_1'('#skF_3',B_103),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | v3_tex_2(B_103,'#skF_3')
      | ~ v2_tex_2(B_103,'#skF_3')
      | ~ m1_subset_1(B_103,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_64,c_693])).

tff(c_88,plain,(
    ! [A_44] :
      ( m1_subset_1(k2_struct_0(A_44),k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ l1_struct_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_96,plain,(
    ! [A_45] :
      ( r1_tarski(k2_struct_0(A_45),u1_struct_0(A_45))
      | ~ l1_struct_0(A_45) ) ),
    inference(resolution,[status(thm)],[c_88,c_6])).

tff(c_102,plain,
    ( r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_3'))
    | ~ l1_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_96])).

tff(c_104,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_102])).

tff(c_107,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_104])).

tff(c_111,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_107])).

tff(c_113,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_102])).

tff(c_94,plain,
    ( m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ l1_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_88])).

tff(c_128,plain,(
    m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_94])).

tff(c_134,plain,(
    ! [A_46,B_47,C_48] :
      ( k9_subset_1(A_46,B_47,C_48) = k3_xboole_0(B_47,C_48)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(A_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_143,plain,(
    ! [B_47] : k9_subset_1(k2_struct_0('#skF_3'),B_47,k2_struct_0('#skF_3')) = k3_xboole_0(B_47,k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_128,c_134])).

tff(c_44,plain,(
    v1_tops_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_298,plain,(
    ! [A_68,B_69] :
      ( k2_pre_topc(A_68,B_69) = k2_struct_0(A_68)
      | ~ v1_tops_1(B_69,A_68)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ l1_pre_topc(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_304,plain,(
    ! [B_69] :
      ( k2_pre_topc('#skF_3',B_69) = k2_struct_0('#skF_3')
      | ~ v1_tops_1(B_69,'#skF_3')
      | ~ m1_subset_1(B_69,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_298])).

tff(c_313,plain,(
    ! [B_70] :
      ( k2_pre_topc('#skF_3',B_70) = k2_struct_0('#skF_3')
      | ~ v1_tops_1(B_70,'#skF_3')
      | ~ m1_subset_1(B_70,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_304])).

tff(c_319,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = k2_struct_0('#skF_3')
    | ~ v1_tops_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_65,c_313])).

tff(c_329,plain,(
    k2_pre_topc('#skF_3','#skF_4') = k2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_319])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_50,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1374,plain,(
    ! [A_141,B_142,C_143] :
      ( k9_subset_1(u1_struct_0(A_141),B_142,k2_pre_topc(A_141,C_143)) = C_143
      | ~ r1_tarski(C_143,B_142)
      | ~ m1_subset_1(C_143,k1_zfmisc_1(u1_struct_0(A_141)))
      | ~ v2_tex_2(B_142,A_141)
      | ~ m1_subset_1(B_142,k1_zfmisc_1(u1_struct_0(A_141)))
      | ~ l1_pre_topc(A_141)
      | ~ v2_pre_topc(A_141)
      | v2_struct_0(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1382,plain,(
    ! [B_142,C_143] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_142,k2_pre_topc('#skF_3',C_143)) = C_143
      | ~ r1_tarski(C_143,B_142)
      | ~ m1_subset_1(C_143,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ v2_tex_2(B_142,'#skF_3')
      | ~ m1_subset_1(B_142,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_1374])).

tff(c_1390,plain,(
    ! [B_142,C_143] :
      ( k9_subset_1(k2_struct_0('#skF_3'),B_142,k2_pre_topc('#skF_3',C_143)) = C_143
      | ~ r1_tarski(C_143,B_142)
      | ~ m1_subset_1(C_143,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ v2_tex_2(B_142,'#skF_3')
      | ~ m1_subset_1(B_142,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_64,c_64,c_1382])).

tff(c_1423,plain,(
    ! [B_145,C_146] :
      ( k9_subset_1(k2_struct_0('#skF_3'),B_145,k2_pre_topc('#skF_3',C_146)) = C_146
      | ~ r1_tarski(C_146,B_145)
      | ~ m1_subset_1(C_146,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ v2_tex_2(B_145,'#skF_3')
      | ~ m1_subset_1(B_145,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1390])).

tff(c_1431,plain,(
    ! [B_145] :
      ( k9_subset_1(k2_struct_0('#skF_3'),B_145,k2_pre_topc('#skF_3','#skF_4')) = '#skF_4'
      | ~ r1_tarski('#skF_4',B_145)
      | ~ v2_tex_2(B_145,'#skF_3')
      | ~ m1_subset_1(B_145,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_65,c_1423])).

tff(c_1441,plain,(
    ! [B_147] :
      ( k3_xboole_0(B_147,k2_struct_0('#skF_3')) = '#skF_4'
      | ~ r1_tarski('#skF_4',B_147)
      | ~ v2_tex_2(B_147,'#skF_3')
      | ~ m1_subset_1(B_147,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_329,c_1431])).

tff(c_2652,plain,(
    ! [B_246] :
      ( k3_xboole_0('#skF_1'('#skF_3',B_246),k2_struct_0('#skF_3')) = '#skF_4'
      | ~ r1_tarski('#skF_4','#skF_1'('#skF_3',B_246))
      | ~ v2_tex_2('#skF_1'('#skF_3',B_246),'#skF_3')
      | v3_tex_2(B_246,'#skF_3')
      | ~ v2_tex_2(B_246,'#skF_3')
      | ~ m1_subset_1(B_246,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_704,c_1441])).

tff(c_2664,plain,
    ( k3_xboole_0('#skF_1'('#skF_3','#skF_4'),k2_struct_0('#skF_3')) = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_1'('#skF_3','#skF_4'))
    | ~ v2_tex_2('#skF_1'('#skF_3','#skF_4'),'#skF_3')
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_65,c_2652])).

tff(c_2675,plain,
    ( '#skF_1'('#skF_3','#skF_4') = '#skF_4'
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_443,c_494,c_1417,c_2664])).

tff(c_2677,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_423,c_2675])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:50:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.15/1.96  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.15/1.97  
% 5.15/1.97  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.15/1.97  %$ v3_tex_2 > v2_tex_2 > v1_tops_1 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 5.15/1.97  
% 5.15/1.97  %Foreground sorts:
% 5.15/1.97  
% 5.15/1.97  
% 5.15/1.97  %Background operators:
% 5.15/1.97  
% 5.15/1.97  
% 5.15/1.97  %Foreground operators:
% 5.15/1.97  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.15/1.97  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.15/1.97  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.15/1.97  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.15/1.97  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 5.15/1.97  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 5.15/1.97  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 5.15/1.97  tff('#skF_3', type, '#skF_3': $i).
% 5.15/1.97  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.15/1.97  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.15/1.97  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.15/1.97  tff('#skF_4', type, '#skF_4': $i).
% 5.15/1.97  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.15/1.97  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.15/1.97  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.15/1.97  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.15/1.97  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.15/1.97  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.15/1.97  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 5.15/1.97  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 5.15/1.97  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 5.15/1.97  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.15/1.97  
% 5.43/1.99  tff(f_112, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v1_tops_1(B, A) & v2_tex_2(B, A)) => v3_tex_2(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_tex_2)).
% 5.43/1.99  tff(f_49, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 5.43/1.99  tff(f_41, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 5.43/1.99  tff(f_76, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_tex_2)).
% 5.43/1.99  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.43/1.99  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 5.43/1.99  tff(f_45, axiom, (![A]: (l1_struct_0(A) => m1_subset_1(k2_struct_0(A), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 5.43/1.99  tff(f_33, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 5.43/1.99  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tops_1)).
% 5.43/1.99  tff(f_95, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C)) = C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_tex_2)).
% 5.43/1.99  tff(c_40, plain, (~v3_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.43/1.99  tff(c_42, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.43/1.99  tff(c_48, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.43/1.99  tff(c_14, plain, (![A_10]: (l1_struct_0(A_10) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.43/1.99  tff(c_54, plain, (![A_36]: (u1_struct_0(A_36)=k2_struct_0(A_36) | ~l1_struct_0(A_36))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.43/1.99  tff(c_60, plain, (![A_39]: (u1_struct_0(A_39)=k2_struct_0(A_39) | ~l1_pre_topc(A_39))), inference(resolution, [status(thm)], [c_14, c_54])).
% 5.43/1.99  tff(c_64, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_48, c_60])).
% 5.43/1.99  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.43/1.99  tff(c_65, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_46])).
% 5.43/1.99  tff(c_379, plain, (![A_78, B_79]: ('#skF_1'(A_78, B_79)!=B_79 | v3_tex_2(B_79, A_78) | ~v2_tex_2(B_79, A_78) | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0(A_78))) | ~l1_pre_topc(A_78))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.43/1.99  tff(c_385, plain, (![B_79]: ('#skF_1'('#skF_3', B_79)!=B_79 | v3_tex_2(B_79, '#skF_3') | ~v2_tex_2(B_79, '#skF_3') | ~m1_subset_1(B_79, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_64, c_379])).
% 5.43/1.99  tff(c_406, plain, (![B_82]: ('#skF_1'('#skF_3', B_82)!=B_82 | v3_tex_2(B_82, '#skF_3') | ~v2_tex_2(B_82, '#skF_3') | ~m1_subset_1(B_82, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_385])).
% 5.43/1.99  tff(c_412, plain, ('#skF_1'('#skF_3', '#skF_4')!='#skF_4' | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_65, c_406])).
% 5.43/1.99  tff(c_422, plain, ('#skF_1'('#skF_3', '#skF_4')!='#skF_4' | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_412])).
% 5.43/1.99  tff(c_423, plain, ('#skF_1'('#skF_3', '#skF_4')!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_40, c_422])).
% 5.43/1.99  tff(c_394, plain, (![A_80, B_81]: (v2_tex_2('#skF_1'(A_80, B_81), A_80) | v3_tex_2(B_81, A_80) | ~v2_tex_2(B_81, A_80) | ~m1_subset_1(B_81, k1_zfmisc_1(u1_struct_0(A_80))) | ~l1_pre_topc(A_80))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.43/1.99  tff(c_398, plain, (![B_81]: (v2_tex_2('#skF_1'('#skF_3', B_81), '#skF_3') | v3_tex_2(B_81, '#skF_3') | ~v2_tex_2(B_81, '#skF_3') | ~m1_subset_1(B_81, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_64, c_394])).
% 5.43/1.99  tff(c_426, plain, (![B_83]: (v2_tex_2('#skF_1'('#skF_3', B_83), '#skF_3') | v3_tex_2(B_83, '#skF_3') | ~v2_tex_2(B_83, '#skF_3') | ~m1_subset_1(B_83, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_398])).
% 5.43/1.99  tff(c_432, plain, (v2_tex_2('#skF_1'('#skF_3', '#skF_4'), '#skF_3') | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_65, c_426])).
% 5.43/1.99  tff(c_442, plain, (v2_tex_2('#skF_1'('#skF_3', '#skF_4'), '#skF_3') | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_432])).
% 5.43/1.99  tff(c_443, plain, (v2_tex_2('#skF_1'('#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_40, c_442])).
% 5.43/1.99  tff(c_459, plain, (![B_86, A_87]: (r1_tarski(B_86, '#skF_1'(A_87, B_86)) | v3_tex_2(B_86, A_87) | ~v2_tex_2(B_86, A_87) | ~m1_subset_1(B_86, k1_zfmisc_1(u1_struct_0(A_87))) | ~l1_pre_topc(A_87))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.43/1.99  tff(c_463, plain, (![B_86]: (r1_tarski(B_86, '#skF_1'('#skF_3', B_86)) | v3_tex_2(B_86, '#skF_3') | ~v2_tex_2(B_86, '#skF_3') | ~m1_subset_1(B_86, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_64, c_459])).
% 5.43/1.99  tff(c_481, plain, (![B_90]: (r1_tarski(B_90, '#skF_1'('#skF_3', B_90)) | v3_tex_2(B_90, '#skF_3') | ~v2_tex_2(B_90, '#skF_3') | ~m1_subset_1(B_90, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_463])).
% 5.43/1.99  tff(c_485, plain, (r1_tarski('#skF_4', '#skF_1'('#skF_3', '#skF_4')) | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_65, c_481])).
% 5.43/1.99  tff(c_493, plain, (r1_tarski('#skF_4', '#skF_1'('#skF_3', '#skF_4')) | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_485])).
% 5.43/1.99  tff(c_494, plain, (r1_tarski('#skF_4', '#skF_1'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_40, c_493])).
% 5.43/1.99  tff(c_667, plain, (![A_102, B_103]: (m1_subset_1('#skF_1'(A_102, B_103), k1_zfmisc_1(u1_struct_0(A_102))) | v3_tex_2(B_103, A_102) | ~v2_tex_2(B_103, A_102) | ~m1_subset_1(B_103, k1_zfmisc_1(u1_struct_0(A_102))) | ~l1_pre_topc(A_102))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.43/1.99  tff(c_693, plain, (![B_103]: (m1_subset_1('#skF_1'('#skF_3', B_103), k1_zfmisc_1(k2_struct_0('#skF_3'))) | v3_tex_2(B_103, '#skF_3') | ~v2_tex_2(B_103, '#skF_3') | ~m1_subset_1(B_103, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_64, c_667])).
% 5.43/1.99  tff(c_808, plain, (![B_109]: (m1_subset_1('#skF_1'('#skF_3', B_109), k1_zfmisc_1(k2_struct_0('#skF_3'))) | v3_tex_2(B_109, '#skF_3') | ~v2_tex_2(B_109, '#skF_3') | ~m1_subset_1(B_109, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_64, c_693])).
% 5.43/1.99  tff(c_6, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.43/1.99  tff(c_945, plain, (![B_114]: (r1_tarski('#skF_1'('#skF_3', B_114), k2_struct_0('#skF_3')) | v3_tex_2(B_114, '#skF_3') | ~v2_tex_2(B_114, '#skF_3') | ~m1_subset_1(B_114, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(resolution, [status(thm)], [c_808, c_6])).
% 5.43/1.99  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.43/1.99  tff(c_1393, plain, (![B_144]: (k3_xboole_0('#skF_1'('#skF_3', B_144), k2_struct_0('#skF_3'))='#skF_1'('#skF_3', B_144) | v3_tex_2(B_144, '#skF_3') | ~v2_tex_2(B_144, '#skF_3') | ~m1_subset_1(B_144, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(resolution, [status(thm)], [c_945, c_2])).
% 5.43/1.99  tff(c_1405, plain, (k3_xboole_0('#skF_1'('#skF_3', '#skF_4'), k2_struct_0('#skF_3'))='#skF_1'('#skF_3', '#skF_4') | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_65, c_1393])).
% 5.43/1.99  tff(c_1416, plain, (k3_xboole_0('#skF_1'('#skF_3', '#skF_4'), k2_struct_0('#skF_3'))='#skF_1'('#skF_3', '#skF_4') | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1405])).
% 5.43/1.99  tff(c_1417, plain, (k3_xboole_0('#skF_1'('#skF_3', '#skF_4'), k2_struct_0('#skF_3'))='#skF_1'('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_40, c_1416])).
% 5.43/1.99  tff(c_704, plain, (![B_103]: (m1_subset_1('#skF_1'('#skF_3', B_103), k1_zfmisc_1(k2_struct_0('#skF_3'))) | v3_tex_2(B_103, '#skF_3') | ~v2_tex_2(B_103, '#skF_3') | ~m1_subset_1(B_103, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_64, c_693])).
% 5.43/1.99  tff(c_88, plain, (![A_44]: (m1_subset_1(k2_struct_0(A_44), k1_zfmisc_1(u1_struct_0(A_44))) | ~l1_struct_0(A_44))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.43/1.99  tff(c_96, plain, (![A_45]: (r1_tarski(k2_struct_0(A_45), u1_struct_0(A_45)) | ~l1_struct_0(A_45))), inference(resolution, [status(thm)], [c_88, c_6])).
% 5.43/1.99  tff(c_102, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_3')) | ~l1_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_64, c_96])).
% 5.43/1.99  tff(c_104, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_102])).
% 5.43/1.99  tff(c_107, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_14, c_104])).
% 5.43/1.99  tff(c_111, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_107])).
% 5.43/1.99  tff(c_113, plain, (l1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_102])).
% 5.43/1.99  tff(c_94, plain, (m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_64, c_88])).
% 5.43/1.99  tff(c_128, plain, (m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_94])).
% 5.43/1.99  tff(c_134, plain, (![A_46, B_47, C_48]: (k9_subset_1(A_46, B_47, C_48)=k3_xboole_0(B_47, C_48) | ~m1_subset_1(C_48, k1_zfmisc_1(A_46)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.43/1.99  tff(c_143, plain, (![B_47]: (k9_subset_1(k2_struct_0('#skF_3'), B_47, k2_struct_0('#skF_3'))=k3_xboole_0(B_47, k2_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_128, c_134])).
% 5.43/1.99  tff(c_44, plain, (v1_tops_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.43/1.99  tff(c_298, plain, (![A_68, B_69]: (k2_pre_topc(A_68, B_69)=k2_struct_0(A_68) | ~v1_tops_1(B_69, A_68) | ~m1_subset_1(B_69, k1_zfmisc_1(u1_struct_0(A_68))) | ~l1_pre_topc(A_68))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.43/1.99  tff(c_304, plain, (![B_69]: (k2_pre_topc('#skF_3', B_69)=k2_struct_0('#skF_3') | ~v1_tops_1(B_69, '#skF_3') | ~m1_subset_1(B_69, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_64, c_298])).
% 5.43/1.99  tff(c_313, plain, (![B_70]: (k2_pre_topc('#skF_3', B_70)=k2_struct_0('#skF_3') | ~v1_tops_1(B_70, '#skF_3') | ~m1_subset_1(B_70, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_304])).
% 5.43/1.99  tff(c_319, plain, (k2_pre_topc('#skF_3', '#skF_4')=k2_struct_0('#skF_3') | ~v1_tops_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_65, c_313])).
% 5.43/1.99  tff(c_329, plain, (k2_pre_topc('#skF_3', '#skF_4')=k2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_319])).
% 5.43/1.99  tff(c_52, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.43/1.99  tff(c_50, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.43/1.99  tff(c_1374, plain, (![A_141, B_142, C_143]: (k9_subset_1(u1_struct_0(A_141), B_142, k2_pre_topc(A_141, C_143))=C_143 | ~r1_tarski(C_143, B_142) | ~m1_subset_1(C_143, k1_zfmisc_1(u1_struct_0(A_141))) | ~v2_tex_2(B_142, A_141) | ~m1_subset_1(B_142, k1_zfmisc_1(u1_struct_0(A_141))) | ~l1_pre_topc(A_141) | ~v2_pre_topc(A_141) | v2_struct_0(A_141))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.43/1.99  tff(c_1382, plain, (![B_142, C_143]: (k9_subset_1(u1_struct_0('#skF_3'), B_142, k2_pre_topc('#skF_3', C_143))=C_143 | ~r1_tarski(C_143, B_142) | ~m1_subset_1(C_143, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v2_tex_2(B_142, '#skF_3') | ~m1_subset_1(B_142, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_64, c_1374])).
% 5.43/1.99  tff(c_1390, plain, (![B_142, C_143]: (k9_subset_1(k2_struct_0('#skF_3'), B_142, k2_pre_topc('#skF_3', C_143))=C_143 | ~r1_tarski(C_143, B_142) | ~m1_subset_1(C_143, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v2_tex_2(B_142, '#skF_3') | ~m1_subset_1(B_142, k1_zfmisc_1(k2_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_64, c_64, c_1382])).
% 5.43/1.99  tff(c_1423, plain, (![B_145, C_146]: (k9_subset_1(k2_struct_0('#skF_3'), B_145, k2_pre_topc('#skF_3', C_146))=C_146 | ~r1_tarski(C_146, B_145) | ~m1_subset_1(C_146, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v2_tex_2(B_145, '#skF_3') | ~m1_subset_1(B_145, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_52, c_1390])).
% 5.43/1.99  tff(c_1431, plain, (![B_145]: (k9_subset_1(k2_struct_0('#skF_3'), B_145, k2_pre_topc('#skF_3', '#skF_4'))='#skF_4' | ~r1_tarski('#skF_4', B_145) | ~v2_tex_2(B_145, '#skF_3') | ~m1_subset_1(B_145, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(resolution, [status(thm)], [c_65, c_1423])).
% 5.43/1.99  tff(c_1441, plain, (![B_147]: (k3_xboole_0(B_147, k2_struct_0('#skF_3'))='#skF_4' | ~r1_tarski('#skF_4', B_147) | ~v2_tex_2(B_147, '#skF_3') | ~m1_subset_1(B_147, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_143, c_329, c_1431])).
% 5.43/1.99  tff(c_2652, plain, (![B_246]: (k3_xboole_0('#skF_1'('#skF_3', B_246), k2_struct_0('#skF_3'))='#skF_4' | ~r1_tarski('#skF_4', '#skF_1'('#skF_3', B_246)) | ~v2_tex_2('#skF_1'('#skF_3', B_246), '#skF_3') | v3_tex_2(B_246, '#skF_3') | ~v2_tex_2(B_246, '#skF_3') | ~m1_subset_1(B_246, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(resolution, [status(thm)], [c_704, c_1441])).
% 5.43/1.99  tff(c_2664, plain, (k3_xboole_0('#skF_1'('#skF_3', '#skF_4'), k2_struct_0('#skF_3'))='#skF_4' | ~r1_tarski('#skF_4', '#skF_1'('#skF_3', '#skF_4')) | ~v2_tex_2('#skF_1'('#skF_3', '#skF_4'), '#skF_3') | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_65, c_2652])).
% 5.43/1.99  tff(c_2675, plain, ('#skF_1'('#skF_3', '#skF_4')='#skF_4' | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_443, c_494, c_1417, c_2664])).
% 5.43/1.99  tff(c_2677, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_423, c_2675])).
% 5.43/1.99  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.43/1.99  
% 5.43/1.99  Inference rules
% 5.43/1.99  ----------------------
% 5.43/1.99  #Ref     : 0
% 5.43/1.99  #Sup     : 548
% 5.43/1.99  #Fact    : 0
% 5.43/1.99  #Define  : 0
% 5.43/1.99  #Split   : 9
% 5.43/1.99  #Chain   : 0
% 5.43/1.99  #Close   : 0
% 5.43/1.99  
% 5.43/1.99  Ordering : KBO
% 5.43/1.99  
% 5.43/1.99  Simplification rules
% 5.43/1.99  ----------------------
% 5.43/1.99  #Subsume      : 140
% 5.43/1.99  #Demod        : 385
% 5.43/1.99  #Tautology    : 166
% 5.43/1.99  #SimpNegUnit  : 125
% 5.43/1.99  #BackRed      : 1
% 5.43/1.99  
% 5.43/1.99  #Partial instantiations: 0
% 5.43/1.99  #Strategies tried      : 1
% 5.43/1.99  
% 5.43/1.99  Timing (in seconds)
% 5.43/1.99  ----------------------
% 5.43/1.99  Preprocessing        : 0.34
% 5.43/1.99  Parsing              : 0.18
% 5.43/1.99  CNF conversion       : 0.02
% 5.43/1.99  Main loop            : 0.88
% 5.43/1.99  Inferencing          : 0.32
% 5.43/1.99  Reduction            : 0.27
% 5.43/1.99  Demodulation         : 0.18
% 5.43/1.99  BG Simplification    : 0.04
% 5.43/1.99  Subsumption          : 0.18
% 5.43/1.99  Abstraction          : 0.05
% 5.43/1.99  MUC search           : 0.00
% 5.43/1.99  Cooper               : 0.00
% 5.43/1.99  Total                : 1.25
% 5.43/1.99  Index Insertion      : 0.00
% 5.43/1.99  Index Deletion       : 0.00
% 5.43/1.99  Index Matching       : 0.00
% 5.43/1.99  BG Taut test         : 0.00
%------------------------------------------------------------------------------
