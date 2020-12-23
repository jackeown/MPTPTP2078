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

% Result     : Theorem 4.27s
% Output     : CNFRefutation 4.33s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 137 expanded)
%              Number of leaves         :   28 (  64 expanded)
%              Depth                    :   13
%              Number of atoms          :  173 ( 459 expanded)
%              Number of equality atoms :   27 (  35 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tex_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = u1_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_3)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_tex_2)).

tff(c_36,plain,(
    ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_44,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_38,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_270,plain,(
    ! [A_64,B_65] :
      ( '#skF_1'(A_64,B_65) != B_65
      | v3_tex_2(B_65,A_64)
      | ~ v2_tex_2(B_65,A_64)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ l1_pre_topc(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_283,plain,
    ( '#skF_1'('#skF_3','#skF_4') != '#skF_4'
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_270])).

tff(c_292,plain,
    ( '#skF_1'('#skF_3','#skF_4') != '#skF_4'
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_38,c_283])).

tff(c_293,plain,(
    '#skF_1'('#skF_3','#skF_4') != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_292])).

tff(c_372,plain,(
    ! [A_73,B_74] :
      ( v2_tex_2('#skF_1'(A_73,B_74),A_73)
      | v3_tex_2(B_74,A_73)
      | ~ v2_tex_2(B_74,A_73)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ l1_pre_topc(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_381,plain,
    ( v2_tex_2('#skF_1'('#skF_3','#skF_4'),'#skF_3')
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_372])).

tff(c_390,plain,
    ( v2_tex_2('#skF_1'('#skF_3','#skF_4'),'#skF_3')
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_38,c_381])).

tff(c_391,plain,(
    v2_tex_2('#skF_1'('#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_390])).

tff(c_295,plain,(
    ! [B_66,A_67] :
      ( r1_tarski(B_66,'#skF_1'(A_67,B_66))
      | v3_tex_2(B_66,A_67)
      | ~ v2_tex_2(B_66,A_67)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ l1_pre_topc(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_304,plain,
    ( r1_tarski('#skF_4','#skF_1'('#skF_3','#skF_4'))
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_295])).

tff(c_313,plain,
    ( r1_tarski('#skF_4','#skF_1'('#skF_3','#skF_4'))
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_38,c_304])).

tff(c_314,plain,(
    r1_tarski('#skF_4','#skF_1'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_313])).

tff(c_479,plain,(
    ! [A_79,B_80] :
      ( m1_subset_1('#skF_1'(A_79,B_80),k1_zfmisc_1(u1_struct_0(A_79)))
      | v3_tex_2(B_80,A_79)
      | ~ v2_tex_2(B_80,A_79)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ l1_pre_topc(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_748,plain,(
    ! [A_108,B_109] :
      ( r1_tarski('#skF_1'(A_108,B_109),u1_struct_0(A_108))
      | v3_tex_2(B_109,A_108)
      | ~ v2_tex_2(B_109,A_108)
      | ~ m1_subset_1(B_109,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ l1_pre_topc(A_108) ) ),
    inference(resolution,[status(thm)],[c_479,c_6])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_894,plain,(
    ! [A_120,B_121] :
      ( k3_xboole_0('#skF_1'(A_120,B_121),u1_struct_0(A_120)) = '#skF_1'(A_120,B_121)
      | v3_tex_2(B_121,A_120)
      | ~ v2_tex_2(B_121,A_120)
      | ~ m1_subset_1(B_121,k1_zfmisc_1(u1_struct_0(A_120)))
      | ~ l1_pre_topc(A_120) ) ),
    inference(resolution,[status(thm)],[c_748,c_2])).

tff(c_907,plain,
    ( k3_xboole_0('#skF_1'('#skF_3','#skF_4'),u1_struct_0('#skF_3')) = '#skF_1'('#skF_3','#skF_4')
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_894])).

tff(c_918,plain,
    ( k3_xboole_0('#skF_1'('#skF_3','#skF_4'),u1_struct_0('#skF_3')) = '#skF_1'('#skF_3','#skF_4')
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_38,c_907])).

tff(c_919,plain,(
    k3_xboole_0('#skF_1'('#skF_3','#skF_4'),u1_struct_0('#skF_3')) = '#skF_1'('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_918])).

tff(c_22,plain,(
    ! [A_13,B_19] :
      ( m1_subset_1('#skF_1'(A_13,B_19),k1_zfmisc_1(u1_struct_0(A_13)))
      | v3_tex_2(B_19,A_13)
      | ~ v2_tex_2(B_19,A_13)
      | ~ m1_subset_1(B_19,k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_46,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_40,plain,(
    v1_tops_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_132,plain,(
    ! [A_55,B_56] :
      ( k2_pre_topc(A_55,B_56) = u1_struct_0(A_55)
      | ~ v1_tops_1(B_56,A_55)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(u1_struct_0(A_55)))
      | ~ l1_pre_topc(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_142,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = u1_struct_0('#skF_3')
    | ~ v1_tops_1('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_132])).

tff(c_147,plain,(
    k2_pre_topc('#skF_3','#skF_4') = u1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_142])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(k2_pre_topc(A_8,B_9),k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ m1_subset_1(B_9,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_154,plain,
    ( m1_subset_1(u1_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_10])).

tff(c_160,plain,(
    m1_subset_1(u1_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_154])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] :
      ( k9_subset_1(A_3,B_4,C_5) = k3_xboole_0(B_4,C_5)
      | ~ m1_subset_1(C_5,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_192,plain,(
    ! [B_4] : k9_subset_1(u1_struct_0('#skF_3'),B_4,u1_struct_0('#skF_3')) = k3_xboole_0(B_4,u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_160,c_4])).

tff(c_1001,plain,(
    ! [A_130,B_131,C_132] :
      ( k9_subset_1(u1_struct_0(A_130),B_131,k2_pre_topc(A_130,C_132)) = C_132
      | ~ r1_tarski(C_132,B_131)
      | ~ m1_subset_1(C_132,k1_zfmisc_1(u1_struct_0(A_130)))
      | ~ v2_tex_2(B_131,A_130)
      | ~ m1_subset_1(B_131,k1_zfmisc_1(u1_struct_0(A_130)))
      | ~ l1_pre_topc(A_130)
      | ~ v2_pre_topc(A_130)
      | v2_struct_0(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1014,plain,(
    ! [B_131] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_131,k2_pre_topc('#skF_3','#skF_4')) = '#skF_4'
      | ~ r1_tarski('#skF_4',B_131)
      | ~ v2_tex_2(B_131,'#skF_3')
      | ~ m1_subset_1(B_131,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_42,c_1001])).

tff(c_1025,plain,(
    ! [B_131] :
      ( k3_xboole_0(B_131,u1_struct_0('#skF_3')) = '#skF_4'
      | ~ r1_tarski('#skF_4',B_131)
      | ~ v2_tex_2(B_131,'#skF_3')
      | ~ m1_subset_1(B_131,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_192,c_147,c_1014])).

tff(c_1027,plain,(
    ! [B_133] :
      ( k3_xboole_0(B_133,u1_struct_0('#skF_3')) = '#skF_4'
      | ~ r1_tarski('#skF_4',B_133)
      | ~ v2_tex_2(B_133,'#skF_3')
      | ~ m1_subset_1(B_133,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_1025])).

tff(c_1035,plain,(
    ! [B_19] :
      ( k3_xboole_0('#skF_1'('#skF_3',B_19),u1_struct_0('#skF_3')) = '#skF_4'
      | ~ r1_tarski('#skF_4','#skF_1'('#skF_3',B_19))
      | ~ v2_tex_2('#skF_1'('#skF_3',B_19),'#skF_3')
      | v3_tex_2(B_19,'#skF_3')
      | ~ v2_tex_2(B_19,'#skF_3')
      | ~ m1_subset_1(B_19,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_22,c_1027])).

tff(c_1865,plain,(
    ! [B_199] :
      ( k3_xboole_0('#skF_1'('#skF_3',B_199),u1_struct_0('#skF_3')) = '#skF_4'
      | ~ r1_tarski('#skF_4','#skF_1'('#skF_3',B_199))
      | ~ v2_tex_2('#skF_1'('#skF_3',B_199),'#skF_3')
      | v3_tex_2(B_199,'#skF_3')
      | ~ v2_tex_2(B_199,'#skF_3')
      | ~ m1_subset_1(B_199,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1035])).

tff(c_1887,plain,
    ( k3_xboole_0('#skF_1'('#skF_3','#skF_4'),u1_struct_0('#skF_3')) = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_1'('#skF_3','#skF_4'))
    | ~ v2_tex_2('#skF_1'('#skF_3','#skF_4'),'#skF_3')
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_1865])).

tff(c_1903,plain,
    ( '#skF_1'('#skF_3','#skF_4') = '#skF_4'
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_391,c_314,c_919,c_1887])).

tff(c_1905,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_293,c_1903])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:24:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.27/1.78  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.33/1.79  
% 4.33/1.79  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.33/1.79  %$ v3_tex_2 > v2_tex_2 > v1_tops_1 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 4.33/1.79  
% 4.33/1.79  %Foreground sorts:
% 4.33/1.79  
% 4.33/1.79  
% 4.33/1.79  %Background operators:
% 4.33/1.79  
% 4.33/1.79  
% 4.33/1.79  %Foreground operators:
% 4.33/1.79  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.33/1.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.33/1.79  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.33/1.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.33/1.79  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 4.33/1.79  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 4.33/1.79  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 4.33/1.79  tff('#skF_3', type, '#skF_3': $i).
% 4.33/1.79  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.33/1.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.33/1.79  tff('#skF_4', type, '#skF_4': $i).
% 4.33/1.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.33/1.79  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.33/1.79  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.33/1.79  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.33/1.79  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.33/1.79  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.33/1.79  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.33/1.79  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 4.33/1.79  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.33/1.79  
% 4.33/1.81  tff(f_106, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v1_tops_1(B, A) & v2_tex_2(B, A)) => v3_tex_2(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tex_2)).
% 4.33/1.81  tff(f_70, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 4.33/1.81  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.33/1.81  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.33/1.81  tff(f_52, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tops_3)).
% 4.33/1.81  tff(f_43, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 4.33/1.81  tff(f_33, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 4.33/1.81  tff(f_89, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C)) = C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_tex_2)).
% 4.33/1.81  tff(c_36, plain, (~v3_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.33/1.81  tff(c_44, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.33/1.81  tff(c_38, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.33/1.81  tff(c_42, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.33/1.81  tff(c_270, plain, (![A_64, B_65]: ('#skF_1'(A_64, B_65)!=B_65 | v3_tex_2(B_65, A_64) | ~v2_tex_2(B_65, A_64) | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0(A_64))) | ~l1_pre_topc(A_64))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.33/1.81  tff(c_283, plain, ('#skF_1'('#skF_3', '#skF_4')!='#skF_4' | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_42, c_270])).
% 4.33/1.81  tff(c_292, plain, ('#skF_1'('#skF_3', '#skF_4')!='#skF_4' | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_38, c_283])).
% 4.33/1.81  tff(c_293, plain, ('#skF_1'('#skF_3', '#skF_4')!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_36, c_292])).
% 4.33/1.81  tff(c_372, plain, (![A_73, B_74]: (v2_tex_2('#skF_1'(A_73, B_74), A_73) | v3_tex_2(B_74, A_73) | ~v2_tex_2(B_74, A_73) | ~m1_subset_1(B_74, k1_zfmisc_1(u1_struct_0(A_73))) | ~l1_pre_topc(A_73))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.33/1.81  tff(c_381, plain, (v2_tex_2('#skF_1'('#skF_3', '#skF_4'), '#skF_3') | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_42, c_372])).
% 4.33/1.81  tff(c_390, plain, (v2_tex_2('#skF_1'('#skF_3', '#skF_4'), '#skF_3') | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_38, c_381])).
% 4.33/1.81  tff(c_391, plain, (v2_tex_2('#skF_1'('#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_36, c_390])).
% 4.33/1.81  tff(c_295, plain, (![B_66, A_67]: (r1_tarski(B_66, '#skF_1'(A_67, B_66)) | v3_tex_2(B_66, A_67) | ~v2_tex_2(B_66, A_67) | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0(A_67))) | ~l1_pre_topc(A_67))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.33/1.81  tff(c_304, plain, (r1_tarski('#skF_4', '#skF_1'('#skF_3', '#skF_4')) | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_42, c_295])).
% 4.33/1.81  tff(c_313, plain, (r1_tarski('#skF_4', '#skF_1'('#skF_3', '#skF_4')) | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_38, c_304])).
% 4.33/1.81  tff(c_314, plain, (r1_tarski('#skF_4', '#skF_1'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_36, c_313])).
% 4.33/1.81  tff(c_479, plain, (![A_79, B_80]: (m1_subset_1('#skF_1'(A_79, B_80), k1_zfmisc_1(u1_struct_0(A_79))) | v3_tex_2(B_80, A_79) | ~v2_tex_2(B_80, A_79) | ~m1_subset_1(B_80, k1_zfmisc_1(u1_struct_0(A_79))) | ~l1_pre_topc(A_79))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.33/1.81  tff(c_6, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.33/1.81  tff(c_748, plain, (![A_108, B_109]: (r1_tarski('#skF_1'(A_108, B_109), u1_struct_0(A_108)) | v3_tex_2(B_109, A_108) | ~v2_tex_2(B_109, A_108) | ~m1_subset_1(B_109, k1_zfmisc_1(u1_struct_0(A_108))) | ~l1_pre_topc(A_108))), inference(resolution, [status(thm)], [c_479, c_6])).
% 4.33/1.81  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.33/1.81  tff(c_894, plain, (![A_120, B_121]: (k3_xboole_0('#skF_1'(A_120, B_121), u1_struct_0(A_120))='#skF_1'(A_120, B_121) | v3_tex_2(B_121, A_120) | ~v2_tex_2(B_121, A_120) | ~m1_subset_1(B_121, k1_zfmisc_1(u1_struct_0(A_120))) | ~l1_pre_topc(A_120))), inference(resolution, [status(thm)], [c_748, c_2])).
% 4.33/1.81  tff(c_907, plain, (k3_xboole_0('#skF_1'('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))='#skF_1'('#skF_3', '#skF_4') | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_42, c_894])).
% 4.33/1.81  tff(c_918, plain, (k3_xboole_0('#skF_1'('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))='#skF_1'('#skF_3', '#skF_4') | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_38, c_907])).
% 4.33/1.81  tff(c_919, plain, (k3_xboole_0('#skF_1'('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))='#skF_1'('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_36, c_918])).
% 4.33/1.81  tff(c_22, plain, (![A_13, B_19]: (m1_subset_1('#skF_1'(A_13, B_19), k1_zfmisc_1(u1_struct_0(A_13))) | v3_tex_2(B_19, A_13) | ~v2_tex_2(B_19, A_13) | ~m1_subset_1(B_19, k1_zfmisc_1(u1_struct_0(A_13))) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.33/1.81  tff(c_48, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.33/1.81  tff(c_46, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.33/1.81  tff(c_40, plain, (v1_tops_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.33/1.81  tff(c_132, plain, (![A_55, B_56]: (k2_pre_topc(A_55, B_56)=u1_struct_0(A_55) | ~v1_tops_1(B_56, A_55) | ~m1_subset_1(B_56, k1_zfmisc_1(u1_struct_0(A_55))) | ~l1_pre_topc(A_55))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.33/1.81  tff(c_142, plain, (k2_pre_topc('#skF_3', '#skF_4')=u1_struct_0('#skF_3') | ~v1_tops_1('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_42, c_132])).
% 4.33/1.81  tff(c_147, plain, (k2_pre_topc('#skF_3', '#skF_4')=u1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_142])).
% 4.33/1.81  tff(c_10, plain, (![A_8, B_9]: (m1_subset_1(k2_pre_topc(A_8, B_9), k1_zfmisc_1(u1_struct_0(A_8))) | ~m1_subset_1(B_9, k1_zfmisc_1(u1_struct_0(A_8))) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.33/1.81  tff(c_154, plain, (m1_subset_1(u1_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_147, c_10])).
% 4.33/1.81  tff(c_160, plain, (m1_subset_1(u1_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_154])).
% 4.33/1.81  tff(c_4, plain, (![A_3, B_4, C_5]: (k9_subset_1(A_3, B_4, C_5)=k3_xboole_0(B_4, C_5) | ~m1_subset_1(C_5, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.33/1.81  tff(c_192, plain, (![B_4]: (k9_subset_1(u1_struct_0('#skF_3'), B_4, u1_struct_0('#skF_3'))=k3_xboole_0(B_4, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_160, c_4])).
% 4.33/1.81  tff(c_1001, plain, (![A_130, B_131, C_132]: (k9_subset_1(u1_struct_0(A_130), B_131, k2_pre_topc(A_130, C_132))=C_132 | ~r1_tarski(C_132, B_131) | ~m1_subset_1(C_132, k1_zfmisc_1(u1_struct_0(A_130))) | ~v2_tex_2(B_131, A_130) | ~m1_subset_1(B_131, k1_zfmisc_1(u1_struct_0(A_130))) | ~l1_pre_topc(A_130) | ~v2_pre_topc(A_130) | v2_struct_0(A_130))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.33/1.81  tff(c_1014, plain, (![B_131]: (k9_subset_1(u1_struct_0('#skF_3'), B_131, k2_pre_topc('#skF_3', '#skF_4'))='#skF_4' | ~r1_tarski('#skF_4', B_131) | ~v2_tex_2(B_131, '#skF_3') | ~m1_subset_1(B_131, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_42, c_1001])).
% 4.33/1.81  tff(c_1025, plain, (![B_131]: (k3_xboole_0(B_131, u1_struct_0('#skF_3'))='#skF_4' | ~r1_tarski('#skF_4', B_131) | ~v2_tex_2(B_131, '#skF_3') | ~m1_subset_1(B_131, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_192, c_147, c_1014])).
% 4.33/1.81  tff(c_1027, plain, (![B_133]: (k3_xboole_0(B_133, u1_struct_0('#skF_3'))='#skF_4' | ~r1_tarski('#skF_4', B_133) | ~v2_tex_2(B_133, '#skF_3') | ~m1_subset_1(B_133, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_48, c_1025])).
% 4.33/1.81  tff(c_1035, plain, (![B_19]: (k3_xboole_0('#skF_1'('#skF_3', B_19), u1_struct_0('#skF_3'))='#skF_4' | ~r1_tarski('#skF_4', '#skF_1'('#skF_3', B_19)) | ~v2_tex_2('#skF_1'('#skF_3', B_19), '#skF_3') | v3_tex_2(B_19, '#skF_3') | ~v2_tex_2(B_19, '#skF_3') | ~m1_subset_1(B_19, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_22, c_1027])).
% 4.33/1.81  tff(c_1865, plain, (![B_199]: (k3_xboole_0('#skF_1'('#skF_3', B_199), u1_struct_0('#skF_3'))='#skF_4' | ~r1_tarski('#skF_4', '#skF_1'('#skF_3', B_199)) | ~v2_tex_2('#skF_1'('#skF_3', B_199), '#skF_3') | v3_tex_2(B_199, '#skF_3') | ~v2_tex_2(B_199, '#skF_3') | ~m1_subset_1(B_199, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_1035])).
% 4.33/1.81  tff(c_1887, plain, (k3_xboole_0('#skF_1'('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))='#skF_4' | ~r1_tarski('#skF_4', '#skF_1'('#skF_3', '#skF_4')) | ~v2_tex_2('#skF_1'('#skF_3', '#skF_4'), '#skF_3') | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_42, c_1865])).
% 4.33/1.81  tff(c_1903, plain, ('#skF_1'('#skF_3', '#skF_4')='#skF_4' | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_391, c_314, c_919, c_1887])).
% 4.33/1.81  tff(c_1905, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_293, c_1903])).
% 4.33/1.81  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.33/1.81  
% 4.33/1.81  Inference rules
% 4.33/1.81  ----------------------
% 4.33/1.81  #Ref     : 0
% 4.33/1.81  #Sup     : 383
% 4.33/1.81  #Fact    : 0
% 4.33/1.81  #Define  : 0
% 4.33/1.81  #Split   : 11
% 4.33/1.81  #Chain   : 0
% 4.33/1.81  #Close   : 0
% 4.33/1.81  
% 4.33/1.81  Ordering : KBO
% 4.33/1.81  
% 4.33/1.81  Simplification rules
% 4.33/1.81  ----------------------
% 4.33/1.81  #Subsume      : 78
% 4.33/1.81  #Demod        : 317
% 4.33/1.81  #Tautology    : 127
% 4.33/1.81  #SimpNegUnit  : 80
% 4.33/1.81  #BackRed      : 0
% 4.33/1.81  
% 4.33/1.81  #Partial instantiations: 0
% 4.33/1.81  #Strategies tried      : 1
% 4.33/1.81  
% 4.33/1.81  Timing (in seconds)
% 4.33/1.81  ----------------------
% 4.33/1.81  Preprocessing        : 0.33
% 4.33/1.81  Parsing              : 0.18
% 4.33/1.81  CNF conversion       : 0.02
% 4.33/1.81  Main loop            : 0.65
% 4.33/1.81  Inferencing          : 0.23
% 4.33/1.81  Reduction            : 0.20
% 4.33/1.81  Demodulation         : 0.13
% 4.33/1.81  BG Simplification    : 0.03
% 4.33/1.81  Subsumption          : 0.15
% 4.33/1.81  Abstraction          : 0.04
% 4.33/1.81  MUC search           : 0.00
% 4.33/1.81  Cooper               : 0.00
% 4.33/1.81  Total                : 1.02
% 4.33/1.81  Index Insertion      : 0.00
% 4.33/1.81  Index Deletion       : 0.00
% 4.33/1.81  Index Matching       : 0.00
% 4.33/1.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
