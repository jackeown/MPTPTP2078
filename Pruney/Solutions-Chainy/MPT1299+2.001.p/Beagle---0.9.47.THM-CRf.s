%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:44 EST 2020

% Result     : Theorem 3.40s
% Output     : CNFRefutation 3.54s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 135 expanded)
%              Number of leaves         :   20 (  54 expanded)
%              Depth                    :   15
%              Number of atoms          :  183 ( 434 expanded)
%              Number of equality atoms :   28 (  52 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tops_2 > v1_tops_2 > r2_hidden > m1_subset_1 > l1_pre_topc > k7_setfam_1 > k3_subset_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_tops_2,type,(
    v1_tops_2: ( $i * $i ) > $o )).

tff(k7_setfam_1,type,(
    k7_setfam_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v2_tops_2,type,(
    v2_tops_2: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_71,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ( v1_tops_2(B,A)
            <=> v2_tops_2(k7_setfam_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tops_2)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k7_setfam_1(A,B),k1_zfmisc_1(k1_zfmisc_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_setfam_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
         => ( C = k7_setfam_1(A,B)
          <=> ! [D] :
                ( m1_subset_1(D,k1_zfmisc_1(A))
               => ( r2_hidden(D,C)
                <=> r2_hidden(k3_subset_1(A,D),B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_setfam_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r2_hidden(k3_subset_1(A,C),k7_setfam_1(A,B))
          <=> r2_hidden(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_setfam_1)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( v2_tops_2(B,A)
          <=> v1_tops_2(k7_setfam_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tops_2)).

tff(c_26,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(k7_setfam_1(A_12,B_13),k1_zfmisc_1(k1_zfmisc_1(A_12)))
      | ~ m1_subset_1(B_13,k1_zfmisc_1(k1_zfmisc_1(A_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_30,plain,
    ( ~ v2_tops_2(k7_setfam_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | ~ v1_tops_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_37,plain,(
    ~ v1_tops_2('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_28,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_36,plain,
    ( v1_tops_2('#skF_3','#skF_2')
    | v2_tops_2(k7_setfam_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_38,plain,(
    v2_tops_2(k7_setfam_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_37,c_36])).

tff(c_2,plain,(
    ! [A_1,B_2,C_8] :
      ( m1_subset_1('#skF_1'(A_1,B_2,C_8),k1_zfmisc_1(A_1))
      | k7_setfam_1(A_1,B_2) = C_8
      | ~ m1_subset_1(C_8,k1_zfmisc_1(k1_zfmisc_1(A_1)))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(k1_zfmisc_1(A_1))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_100,plain,(
    ! [A_52,B_53,C_54] :
      ( r2_hidden('#skF_1'(A_52,B_53,C_54),C_54)
      | r2_hidden(k3_subset_1(A_52,'#skF_1'(A_52,B_53,C_54)),B_53)
      | k7_setfam_1(A_52,B_53) = C_54
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k1_zfmisc_1(A_52)))
      | ~ m1_subset_1(B_53,k1_zfmisc_1(k1_zfmisc_1(A_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_20,plain,(
    ! [C_17,B_15,A_14] :
      ( r2_hidden(C_17,B_15)
      | ~ r2_hidden(k3_subset_1(A_14,C_17),k7_setfam_1(A_14,B_15))
      | ~ m1_subset_1(C_17,k1_zfmisc_1(A_14))
      | ~ m1_subset_1(B_15,k1_zfmisc_1(k1_zfmisc_1(A_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_279,plain,(
    ! [A_89,B_90,C_91] :
      ( r2_hidden('#skF_1'(A_89,k7_setfam_1(A_89,B_90),C_91),B_90)
      | ~ m1_subset_1('#skF_1'(A_89,k7_setfam_1(A_89,B_90),C_91),k1_zfmisc_1(A_89))
      | ~ m1_subset_1(B_90,k1_zfmisc_1(k1_zfmisc_1(A_89)))
      | r2_hidden('#skF_1'(A_89,k7_setfam_1(A_89,B_90),C_91),C_91)
      | k7_setfam_1(A_89,k7_setfam_1(A_89,B_90)) = C_91
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k1_zfmisc_1(A_89)))
      | ~ m1_subset_1(k7_setfam_1(A_89,B_90),k1_zfmisc_1(k1_zfmisc_1(A_89))) ) ),
    inference(resolution,[status(thm)],[c_100,c_20])).

tff(c_284,plain,(
    ! [A_92,B_93,C_94] :
      ( r2_hidden('#skF_1'(A_92,k7_setfam_1(A_92,B_93),C_94),B_93)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(k1_zfmisc_1(A_92)))
      | r2_hidden('#skF_1'(A_92,k7_setfam_1(A_92,B_93),C_94),C_94)
      | k7_setfam_1(A_92,k7_setfam_1(A_92,B_93)) = C_94
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k1_zfmisc_1(A_92)))
      | ~ m1_subset_1(k7_setfam_1(A_92,B_93),k1_zfmisc_1(k1_zfmisc_1(A_92))) ) ),
    inference(resolution,[status(thm)],[c_2,c_279])).

tff(c_287,plain,(
    ! [A_12,B_13,C_94] :
      ( r2_hidden('#skF_1'(A_12,k7_setfam_1(A_12,B_13),C_94),B_13)
      | r2_hidden('#skF_1'(A_12,k7_setfam_1(A_12,B_13),C_94),C_94)
      | k7_setfam_1(A_12,k7_setfam_1(A_12,B_13)) = C_94
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k1_zfmisc_1(A_12)))
      | ~ m1_subset_1(B_13,k1_zfmisc_1(k1_zfmisc_1(A_12))) ) ),
    inference(resolution,[status(thm)],[c_16,c_284])).

tff(c_300,plain,(
    ! [A_12,B_13] :
      ( k7_setfam_1(A_12,k7_setfam_1(A_12,B_13)) = B_13
      | ~ m1_subset_1(B_13,k1_zfmisc_1(k1_zfmisc_1(A_12)))
      | r2_hidden('#skF_1'(A_12,k7_setfam_1(A_12,B_13),B_13),B_13) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_287])).

tff(c_341,plain,(
    ! [A_101,B_102] :
      ( k7_setfam_1(A_101,k7_setfam_1(A_101,B_102)) = B_102
      | ~ m1_subset_1(B_102,k1_zfmisc_1(k1_zfmisc_1(A_101)))
      | r2_hidden('#skF_1'(A_101,k7_setfam_1(A_101,B_102),B_102),B_102) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_287])).

tff(c_18,plain,(
    ! [A_14,C_17,B_15] :
      ( r2_hidden(k3_subset_1(A_14,C_17),k7_setfam_1(A_14,B_15))
      | ~ r2_hidden(C_17,B_15)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(A_14))
      | ~ m1_subset_1(B_15,k1_zfmisc_1(k1_zfmisc_1(A_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_130,plain,(
    ! [A_58,B_59,C_60] :
      ( ~ r2_hidden(k3_subset_1(A_58,'#skF_1'(A_58,B_59,C_60)),B_59)
      | ~ r2_hidden('#skF_1'(A_58,B_59,C_60),C_60)
      | k7_setfam_1(A_58,B_59) = C_60
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k1_zfmisc_1(A_58)))
      | ~ m1_subset_1(B_59,k1_zfmisc_1(k1_zfmisc_1(A_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_147,plain,(
    ! [A_14,B_15,C_60] :
      ( ~ r2_hidden('#skF_1'(A_14,k7_setfam_1(A_14,B_15),C_60),C_60)
      | k7_setfam_1(A_14,k7_setfam_1(A_14,B_15)) = C_60
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k1_zfmisc_1(A_14)))
      | ~ m1_subset_1(k7_setfam_1(A_14,B_15),k1_zfmisc_1(k1_zfmisc_1(A_14)))
      | ~ r2_hidden('#skF_1'(A_14,k7_setfam_1(A_14,B_15),C_60),B_15)
      | ~ m1_subset_1('#skF_1'(A_14,k7_setfam_1(A_14,B_15),C_60),k1_zfmisc_1(A_14))
      | ~ m1_subset_1(B_15,k1_zfmisc_1(k1_zfmisc_1(A_14))) ) ),
    inference(resolution,[status(thm)],[c_18,c_130])).

tff(c_355,plain,(
    ! [A_103,B_104] :
      ( ~ m1_subset_1(k7_setfam_1(A_103,B_104),k1_zfmisc_1(k1_zfmisc_1(A_103)))
      | ~ r2_hidden('#skF_1'(A_103,k7_setfam_1(A_103,B_104),B_104),B_104)
      | ~ m1_subset_1('#skF_1'(A_103,k7_setfam_1(A_103,B_104),B_104),k1_zfmisc_1(A_103))
      | k7_setfam_1(A_103,k7_setfam_1(A_103,B_104)) = B_104
      | ~ m1_subset_1(B_104,k1_zfmisc_1(k1_zfmisc_1(A_103))) ) ),
    inference(resolution,[status(thm)],[c_341,c_147])).

tff(c_372,plain,(
    ! [A_109,B_110] :
      ( ~ m1_subset_1(k7_setfam_1(A_109,B_110),k1_zfmisc_1(k1_zfmisc_1(A_109)))
      | ~ m1_subset_1('#skF_1'(A_109,k7_setfam_1(A_109,B_110),B_110),k1_zfmisc_1(A_109))
      | k7_setfam_1(A_109,k7_setfam_1(A_109,B_110)) = B_110
      | ~ m1_subset_1(B_110,k1_zfmisc_1(k1_zfmisc_1(A_109))) ) ),
    inference(resolution,[status(thm)],[c_300,c_355])).

tff(c_378,plain,(
    ! [A_111,C_112] :
      ( k7_setfam_1(A_111,k7_setfam_1(A_111,C_112)) = C_112
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k1_zfmisc_1(A_111)))
      | ~ m1_subset_1(k7_setfam_1(A_111,C_112),k1_zfmisc_1(k1_zfmisc_1(A_111))) ) ),
    inference(resolution,[status(thm)],[c_2,c_372])).

tff(c_383,plain,(
    ! [A_113,B_114] :
      ( k7_setfam_1(A_113,k7_setfam_1(A_113,B_114)) = B_114
      | ~ m1_subset_1(B_114,k1_zfmisc_1(k1_zfmisc_1(A_113))) ) ),
    inference(resolution,[status(thm)],[c_16,c_378])).

tff(c_393,plain,(
    k7_setfam_1(u1_struct_0('#skF_2'),k7_setfam_1(u1_struct_0('#skF_2'),'#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_26,c_383])).

tff(c_41,plain,(
    ! [A_26,B_27] :
      ( v1_tops_2(k7_setfam_1(u1_struct_0(A_26),B_27),A_26)
      | ~ v2_tops_2(B_27,A_26)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_26))))
      | ~ l1_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_47,plain,(
    ! [A_26,B_13] :
      ( v1_tops_2(k7_setfam_1(u1_struct_0(A_26),k7_setfam_1(u1_struct_0(A_26),B_13)),A_26)
      | ~ v2_tops_2(k7_setfam_1(u1_struct_0(A_26),B_13),A_26)
      | ~ l1_pre_topc(A_26)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_26)))) ) ),
    inference(resolution,[status(thm)],[c_16,c_41])).

tff(c_440,plain,
    ( v1_tops_2('#skF_3','#skF_2')
    | ~ v2_tops_2(k7_setfam_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_393,c_47])).

tff(c_477,plain,(
    v1_tops_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_38,c_440])).

tff(c_479,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_37,c_477])).

tff(c_480,plain,(
    ~ v2_tops_2(k7_setfam_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_481,plain,(
    v1_tops_2('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_556,plain,(
    ! [A_148,B_149,C_150] :
      ( r2_hidden('#skF_1'(A_148,B_149,C_150),C_150)
      | r2_hidden(k3_subset_1(A_148,'#skF_1'(A_148,B_149,C_150)),B_149)
      | k7_setfam_1(A_148,B_149) = C_150
      | ~ m1_subset_1(C_150,k1_zfmisc_1(k1_zfmisc_1(A_148)))
      | ~ m1_subset_1(B_149,k1_zfmisc_1(k1_zfmisc_1(A_148))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_717,plain,(
    ! [A_180,B_181,C_182] :
      ( r2_hidden('#skF_1'(A_180,k7_setfam_1(A_180,B_181),C_182),B_181)
      | ~ m1_subset_1('#skF_1'(A_180,k7_setfam_1(A_180,B_181),C_182),k1_zfmisc_1(A_180))
      | ~ m1_subset_1(B_181,k1_zfmisc_1(k1_zfmisc_1(A_180)))
      | r2_hidden('#skF_1'(A_180,k7_setfam_1(A_180,B_181),C_182),C_182)
      | k7_setfam_1(A_180,k7_setfam_1(A_180,B_181)) = C_182
      | ~ m1_subset_1(C_182,k1_zfmisc_1(k1_zfmisc_1(A_180)))
      | ~ m1_subset_1(k7_setfam_1(A_180,B_181),k1_zfmisc_1(k1_zfmisc_1(A_180))) ) ),
    inference(resolution,[status(thm)],[c_556,c_20])).

tff(c_722,plain,(
    ! [A_183,B_184,C_185] :
      ( r2_hidden('#skF_1'(A_183,k7_setfam_1(A_183,B_184),C_185),B_184)
      | ~ m1_subset_1(B_184,k1_zfmisc_1(k1_zfmisc_1(A_183)))
      | r2_hidden('#skF_1'(A_183,k7_setfam_1(A_183,B_184),C_185),C_185)
      | k7_setfam_1(A_183,k7_setfam_1(A_183,B_184)) = C_185
      | ~ m1_subset_1(C_185,k1_zfmisc_1(k1_zfmisc_1(A_183)))
      | ~ m1_subset_1(k7_setfam_1(A_183,B_184),k1_zfmisc_1(k1_zfmisc_1(A_183))) ) ),
    inference(resolution,[status(thm)],[c_2,c_717])).

tff(c_725,plain,(
    ! [A_12,B_13,C_185] :
      ( r2_hidden('#skF_1'(A_12,k7_setfam_1(A_12,B_13),C_185),B_13)
      | r2_hidden('#skF_1'(A_12,k7_setfam_1(A_12,B_13),C_185),C_185)
      | k7_setfam_1(A_12,k7_setfam_1(A_12,B_13)) = C_185
      | ~ m1_subset_1(C_185,k1_zfmisc_1(k1_zfmisc_1(A_12)))
      | ~ m1_subset_1(B_13,k1_zfmisc_1(k1_zfmisc_1(A_12))) ) ),
    inference(resolution,[status(thm)],[c_16,c_722])).

tff(c_752,plain,(
    ! [A_12,B_13] :
      ( k7_setfam_1(A_12,k7_setfam_1(A_12,B_13)) = B_13
      | ~ m1_subset_1(B_13,k1_zfmisc_1(k1_zfmisc_1(A_12)))
      | r2_hidden('#skF_1'(A_12,k7_setfam_1(A_12,B_13),B_13),B_13) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_725])).

tff(c_779,plain,(
    ! [A_192,B_193] :
      ( k7_setfam_1(A_192,k7_setfam_1(A_192,B_193)) = B_193
      | ~ m1_subset_1(B_193,k1_zfmisc_1(k1_zfmisc_1(A_192)))
      | r2_hidden('#skF_1'(A_192,k7_setfam_1(A_192,B_193),B_193),B_193) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_725])).

tff(c_575,plain,(
    ! [A_151,B_152,C_153] :
      ( ~ r2_hidden(k3_subset_1(A_151,'#skF_1'(A_151,B_152,C_153)),B_152)
      | ~ r2_hidden('#skF_1'(A_151,B_152,C_153),C_153)
      | k7_setfam_1(A_151,B_152) = C_153
      | ~ m1_subset_1(C_153,k1_zfmisc_1(k1_zfmisc_1(A_151)))
      | ~ m1_subset_1(B_152,k1_zfmisc_1(k1_zfmisc_1(A_151))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_592,plain,(
    ! [A_14,B_15,C_153] :
      ( ~ r2_hidden('#skF_1'(A_14,k7_setfam_1(A_14,B_15),C_153),C_153)
      | k7_setfam_1(A_14,k7_setfam_1(A_14,B_15)) = C_153
      | ~ m1_subset_1(C_153,k1_zfmisc_1(k1_zfmisc_1(A_14)))
      | ~ m1_subset_1(k7_setfam_1(A_14,B_15),k1_zfmisc_1(k1_zfmisc_1(A_14)))
      | ~ r2_hidden('#skF_1'(A_14,k7_setfam_1(A_14,B_15),C_153),B_15)
      | ~ m1_subset_1('#skF_1'(A_14,k7_setfam_1(A_14,B_15),C_153),k1_zfmisc_1(A_14))
      | ~ m1_subset_1(B_15,k1_zfmisc_1(k1_zfmisc_1(A_14))) ) ),
    inference(resolution,[status(thm)],[c_18,c_575])).

tff(c_800,plain,(
    ! [A_196,B_197] :
      ( ~ m1_subset_1(k7_setfam_1(A_196,B_197),k1_zfmisc_1(k1_zfmisc_1(A_196)))
      | ~ r2_hidden('#skF_1'(A_196,k7_setfam_1(A_196,B_197),B_197),B_197)
      | ~ m1_subset_1('#skF_1'(A_196,k7_setfam_1(A_196,B_197),B_197),k1_zfmisc_1(A_196))
      | k7_setfam_1(A_196,k7_setfam_1(A_196,B_197)) = B_197
      | ~ m1_subset_1(B_197,k1_zfmisc_1(k1_zfmisc_1(A_196))) ) ),
    inference(resolution,[status(thm)],[c_779,c_592])).

tff(c_812,plain,(
    ! [A_198,B_199] :
      ( ~ m1_subset_1(k7_setfam_1(A_198,B_199),k1_zfmisc_1(k1_zfmisc_1(A_198)))
      | ~ m1_subset_1('#skF_1'(A_198,k7_setfam_1(A_198,B_199),B_199),k1_zfmisc_1(A_198))
      | k7_setfam_1(A_198,k7_setfam_1(A_198,B_199)) = B_199
      | ~ m1_subset_1(B_199,k1_zfmisc_1(k1_zfmisc_1(A_198))) ) ),
    inference(resolution,[status(thm)],[c_752,c_800])).

tff(c_818,plain,(
    ! [A_200,C_201] :
      ( k7_setfam_1(A_200,k7_setfam_1(A_200,C_201)) = C_201
      | ~ m1_subset_1(C_201,k1_zfmisc_1(k1_zfmisc_1(A_200)))
      | ~ m1_subset_1(k7_setfam_1(A_200,C_201),k1_zfmisc_1(k1_zfmisc_1(A_200))) ) ),
    inference(resolution,[status(thm)],[c_2,c_812])).

tff(c_823,plain,(
    ! [A_202,B_203] :
      ( k7_setfam_1(A_202,k7_setfam_1(A_202,B_203)) = B_203
      | ~ m1_subset_1(B_203,k1_zfmisc_1(k1_zfmisc_1(A_202))) ) ),
    inference(resolution,[status(thm)],[c_16,c_818])).

tff(c_833,plain,(
    k7_setfam_1(u1_struct_0('#skF_2'),k7_setfam_1(u1_struct_0('#skF_2'),'#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_26,c_823])).

tff(c_22,plain,(
    ! [B_20,A_18] :
      ( v2_tops_2(B_20,A_18)
      | ~ v1_tops_2(k7_setfam_1(u1_struct_0(A_18),B_20),A_18)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_18))))
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_884,plain,
    ( v2_tops_2(k7_setfam_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | ~ v1_tops_2('#skF_3','#skF_2')
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_833,c_22])).

tff(c_912,plain,
    ( v2_tops_2(k7_setfam_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_481,c_884])).

tff(c_913,plain,(
    ~ m1_subset_1(k7_setfam_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(negUnitSimplification,[status(thm)],[c_480,c_912])).

tff(c_940,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(resolution,[status(thm)],[c_16,c_913])).

tff(c_944,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_940])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:04:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.40/1.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.40/1.53  
% 3.40/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.40/1.53  %$ v2_tops_2 > v1_tops_2 > r2_hidden > m1_subset_1 > l1_pre_topc > k7_setfam_1 > k3_subset_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3
% 3.40/1.53  
% 3.40/1.53  %Foreground sorts:
% 3.40/1.53  
% 3.40/1.53  
% 3.40/1.53  %Background operators:
% 3.40/1.53  
% 3.40/1.53  
% 3.40/1.53  %Foreground operators:
% 3.40/1.53  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.40/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.40/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.40/1.53  tff(v1_tops_2, type, v1_tops_2: ($i * $i) > $o).
% 3.40/1.53  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 3.40/1.53  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.40/1.53  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.40/1.53  tff('#skF_2', type, '#skF_2': $i).
% 3.40/1.53  tff('#skF_3', type, '#skF_3': $i).
% 3.40/1.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.40/1.53  tff(v2_tops_2, type, v2_tops_2: ($i * $i) > $o).
% 3.40/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.40/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.40/1.53  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.40/1.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.40/1.53  
% 3.54/1.54  tff(f_71, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) <=> v2_tops_2(k7_setfam_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_tops_2)).
% 3.54/1.54  tff(f_43, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k7_setfam_1(A, B), k1_zfmisc_1(k1_zfmisc_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_setfam_1)).
% 3.54/1.54  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => ((C = k7_setfam_1(A, B)) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (r2_hidden(D, C) <=> r2_hidden(k3_subset_1(A, D), B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_setfam_1)).
% 3.54/1.54  tff(f_52, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r2_hidden(k3_subset_1(A, C), k7_setfam_1(A, B)) <=> r2_hidden(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_setfam_1)).
% 3.54/1.55  tff(f_61, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v2_tops_2(B, A) <=> v1_tops_2(k7_setfam_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_tops_2)).
% 3.54/1.55  tff(c_26, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.54/1.55  tff(c_16, plain, (![A_12, B_13]: (m1_subset_1(k7_setfam_1(A_12, B_13), k1_zfmisc_1(k1_zfmisc_1(A_12))) | ~m1_subset_1(B_13, k1_zfmisc_1(k1_zfmisc_1(A_12))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.54/1.55  tff(c_30, plain, (~v2_tops_2(k7_setfam_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~v1_tops_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.54/1.55  tff(c_37, plain, (~v1_tops_2('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_30])).
% 3.54/1.55  tff(c_28, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.54/1.55  tff(c_36, plain, (v1_tops_2('#skF_3', '#skF_2') | v2_tops_2(k7_setfam_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.54/1.55  tff(c_38, plain, (v2_tops_2(k7_setfam_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_37, c_36])).
% 3.54/1.55  tff(c_2, plain, (![A_1, B_2, C_8]: (m1_subset_1('#skF_1'(A_1, B_2, C_8), k1_zfmisc_1(A_1)) | k7_setfam_1(A_1, B_2)=C_8 | ~m1_subset_1(C_8, k1_zfmisc_1(k1_zfmisc_1(A_1))) | ~m1_subset_1(B_2, k1_zfmisc_1(k1_zfmisc_1(A_1))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.54/1.55  tff(c_100, plain, (![A_52, B_53, C_54]: (r2_hidden('#skF_1'(A_52, B_53, C_54), C_54) | r2_hidden(k3_subset_1(A_52, '#skF_1'(A_52, B_53, C_54)), B_53) | k7_setfam_1(A_52, B_53)=C_54 | ~m1_subset_1(C_54, k1_zfmisc_1(k1_zfmisc_1(A_52))) | ~m1_subset_1(B_53, k1_zfmisc_1(k1_zfmisc_1(A_52))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.54/1.55  tff(c_20, plain, (![C_17, B_15, A_14]: (r2_hidden(C_17, B_15) | ~r2_hidden(k3_subset_1(A_14, C_17), k7_setfam_1(A_14, B_15)) | ~m1_subset_1(C_17, k1_zfmisc_1(A_14)) | ~m1_subset_1(B_15, k1_zfmisc_1(k1_zfmisc_1(A_14))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.54/1.55  tff(c_279, plain, (![A_89, B_90, C_91]: (r2_hidden('#skF_1'(A_89, k7_setfam_1(A_89, B_90), C_91), B_90) | ~m1_subset_1('#skF_1'(A_89, k7_setfam_1(A_89, B_90), C_91), k1_zfmisc_1(A_89)) | ~m1_subset_1(B_90, k1_zfmisc_1(k1_zfmisc_1(A_89))) | r2_hidden('#skF_1'(A_89, k7_setfam_1(A_89, B_90), C_91), C_91) | k7_setfam_1(A_89, k7_setfam_1(A_89, B_90))=C_91 | ~m1_subset_1(C_91, k1_zfmisc_1(k1_zfmisc_1(A_89))) | ~m1_subset_1(k7_setfam_1(A_89, B_90), k1_zfmisc_1(k1_zfmisc_1(A_89))))), inference(resolution, [status(thm)], [c_100, c_20])).
% 3.54/1.55  tff(c_284, plain, (![A_92, B_93, C_94]: (r2_hidden('#skF_1'(A_92, k7_setfam_1(A_92, B_93), C_94), B_93) | ~m1_subset_1(B_93, k1_zfmisc_1(k1_zfmisc_1(A_92))) | r2_hidden('#skF_1'(A_92, k7_setfam_1(A_92, B_93), C_94), C_94) | k7_setfam_1(A_92, k7_setfam_1(A_92, B_93))=C_94 | ~m1_subset_1(C_94, k1_zfmisc_1(k1_zfmisc_1(A_92))) | ~m1_subset_1(k7_setfam_1(A_92, B_93), k1_zfmisc_1(k1_zfmisc_1(A_92))))), inference(resolution, [status(thm)], [c_2, c_279])).
% 3.54/1.55  tff(c_287, plain, (![A_12, B_13, C_94]: (r2_hidden('#skF_1'(A_12, k7_setfam_1(A_12, B_13), C_94), B_13) | r2_hidden('#skF_1'(A_12, k7_setfam_1(A_12, B_13), C_94), C_94) | k7_setfam_1(A_12, k7_setfam_1(A_12, B_13))=C_94 | ~m1_subset_1(C_94, k1_zfmisc_1(k1_zfmisc_1(A_12))) | ~m1_subset_1(B_13, k1_zfmisc_1(k1_zfmisc_1(A_12))))), inference(resolution, [status(thm)], [c_16, c_284])).
% 3.54/1.55  tff(c_300, plain, (![A_12, B_13]: (k7_setfam_1(A_12, k7_setfam_1(A_12, B_13))=B_13 | ~m1_subset_1(B_13, k1_zfmisc_1(k1_zfmisc_1(A_12))) | r2_hidden('#skF_1'(A_12, k7_setfam_1(A_12, B_13), B_13), B_13))), inference(factorization, [status(thm), theory('equality')], [c_287])).
% 3.54/1.55  tff(c_341, plain, (![A_101, B_102]: (k7_setfam_1(A_101, k7_setfam_1(A_101, B_102))=B_102 | ~m1_subset_1(B_102, k1_zfmisc_1(k1_zfmisc_1(A_101))) | r2_hidden('#skF_1'(A_101, k7_setfam_1(A_101, B_102), B_102), B_102))), inference(factorization, [status(thm), theory('equality')], [c_287])).
% 3.54/1.55  tff(c_18, plain, (![A_14, C_17, B_15]: (r2_hidden(k3_subset_1(A_14, C_17), k7_setfam_1(A_14, B_15)) | ~r2_hidden(C_17, B_15) | ~m1_subset_1(C_17, k1_zfmisc_1(A_14)) | ~m1_subset_1(B_15, k1_zfmisc_1(k1_zfmisc_1(A_14))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.54/1.55  tff(c_130, plain, (![A_58, B_59, C_60]: (~r2_hidden(k3_subset_1(A_58, '#skF_1'(A_58, B_59, C_60)), B_59) | ~r2_hidden('#skF_1'(A_58, B_59, C_60), C_60) | k7_setfam_1(A_58, B_59)=C_60 | ~m1_subset_1(C_60, k1_zfmisc_1(k1_zfmisc_1(A_58))) | ~m1_subset_1(B_59, k1_zfmisc_1(k1_zfmisc_1(A_58))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.54/1.55  tff(c_147, plain, (![A_14, B_15, C_60]: (~r2_hidden('#skF_1'(A_14, k7_setfam_1(A_14, B_15), C_60), C_60) | k7_setfam_1(A_14, k7_setfam_1(A_14, B_15))=C_60 | ~m1_subset_1(C_60, k1_zfmisc_1(k1_zfmisc_1(A_14))) | ~m1_subset_1(k7_setfam_1(A_14, B_15), k1_zfmisc_1(k1_zfmisc_1(A_14))) | ~r2_hidden('#skF_1'(A_14, k7_setfam_1(A_14, B_15), C_60), B_15) | ~m1_subset_1('#skF_1'(A_14, k7_setfam_1(A_14, B_15), C_60), k1_zfmisc_1(A_14)) | ~m1_subset_1(B_15, k1_zfmisc_1(k1_zfmisc_1(A_14))))), inference(resolution, [status(thm)], [c_18, c_130])).
% 3.54/1.55  tff(c_355, plain, (![A_103, B_104]: (~m1_subset_1(k7_setfam_1(A_103, B_104), k1_zfmisc_1(k1_zfmisc_1(A_103))) | ~r2_hidden('#skF_1'(A_103, k7_setfam_1(A_103, B_104), B_104), B_104) | ~m1_subset_1('#skF_1'(A_103, k7_setfam_1(A_103, B_104), B_104), k1_zfmisc_1(A_103)) | k7_setfam_1(A_103, k7_setfam_1(A_103, B_104))=B_104 | ~m1_subset_1(B_104, k1_zfmisc_1(k1_zfmisc_1(A_103))))), inference(resolution, [status(thm)], [c_341, c_147])).
% 3.54/1.55  tff(c_372, plain, (![A_109, B_110]: (~m1_subset_1(k7_setfam_1(A_109, B_110), k1_zfmisc_1(k1_zfmisc_1(A_109))) | ~m1_subset_1('#skF_1'(A_109, k7_setfam_1(A_109, B_110), B_110), k1_zfmisc_1(A_109)) | k7_setfam_1(A_109, k7_setfam_1(A_109, B_110))=B_110 | ~m1_subset_1(B_110, k1_zfmisc_1(k1_zfmisc_1(A_109))))), inference(resolution, [status(thm)], [c_300, c_355])).
% 3.54/1.55  tff(c_378, plain, (![A_111, C_112]: (k7_setfam_1(A_111, k7_setfam_1(A_111, C_112))=C_112 | ~m1_subset_1(C_112, k1_zfmisc_1(k1_zfmisc_1(A_111))) | ~m1_subset_1(k7_setfam_1(A_111, C_112), k1_zfmisc_1(k1_zfmisc_1(A_111))))), inference(resolution, [status(thm)], [c_2, c_372])).
% 3.54/1.55  tff(c_383, plain, (![A_113, B_114]: (k7_setfam_1(A_113, k7_setfam_1(A_113, B_114))=B_114 | ~m1_subset_1(B_114, k1_zfmisc_1(k1_zfmisc_1(A_113))))), inference(resolution, [status(thm)], [c_16, c_378])).
% 3.54/1.55  tff(c_393, plain, (k7_setfam_1(u1_struct_0('#skF_2'), k7_setfam_1(u1_struct_0('#skF_2'), '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_26, c_383])).
% 3.54/1.55  tff(c_41, plain, (![A_26, B_27]: (v1_tops_2(k7_setfam_1(u1_struct_0(A_26), B_27), A_26) | ~v2_tops_2(B_27, A_26) | ~m1_subset_1(B_27, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_26)))) | ~l1_pre_topc(A_26))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.54/1.55  tff(c_47, plain, (![A_26, B_13]: (v1_tops_2(k7_setfam_1(u1_struct_0(A_26), k7_setfam_1(u1_struct_0(A_26), B_13)), A_26) | ~v2_tops_2(k7_setfam_1(u1_struct_0(A_26), B_13), A_26) | ~l1_pre_topc(A_26) | ~m1_subset_1(B_13, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_26)))))), inference(resolution, [status(thm)], [c_16, c_41])).
% 3.54/1.55  tff(c_440, plain, (v1_tops_2('#skF_3', '#skF_2') | ~v2_tops_2(k7_setfam_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_393, c_47])).
% 3.54/1.55  tff(c_477, plain, (v1_tops_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_28, c_38, c_440])).
% 3.54/1.55  tff(c_479, plain, $false, inference(negUnitSimplification, [status(thm)], [c_37, c_477])).
% 3.54/1.55  tff(c_480, plain, (~v2_tops_2(k7_setfam_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_30])).
% 3.54/1.55  tff(c_481, plain, (v1_tops_2('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_30])).
% 3.54/1.55  tff(c_556, plain, (![A_148, B_149, C_150]: (r2_hidden('#skF_1'(A_148, B_149, C_150), C_150) | r2_hidden(k3_subset_1(A_148, '#skF_1'(A_148, B_149, C_150)), B_149) | k7_setfam_1(A_148, B_149)=C_150 | ~m1_subset_1(C_150, k1_zfmisc_1(k1_zfmisc_1(A_148))) | ~m1_subset_1(B_149, k1_zfmisc_1(k1_zfmisc_1(A_148))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.54/1.55  tff(c_717, plain, (![A_180, B_181, C_182]: (r2_hidden('#skF_1'(A_180, k7_setfam_1(A_180, B_181), C_182), B_181) | ~m1_subset_1('#skF_1'(A_180, k7_setfam_1(A_180, B_181), C_182), k1_zfmisc_1(A_180)) | ~m1_subset_1(B_181, k1_zfmisc_1(k1_zfmisc_1(A_180))) | r2_hidden('#skF_1'(A_180, k7_setfam_1(A_180, B_181), C_182), C_182) | k7_setfam_1(A_180, k7_setfam_1(A_180, B_181))=C_182 | ~m1_subset_1(C_182, k1_zfmisc_1(k1_zfmisc_1(A_180))) | ~m1_subset_1(k7_setfam_1(A_180, B_181), k1_zfmisc_1(k1_zfmisc_1(A_180))))), inference(resolution, [status(thm)], [c_556, c_20])).
% 3.54/1.55  tff(c_722, plain, (![A_183, B_184, C_185]: (r2_hidden('#skF_1'(A_183, k7_setfam_1(A_183, B_184), C_185), B_184) | ~m1_subset_1(B_184, k1_zfmisc_1(k1_zfmisc_1(A_183))) | r2_hidden('#skF_1'(A_183, k7_setfam_1(A_183, B_184), C_185), C_185) | k7_setfam_1(A_183, k7_setfam_1(A_183, B_184))=C_185 | ~m1_subset_1(C_185, k1_zfmisc_1(k1_zfmisc_1(A_183))) | ~m1_subset_1(k7_setfam_1(A_183, B_184), k1_zfmisc_1(k1_zfmisc_1(A_183))))), inference(resolution, [status(thm)], [c_2, c_717])).
% 3.54/1.55  tff(c_725, plain, (![A_12, B_13, C_185]: (r2_hidden('#skF_1'(A_12, k7_setfam_1(A_12, B_13), C_185), B_13) | r2_hidden('#skF_1'(A_12, k7_setfam_1(A_12, B_13), C_185), C_185) | k7_setfam_1(A_12, k7_setfam_1(A_12, B_13))=C_185 | ~m1_subset_1(C_185, k1_zfmisc_1(k1_zfmisc_1(A_12))) | ~m1_subset_1(B_13, k1_zfmisc_1(k1_zfmisc_1(A_12))))), inference(resolution, [status(thm)], [c_16, c_722])).
% 3.54/1.55  tff(c_752, plain, (![A_12, B_13]: (k7_setfam_1(A_12, k7_setfam_1(A_12, B_13))=B_13 | ~m1_subset_1(B_13, k1_zfmisc_1(k1_zfmisc_1(A_12))) | r2_hidden('#skF_1'(A_12, k7_setfam_1(A_12, B_13), B_13), B_13))), inference(factorization, [status(thm), theory('equality')], [c_725])).
% 3.54/1.55  tff(c_779, plain, (![A_192, B_193]: (k7_setfam_1(A_192, k7_setfam_1(A_192, B_193))=B_193 | ~m1_subset_1(B_193, k1_zfmisc_1(k1_zfmisc_1(A_192))) | r2_hidden('#skF_1'(A_192, k7_setfam_1(A_192, B_193), B_193), B_193))), inference(factorization, [status(thm), theory('equality')], [c_725])).
% 3.54/1.55  tff(c_575, plain, (![A_151, B_152, C_153]: (~r2_hidden(k3_subset_1(A_151, '#skF_1'(A_151, B_152, C_153)), B_152) | ~r2_hidden('#skF_1'(A_151, B_152, C_153), C_153) | k7_setfam_1(A_151, B_152)=C_153 | ~m1_subset_1(C_153, k1_zfmisc_1(k1_zfmisc_1(A_151))) | ~m1_subset_1(B_152, k1_zfmisc_1(k1_zfmisc_1(A_151))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.54/1.55  tff(c_592, plain, (![A_14, B_15, C_153]: (~r2_hidden('#skF_1'(A_14, k7_setfam_1(A_14, B_15), C_153), C_153) | k7_setfam_1(A_14, k7_setfam_1(A_14, B_15))=C_153 | ~m1_subset_1(C_153, k1_zfmisc_1(k1_zfmisc_1(A_14))) | ~m1_subset_1(k7_setfam_1(A_14, B_15), k1_zfmisc_1(k1_zfmisc_1(A_14))) | ~r2_hidden('#skF_1'(A_14, k7_setfam_1(A_14, B_15), C_153), B_15) | ~m1_subset_1('#skF_1'(A_14, k7_setfam_1(A_14, B_15), C_153), k1_zfmisc_1(A_14)) | ~m1_subset_1(B_15, k1_zfmisc_1(k1_zfmisc_1(A_14))))), inference(resolution, [status(thm)], [c_18, c_575])).
% 3.54/1.55  tff(c_800, plain, (![A_196, B_197]: (~m1_subset_1(k7_setfam_1(A_196, B_197), k1_zfmisc_1(k1_zfmisc_1(A_196))) | ~r2_hidden('#skF_1'(A_196, k7_setfam_1(A_196, B_197), B_197), B_197) | ~m1_subset_1('#skF_1'(A_196, k7_setfam_1(A_196, B_197), B_197), k1_zfmisc_1(A_196)) | k7_setfam_1(A_196, k7_setfam_1(A_196, B_197))=B_197 | ~m1_subset_1(B_197, k1_zfmisc_1(k1_zfmisc_1(A_196))))), inference(resolution, [status(thm)], [c_779, c_592])).
% 3.54/1.55  tff(c_812, plain, (![A_198, B_199]: (~m1_subset_1(k7_setfam_1(A_198, B_199), k1_zfmisc_1(k1_zfmisc_1(A_198))) | ~m1_subset_1('#skF_1'(A_198, k7_setfam_1(A_198, B_199), B_199), k1_zfmisc_1(A_198)) | k7_setfam_1(A_198, k7_setfam_1(A_198, B_199))=B_199 | ~m1_subset_1(B_199, k1_zfmisc_1(k1_zfmisc_1(A_198))))), inference(resolution, [status(thm)], [c_752, c_800])).
% 3.54/1.55  tff(c_818, plain, (![A_200, C_201]: (k7_setfam_1(A_200, k7_setfam_1(A_200, C_201))=C_201 | ~m1_subset_1(C_201, k1_zfmisc_1(k1_zfmisc_1(A_200))) | ~m1_subset_1(k7_setfam_1(A_200, C_201), k1_zfmisc_1(k1_zfmisc_1(A_200))))), inference(resolution, [status(thm)], [c_2, c_812])).
% 3.54/1.55  tff(c_823, plain, (![A_202, B_203]: (k7_setfam_1(A_202, k7_setfam_1(A_202, B_203))=B_203 | ~m1_subset_1(B_203, k1_zfmisc_1(k1_zfmisc_1(A_202))))), inference(resolution, [status(thm)], [c_16, c_818])).
% 3.54/1.55  tff(c_833, plain, (k7_setfam_1(u1_struct_0('#skF_2'), k7_setfam_1(u1_struct_0('#skF_2'), '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_26, c_823])).
% 3.54/1.55  tff(c_22, plain, (![B_20, A_18]: (v2_tops_2(B_20, A_18) | ~v1_tops_2(k7_setfam_1(u1_struct_0(A_18), B_20), A_18) | ~m1_subset_1(B_20, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_18)))) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.54/1.55  tff(c_884, plain, (v2_tops_2(k7_setfam_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~v1_tops_2('#skF_3', '#skF_2') | ~m1_subset_1(k7_setfam_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_833, c_22])).
% 3.54/1.55  tff(c_912, plain, (v2_tops_2(k7_setfam_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~m1_subset_1(k7_setfam_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_481, c_884])).
% 3.54/1.55  tff(c_913, plain, (~m1_subset_1(k7_setfam_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_480, c_912])).
% 3.54/1.55  tff(c_940, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_16, c_913])).
% 3.54/1.55  tff(c_944, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_940])).
% 3.54/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.54/1.55  
% 3.54/1.55  Inference rules
% 3.54/1.55  ----------------------
% 3.54/1.55  #Ref     : 0
% 3.54/1.55  #Sup     : 183
% 3.54/1.55  #Fact    : 8
% 3.54/1.55  #Define  : 0
% 3.54/1.55  #Split   : 3
% 3.54/1.55  #Chain   : 0
% 3.54/1.55  #Close   : 0
% 3.54/1.55  
% 3.54/1.55  Ordering : KBO
% 3.54/1.55  
% 3.54/1.55  Simplification rules
% 3.54/1.55  ----------------------
% 3.54/1.55  #Subsume      : 51
% 3.54/1.55  #Demod        : 96
% 3.54/1.55  #Tautology    : 44
% 3.54/1.55  #SimpNegUnit  : 4
% 3.54/1.55  #BackRed      : 0
% 3.54/1.55  
% 3.54/1.55  #Partial instantiations: 0
% 3.54/1.55  #Strategies tried      : 1
% 3.54/1.55  
% 3.54/1.55  Timing (in seconds)
% 3.54/1.55  ----------------------
% 3.54/1.55  Preprocessing        : 0.28
% 3.54/1.55  Parsing              : 0.15
% 3.54/1.55  CNF conversion       : 0.02
% 3.54/1.55  Main loop            : 0.49
% 3.54/1.55  Inferencing          : 0.19
% 3.54/1.55  Reduction            : 0.12
% 3.54/1.55  Demodulation         : 0.08
% 3.54/1.55  BG Simplification    : 0.03
% 3.54/1.55  Subsumption          : 0.11
% 3.54/1.55  Abstraction          : 0.03
% 3.54/1.55  MUC search           : 0.00
% 3.54/1.55  Cooper               : 0.00
% 3.54/1.55  Total                : 0.80
% 3.54/1.55  Index Insertion      : 0.00
% 3.54/1.55  Index Deletion       : 0.00
% 3.54/1.55  Index Matching       : 0.00
% 3.54/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
