%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1704+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:16 EST 2020

% Result     : Theorem 4.07s
% Output     : CNFRefutation 4.65s
% Verified   : 
% Statistics : Number of formulae       :  190 (2127 expanded)
%              Number of leaves         :   25 ( 711 expanded)
%              Depth                    :   18
%              Number of atoms          :  444 (7804 expanded)
%              Number of equality atoms :  109 (1779 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v1_borsuk_1 > m1_subset_1 > m1_pre_topc > v2_pre_topc > v1_pre_topc > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v1_borsuk_1,type,(
    v1_borsuk_1: ( $i * $i ) > $o )).

tff(f_124,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v2_pre_topc(B)
              & l1_pre_topc(B) )
           => ! [C] :
                ( ( v2_pre_topc(C)
                  & l1_pre_topc(C) )
               => ( C = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
                 => ( ( v1_borsuk_1(B,A)
                      & m1_pre_topc(B,A) )
                  <=> ( v1_borsuk_1(C,A)
                      & m1_pre_topc(C,A) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_tmap_1)).

tff(f_47,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( v1_pre_topc(g1_pre_topc(A,B))
        & l1_pre_topc(g1_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

tff(f_30,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_pre_topc(A)
       => A = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(f_92,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( ( v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v2_pre_topc(C)
                & l1_pre_topc(C) )
             => ( B = g1_pre_topc(u1_struct_0(C),u1_pre_topc(C))
               => ( m1_pre_topc(B,A)
                <=> m1_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_tmap_1)).

tff(f_99,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_74,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = u1_struct_0(B)
               => ( ( v1_borsuk_1(B,A)
                    & m1_pre_topc(B,A) )
                <=> v4_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tsep_1)).

tff(c_38,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_52,plain,
    ( v1_borsuk_1('#skF_2','#skF_1')
    | m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_60,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_32,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_30,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_34,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_28,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_10,plain,(
    ! [A_7] :
      ( m1_subset_1(u1_pre_topc(A_7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_7))))
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_75,plain,(
    ! [A_38,B_39] :
      ( v1_pre_topc(g1_pre_topc(A_38,B_39))
      | ~ m1_subset_1(B_39,k1_zfmisc_1(k1_zfmisc_1(A_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_80,plain,(
    ! [A_40] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(A_40),u1_pre_topc(A_40)))
      | ~ l1_pre_topc(A_40) ) ),
    inference(resolution,[status(thm)],[c_10,c_75])).

tff(c_83,plain,
    ( v1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_80])).

tff(c_85,plain,(
    v1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_83])).

tff(c_2,plain,(
    ! [A_1] :
      ( g1_pre_topc(u1_struct_0(A_1),u1_pre_topc(A_1)) = A_1
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_869,plain,(
    ! [D_112,B_113,C_114,A_115] :
      ( D_112 = B_113
      | g1_pre_topc(C_114,D_112) != g1_pre_topc(A_115,B_113)
      | ~ m1_subset_1(B_113,k1_zfmisc_1(k1_zfmisc_1(A_115))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_877,plain,(
    ! [D_112,C_114] :
      ( u1_pre_topc('#skF_2') = D_112
      | g1_pre_topc(C_114,D_112) != '#skF_3'
      | ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_869])).

tff(c_923,plain,(
    ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_877])).

tff(c_926,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_923])).

tff(c_930,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_926])).

tff(c_933,plain,(
    ! [D_126,C_127] :
      ( u1_pre_topc('#skF_2') = D_126
      | g1_pre_topc(C_127,D_126) != '#skF_3' ) ),
    inference(splitRight,[status(thm)],[c_877])).

tff(c_960,plain,(
    ! [A_128] :
      ( u1_pre_topc(A_128) = u1_pre_topc('#skF_2')
      | A_128 != '#skF_3'
      | ~ v1_pre_topc(A_128)
      | ~ l1_pre_topc(A_128) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_933])).

tff(c_963,plain,
    ( u1_pre_topc('#skF_2') = u1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_85,c_960])).

tff(c_969,plain,(
    u1_pre_topc('#skF_2') = u1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_963])).

tff(c_932,plain,(
    m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_877])).

tff(c_972,plain,(
    m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_969,c_932])).

tff(c_887,plain,(
    ! [C_118,A_119,D_120,B_121] :
      ( C_118 = A_119
      | g1_pre_topc(C_118,D_120) != g1_pre_topc(A_119,B_121)
      | ~ m1_subset_1(B_121,k1_zfmisc_1(k1_zfmisc_1(A_119))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_895,plain,(
    ! [C_118,D_120] :
      ( u1_struct_0('#skF_2') = C_118
      | g1_pre_topc(C_118,D_120) != '#skF_3'
      | ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_887])).

tff(c_1024,plain,(
    ! [C_118,D_120] :
      ( u1_struct_0('#skF_2') = C_118
      | g1_pre_topc(C_118,D_120) != '#skF_3'
      | ~ m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_969,c_895])).

tff(c_1025,plain,(
    ~ m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_1024])).

tff(c_1053,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_972,c_1025])).

tff(c_1087,plain,(
    ! [C_137,D_138] :
      ( u1_struct_0('#skF_2') = C_137
      | g1_pre_topc(C_137,D_138) != '#skF_3' ) ),
    inference(splitRight,[status(thm)],[c_1024])).

tff(c_1112,plain,(
    ! [A_140] :
      ( u1_struct_0(A_140) = u1_struct_0('#skF_2')
      | A_140 != '#skF_3'
      | ~ v1_pre_topc(A_140)
      | ~ l1_pre_topc(A_140) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1087])).

tff(c_1115,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_85,c_1112])).

tff(c_1121,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1115])).

tff(c_974,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_969,c_28])).

tff(c_1126,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1121,c_974])).

tff(c_36,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_1281,plain,(
    ! [C_147,A_148] :
      ( m1_pre_topc(C_147,A_148)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(C_147),u1_pre_topc(C_147)),A_148)
      | ~ l1_pre_topc(C_147)
      | ~ v2_pre_topc(C_147)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(C_147),u1_pre_topc(C_147)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(C_147),u1_pre_topc(C_147)))
      | ~ l1_pre_topc(A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1293,plain,(
    ! [A_148] :
      ( m1_pre_topc('#skF_2',A_148)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_3')),A_148)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc(A_148) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_969,c_1281])).

tff(c_1304,plain,(
    ! [A_149] :
      ( m1_pre_topc('#skF_2',A_149)
      | ~ m1_pre_topc('#skF_3',A_149)
      | ~ l1_pre_topc(A_149) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1126,c_1121,c_969,c_30,c_1126,c_1121,c_969,c_36,c_34,c_1126,c_1121,c_1293])).

tff(c_131,plain,(
    ! [D_47,B_48,C_49,A_50] :
      ( D_47 = B_48
      | g1_pre_topc(C_49,D_47) != g1_pre_topc(A_50,B_48)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(k1_zfmisc_1(A_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_139,plain,(
    ! [D_47,C_49] :
      ( u1_pre_topc('#skF_2') = D_47
      | g1_pre_topc(C_49,D_47) != '#skF_3'
      | ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_131])).

tff(c_145,plain,(
    ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_139])).

tff(c_148,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_145])).

tff(c_152,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_148])).

tff(c_155,plain,(
    ! [D_53,C_54] :
      ( u1_pre_topc('#skF_2') = D_53
      | g1_pre_topc(C_54,D_53) != '#skF_3' ) ),
    inference(splitRight,[status(thm)],[c_139])).

tff(c_175,plain,(
    ! [A_55] :
      ( u1_pre_topc(A_55) = u1_pre_topc('#skF_2')
      | A_55 != '#skF_3'
      | ~ v1_pre_topc(A_55)
      | ~ l1_pre_topc(A_55) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_155])).

tff(c_178,plain,
    ( u1_pre_topc('#skF_2') = u1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_85,c_175])).

tff(c_184,plain,(
    u1_pre_topc('#skF_2') = u1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_178])).

tff(c_154,plain,(
    m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_139])).

tff(c_187,plain,(
    m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_154])).

tff(c_189,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_28])).

tff(c_14,plain,(
    ! [C_12,A_8,D_13,B_9] :
      ( C_12 = A_8
      | g1_pre_topc(C_12,D_13) != g1_pre_topc(A_8,B_9)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(k1_zfmisc_1(A_8))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_227,plain,(
    ! [C_12,D_13] :
      ( u1_struct_0('#skF_2') = C_12
      | g1_pre_topc(C_12,D_13) != '#skF_3'
      | ~ m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_14])).

tff(c_299,plain,(
    ! [C_68,D_69] :
      ( u1_struct_0('#skF_2') = C_68
      | g1_pre_topc(C_68,D_69) != '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_227])).

tff(c_309,plain,(
    ! [A_70] :
      ( u1_struct_0(A_70) = u1_struct_0('#skF_2')
      | A_70 != '#skF_3'
      | ~ v1_pre_topc(A_70)
      | ~ l1_pre_topc(A_70) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_299])).

tff(c_312,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_85,c_309])).

tff(c_318,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_312])).

tff(c_323,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_318,c_189])).

tff(c_548,plain,(
    ! [C_87,A_88] :
      ( m1_pre_topc(C_87,A_88)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(C_87),u1_pre_topc(C_87)),A_88)
      | ~ l1_pre_topc(C_87)
      | ~ v2_pre_topc(C_87)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(C_87),u1_pre_topc(C_87)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(C_87),u1_pre_topc(C_87)))
      | ~ l1_pre_topc(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_560,plain,(
    ! [A_88] :
      ( m1_pre_topc('#skF_2',A_88)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_3')),A_88)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc(A_88) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_548])).

tff(c_570,plain,(
    ! [A_88] :
      ( m1_pre_topc('#skF_2',A_88)
      | ~ m1_pre_topc('#skF_3',A_88)
      | ~ l1_pre_topc(A_88) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_323,c_318,c_184,c_30,c_323,c_318,c_184,c_36,c_34,c_323,c_318,c_560])).

tff(c_40,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_58,plain,
    ( v1_borsuk_1('#skF_2','#skF_1')
    | v1_borsuk_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_59,plain,(
    v1_borsuk_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_26,plain,(
    ! [B_30,A_28] :
      ( m1_subset_1(u1_struct_0(B_30),k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ m1_pre_topc(B_30,A_28)
      | ~ l1_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_406,plain,(
    ! [B_71,A_72] :
      ( v4_pre_topc(u1_struct_0(B_71),A_72)
      | ~ v1_borsuk_1(B_71,A_72)
      | ~ m1_subset_1(u1_struct_0(B_71),k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ m1_pre_topc(B_71,A_72)
      | ~ l1_pre_topc(A_72)
      | ~ v2_pre_topc(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_419,plain,(
    ! [B_30,A_28] :
      ( v4_pre_topc(u1_struct_0(B_30),A_28)
      | ~ v1_borsuk_1(B_30,A_28)
      | ~ v2_pre_topc(A_28)
      | ~ m1_pre_topc(B_30,A_28)
      | ~ l1_pre_topc(A_28) ) ),
    inference(resolution,[status(thm)],[c_26,c_406])).

tff(c_280,plain,(
    ! [B_64,A_65] :
      ( v1_borsuk_1(B_64,A_65)
      | ~ v4_pre_topc(u1_struct_0(B_64),A_65)
      | ~ m1_subset_1(u1_struct_0(B_64),k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ m1_pre_topc(B_64,A_65)
      | ~ l1_pre_topc(A_65)
      | ~ v2_pre_topc(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_534,plain,(
    ! [B_85,A_86] :
      ( v1_borsuk_1(B_85,A_86)
      | ~ v4_pre_topc(u1_struct_0(B_85),A_86)
      | ~ v2_pre_topc(A_86)
      | ~ m1_pre_topc(B_85,A_86)
      | ~ l1_pre_topc(A_86) ) ),
    inference(resolution,[status(thm)],[c_26,c_280])).

tff(c_589,plain,(
    ! [A_90] :
      ( v1_borsuk_1('#skF_2',A_90)
      | ~ v4_pre_topc(u1_struct_0('#skF_3'),A_90)
      | ~ v2_pre_topc(A_90)
      | ~ m1_pre_topc('#skF_2',A_90)
      | ~ l1_pre_topc(A_90) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_318,c_534])).

tff(c_816,plain,(
    ! [A_107] :
      ( v1_borsuk_1('#skF_2',A_107)
      | ~ m1_pre_topc('#skF_2',A_107)
      | ~ v1_borsuk_1('#skF_3',A_107)
      | ~ v2_pre_topc(A_107)
      | ~ m1_pre_topc('#skF_3',A_107)
      | ~ l1_pre_topc(A_107) ) ),
    inference(resolution,[status(thm)],[c_419,c_589])).

tff(c_42,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ v1_borsuk_1('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ v1_borsuk_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_92,plain,
    ( ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ v1_borsuk_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_60,c_42])).

tff(c_93,plain,(
    ~ v1_borsuk_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_92])).

tff(c_819,plain,
    ( ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ v1_borsuk_1('#skF_3','#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_816,c_93])).

tff(c_822,plain,(
    ~ m1_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_60,c_40,c_59,c_819])).

tff(c_825,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_570,c_822])).

tff(c_829,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_60,c_825])).

tff(c_830,plain,(
    ~ m1_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_1313,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_1304,c_830])).

tff(c_1324,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_60,c_1313])).

tff(c_1326,plain,(
    ~ m1_pre_topc('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_50,plain,
    ( m1_pre_topc('#skF_2','#skF_1')
    | m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_1332,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_1326,c_50])).

tff(c_1341,plain,(
    ! [A_153,B_154] :
      ( v1_pre_topc(g1_pre_topc(A_153,B_154))
      | ~ m1_subset_1(B_154,k1_zfmisc_1(k1_zfmisc_1(A_153))) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1346,plain,(
    ! [A_155] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(A_155),u1_pre_topc(A_155)))
      | ~ l1_pre_topc(A_155) ) ),
    inference(resolution,[status(thm)],[c_10,c_1341])).

tff(c_1349,plain,
    ( v1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1346])).

tff(c_1351,plain,(
    v1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1349])).

tff(c_1396,plain,(
    ! [C_162,A_163,D_164,B_165] :
      ( C_162 = A_163
      | g1_pre_topc(C_162,D_164) != g1_pre_topc(A_163,B_165)
      | ~ m1_subset_1(B_165,k1_zfmisc_1(k1_zfmisc_1(A_163))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1404,plain,(
    ! [C_162,D_164] :
      ( u1_struct_0('#skF_2') = C_162
      | g1_pre_topc(C_162,D_164) != '#skF_3'
      | ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1396])).

tff(c_1421,plain,(
    ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_1404])).

tff(c_1424,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_1421])).

tff(c_1428,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1424])).

tff(c_1431,plain,(
    ! [C_169,D_170] :
      ( u1_struct_0('#skF_2') = C_169
      | g1_pre_topc(C_169,D_170) != '#skF_3' ) ),
    inference(splitRight,[status(thm)],[c_1404])).

tff(c_1451,plain,(
    ! [A_171] :
      ( u1_struct_0(A_171) = u1_struct_0('#skF_2')
      | A_171 != '#skF_3'
      | ~ v1_pre_topc(A_171)
      | ~ l1_pre_topc(A_171) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1431])).

tff(c_1454,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_1351,c_1451])).

tff(c_1460,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1454])).

tff(c_1465,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1460,c_28])).

tff(c_12,plain,(
    ! [D_13,B_9,C_12,A_8] :
      ( D_13 = B_9
      | g1_pre_topc(C_12,D_13) != g1_pre_topc(A_8,B_9)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(k1_zfmisc_1(A_8))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1521,plain,(
    ! [B_176,A_177] :
      ( u1_pre_topc('#skF_2') = B_176
      | g1_pre_topc(A_177,B_176) != '#skF_3'
      | ~ m1_subset_1(B_176,k1_zfmisc_1(k1_zfmisc_1(A_177))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1465,c_12])).

tff(c_1602,plain,(
    ! [A_185] :
      ( u1_pre_topc(A_185) = u1_pre_topc('#skF_2')
      | g1_pre_topc(u1_struct_0(A_185),u1_pre_topc(A_185)) != '#skF_3'
      | ~ l1_pre_topc(A_185) ) ),
    inference(resolution,[status(thm)],[c_10,c_1521])).

tff(c_1613,plain,(
    ! [A_186] :
      ( u1_pre_topc(A_186) = u1_pre_topc('#skF_2')
      | A_186 != '#skF_3'
      | ~ l1_pre_topc(A_186)
      | ~ v1_pre_topc(A_186)
      | ~ l1_pre_topc(A_186) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1602])).

tff(c_1616,plain,
    ( u1_pre_topc('#skF_2') = u1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_1351,c_1613])).

tff(c_1622,plain,(
    u1_pre_topc('#skF_2') = u1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1616])).

tff(c_1628,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1622,c_1465])).

tff(c_1754,plain,(
    ! [C_191,A_192] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(C_191),u1_pre_topc(C_191)),A_192)
      | ~ m1_pre_topc(C_191,A_192)
      | ~ l1_pre_topc(C_191)
      | ~ v2_pre_topc(C_191)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(C_191),u1_pre_topc(C_191)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(C_191),u1_pre_topc(C_191)))
      | ~ l1_pre_topc(A_192) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1766,plain,(
    ! [A_192] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_2')),A_192)
      | ~ m1_pre_topc('#skF_2',A_192)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc(A_192) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1460,c_1754])).

tff(c_1778,plain,(
    ! [A_193] :
      ( m1_pre_topc('#skF_3',A_193)
      | ~ m1_pre_topc('#skF_2',A_193)
      | ~ l1_pre_topc(A_193) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1628,c_1460,c_1622,c_30,c_1628,c_1460,c_1622,c_36,c_34,c_1628,c_1622,c_1766])).

tff(c_1781,plain,
    ( m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_1332,c_1778])).

tff(c_1784,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1781])).

tff(c_1786,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1326,c_1784])).

tff(c_1788,plain,(
    ~ v1_borsuk_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_56,plain,
    ( m1_pre_topc('#skF_2','#skF_1')
    | v1_borsuk_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_1795,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_1788,c_56])).

tff(c_1789,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_1787,plain,(
    v1_borsuk_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_1811,plain,(
    ! [A_200] :
      ( m1_subset_1(u1_pre_topc(A_200),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_200))))
      | ~ l1_pre_topc(A_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( v1_pre_topc(g1_pre_topc(A_2,B_3))
      | ~ m1_subset_1(B_3,k1_zfmisc_1(k1_zfmisc_1(A_2))) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1822,plain,(
    ! [A_201] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(A_201),u1_pre_topc(A_201)))
      | ~ l1_pre_topc(A_201) ) ),
    inference(resolution,[status(thm)],[c_1811,c_6])).

tff(c_1825,plain,
    ( v1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1822])).

tff(c_1827,plain,(
    v1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1825])).

tff(c_1865,plain,(
    ! [D_206,B_207,C_208,A_209] :
      ( D_206 = B_207
      | g1_pre_topc(C_208,D_206) != g1_pre_topc(A_209,B_207)
      | ~ m1_subset_1(B_207,k1_zfmisc_1(k1_zfmisc_1(A_209))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1874,plain,(
    ! [B_210,A_211] :
      ( u1_pre_topc('#skF_2') = B_210
      | g1_pre_topc(A_211,B_210) != '#skF_3'
      | ~ m1_subset_1(B_210,k1_zfmisc_1(k1_zfmisc_1(A_211))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1865])).

tff(c_1879,plain,(
    ! [A_212] :
      ( u1_pre_topc(A_212) = u1_pre_topc('#skF_2')
      | g1_pre_topc(u1_struct_0(A_212),u1_pre_topc(A_212)) != '#skF_3'
      | ~ l1_pre_topc(A_212) ) ),
    inference(resolution,[status(thm)],[c_10,c_1874])).

tff(c_1891,plain,(
    ! [A_213] :
      ( u1_pre_topc(A_213) = u1_pre_topc('#skF_2')
      | A_213 != '#skF_3'
      | ~ l1_pre_topc(A_213)
      | ~ v1_pre_topc(A_213)
      | ~ l1_pre_topc(A_213) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1879])).

tff(c_1894,plain,
    ( u1_pre_topc('#skF_2') = u1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_1827,c_1891])).

tff(c_1900,plain,(
    u1_pre_topc('#skF_2') = u1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1894])).

tff(c_1905,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1900,c_28])).

tff(c_1943,plain,(
    ! [C_214,A_215,D_216,B_217] :
      ( C_214 = A_215
      | g1_pre_topc(C_214,D_216) != g1_pre_topc(A_215,B_217)
      | ~ m1_subset_1(B_217,k1_zfmisc_1(k1_zfmisc_1(A_215))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2004,plain,(
    ! [A_225,B_226] :
      ( u1_struct_0('#skF_2') = A_225
      | g1_pre_topc(A_225,B_226) != '#skF_3'
      | ~ m1_subset_1(B_226,k1_zfmisc_1(k1_zfmisc_1(A_225))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1905,c_1943])).

tff(c_2016,plain,(
    ! [A_227] :
      ( u1_struct_0(A_227) = u1_struct_0('#skF_2')
      | g1_pre_topc(u1_struct_0(A_227),u1_pre_topc(A_227)) != '#skF_3'
      | ~ l1_pre_topc(A_227) ) ),
    inference(resolution,[status(thm)],[c_10,c_2004])).

tff(c_2027,plain,(
    ! [A_228] :
      ( u1_struct_0(A_228) = u1_struct_0('#skF_2')
      | A_228 != '#skF_3'
      | ~ l1_pre_topc(A_228)
      | ~ v1_pre_topc(A_228)
      | ~ l1_pre_topc(A_228) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2016])).

tff(c_2030,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_1827,c_2027])).

tff(c_2036,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_2030])).

tff(c_2145,plain,(
    ! [B_231,A_232] :
      ( v4_pre_topc(u1_struct_0(B_231),A_232)
      | ~ v1_borsuk_1(B_231,A_232)
      | ~ m1_subset_1(u1_struct_0(B_231),k1_zfmisc_1(u1_struct_0(A_232)))
      | ~ m1_pre_topc(B_231,A_232)
      | ~ l1_pre_topc(A_232)
      | ~ v2_pre_topc(A_232) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2258,plain,(
    ! [B_243,A_244] :
      ( v4_pre_topc(u1_struct_0(B_243),A_244)
      | ~ v1_borsuk_1(B_243,A_244)
      | ~ v2_pre_topc(A_244)
      | ~ m1_pre_topc(B_243,A_244)
      | ~ l1_pre_topc(A_244) ) ),
    inference(resolution,[status(thm)],[c_26,c_2145])).

tff(c_2348,plain,(
    ! [A_251] :
      ( v4_pre_topc(u1_struct_0('#skF_3'),A_251)
      | ~ v1_borsuk_1('#skF_2',A_251)
      | ~ v2_pre_topc(A_251)
      | ~ m1_pre_topc('#skF_2',A_251)
      | ~ l1_pre_topc(A_251) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2036,c_2258])).

tff(c_1999,plain,(
    ! [B_223,A_224] :
      ( v1_borsuk_1(B_223,A_224)
      | ~ v4_pre_topc(u1_struct_0(B_223),A_224)
      | ~ m1_subset_1(u1_struct_0(B_223),k1_zfmisc_1(u1_struct_0(A_224)))
      | ~ m1_pre_topc(B_223,A_224)
      | ~ l1_pre_topc(A_224)
      | ~ v2_pre_topc(A_224) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2003,plain,(
    ! [B_30,A_28] :
      ( v1_borsuk_1(B_30,A_28)
      | ~ v4_pre_topc(u1_struct_0(B_30),A_28)
      | ~ v2_pre_topc(A_28)
      | ~ m1_pre_topc(B_30,A_28)
      | ~ l1_pre_topc(A_28) ) ),
    inference(resolution,[status(thm)],[c_26,c_1999])).

tff(c_2551,plain,(
    ! [A_267] :
      ( v1_borsuk_1('#skF_3',A_267)
      | ~ m1_pre_topc('#skF_3',A_267)
      | ~ v1_borsuk_1('#skF_2',A_267)
      | ~ v2_pre_topc(A_267)
      | ~ m1_pre_topc('#skF_2',A_267)
      | ~ l1_pre_topc(A_267) ) ),
    inference(resolution,[status(thm)],[c_2348,c_2003])).

tff(c_2554,plain,
    ( v1_borsuk_1('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_1787,c_2551])).

tff(c_2557,plain,(
    v1_borsuk_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1795,c_40,c_1789,c_2554])).

tff(c_2559,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1788,c_2557])).

tff(c_2561,plain,(
    ~ m1_pre_topc('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_2560,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_2589,plain,(
    ! [A_274,B_275] :
      ( v1_pre_topc(g1_pre_topc(A_274,B_275))
      | ~ m1_subset_1(B_275,k1_zfmisc_1(k1_zfmisc_1(A_274))) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2619,plain,(
    ! [A_277] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(A_277),u1_pre_topc(A_277)))
      | ~ l1_pre_topc(A_277) ) ),
    inference(resolution,[status(thm)],[c_10,c_2589])).

tff(c_2625,plain,
    ( v1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_2619])).

tff(c_2627,plain,(
    v1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_2625])).

tff(c_2633,plain,(
    ! [C_280,A_281,D_282,B_283] :
      ( C_280 = A_281
      | g1_pre_topc(C_280,D_282) != g1_pre_topc(A_281,B_283)
      | ~ m1_subset_1(B_283,k1_zfmisc_1(k1_zfmisc_1(A_281))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2641,plain,(
    ! [C_280,D_282] :
      ( u1_struct_0('#skF_2') = C_280
      | g1_pre_topc(C_280,D_282) != '#skF_3'
      | ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_2633])).

tff(c_2687,plain,(
    ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_2641])).

tff(c_2690,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_2687])).

tff(c_2694,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_2690])).

tff(c_2697,plain,(
    ! [C_294,D_295] :
      ( u1_struct_0('#skF_2') = C_294
      | g1_pre_topc(C_294,D_295) != '#skF_3' ) ),
    inference(splitRight,[status(thm)],[c_2641])).

tff(c_2724,plain,(
    ! [A_296] :
      ( u1_struct_0(A_296) = u1_struct_0('#skF_2')
      | A_296 != '#skF_3'
      | ~ v1_pre_topc(A_296)
      | ~ l1_pre_topc(A_296) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2697])).

tff(c_2727,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_2627,c_2724])).

tff(c_2733,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_2727])).

tff(c_2738,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2733,c_28])).

tff(c_2930,plain,(
    ! [C_310,A_311] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(C_310),u1_pre_topc(C_310)),A_311)
      | ~ m1_pre_topc(C_310,A_311)
      | ~ l1_pre_topc(C_310)
      | ~ v2_pre_topc(C_310)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(C_310),u1_pre_topc(C_310)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(C_310),u1_pre_topc(C_310)))
      | ~ l1_pre_topc(A_311) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2936,plain,(
    ! [A_311] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_2')),A_311)
      | ~ m1_pre_topc('#skF_2',A_311)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc(A_311) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2733,c_2930])).

tff(c_3043,plain,(
    ! [A_314] :
      ( m1_pre_topc('#skF_3',A_314)
      | ~ m1_pre_topc('#skF_2',A_314)
      | ~ l1_pre_topc(A_314) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_2738,c_2733,c_30,c_2738,c_2733,c_36,c_34,c_2738,c_2936])).

tff(c_3046,plain,
    ( m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_2560,c_3043])).

tff(c_3049,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_3046])).

tff(c_3051,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2561,c_3049])).

%------------------------------------------------------------------------------
