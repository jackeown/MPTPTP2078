%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:09 EST 2020

% Result     : Theorem 5.33s
% Output     : CNFRefutation 5.33s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 417 expanded)
%              Number of leaves         :   41 ( 157 expanded)
%              Depth                    :   13
%              Number of atoms          :  337 (1194 expanded)
%              Number of equality atoms :   30 ( 108 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v2_tex_2 > v1_tops_1 > v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_pre_topc > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_tdlat_3,type,(
    v1_tdlat_3: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_34,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_50,axiom,(
    ! [A] : ~ v1_subset_1(k2_subset_1(A),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_subset_1)).

tff(f_173,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v1_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_tex_2(B,A)
            <=> ~ v1_subset_1(B,u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tex_2)).

tff(f_36,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_40,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_125,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v1_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => v3_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_tdlat_3)).

tff(f_74,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).

tff(f_89,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = u1_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_3)).

tff(f_139,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v1_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).

tff(f_155,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v1_tops_1(B,A)
              & v2_tex_2(B,A) )
           => v3_tex_2(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tex_2)).

tff(f_114,axiom,(
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

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(c_8,plain,(
    ! [A_6] : k2_subset_1(A_6) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_16,plain,(
    ! [A_14] : ~ v1_subset_1(k2_subset_1(A_14),A_14) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_75,plain,(
    ! [A_14] : ~ v1_subset_1(A_14,A_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_16])).

tff(c_60,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_58,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_74,plain,
    ( v3_tex_2('#skF_5','#skF_4')
    | ~ v1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_89,plain,(
    ~ v1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_68,plain,
    ( v1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ v3_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_90,plain,(
    ~ v3_tex_2('#skF_5','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_68])).

tff(c_10,plain,(
    ! [A_7] : m1_subset_1(k2_subset_1(A_7),k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_76,plain,(
    ! [A_7] : m1_subset_1(A_7,k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10])).

tff(c_103,plain,(
    ! [B_60,A_61] :
      ( v1_subset_1(B_60,A_61)
      | B_60 = A_61
      | ~ m1_subset_1(B_60,k1_zfmisc_1(A_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_106,plain,
    ( v1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | u1_struct_0('#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_58,c_103])).

tff(c_112,plain,(
    u1_struct_0('#skF_4') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_106])).

tff(c_228,plain,(
    ! [A_87,B_88] :
      ( k2_pre_topc(A_87,B_88) = B_88
      | ~ v4_pre_topc(B_88,A_87)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ l1_pre_topc(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_238,plain,(
    ! [B_88] :
      ( k2_pre_topc('#skF_4',B_88) = B_88
      | ~ v4_pre_topc(B_88,'#skF_4')
      | ~ m1_subset_1(B_88,k1_zfmisc_1('#skF_5'))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_228])).

tff(c_248,plain,(
    ! [B_89] :
      ( k2_pre_topc('#skF_4',B_89) = B_89
      | ~ v4_pre_topc(B_89,'#skF_4')
      | ~ m1_subset_1(B_89,k1_zfmisc_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_238])).

tff(c_258,plain,
    ( k2_pre_topc('#skF_4','#skF_5') = '#skF_5'
    | ~ v4_pre_topc('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_248])).

tff(c_259,plain,(
    ~ v4_pre_topc('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_258])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(k3_subset_1(A_8,B_9),k1_zfmisc_1(A_8))
      | ~ m1_subset_1(B_9,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_64,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_62,plain,(
    v1_tdlat_3('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_260,plain,(
    ! [B_90,A_91] :
      ( v3_pre_topc(B_90,A_91)
      | ~ m1_subset_1(B_90,k1_zfmisc_1(u1_struct_0(A_91)))
      | ~ v1_tdlat_3(A_91)
      | ~ l1_pre_topc(A_91)
      | ~ v2_pre_topc(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_270,plain,(
    ! [B_90] :
      ( v3_pre_topc(B_90,'#skF_4')
      | ~ m1_subset_1(B_90,k1_zfmisc_1('#skF_5'))
      | ~ v1_tdlat_3('#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_260])).

tff(c_280,plain,(
    ! [B_92] :
      ( v3_pre_topc(B_92,'#skF_4')
      | ~ m1_subset_1(B_92,k1_zfmisc_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_62,c_270])).

tff(c_289,plain,(
    ! [B_9] :
      ( v3_pre_topc(k3_subset_1('#skF_5',B_9),'#skF_4')
      | ~ m1_subset_1(B_9,k1_zfmisc_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_12,c_280])).

tff(c_437,plain,(
    ! [B_123,A_124] :
      ( v4_pre_topc(B_123,A_124)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_124),B_123),A_124)
      | ~ m1_subset_1(B_123,k1_zfmisc_1(u1_struct_0(A_124)))
      | ~ l1_pre_topc(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_443,plain,(
    ! [B_123] :
      ( v4_pre_topc(B_123,'#skF_4')
      | ~ v3_pre_topc(k3_subset_1('#skF_5',B_123),'#skF_4')
      | ~ m1_subset_1(B_123,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_437])).

tff(c_447,plain,(
    ! [B_125] :
      ( v4_pre_topc(B_125,'#skF_4')
      | ~ v3_pre_topc(k3_subset_1('#skF_5',B_125),'#skF_4')
      | ~ m1_subset_1(B_125,k1_zfmisc_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_112,c_443])).

tff(c_452,plain,(
    ! [B_126] :
      ( v4_pre_topc(B_126,'#skF_4')
      | ~ m1_subset_1(B_126,k1_zfmisc_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_289,c_447])).

tff(c_460,plain,(
    v4_pre_topc('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_452])).

tff(c_465,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_259,c_460])).

tff(c_466,plain,(
    k2_pre_topc('#skF_4','#skF_5') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_258])).

tff(c_548,plain,(
    ! [B_141,A_142] :
      ( v1_tops_1(B_141,A_142)
      | k2_pre_topc(A_142,B_141) != u1_struct_0(A_142)
      | ~ m1_subset_1(B_141,k1_zfmisc_1(u1_struct_0(A_142)))
      | ~ l1_pre_topc(A_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_558,plain,(
    ! [B_141] :
      ( v1_tops_1(B_141,'#skF_4')
      | k2_pre_topc('#skF_4',B_141) != u1_struct_0('#skF_4')
      | ~ m1_subset_1(B_141,k1_zfmisc_1('#skF_5'))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_548])).

tff(c_580,plain,(
    ! [B_144] :
      ( v1_tops_1(B_144,'#skF_4')
      | k2_pre_topc('#skF_4',B_144) != '#skF_5'
      | ~ m1_subset_1(B_144,k1_zfmisc_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_112,c_558])).

tff(c_588,plain,
    ( v1_tops_1('#skF_5','#skF_4')
    | k2_pre_topc('#skF_4','#skF_5') != '#skF_5' ),
    inference(resolution,[status(thm)],[c_76,c_580])).

tff(c_592,plain,(
    v1_tops_1('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_466,c_588])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_727,plain,(
    ! [B_170,A_171] :
      ( v2_tex_2(B_170,A_171)
      | ~ m1_subset_1(B_170,k1_zfmisc_1(u1_struct_0(A_171)))
      | ~ l1_pre_topc(A_171)
      | ~ v1_tdlat_3(A_171)
      | ~ v2_pre_topc(A_171)
      | v2_struct_0(A_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_737,plain,(
    ! [B_170] :
      ( v2_tex_2(B_170,'#skF_4')
      | ~ m1_subset_1(B_170,k1_zfmisc_1('#skF_5'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v1_tdlat_3('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_727])).

tff(c_745,plain,(
    ! [B_170] :
      ( v2_tex_2(B_170,'#skF_4')
      | ~ m1_subset_1(B_170,k1_zfmisc_1('#skF_5'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_737])).

tff(c_748,plain,(
    ! [B_172] :
      ( v2_tex_2(B_172,'#skF_4')
      | ~ m1_subset_1(B_172,k1_zfmisc_1('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_745])).

tff(c_758,plain,(
    v2_tex_2('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_748])).

tff(c_1142,plain,(
    ! [B_216,A_217] :
      ( v3_tex_2(B_216,A_217)
      | ~ v2_tex_2(B_216,A_217)
      | ~ v1_tops_1(B_216,A_217)
      | ~ m1_subset_1(B_216,k1_zfmisc_1(u1_struct_0(A_217)))
      | ~ l1_pre_topc(A_217)
      | ~ v2_pre_topc(A_217)
      | v2_struct_0(A_217) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_1155,plain,(
    ! [B_216] :
      ( v3_tex_2(B_216,'#skF_4')
      | ~ v2_tex_2(B_216,'#skF_4')
      | ~ v1_tops_1(B_216,'#skF_4')
      | ~ m1_subset_1(B_216,k1_zfmisc_1('#skF_5'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_1142])).

tff(c_1164,plain,(
    ! [B_216] :
      ( v3_tex_2(B_216,'#skF_4')
      | ~ v2_tex_2(B_216,'#skF_4')
      | ~ v1_tops_1(B_216,'#skF_4')
      | ~ m1_subset_1(B_216,k1_zfmisc_1('#skF_5'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_1155])).

tff(c_1167,plain,(
    ! [B_218] :
      ( v3_tex_2(B_218,'#skF_4')
      | ~ v2_tex_2(B_218,'#skF_4')
      | ~ v1_tops_1(B_218,'#skF_4')
      | ~ m1_subset_1(B_218,k1_zfmisc_1('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1164])).

tff(c_1178,plain,
    ( v3_tex_2('#skF_5','#skF_4')
    | ~ v2_tex_2('#skF_5','#skF_4')
    | ~ v1_tops_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_1167])).

tff(c_1183,plain,(
    v3_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_592,c_758,c_1178])).

tff(c_1185,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_1183])).

tff(c_1186,plain,(
    v3_tex_2('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_1961,plain,(
    ! [B_377,A_378] :
      ( v2_tex_2(B_377,A_378)
      | ~ m1_subset_1(B_377,k1_zfmisc_1(u1_struct_0(A_378)))
      | ~ l1_pre_topc(A_378)
      | ~ v1_tdlat_3(A_378)
      | ~ v2_pre_topc(A_378)
      | v2_struct_0(A_378) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_1982,plain,(
    ! [A_378] :
      ( v2_tex_2(u1_struct_0(A_378),A_378)
      | ~ l1_pre_topc(A_378)
      | ~ v1_tdlat_3(A_378)
      | ~ v2_pre_topc(A_378)
      | v2_struct_0(A_378) ) ),
    inference(resolution,[status(thm)],[c_76,c_1961])).

tff(c_2161,plain,(
    ! [B_416,A_417] :
      ( r1_tarski(B_416,'#skF_2'(A_417,B_416))
      | v3_tex_2(B_416,A_417)
      | ~ v2_tex_2(B_416,A_417)
      | ~ m1_subset_1(B_416,k1_zfmisc_1(u1_struct_0(A_417)))
      | ~ l1_pre_topc(A_417) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_2178,plain,(
    ! [A_418] :
      ( r1_tarski(u1_struct_0(A_418),'#skF_2'(A_418,u1_struct_0(A_418)))
      | v3_tex_2(u1_struct_0(A_418),A_418)
      | ~ v2_tex_2(u1_struct_0(A_418),A_418)
      | ~ l1_pre_topc(A_418) ) ),
    inference(resolution,[status(thm)],[c_76,c_2161])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1216,plain,(
    ! [C_230,A_231,B_232] :
      ( r2_hidden(C_230,A_231)
      | ~ r2_hidden(C_230,B_232)
      | ~ m1_subset_1(B_232,k1_zfmisc_1(A_231)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1242,plain,(
    ! [A_239,B_240,A_241] :
      ( r2_hidden('#skF_1'(A_239,B_240),A_241)
      | ~ m1_subset_1(A_239,k1_zfmisc_1(A_241))
      | r1_tarski(A_239,B_240) ) ),
    inference(resolution,[status(thm)],[c_6,c_1216])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1254,plain,(
    ! [A_242,A_243] :
      ( ~ m1_subset_1(A_242,k1_zfmisc_1(A_243))
      | r1_tarski(A_242,A_243) ) ),
    inference(resolution,[status(thm)],[c_1242,c_4])).

tff(c_1269,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_58,c_1254])).

tff(c_1211,plain,(
    ! [C_226,B_227,A_228] :
      ( r2_hidden(C_226,B_227)
      | ~ r2_hidden(C_226,A_228)
      | ~ r1_tarski(A_228,B_227) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1225,plain,(
    ! [A_235,B_236,B_237] :
      ( r2_hidden('#skF_1'(A_235,B_236),B_237)
      | ~ r1_tarski(A_235,B_237)
      | r1_tarski(A_235,B_236) ) ),
    inference(resolution,[status(thm)],[c_6,c_1211])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1784,plain,(
    ! [A_342,B_343,B_344,B_345] :
      ( r2_hidden('#skF_1'(A_342,B_343),B_344)
      | ~ r1_tarski(B_345,B_344)
      | ~ r1_tarski(A_342,B_345)
      | r1_tarski(A_342,B_343) ) ),
    inference(resolution,[status(thm)],[c_1225,c_2])).

tff(c_1797,plain,(
    ! [A_346,B_347] :
      ( r2_hidden('#skF_1'(A_346,B_347),u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_346,'#skF_5')
      | r1_tarski(A_346,B_347) ) ),
    inference(resolution,[status(thm)],[c_1269,c_1784])).

tff(c_1840,plain,(
    ! [A_352,B_353,B_354] :
      ( r2_hidden('#skF_1'(A_352,B_353),B_354)
      | ~ r1_tarski(u1_struct_0('#skF_4'),B_354)
      | ~ r1_tarski(A_352,'#skF_5')
      | r1_tarski(A_352,B_353) ) ),
    inference(resolution,[status(thm)],[c_1797,c_2])).

tff(c_1851,plain,(
    ! [B_354,A_352] :
      ( ~ r1_tarski(u1_struct_0('#skF_4'),B_354)
      | ~ r1_tarski(A_352,'#skF_5')
      | r1_tarski(A_352,B_354) ) ),
    inference(resolution,[status(thm)],[c_1840,c_4])).

tff(c_2190,plain,(
    ! [A_352] :
      ( ~ r1_tarski(A_352,'#skF_5')
      | r1_tarski(A_352,'#skF_2'('#skF_4',u1_struct_0('#skF_4')))
      | v3_tex_2(u1_struct_0('#skF_4'),'#skF_4')
      | ~ v2_tex_2(u1_struct_0('#skF_4'),'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2178,c_1851])).

tff(c_2201,plain,(
    ! [A_352] :
      ( ~ r1_tarski(A_352,'#skF_5')
      | r1_tarski(A_352,'#skF_2'('#skF_4',u1_struct_0('#skF_4')))
      | v3_tex_2(u1_struct_0('#skF_4'),'#skF_4')
      | ~ v2_tex_2(u1_struct_0('#skF_4'),'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_2190])).

tff(c_2243,plain,(
    ~ v2_tex_2(u1_struct_0('#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2201])).

tff(c_2246,plain,
    ( ~ l1_pre_topc('#skF_4')
    | ~ v1_tdlat_3('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1982,c_2243])).

tff(c_2249,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_2246])).

tff(c_2251,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_2249])).

tff(c_2253,plain,(
    v2_tex_2(u1_struct_0('#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_2201])).

tff(c_1297,plain,(
    ! [A_252,B_253] :
      ( k2_pre_topc(A_252,B_253) = B_253
      | ~ v4_pre_topc(B_253,A_252)
      | ~ m1_subset_1(B_253,k1_zfmisc_1(u1_struct_0(A_252)))
      | ~ l1_pre_topc(A_252) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1307,plain,
    ( k2_pre_topc('#skF_4','#skF_5') = '#skF_5'
    | ~ v4_pre_topc('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_1297])).

tff(c_1316,plain,
    ( k2_pre_topc('#skF_4','#skF_5') = '#skF_5'
    | ~ v4_pre_topc('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1307])).

tff(c_1318,plain,(
    ~ v4_pre_topc('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1316])).

tff(c_1320,plain,(
    ! [B_255,A_256] :
      ( v3_pre_topc(B_255,A_256)
      | ~ m1_subset_1(B_255,k1_zfmisc_1(u1_struct_0(A_256)))
      | ~ v1_tdlat_3(A_256)
      | ~ l1_pre_topc(A_256)
      | ~ v2_pre_topc(A_256) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1704,plain,(
    ! [A_330,B_331] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0(A_330),B_331),A_330)
      | ~ v1_tdlat_3(A_330)
      | ~ l1_pre_topc(A_330)
      | ~ v2_pre_topc(A_330)
      | ~ m1_subset_1(B_331,k1_zfmisc_1(u1_struct_0(A_330))) ) ),
    inference(resolution,[status(thm)],[c_12,c_1320])).

tff(c_22,plain,(
    ! [B_20,A_18] :
      ( v4_pre_topc(B_20,A_18)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_18),B_20),A_18)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1709,plain,(
    ! [B_332,A_333] :
      ( v4_pre_topc(B_332,A_333)
      | ~ v1_tdlat_3(A_333)
      | ~ l1_pre_topc(A_333)
      | ~ v2_pre_topc(A_333)
      | ~ m1_subset_1(B_332,k1_zfmisc_1(u1_struct_0(A_333))) ) ),
    inference(resolution,[status(thm)],[c_1704,c_22])).

tff(c_1719,plain,
    ( v4_pre_topc('#skF_5','#skF_4')
    | ~ v1_tdlat_3('#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_1709])).

tff(c_1728,plain,(
    v4_pre_topc('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_62,c_1719])).

tff(c_1730,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1318,c_1728])).

tff(c_1731,plain,(
    k2_pre_topc('#skF_4','#skF_5') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1316])).

tff(c_1761,plain,(
    ! [B_339,A_340] :
      ( v1_tops_1(B_339,A_340)
      | k2_pre_topc(A_340,B_339) != u1_struct_0(A_340)
      | ~ m1_subset_1(B_339,k1_zfmisc_1(u1_struct_0(A_340)))
      | ~ l1_pre_topc(A_340) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1771,plain,
    ( v1_tops_1('#skF_5','#skF_4')
    | k2_pre_topc('#skF_4','#skF_5') != u1_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_1761])).

tff(c_1780,plain,
    ( v1_tops_1('#skF_5','#skF_4')
    | u1_struct_0('#skF_4') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1731,c_1771])).

tff(c_1782,plain,(
    u1_struct_0('#skF_4') != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_1780])).

tff(c_2491,plain,(
    ! [C_471,B_472,A_473] :
      ( C_471 = B_472
      | ~ r1_tarski(B_472,C_471)
      | ~ v2_tex_2(C_471,A_473)
      | ~ m1_subset_1(C_471,k1_zfmisc_1(u1_struct_0(A_473)))
      | ~ v3_tex_2(B_472,A_473)
      | ~ m1_subset_1(B_472,k1_zfmisc_1(u1_struct_0(A_473)))
      | ~ l1_pre_topc(A_473) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_2509,plain,(
    ! [A_473] :
      ( u1_struct_0('#skF_4') = '#skF_5'
      | ~ v2_tex_2(u1_struct_0('#skF_4'),A_473)
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_473)))
      | ~ v3_tex_2('#skF_5',A_473)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_473)))
      | ~ l1_pre_topc(A_473) ) ),
    inference(resolution,[status(thm)],[c_1269,c_2491])).

tff(c_2562,plain,(
    ! [A_481] :
      ( ~ v2_tex_2(u1_struct_0('#skF_4'),A_481)
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_481)))
      | ~ v3_tex_2('#skF_5',A_481)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_481)))
      | ~ l1_pre_topc(A_481) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1782,c_2509])).

tff(c_2566,plain,
    ( ~ v2_tex_2(u1_struct_0('#skF_4'),'#skF_4')
    | ~ v3_tex_2('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_2562])).

tff(c_2570,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_1186,c_2253,c_2566])).

tff(c_2572,plain,(
    u1_struct_0('#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1780])).

tff(c_1187,plain,(
    v1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_2574,plain,(
    v1_subset_1('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2572,c_1187])).

tff(c_2578,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_2574])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:56:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.33/2.02  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.33/2.03  
% 5.33/2.03  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.33/2.03  %$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v2_tex_2 > v1_tops_1 > v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_pre_topc > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 5.33/2.03  
% 5.33/2.03  %Foreground sorts:
% 5.33/2.03  
% 5.33/2.03  
% 5.33/2.03  %Background operators:
% 5.33/2.03  
% 5.33/2.03  
% 5.33/2.03  %Foreground operators:
% 5.33/2.03  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.33/2.03  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 5.33/2.03  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.33/2.03  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.33/2.03  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 5.33/2.03  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.33/2.03  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 5.33/2.03  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.33/2.03  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 5.33/2.03  tff('#skF_5', type, '#skF_5': $i).
% 5.33/2.03  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 5.33/2.03  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 5.33/2.03  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 5.33/2.03  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.33/2.03  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 5.33/2.03  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.33/2.03  tff('#skF_4', type, '#skF_4': $i).
% 5.33/2.03  tff('#skF_3', type, '#skF_3': $i > $i).
% 5.33/2.03  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.33/2.03  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.33/2.03  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.33/2.03  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.33/2.03  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.33/2.03  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 5.33/2.03  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 5.33/2.03  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.33/2.03  
% 5.33/2.06  tff(f_34, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 5.33/2.06  tff(f_50, axiom, (![A]: ~v1_subset_1(k2_subset_1(A), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc14_subset_1)).
% 5.33/2.06  tff(f_173, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> ~v1_subset_1(B, u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_tex_2)).
% 5.33/2.06  tff(f_36, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 5.33/2.06  tff(f_96, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 5.33/2.06  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 5.33/2.06  tff(f_40, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 5.33/2.06  tff(f_125, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v1_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v3_pre_topc(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_tdlat_3)).
% 5.33/2.06  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_tops_1)).
% 5.33/2.06  tff(f_89, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tops_3)).
% 5.33/2.06  tff(f_139, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_tex_2)).
% 5.33/2.06  tff(f_155, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v1_tops_1(B, A) & v2_tex_2(B, A)) => v3_tex_2(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tex_2)).
% 5.33/2.06  tff(f_114, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 5.33/2.06  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.33/2.06  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 5.33/2.06  tff(c_8, plain, (![A_6]: (k2_subset_1(A_6)=A_6)), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.33/2.06  tff(c_16, plain, (![A_14]: (~v1_subset_1(k2_subset_1(A_14), A_14))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.33/2.06  tff(c_75, plain, (![A_14]: (~v1_subset_1(A_14, A_14))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_16])).
% 5.33/2.06  tff(c_60, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_173])).
% 5.33/2.06  tff(c_58, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_173])).
% 5.33/2.06  tff(c_74, plain, (v3_tex_2('#skF_5', '#skF_4') | ~v1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_173])).
% 5.33/2.06  tff(c_89, plain, (~v1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_74])).
% 5.33/2.06  tff(c_68, plain, (v1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~v3_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_173])).
% 5.33/2.06  tff(c_90, plain, (~v3_tex_2('#skF_5', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_89, c_68])).
% 5.33/2.06  tff(c_10, plain, (![A_7]: (m1_subset_1(k2_subset_1(A_7), k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.33/2.06  tff(c_76, plain, (![A_7]: (m1_subset_1(A_7, k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10])).
% 5.33/2.06  tff(c_103, plain, (![B_60, A_61]: (v1_subset_1(B_60, A_61) | B_60=A_61 | ~m1_subset_1(B_60, k1_zfmisc_1(A_61)))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.33/2.06  tff(c_106, plain, (v1_subset_1('#skF_5', u1_struct_0('#skF_4')) | u1_struct_0('#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_58, c_103])).
% 5.33/2.06  tff(c_112, plain, (u1_struct_0('#skF_4')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_89, c_106])).
% 5.33/2.06  tff(c_228, plain, (![A_87, B_88]: (k2_pre_topc(A_87, B_88)=B_88 | ~v4_pre_topc(B_88, A_87) | ~m1_subset_1(B_88, k1_zfmisc_1(u1_struct_0(A_87))) | ~l1_pre_topc(A_87))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.33/2.06  tff(c_238, plain, (![B_88]: (k2_pre_topc('#skF_4', B_88)=B_88 | ~v4_pre_topc(B_88, '#skF_4') | ~m1_subset_1(B_88, k1_zfmisc_1('#skF_5')) | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_112, c_228])).
% 5.33/2.06  tff(c_248, plain, (![B_89]: (k2_pre_topc('#skF_4', B_89)=B_89 | ~v4_pre_topc(B_89, '#skF_4') | ~m1_subset_1(B_89, k1_zfmisc_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_238])).
% 5.33/2.06  tff(c_258, plain, (k2_pre_topc('#skF_4', '#skF_5')='#skF_5' | ~v4_pre_topc('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_76, c_248])).
% 5.33/2.06  tff(c_259, plain, (~v4_pre_topc('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_258])).
% 5.33/2.06  tff(c_12, plain, (![A_8, B_9]: (m1_subset_1(k3_subset_1(A_8, B_9), k1_zfmisc_1(A_8)) | ~m1_subset_1(B_9, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.33/2.06  tff(c_64, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_173])).
% 5.33/2.06  tff(c_62, plain, (v1_tdlat_3('#skF_4')), inference(cnfTransformation, [status(thm)], [f_173])).
% 5.33/2.06  tff(c_260, plain, (![B_90, A_91]: (v3_pre_topc(B_90, A_91) | ~m1_subset_1(B_90, k1_zfmisc_1(u1_struct_0(A_91))) | ~v1_tdlat_3(A_91) | ~l1_pre_topc(A_91) | ~v2_pre_topc(A_91))), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.33/2.06  tff(c_270, plain, (![B_90]: (v3_pre_topc(B_90, '#skF_4') | ~m1_subset_1(B_90, k1_zfmisc_1('#skF_5')) | ~v1_tdlat_3('#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_112, c_260])).
% 5.33/2.06  tff(c_280, plain, (![B_92]: (v3_pre_topc(B_92, '#skF_4') | ~m1_subset_1(B_92, k1_zfmisc_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_62, c_270])).
% 5.33/2.06  tff(c_289, plain, (![B_9]: (v3_pre_topc(k3_subset_1('#skF_5', B_9), '#skF_4') | ~m1_subset_1(B_9, k1_zfmisc_1('#skF_5')))), inference(resolution, [status(thm)], [c_12, c_280])).
% 5.33/2.06  tff(c_437, plain, (![B_123, A_124]: (v4_pre_topc(B_123, A_124) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_124), B_123), A_124) | ~m1_subset_1(B_123, k1_zfmisc_1(u1_struct_0(A_124))) | ~l1_pre_topc(A_124))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.33/2.06  tff(c_443, plain, (![B_123]: (v4_pre_topc(B_123, '#skF_4') | ~v3_pre_topc(k3_subset_1('#skF_5', B_123), '#skF_4') | ~m1_subset_1(B_123, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_112, c_437])).
% 5.33/2.06  tff(c_447, plain, (![B_125]: (v4_pre_topc(B_125, '#skF_4') | ~v3_pre_topc(k3_subset_1('#skF_5', B_125), '#skF_4') | ~m1_subset_1(B_125, k1_zfmisc_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_112, c_443])).
% 5.33/2.06  tff(c_452, plain, (![B_126]: (v4_pre_topc(B_126, '#skF_4') | ~m1_subset_1(B_126, k1_zfmisc_1('#skF_5')))), inference(resolution, [status(thm)], [c_289, c_447])).
% 5.33/2.06  tff(c_460, plain, (v4_pre_topc('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_76, c_452])).
% 5.33/2.06  tff(c_465, plain, $false, inference(negUnitSimplification, [status(thm)], [c_259, c_460])).
% 5.33/2.06  tff(c_466, plain, (k2_pre_topc('#skF_4', '#skF_5')='#skF_5'), inference(splitRight, [status(thm)], [c_258])).
% 5.33/2.06  tff(c_548, plain, (![B_141, A_142]: (v1_tops_1(B_141, A_142) | k2_pre_topc(A_142, B_141)!=u1_struct_0(A_142) | ~m1_subset_1(B_141, k1_zfmisc_1(u1_struct_0(A_142))) | ~l1_pre_topc(A_142))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.33/2.06  tff(c_558, plain, (![B_141]: (v1_tops_1(B_141, '#skF_4') | k2_pre_topc('#skF_4', B_141)!=u1_struct_0('#skF_4') | ~m1_subset_1(B_141, k1_zfmisc_1('#skF_5')) | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_112, c_548])).
% 5.33/2.06  tff(c_580, plain, (![B_144]: (v1_tops_1(B_144, '#skF_4') | k2_pre_topc('#skF_4', B_144)!='#skF_5' | ~m1_subset_1(B_144, k1_zfmisc_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_112, c_558])).
% 5.33/2.06  tff(c_588, plain, (v1_tops_1('#skF_5', '#skF_4') | k2_pre_topc('#skF_4', '#skF_5')!='#skF_5'), inference(resolution, [status(thm)], [c_76, c_580])).
% 5.33/2.06  tff(c_592, plain, (v1_tops_1('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_466, c_588])).
% 5.33/2.06  tff(c_66, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_173])).
% 5.33/2.06  tff(c_727, plain, (![B_170, A_171]: (v2_tex_2(B_170, A_171) | ~m1_subset_1(B_170, k1_zfmisc_1(u1_struct_0(A_171))) | ~l1_pre_topc(A_171) | ~v1_tdlat_3(A_171) | ~v2_pre_topc(A_171) | v2_struct_0(A_171))), inference(cnfTransformation, [status(thm)], [f_139])).
% 5.33/2.06  tff(c_737, plain, (![B_170]: (v2_tex_2(B_170, '#skF_4') | ~m1_subset_1(B_170, k1_zfmisc_1('#skF_5')) | ~l1_pre_topc('#skF_4') | ~v1_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_112, c_727])).
% 5.33/2.06  tff(c_745, plain, (![B_170]: (v2_tex_2(B_170, '#skF_4') | ~m1_subset_1(B_170, k1_zfmisc_1('#skF_5')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_737])).
% 5.33/2.06  tff(c_748, plain, (![B_172]: (v2_tex_2(B_172, '#skF_4') | ~m1_subset_1(B_172, k1_zfmisc_1('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_66, c_745])).
% 5.33/2.06  tff(c_758, plain, (v2_tex_2('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_76, c_748])).
% 5.33/2.06  tff(c_1142, plain, (![B_216, A_217]: (v3_tex_2(B_216, A_217) | ~v2_tex_2(B_216, A_217) | ~v1_tops_1(B_216, A_217) | ~m1_subset_1(B_216, k1_zfmisc_1(u1_struct_0(A_217))) | ~l1_pre_topc(A_217) | ~v2_pre_topc(A_217) | v2_struct_0(A_217))), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.33/2.06  tff(c_1155, plain, (![B_216]: (v3_tex_2(B_216, '#skF_4') | ~v2_tex_2(B_216, '#skF_4') | ~v1_tops_1(B_216, '#skF_4') | ~m1_subset_1(B_216, k1_zfmisc_1('#skF_5')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_112, c_1142])).
% 5.33/2.06  tff(c_1164, plain, (![B_216]: (v3_tex_2(B_216, '#skF_4') | ~v2_tex_2(B_216, '#skF_4') | ~v1_tops_1(B_216, '#skF_4') | ~m1_subset_1(B_216, k1_zfmisc_1('#skF_5')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_1155])).
% 5.33/2.06  tff(c_1167, plain, (![B_218]: (v3_tex_2(B_218, '#skF_4') | ~v2_tex_2(B_218, '#skF_4') | ~v1_tops_1(B_218, '#skF_4') | ~m1_subset_1(B_218, k1_zfmisc_1('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_66, c_1164])).
% 5.33/2.06  tff(c_1178, plain, (v3_tex_2('#skF_5', '#skF_4') | ~v2_tex_2('#skF_5', '#skF_4') | ~v1_tops_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_76, c_1167])).
% 5.33/2.06  tff(c_1183, plain, (v3_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_592, c_758, c_1178])).
% 5.33/2.06  tff(c_1185, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_1183])).
% 5.33/2.06  tff(c_1186, plain, (v3_tex_2('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_74])).
% 5.33/2.06  tff(c_1961, plain, (![B_377, A_378]: (v2_tex_2(B_377, A_378) | ~m1_subset_1(B_377, k1_zfmisc_1(u1_struct_0(A_378))) | ~l1_pre_topc(A_378) | ~v1_tdlat_3(A_378) | ~v2_pre_topc(A_378) | v2_struct_0(A_378))), inference(cnfTransformation, [status(thm)], [f_139])).
% 5.33/2.06  tff(c_1982, plain, (![A_378]: (v2_tex_2(u1_struct_0(A_378), A_378) | ~l1_pre_topc(A_378) | ~v1_tdlat_3(A_378) | ~v2_pre_topc(A_378) | v2_struct_0(A_378))), inference(resolution, [status(thm)], [c_76, c_1961])).
% 5.33/2.06  tff(c_2161, plain, (![B_416, A_417]: (r1_tarski(B_416, '#skF_2'(A_417, B_416)) | v3_tex_2(B_416, A_417) | ~v2_tex_2(B_416, A_417) | ~m1_subset_1(B_416, k1_zfmisc_1(u1_struct_0(A_417))) | ~l1_pre_topc(A_417))), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.33/2.06  tff(c_2178, plain, (![A_418]: (r1_tarski(u1_struct_0(A_418), '#skF_2'(A_418, u1_struct_0(A_418))) | v3_tex_2(u1_struct_0(A_418), A_418) | ~v2_tex_2(u1_struct_0(A_418), A_418) | ~l1_pre_topc(A_418))), inference(resolution, [status(thm)], [c_76, c_2161])).
% 5.33/2.06  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.33/2.06  tff(c_1216, plain, (![C_230, A_231, B_232]: (r2_hidden(C_230, A_231) | ~r2_hidden(C_230, B_232) | ~m1_subset_1(B_232, k1_zfmisc_1(A_231)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.33/2.06  tff(c_1242, plain, (![A_239, B_240, A_241]: (r2_hidden('#skF_1'(A_239, B_240), A_241) | ~m1_subset_1(A_239, k1_zfmisc_1(A_241)) | r1_tarski(A_239, B_240))), inference(resolution, [status(thm)], [c_6, c_1216])).
% 5.33/2.06  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.33/2.06  tff(c_1254, plain, (![A_242, A_243]: (~m1_subset_1(A_242, k1_zfmisc_1(A_243)) | r1_tarski(A_242, A_243))), inference(resolution, [status(thm)], [c_1242, c_4])).
% 5.33/2.06  tff(c_1269, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_58, c_1254])).
% 5.33/2.06  tff(c_1211, plain, (![C_226, B_227, A_228]: (r2_hidden(C_226, B_227) | ~r2_hidden(C_226, A_228) | ~r1_tarski(A_228, B_227))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.33/2.06  tff(c_1225, plain, (![A_235, B_236, B_237]: (r2_hidden('#skF_1'(A_235, B_236), B_237) | ~r1_tarski(A_235, B_237) | r1_tarski(A_235, B_236))), inference(resolution, [status(thm)], [c_6, c_1211])).
% 5.33/2.06  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.33/2.06  tff(c_1784, plain, (![A_342, B_343, B_344, B_345]: (r2_hidden('#skF_1'(A_342, B_343), B_344) | ~r1_tarski(B_345, B_344) | ~r1_tarski(A_342, B_345) | r1_tarski(A_342, B_343))), inference(resolution, [status(thm)], [c_1225, c_2])).
% 5.33/2.06  tff(c_1797, plain, (![A_346, B_347]: (r2_hidden('#skF_1'(A_346, B_347), u1_struct_0('#skF_4')) | ~r1_tarski(A_346, '#skF_5') | r1_tarski(A_346, B_347))), inference(resolution, [status(thm)], [c_1269, c_1784])).
% 5.33/2.06  tff(c_1840, plain, (![A_352, B_353, B_354]: (r2_hidden('#skF_1'(A_352, B_353), B_354) | ~r1_tarski(u1_struct_0('#skF_4'), B_354) | ~r1_tarski(A_352, '#skF_5') | r1_tarski(A_352, B_353))), inference(resolution, [status(thm)], [c_1797, c_2])).
% 5.33/2.06  tff(c_1851, plain, (![B_354, A_352]: (~r1_tarski(u1_struct_0('#skF_4'), B_354) | ~r1_tarski(A_352, '#skF_5') | r1_tarski(A_352, B_354))), inference(resolution, [status(thm)], [c_1840, c_4])).
% 5.33/2.06  tff(c_2190, plain, (![A_352]: (~r1_tarski(A_352, '#skF_5') | r1_tarski(A_352, '#skF_2'('#skF_4', u1_struct_0('#skF_4'))) | v3_tex_2(u1_struct_0('#skF_4'), '#skF_4') | ~v2_tex_2(u1_struct_0('#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_2178, c_1851])).
% 5.33/2.06  tff(c_2201, plain, (![A_352]: (~r1_tarski(A_352, '#skF_5') | r1_tarski(A_352, '#skF_2'('#skF_4', u1_struct_0('#skF_4'))) | v3_tex_2(u1_struct_0('#skF_4'), '#skF_4') | ~v2_tex_2(u1_struct_0('#skF_4'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_2190])).
% 5.33/2.06  tff(c_2243, plain, (~v2_tex_2(u1_struct_0('#skF_4'), '#skF_4')), inference(splitLeft, [status(thm)], [c_2201])).
% 5.33/2.06  tff(c_2246, plain, (~l1_pre_topc('#skF_4') | ~v1_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_1982, c_2243])).
% 5.33/2.06  tff(c_2249, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_2246])).
% 5.33/2.06  tff(c_2251, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_2249])).
% 5.33/2.06  tff(c_2253, plain, (v2_tex_2(u1_struct_0('#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_2201])).
% 5.33/2.06  tff(c_1297, plain, (![A_252, B_253]: (k2_pre_topc(A_252, B_253)=B_253 | ~v4_pre_topc(B_253, A_252) | ~m1_subset_1(B_253, k1_zfmisc_1(u1_struct_0(A_252))) | ~l1_pre_topc(A_252))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.33/2.06  tff(c_1307, plain, (k2_pre_topc('#skF_4', '#skF_5')='#skF_5' | ~v4_pre_topc('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_58, c_1297])).
% 5.33/2.06  tff(c_1316, plain, (k2_pre_topc('#skF_4', '#skF_5')='#skF_5' | ~v4_pre_topc('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1307])).
% 5.33/2.06  tff(c_1318, plain, (~v4_pre_topc('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_1316])).
% 5.33/2.06  tff(c_1320, plain, (![B_255, A_256]: (v3_pre_topc(B_255, A_256) | ~m1_subset_1(B_255, k1_zfmisc_1(u1_struct_0(A_256))) | ~v1_tdlat_3(A_256) | ~l1_pre_topc(A_256) | ~v2_pre_topc(A_256))), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.33/2.06  tff(c_1704, plain, (![A_330, B_331]: (v3_pre_topc(k3_subset_1(u1_struct_0(A_330), B_331), A_330) | ~v1_tdlat_3(A_330) | ~l1_pre_topc(A_330) | ~v2_pre_topc(A_330) | ~m1_subset_1(B_331, k1_zfmisc_1(u1_struct_0(A_330))))), inference(resolution, [status(thm)], [c_12, c_1320])).
% 5.33/2.06  tff(c_22, plain, (![B_20, A_18]: (v4_pre_topc(B_20, A_18) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_18), B_20), A_18) | ~m1_subset_1(B_20, k1_zfmisc_1(u1_struct_0(A_18))) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.33/2.06  tff(c_1709, plain, (![B_332, A_333]: (v4_pre_topc(B_332, A_333) | ~v1_tdlat_3(A_333) | ~l1_pre_topc(A_333) | ~v2_pre_topc(A_333) | ~m1_subset_1(B_332, k1_zfmisc_1(u1_struct_0(A_333))))), inference(resolution, [status(thm)], [c_1704, c_22])).
% 5.33/2.06  tff(c_1719, plain, (v4_pre_topc('#skF_5', '#skF_4') | ~v1_tdlat_3('#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_58, c_1709])).
% 5.33/2.06  tff(c_1728, plain, (v4_pre_topc('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_62, c_1719])).
% 5.33/2.06  tff(c_1730, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1318, c_1728])).
% 5.33/2.06  tff(c_1731, plain, (k2_pre_topc('#skF_4', '#skF_5')='#skF_5'), inference(splitRight, [status(thm)], [c_1316])).
% 5.33/2.06  tff(c_1761, plain, (![B_339, A_340]: (v1_tops_1(B_339, A_340) | k2_pre_topc(A_340, B_339)!=u1_struct_0(A_340) | ~m1_subset_1(B_339, k1_zfmisc_1(u1_struct_0(A_340))) | ~l1_pre_topc(A_340))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.33/2.06  tff(c_1771, plain, (v1_tops_1('#skF_5', '#skF_4') | k2_pre_topc('#skF_4', '#skF_5')!=u1_struct_0('#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_58, c_1761])).
% 5.33/2.06  tff(c_1780, plain, (v1_tops_1('#skF_5', '#skF_4') | u1_struct_0('#skF_4')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1731, c_1771])).
% 5.33/2.06  tff(c_1782, plain, (u1_struct_0('#skF_4')!='#skF_5'), inference(splitLeft, [status(thm)], [c_1780])).
% 5.33/2.06  tff(c_2491, plain, (![C_471, B_472, A_473]: (C_471=B_472 | ~r1_tarski(B_472, C_471) | ~v2_tex_2(C_471, A_473) | ~m1_subset_1(C_471, k1_zfmisc_1(u1_struct_0(A_473))) | ~v3_tex_2(B_472, A_473) | ~m1_subset_1(B_472, k1_zfmisc_1(u1_struct_0(A_473))) | ~l1_pre_topc(A_473))), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.33/2.06  tff(c_2509, plain, (![A_473]: (u1_struct_0('#skF_4')='#skF_5' | ~v2_tex_2(u1_struct_0('#skF_4'), A_473) | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0(A_473))) | ~v3_tex_2('#skF_5', A_473) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(A_473))) | ~l1_pre_topc(A_473))), inference(resolution, [status(thm)], [c_1269, c_2491])).
% 5.33/2.06  tff(c_2562, plain, (![A_481]: (~v2_tex_2(u1_struct_0('#skF_4'), A_481) | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0(A_481))) | ~v3_tex_2('#skF_5', A_481) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(A_481))) | ~l1_pre_topc(A_481))), inference(negUnitSimplification, [status(thm)], [c_1782, c_2509])).
% 5.33/2.06  tff(c_2566, plain, (~v2_tex_2(u1_struct_0('#skF_4'), '#skF_4') | ~v3_tex_2('#skF_5', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_76, c_2562])).
% 5.33/2.06  tff(c_2570, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_1186, c_2253, c_2566])).
% 5.33/2.06  tff(c_2572, plain, (u1_struct_0('#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_1780])).
% 5.33/2.06  tff(c_1187, plain, (v1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_74])).
% 5.33/2.06  tff(c_2574, plain, (v1_subset_1('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2572, c_1187])).
% 5.33/2.06  tff(c_2578, plain, $false, inference(negUnitSimplification, [status(thm)], [c_75, c_2574])).
% 5.33/2.06  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.33/2.06  
% 5.33/2.06  Inference rules
% 5.33/2.06  ----------------------
% 5.33/2.06  #Ref     : 0
% 5.33/2.06  #Sup     : 552
% 5.33/2.06  #Fact    : 0
% 5.33/2.06  #Define  : 0
% 5.33/2.06  #Split   : 12
% 5.33/2.06  #Chain   : 0
% 5.33/2.06  #Close   : 0
% 5.33/2.06  
% 5.33/2.06  Ordering : KBO
% 5.33/2.06  
% 5.33/2.06  Simplification rules
% 5.33/2.06  ----------------------
% 5.33/2.06  #Subsume      : 92
% 5.33/2.06  #Demod        : 220
% 5.33/2.06  #Tautology    : 92
% 5.33/2.06  #SimpNegUnit  : 27
% 5.33/2.06  #BackRed      : 5
% 5.33/2.06  
% 5.33/2.06  #Partial instantiations: 0
% 5.33/2.06  #Strategies tried      : 1
% 5.33/2.06  
% 5.33/2.06  Timing (in seconds)
% 5.33/2.06  ----------------------
% 5.33/2.06  Preprocessing        : 0.34
% 5.33/2.06  Parsing              : 0.18
% 5.33/2.06  CNF conversion       : 0.03
% 5.33/2.07  Main loop            : 0.92
% 5.33/2.07  Inferencing          : 0.33
% 5.33/2.07  Reduction            : 0.25
% 5.33/2.07  Demodulation         : 0.16
% 5.33/2.07  BG Simplification    : 0.04
% 5.33/2.07  Subsumption          : 0.23
% 5.33/2.07  Abstraction          : 0.04
% 5.33/2.07  MUC search           : 0.00
% 5.33/2.07  Cooper               : 0.00
% 5.33/2.07  Total                : 1.31
% 5.33/2.07  Index Insertion      : 0.00
% 5.33/2.07  Index Deletion       : 0.00
% 5.33/2.07  Index Matching       : 0.00
% 5.33/2.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
