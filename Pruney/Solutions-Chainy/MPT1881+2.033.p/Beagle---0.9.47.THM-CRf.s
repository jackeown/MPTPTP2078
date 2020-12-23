%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:10 EST 2020

% Result     : Theorem 3.57s
% Output     : CNFRefutation 3.57s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 382 expanded)
%              Number of leaves         :   33 ( 144 expanded)
%              Depth                    :   13
%              Number of atoms          :  227 ( 969 expanded)
%              Number of equality atoms :   18 ( 119 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > v1_tops_1 > v1_subset_1 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_tdlat_3,type,(
    v1_tdlat_3: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_32,axiom,(
    ! [A] : ~ v1_subset_1(k2_subset_1(A),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_subset_1)).

tff(f_127,negated_conjecture,(
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

tff(f_44,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_40,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => v1_tops_1(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc12_tops_1)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_93,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v1_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).

tff(f_109,axiom,(
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

tff(f_79,axiom,(
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

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_3] : ~ v1_subset_1(k2_subset_1(A_3),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_57,plain,(
    ! [A_3] : ~ v1_subset_1(A_3,A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_6])).

tff(c_42,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_14,plain,(
    ! [A_7] :
      ( l1_struct_0(A_7)
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_486,plain,(
    ! [A_91] :
      ( u1_struct_0(A_91) = k2_struct_0(A_91)
      | ~ l1_struct_0(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_494,plain,(
    ! [A_93] :
      ( u1_struct_0(A_93) = k2_struct_0(A_93)
      | ~ l1_pre_topc(A_93) ) ),
    inference(resolution,[status(thm)],[c_14,c_486])).

tff(c_498,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_494])).

tff(c_40,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_500,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_498,c_40])).

tff(c_56,plain,
    ( v3_tex_2('#skF_3','#skF_2')
    | ~ v1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_71,plain,(
    ~ v1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_50,plain,
    ( v1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ v3_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_84,plain,(
    ~ v3_tex_2('#skF_3','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_50])).

tff(c_73,plain,(
    ! [A_34] :
      ( u1_struct_0(A_34) = k2_struct_0(A_34)
      | ~ l1_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_79,plain,(
    ! [A_36] :
      ( u1_struct_0(A_36) = k2_struct_0(A_36)
      | ~ l1_pre_topc(A_36) ) ),
    inference(resolution,[status(thm)],[c_14,c_73])).

tff(c_83,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_79])).

tff(c_85,plain,(
    ~ v1_subset_1('#skF_3',k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_71])).

tff(c_86,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_40])).

tff(c_106,plain,(
    ! [B_42,A_43] :
      ( v1_subset_1(B_42,A_43)
      | B_42 = A_43
      | ~ m1_subset_1(B_42,k1_zfmisc_1(A_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_112,plain,
    ( v1_subset_1('#skF_3',k2_struct_0('#skF_2'))
    | k2_struct_0('#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_86,c_106])).

tff(c_119,plain,(
    k2_struct_0('#skF_2') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_112])).

tff(c_16,plain,(
    ! [A_8] :
      ( v1_tops_1(k2_struct_0(A_8),A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_133,plain,
    ( v1_tops_1('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_16])).

tff(c_137,plain,(
    v1_tops_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_133])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k2_subset_1(A_2),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_58,plain,(
    ! [A_2] : m1_subset_1(A_2,k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_46,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_44,plain,(
    v1_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_127,plain,(
    u1_struct_0('#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_83])).

tff(c_197,plain,(
    ! [B_53,A_54] :
      ( v2_tex_2(B_53,A_54)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ l1_pre_topc(A_54)
      | ~ v1_tdlat_3(A_54)
      | ~ v2_pre_topc(A_54)
      | v2_struct_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_200,plain,(
    ! [B_53] :
      ( v2_tex_2(B_53,'#skF_2')
      | ~ m1_subset_1(B_53,k1_zfmisc_1('#skF_3'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v1_tdlat_3('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_197])).

tff(c_210,plain,(
    ! [B_53] :
      ( v2_tex_2(B_53,'#skF_2')
      | ~ m1_subset_1(B_53,k1_zfmisc_1('#skF_3'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_200])).

tff(c_214,plain,(
    ! [B_55] :
      ( v2_tex_2(B_55,'#skF_2')
      | ~ m1_subset_1(B_55,k1_zfmisc_1('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_210])).

tff(c_224,plain,(
    v2_tex_2('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_214])).

tff(c_443,plain,(
    ! [B_87,A_88] :
      ( v3_tex_2(B_87,A_88)
      | ~ v2_tex_2(B_87,A_88)
      | ~ v1_tops_1(B_87,A_88)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ l1_pre_topc(A_88)
      | ~ v2_pre_topc(A_88)
      | v2_struct_0(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_449,plain,(
    ! [B_87] :
      ( v3_tex_2(B_87,'#skF_2')
      | ~ v2_tex_2(B_87,'#skF_2')
      | ~ v1_tops_1(B_87,'#skF_2')
      | ~ m1_subset_1(B_87,k1_zfmisc_1('#skF_3'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_443])).

tff(c_460,plain,(
    ! [B_87] :
      ( v3_tex_2(B_87,'#skF_2')
      | ~ v2_tex_2(B_87,'#skF_2')
      | ~ v1_tops_1(B_87,'#skF_2')
      | ~ m1_subset_1(B_87,k1_zfmisc_1('#skF_3'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_449])).

tff(c_464,plain,(
    ! [B_89] :
      ( v3_tex_2(B_89,'#skF_2')
      | ~ v2_tex_2(B_89,'#skF_2')
      | ~ v1_tops_1(B_89,'#skF_2')
      | ~ m1_subset_1(B_89,k1_zfmisc_1('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_460])).

tff(c_475,plain,
    ( v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ v1_tops_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_464])).

tff(c_480,plain,(
    v3_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_224,c_475])).

tff(c_482,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_480])).

tff(c_483,plain,(
    v3_tex_2('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_537,plain,(
    ! [B_101,A_102] :
      ( v2_tex_2(B_101,A_102)
      | ~ v3_tex_2(B_101,A_102)
      | ~ m1_subset_1(B_101,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ l1_pre_topc(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_562,plain,(
    ! [A_105] :
      ( v2_tex_2(u1_struct_0(A_105),A_105)
      | ~ v3_tex_2(u1_struct_0(A_105),A_105)
      | ~ l1_pre_topc(A_105) ) ),
    inference(resolution,[status(thm)],[c_58,c_537])).

tff(c_565,plain,
    ( v2_tex_2(u1_struct_0('#skF_2'),'#skF_2')
    | ~ v3_tex_2(k2_struct_0('#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_498,c_562])).

tff(c_567,plain,
    ( v2_tex_2(k2_struct_0('#skF_2'),'#skF_2')
    | ~ v3_tex_2(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_498,c_565])).

tff(c_568,plain,(
    ~ v3_tex_2(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_567])).

tff(c_586,plain,(
    ! [B_107,A_108] :
      ( v2_tex_2(B_107,A_108)
      | ~ m1_subset_1(B_107,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ l1_pre_topc(A_108)
      | ~ v1_tdlat_3(A_108)
      | ~ v2_pre_topc(A_108)
      | v2_struct_0(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_593,plain,(
    ! [B_107] :
      ( v2_tex_2(B_107,'#skF_2')
      | ~ m1_subset_1(B_107,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v1_tdlat_3('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_498,c_586])).

tff(c_600,plain,(
    ! [B_107] :
      ( v2_tex_2(B_107,'#skF_2')
      | ~ m1_subset_1(B_107,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_593])).

tff(c_603,plain,(
    ! [B_109] :
      ( v2_tex_2(B_109,'#skF_2')
      | ~ m1_subset_1(B_109,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_600])).

tff(c_618,plain,(
    v2_tex_2(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_603])).

tff(c_909,plain,(
    ! [B_141,A_142] :
      ( v3_tex_2(B_141,A_142)
      | ~ v2_tex_2(B_141,A_142)
      | ~ v1_tops_1(B_141,A_142)
      | ~ m1_subset_1(B_141,k1_zfmisc_1(u1_struct_0(A_142)))
      | ~ l1_pre_topc(A_142)
      | ~ v2_pre_topc(A_142)
      | v2_struct_0(A_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_919,plain,(
    ! [B_141] :
      ( v3_tex_2(B_141,'#skF_2')
      | ~ v2_tex_2(B_141,'#skF_2')
      | ~ v1_tops_1(B_141,'#skF_2')
      | ~ m1_subset_1(B_141,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_498,c_909])).

tff(c_927,plain,(
    ! [B_141] :
      ( v3_tex_2(B_141,'#skF_2')
      | ~ v2_tex_2(B_141,'#skF_2')
      | ~ v1_tops_1(B_141,'#skF_2')
      | ~ m1_subset_1(B_141,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_919])).

tff(c_930,plain,(
    ! [B_143] :
      ( v3_tex_2(B_143,'#skF_2')
      | ~ v2_tex_2(B_143,'#skF_2')
      | ~ v1_tops_1(B_143,'#skF_2')
      | ~ m1_subset_1(B_143,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_927])).

tff(c_944,plain,
    ( v3_tex_2(k2_struct_0('#skF_2'),'#skF_2')
    | ~ v2_tex_2(k2_struct_0('#skF_2'),'#skF_2')
    | ~ v1_tops_1(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_930])).

tff(c_952,plain,
    ( v3_tex_2(k2_struct_0('#skF_2'),'#skF_2')
    | ~ v1_tops_1(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_618,c_944])).

tff(c_953,plain,(
    ~ v1_tops_1(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_568,c_952])).

tff(c_956,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_953])).

tff(c_960,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_956])).

tff(c_961,plain,(
    v2_tex_2(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_567])).

tff(c_506,plain,(
    ! [A_96,B_97] :
      ( r1_tarski(A_96,B_97)
      | ~ m1_subset_1(A_96,k1_zfmisc_1(B_97)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_517,plain,(
    r1_tarski('#skF_3',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_500,c_506])).

tff(c_1421,plain,(
    ! [C_190,B_191,A_192] :
      ( C_190 = B_191
      | ~ r1_tarski(B_191,C_190)
      | ~ v2_tex_2(C_190,A_192)
      | ~ m1_subset_1(C_190,k1_zfmisc_1(u1_struct_0(A_192)))
      | ~ v3_tex_2(B_191,A_192)
      | ~ m1_subset_1(B_191,k1_zfmisc_1(u1_struct_0(A_192)))
      | ~ l1_pre_topc(A_192) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1435,plain,(
    ! [A_192] :
      ( k2_struct_0('#skF_2') = '#skF_3'
      | ~ v2_tex_2(k2_struct_0('#skF_2'),A_192)
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_192)))
      | ~ v3_tex_2('#skF_3',A_192)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_192)))
      | ~ l1_pre_topc(A_192) ) ),
    inference(resolution,[status(thm)],[c_517,c_1421])).

tff(c_1439,plain,(
    ! [A_193] :
      ( ~ v2_tex_2(k2_struct_0('#skF_2'),A_193)
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_193)))
      | ~ v3_tex_2('#skF_3',A_193)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_193)))
      | ~ l1_pre_topc(A_193) ) ),
    inference(splitLeft,[status(thm)],[c_1435])).

tff(c_1445,plain,
    ( ~ v2_tex_2(k2_struct_0('#skF_2'),'#skF_2')
    | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ v3_tex_2('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_498,c_1439])).

tff(c_1449,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_500,c_498,c_483,c_58,c_961,c_1445])).

tff(c_1450,plain,(
    k2_struct_0('#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1435])).

tff(c_484,plain,(
    v1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_499,plain,(
    v1_subset_1('#skF_3',k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_498,c_484])).

tff(c_1468,plain,(
    v1_subset_1('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1450,c_499])).

tff(c_1475,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_1468])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:13:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.57/1.54  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.57/1.55  
% 3.57/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.57/1.55  %$ v3_tex_2 > v2_tex_2 > v1_tops_1 > v1_subset_1 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 3.57/1.55  
% 3.57/1.55  %Foreground sorts:
% 3.57/1.55  
% 3.57/1.55  
% 3.57/1.55  %Background operators:
% 3.57/1.55  
% 3.57/1.55  
% 3.57/1.55  %Foreground operators:
% 3.57/1.55  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.57/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.57/1.55  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.57/1.55  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.57/1.55  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 3.57/1.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.57/1.55  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 3.57/1.55  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 3.57/1.55  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.57/1.55  tff('#skF_2', type, '#skF_2': $i).
% 3.57/1.55  tff('#skF_3', type, '#skF_3': $i).
% 3.57/1.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.57/1.55  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.57/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.57/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.57/1.55  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.57/1.55  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.57/1.55  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.57/1.55  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.57/1.55  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.57/1.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.57/1.55  
% 3.57/1.57  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 3.57/1.57  tff(f_32, axiom, (![A]: ~v1_subset_1(k2_subset_1(A), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc14_subset_1)).
% 3.57/1.57  tff(f_127, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> ~v1_subset_1(B, u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_tex_2)).
% 3.57/1.57  tff(f_44, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.57/1.57  tff(f_40, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.57/1.57  tff(f_61, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 3.57/1.57  tff(f_48, axiom, (![A]: (l1_pre_topc(A) => v1_tops_1(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc12_tops_1)).
% 3.57/1.57  tff(f_29, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.57/1.57  tff(f_93, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_tex_2)).
% 3.57/1.57  tff(f_109, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v1_tops_1(B, A) & v2_tex_2(B, A)) => v3_tex_2(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tex_2)).
% 3.57/1.57  tff(f_79, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 3.57/1.57  tff(f_36, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.57/1.57  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.57/1.57  tff(c_6, plain, (![A_3]: (~v1_subset_1(k2_subset_1(A_3), A_3))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.57/1.57  tff(c_57, plain, (![A_3]: (~v1_subset_1(A_3, A_3))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_6])).
% 3.57/1.57  tff(c_42, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.57/1.57  tff(c_14, plain, (![A_7]: (l1_struct_0(A_7) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.57/1.57  tff(c_486, plain, (![A_91]: (u1_struct_0(A_91)=k2_struct_0(A_91) | ~l1_struct_0(A_91))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.57/1.57  tff(c_494, plain, (![A_93]: (u1_struct_0(A_93)=k2_struct_0(A_93) | ~l1_pre_topc(A_93))), inference(resolution, [status(thm)], [c_14, c_486])).
% 3.57/1.57  tff(c_498, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_494])).
% 3.57/1.57  tff(c_40, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.57/1.57  tff(c_500, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_498, c_40])).
% 3.57/1.57  tff(c_56, plain, (v3_tex_2('#skF_3', '#skF_2') | ~v1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.57/1.57  tff(c_71, plain, (~v1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_56])).
% 3.57/1.57  tff(c_50, plain, (v1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~v3_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.57/1.57  tff(c_84, plain, (~v3_tex_2('#skF_3', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_71, c_50])).
% 3.57/1.57  tff(c_73, plain, (![A_34]: (u1_struct_0(A_34)=k2_struct_0(A_34) | ~l1_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.57/1.57  tff(c_79, plain, (![A_36]: (u1_struct_0(A_36)=k2_struct_0(A_36) | ~l1_pre_topc(A_36))), inference(resolution, [status(thm)], [c_14, c_73])).
% 3.57/1.57  tff(c_83, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_79])).
% 3.57/1.57  tff(c_85, plain, (~v1_subset_1('#skF_3', k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_71])).
% 3.57/1.57  tff(c_86, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_40])).
% 3.57/1.57  tff(c_106, plain, (![B_42, A_43]: (v1_subset_1(B_42, A_43) | B_42=A_43 | ~m1_subset_1(B_42, k1_zfmisc_1(A_43)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.57/1.57  tff(c_112, plain, (v1_subset_1('#skF_3', k2_struct_0('#skF_2')) | k2_struct_0('#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_86, c_106])).
% 3.57/1.57  tff(c_119, plain, (k2_struct_0('#skF_2')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_85, c_112])).
% 3.57/1.57  tff(c_16, plain, (![A_8]: (v1_tops_1(k2_struct_0(A_8), A_8) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.57/1.57  tff(c_133, plain, (v1_tops_1('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_119, c_16])).
% 3.57/1.57  tff(c_137, plain, (v1_tops_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_133])).
% 3.57/1.57  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.57/1.57  tff(c_58, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 3.57/1.57  tff(c_48, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.57/1.57  tff(c_46, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.57/1.57  tff(c_44, plain, (v1_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.57/1.57  tff(c_127, plain, (u1_struct_0('#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_119, c_83])).
% 3.57/1.57  tff(c_197, plain, (![B_53, A_54]: (v2_tex_2(B_53, A_54) | ~m1_subset_1(B_53, k1_zfmisc_1(u1_struct_0(A_54))) | ~l1_pre_topc(A_54) | ~v1_tdlat_3(A_54) | ~v2_pre_topc(A_54) | v2_struct_0(A_54))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.57/1.57  tff(c_200, plain, (![B_53]: (v2_tex_2(B_53, '#skF_2') | ~m1_subset_1(B_53, k1_zfmisc_1('#skF_3')) | ~l1_pre_topc('#skF_2') | ~v1_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_127, c_197])).
% 3.57/1.57  tff(c_210, plain, (![B_53]: (v2_tex_2(B_53, '#skF_2') | ~m1_subset_1(B_53, k1_zfmisc_1('#skF_3')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_200])).
% 3.57/1.57  tff(c_214, plain, (![B_55]: (v2_tex_2(B_55, '#skF_2') | ~m1_subset_1(B_55, k1_zfmisc_1('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_48, c_210])).
% 3.57/1.57  tff(c_224, plain, (v2_tex_2('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_58, c_214])).
% 3.57/1.57  tff(c_443, plain, (![B_87, A_88]: (v3_tex_2(B_87, A_88) | ~v2_tex_2(B_87, A_88) | ~v1_tops_1(B_87, A_88) | ~m1_subset_1(B_87, k1_zfmisc_1(u1_struct_0(A_88))) | ~l1_pre_topc(A_88) | ~v2_pre_topc(A_88) | v2_struct_0(A_88))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.57/1.57  tff(c_449, plain, (![B_87]: (v3_tex_2(B_87, '#skF_2') | ~v2_tex_2(B_87, '#skF_2') | ~v1_tops_1(B_87, '#skF_2') | ~m1_subset_1(B_87, k1_zfmisc_1('#skF_3')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_127, c_443])).
% 3.57/1.57  tff(c_460, plain, (![B_87]: (v3_tex_2(B_87, '#skF_2') | ~v2_tex_2(B_87, '#skF_2') | ~v1_tops_1(B_87, '#skF_2') | ~m1_subset_1(B_87, k1_zfmisc_1('#skF_3')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_42, c_449])).
% 3.57/1.57  tff(c_464, plain, (![B_89]: (v3_tex_2(B_89, '#skF_2') | ~v2_tex_2(B_89, '#skF_2') | ~v1_tops_1(B_89, '#skF_2') | ~m1_subset_1(B_89, k1_zfmisc_1('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_48, c_460])).
% 3.57/1.57  tff(c_475, plain, (v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2') | ~v1_tops_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_58, c_464])).
% 3.57/1.57  tff(c_480, plain, (v3_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_137, c_224, c_475])).
% 3.57/1.57  tff(c_482, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_480])).
% 3.57/1.57  tff(c_483, plain, (v3_tex_2('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_56])).
% 3.57/1.57  tff(c_537, plain, (![B_101, A_102]: (v2_tex_2(B_101, A_102) | ~v3_tex_2(B_101, A_102) | ~m1_subset_1(B_101, k1_zfmisc_1(u1_struct_0(A_102))) | ~l1_pre_topc(A_102))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.57/1.57  tff(c_562, plain, (![A_105]: (v2_tex_2(u1_struct_0(A_105), A_105) | ~v3_tex_2(u1_struct_0(A_105), A_105) | ~l1_pre_topc(A_105))), inference(resolution, [status(thm)], [c_58, c_537])).
% 3.57/1.57  tff(c_565, plain, (v2_tex_2(u1_struct_0('#skF_2'), '#skF_2') | ~v3_tex_2(k2_struct_0('#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_498, c_562])).
% 3.57/1.57  tff(c_567, plain, (v2_tex_2(k2_struct_0('#skF_2'), '#skF_2') | ~v3_tex_2(k2_struct_0('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_498, c_565])).
% 3.57/1.57  tff(c_568, plain, (~v3_tex_2(k2_struct_0('#skF_2'), '#skF_2')), inference(splitLeft, [status(thm)], [c_567])).
% 3.57/1.57  tff(c_586, plain, (![B_107, A_108]: (v2_tex_2(B_107, A_108) | ~m1_subset_1(B_107, k1_zfmisc_1(u1_struct_0(A_108))) | ~l1_pre_topc(A_108) | ~v1_tdlat_3(A_108) | ~v2_pre_topc(A_108) | v2_struct_0(A_108))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.57/1.57  tff(c_593, plain, (![B_107]: (v2_tex_2(B_107, '#skF_2') | ~m1_subset_1(B_107, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v1_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_498, c_586])).
% 3.57/1.57  tff(c_600, plain, (![B_107]: (v2_tex_2(B_107, '#skF_2') | ~m1_subset_1(B_107, k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_593])).
% 3.57/1.57  tff(c_603, plain, (![B_109]: (v2_tex_2(B_109, '#skF_2') | ~m1_subset_1(B_109, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_48, c_600])).
% 3.57/1.57  tff(c_618, plain, (v2_tex_2(k2_struct_0('#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_58, c_603])).
% 3.57/1.57  tff(c_909, plain, (![B_141, A_142]: (v3_tex_2(B_141, A_142) | ~v2_tex_2(B_141, A_142) | ~v1_tops_1(B_141, A_142) | ~m1_subset_1(B_141, k1_zfmisc_1(u1_struct_0(A_142))) | ~l1_pre_topc(A_142) | ~v2_pre_topc(A_142) | v2_struct_0(A_142))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.57/1.57  tff(c_919, plain, (![B_141]: (v3_tex_2(B_141, '#skF_2') | ~v2_tex_2(B_141, '#skF_2') | ~v1_tops_1(B_141, '#skF_2') | ~m1_subset_1(B_141, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_498, c_909])).
% 3.57/1.57  tff(c_927, plain, (![B_141]: (v3_tex_2(B_141, '#skF_2') | ~v2_tex_2(B_141, '#skF_2') | ~v1_tops_1(B_141, '#skF_2') | ~m1_subset_1(B_141, k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_42, c_919])).
% 3.57/1.57  tff(c_930, plain, (![B_143]: (v3_tex_2(B_143, '#skF_2') | ~v2_tex_2(B_143, '#skF_2') | ~v1_tops_1(B_143, '#skF_2') | ~m1_subset_1(B_143, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_48, c_927])).
% 3.57/1.57  tff(c_944, plain, (v3_tex_2(k2_struct_0('#skF_2'), '#skF_2') | ~v2_tex_2(k2_struct_0('#skF_2'), '#skF_2') | ~v1_tops_1(k2_struct_0('#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_58, c_930])).
% 3.57/1.57  tff(c_952, plain, (v3_tex_2(k2_struct_0('#skF_2'), '#skF_2') | ~v1_tops_1(k2_struct_0('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_618, c_944])).
% 3.57/1.57  tff(c_953, plain, (~v1_tops_1(k2_struct_0('#skF_2'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_568, c_952])).
% 3.57/1.57  tff(c_956, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_16, c_953])).
% 3.57/1.57  tff(c_960, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_956])).
% 3.57/1.57  tff(c_961, plain, (v2_tex_2(k2_struct_0('#skF_2'), '#skF_2')), inference(splitRight, [status(thm)], [c_567])).
% 3.57/1.57  tff(c_506, plain, (![A_96, B_97]: (r1_tarski(A_96, B_97) | ~m1_subset_1(A_96, k1_zfmisc_1(B_97)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.57/1.57  tff(c_517, plain, (r1_tarski('#skF_3', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_500, c_506])).
% 3.57/1.57  tff(c_1421, plain, (![C_190, B_191, A_192]: (C_190=B_191 | ~r1_tarski(B_191, C_190) | ~v2_tex_2(C_190, A_192) | ~m1_subset_1(C_190, k1_zfmisc_1(u1_struct_0(A_192))) | ~v3_tex_2(B_191, A_192) | ~m1_subset_1(B_191, k1_zfmisc_1(u1_struct_0(A_192))) | ~l1_pre_topc(A_192))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.57/1.57  tff(c_1435, plain, (![A_192]: (k2_struct_0('#skF_2')='#skF_3' | ~v2_tex_2(k2_struct_0('#skF_2'), A_192) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_192))) | ~v3_tex_2('#skF_3', A_192) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_192))) | ~l1_pre_topc(A_192))), inference(resolution, [status(thm)], [c_517, c_1421])).
% 3.57/1.57  tff(c_1439, plain, (![A_193]: (~v2_tex_2(k2_struct_0('#skF_2'), A_193) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_193))) | ~v3_tex_2('#skF_3', A_193) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_193))) | ~l1_pre_topc(A_193))), inference(splitLeft, [status(thm)], [c_1435])).
% 3.57/1.57  tff(c_1445, plain, (~v2_tex_2(k2_struct_0('#skF_2'), '#skF_2') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~v3_tex_2('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_498, c_1439])).
% 3.57/1.57  tff(c_1449, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_500, c_498, c_483, c_58, c_961, c_1445])).
% 3.57/1.57  tff(c_1450, plain, (k2_struct_0('#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_1435])).
% 3.57/1.57  tff(c_484, plain, (v1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_56])).
% 3.57/1.57  tff(c_499, plain, (v1_subset_1('#skF_3', k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_498, c_484])).
% 3.57/1.57  tff(c_1468, plain, (v1_subset_1('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1450, c_499])).
% 3.57/1.57  tff(c_1475, plain, $false, inference(negUnitSimplification, [status(thm)], [c_57, c_1468])).
% 3.57/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.57/1.57  
% 3.57/1.57  Inference rules
% 3.57/1.57  ----------------------
% 3.57/1.57  #Ref     : 0
% 3.57/1.57  #Sup     : 262
% 3.57/1.57  #Fact    : 0
% 3.57/1.57  #Define  : 0
% 3.57/1.57  #Split   : 3
% 3.57/1.57  #Chain   : 0
% 3.57/1.57  #Close   : 0
% 3.57/1.57  
% 3.57/1.57  Ordering : KBO
% 3.57/1.57  
% 3.57/1.57  Simplification rules
% 3.57/1.57  ----------------------
% 3.57/1.57  #Subsume      : 58
% 3.57/1.57  #Demod        : 270
% 3.57/1.57  #Tautology    : 74
% 3.57/1.57  #SimpNegUnit  : 35
% 3.57/1.57  #BackRed      : 27
% 3.57/1.57  
% 3.57/1.57  #Partial instantiations: 0
% 3.57/1.57  #Strategies tried      : 1
% 3.57/1.57  
% 3.57/1.57  Timing (in seconds)
% 3.57/1.57  ----------------------
% 3.73/1.57  Preprocessing        : 0.32
% 3.73/1.57  Parsing              : 0.17
% 3.73/1.57  CNF conversion       : 0.02
% 3.73/1.57  Main loop            : 0.49
% 3.73/1.57  Inferencing          : 0.18
% 3.73/1.57  Reduction            : 0.15
% 3.73/1.57  Demodulation         : 0.10
% 3.73/1.57  BG Simplification    : 0.02
% 3.73/1.57  Subsumption          : 0.10
% 3.73/1.57  Abstraction          : 0.02
% 3.73/1.57  MUC search           : 0.00
% 3.73/1.57  Cooper               : 0.00
% 3.73/1.57  Total                : 0.85
% 3.73/1.57  Index Insertion      : 0.00
% 3.73/1.57  Index Deletion       : 0.00
% 3.73/1.57  Index Matching       : 0.00
% 3.73/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
