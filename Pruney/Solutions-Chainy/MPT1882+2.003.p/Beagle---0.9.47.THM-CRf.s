%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:13 EST 2020

% Result     : Theorem 5.86s
% Output     : CNFRefutation 5.86s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 455 expanded)
%              Number of leaves         :   30 ( 163 expanded)
%              Depth                    :   12
%              Number of atoms          :  229 (1713 expanded)
%              Number of equality atoms :   10 (  90 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(v2_tdlat_3,type,(
    v2_tdlat_3: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_134,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v2_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ( v3_tex_2(B,A)
            <=> v1_zfmisc_1(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_tex_2)).

tff(f_82,axiom,(
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

tff(f_114,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v2_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ( v2_tex_2(B,A)
          <=> v1_zfmisc_1(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tex_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_95,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_50,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_60,plain,
    ( ~ v1_zfmisc_1('#skF_6')
    | ~ v3_tex_2('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_67,plain,(
    ~ v3_tex_2('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_52,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_48,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_283,plain,(
    ! [A_78,B_79] :
      ( '#skF_4'(A_78,B_79) != B_79
      | v3_tex_2(B_79,A_78)
      | ~ v2_tex_2(B_79,A_78)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ l1_pre_topc(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_298,plain,
    ( '#skF_4'('#skF_5','#skF_6') != '#skF_6'
    | v3_tex_2('#skF_6','#skF_5')
    | ~ v2_tex_2('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_283])).

tff(c_304,plain,
    ( '#skF_4'('#skF_5','#skF_6') != '#skF_6'
    | v3_tex_2('#skF_6','#skF_5')
    | ~ v2_tex_2('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_298])).

tff(c_305,plain,
    ( '#skF_4'('#skF_5','#skF_6') != '#skF_6'
    | ~ v2_tex_2('#skF_6','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_304])).

tff(c_306,plain,(
    ~ v2_tex_2('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_305])).

tff(c_56,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_54,plain,(
    v2_tdlat_3('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_66,plain,
    ( v3_tex_2('#skF_6','#skF_5')
    | v1_zfmisc_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_69,plain,(
    v1_zfmisc_1('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_66])).

tff(c_608,plain,(
    ! [B_115,A_116] :
      ( v2_tex_2(B_115,A_116)
      | ~ v1_zfmisc_1(B_115)
      | ~ m1_subset_1(B_115,k1_zfmisc_1(u1_struct_0(A_116)))
      | v1_xboole_0(B_115)
      | ~ l1_pre_topc(A_116)
      | ~ v2_tdlat_3(A_116)
      | ~ v2_pre_topc(A_116)
      | v2_struct_0(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_634,plain,
    ( v2_tex_2('#skF_6','#skF_5')
    | ~ v1_zfmisc_1('#skF_6')
    | v1_xboole_0('#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_tdlat_3('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_608])).

tff(c_643,plain,
    ( v2_tex_2('#skF_6','#skF_5')
    | v1_xboole_0('#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_69,c_634])).

tff(c_645,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_50,c_306,c_643])).

tff(c_647,plain,(
    v2_tex_2('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_305])).

tff(c_739,plain,(
    ! [B_130,A_131] :
      ( r1_tarski(B_130,'#skF_4'(A_131,B_130))
      | v3_tex_2(B_130,A_131)
      | ~ v2_tex_2(B_130,A_131)
      | ~ m1_subset_1(B_130,k1_zfmisc_1(u1_struct_0(A_131)))
      | ~ l1_pre_topc(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_753,plain,
    ( r1_tarski('#skF_6','#skF_4'('#skF_5','#skF_6'))
    | v3_tex_2('#skF_6','#skF_5')
    | ~ v2_tex_2('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_739])).

tff(c_760,plain,
    ( r1_tarski('#skF_6','#skF_4'('#skF_5','#skF_6'))
    | v3_tex_2('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_647,c_753])).

tff(c_761,plain,(
    r1_tarski('#skF_6','#skF_4'('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_760])).

tff(c_8,plain,(
    ! [C_9,A_5] :
      ( r2_hidden(C_9,k1_zfmisc_1(A_5))
      | ~ r1_tarski(C_9,A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_122,plain,(
    ! [B_49,A_50] :
      ( m1_subset_1(B_49,A_50)
      | ~ r2_hidden(B_49,A_50)
      | v1_xboole_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_162,plain,(
    ! [C_58,A_59] :
      ( m1_subset_1(C_58,k1_zfmisc_1(A_59))
      | v1_xboole_0(k1_zfmisc_1(A_59))
      | ~ r1_tarski(C_58,A_59) ) ),
    inference(resolution,[status(thm)],[c_8,c_122])).

tff(c_26,plain,(
    ! [B_14,A_12] :
      ( v1_xboole_0(B_14)
      | ~ m1_subset_1(B_14,k1_zfmisc_1(A_12))
      | ~ v1_xboole_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_169,plain,(
    ! [C_58,A_59] :
      ( v1_xboole_0(C_58)
      | ~ v1_xboole_0(A_59)
      | v1_xboole_0(k1_zfmisc_1(A_59))
      | ~ r1_tarski(C_58,A_59) ) ),
    inference(resolution,[status(thm)],[c_162,c_26])).

tff(c_765,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0('#skF_4'('#skF_5','#skF_6'))
    | v1_xboole_0(k1_zfmisc_1('#skF_4'('#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_761,c_169])).

tff(c_772,plain,
    ( ~ v1_xboole_0('#skF_4'('#skF_5','#skF_6'))
    | v1_xboole_0(k1_zfmisc_1('#skF_4'('#skF_5','#skF_6'))) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_765])).

tff(c_777,plain,(
    ~ v1_xboole_0('#skF_4'('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_772])).

tff(c_646,plain,(
    '#skF_4'('#skF_5','#skF_6') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_305])).

tff(c_42,plain,(
    ! [B_28,A_26] :
      ( B_28 = A_26
      | ~ r1_tarski(A_26,B_28)
      | ~ v1_zfmisc_1(B_28)
      | v1_xboole_0(B_28)
      | v1_xboole_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_768,plain,
    ( '#skF_4'('#skF_5','#skF_6') = '#skF_6'
    | ~ v1_zfmisc_1('#skF_4'('#skF_5','#skF_6'))
    | v1_xboole_0('#skF_4'('#skF_5','#skF_6'))
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_761,c_42])).

tff(c_775,plain,
    ( ~ v1_zfmisc_1('#skF_4'('#skF_5','#skF_6'))
    | v1_xboole_0('#skF_4'('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_646,c_768])).

tff(c_776,plain,(
    ~ v1_zfmisc_1('#skF_4'('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_775])).

tff(c_670,plain,(
    ! [A_124,B_125] :
      ( v2_tex_2('#skF_4'(A_124,B_125),A_124)
      | v3_tex_2(B_125,A_124)
      | ~ v2_tex_2(B_125,A_124)
      | ~ m1_subset_1(B_125,k1_zfmisc_1(u1_struct_0(A_124)))
      | ~ l1_pre_topc(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_681,plain,
    ( v2_tex_2('#skF_4'('#skF_5','#skF_6'),'#skF_5')
    | v3_tex_2('#skF_6','#skF_5')
    | ~ v2_tex_2('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_670])).

tff(c_687,plain,
    ( v2_tex_2('#skF_4'('#skF_5','#skF_6'),'#skF_5')
    | v3_tex_2('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_647,c_681])).

tff(c_688,plain,(
    v2_tex_2('#skF_4'('#skF_5','#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_687])).

tff(c_36,plain,(
    ! [A_16,B_22] :
      ( m1_subset_1('#skF_4'(A_16,B_22),k1_zfmisc_1(u1_struct_0(A_16)))
      | v3_tex_2(B_22,A_16)
      | ~ v2_tex_2(B_22,A_16)
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_961,plain,(
    ! [B_150,A_151] :
      ( v1_zfmisc_1(B_150)
      | ~ v2_tex_2(B_150,A_151)
      | ~ m1_subset_1(B_150,k1_zfmisc_1(u1_struct_0(A_151)))
      | v1_xboole_0(B_150)
      | ~ l1_pre_topc(A_151)
      | ~ v2_tdlat_3(A_151)
      | ~ v2_pre_topc(A_151)
      | v2_struct_0(A_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_2316,plain,(
    ! [A_244,B_245] :
      ( v1_zfmisc_1('#skF_4'(A_244,B_245))
      | ~ v2_tex_2('#skF_4'(A_244,B_245),A_244)
      | v1_xboole_0('#skF_4'(A_244,B_245))
      | ~ v2_tdlat_3(A_244)
      | ~ v2_pre_topc(A_244)
      | v2_struct_0(A_244)
      | v3_tex_2(B_245,A_244)
      | ~ v2_tex_2(B_245,A_244)
      | ~ m1_subset_1(B_245,k1_zfmisc_1(u1_struct_0(A_244)))
      | ~ l1_pre_topc(A_244) ) ),
    inference(resolution,[status(thm)],[c_36,c_961])).

tff(c_2324,plain,
    ( v1_zfmisc_1('#skF_4'('#skF_5','#skF_6'))
    | v1_xboole_0('#skF_4'('#skF_5','#skF_6'))
    | ~ v2_tdlat_3('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5')
    | v3_tex_2('#skF_6','#skF_5')
    | ~ v2_tex_2('#skF_6','#skF_5')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_688,c_2316])).

tff(c_2333,plain,
    ( v1_zfmisc_1('#skF_4'('#skF_5','#skF_6'))
    | v1_xboole_0('#skF_4'('#skF_5','#skF_6'))
    | v2_struct_0('#skF_5')
    | v3_tex_2('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_647,c_56,c_54,c_2324])).

tff(c_2335,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_58,c_777,c_776,c_2333])).

tff(c_2336,plain,(
    v1_xboole_0(k1_zfmisc_1('#skF_4'('#skF_5','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_772])).

tff(c_82,plain,(
    ! [C_37,A_38] :
      ( r2_hidden(C_37,k1_zfmisc_1(A_38))
      | ~ r1_tarski(C_37,A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_86,plain,(
    ! [A_38,C_37] :
      ( ~ v1_xboole_0(k1_zfmisc_1(A_38))
      | ~ r1_tarski(C_37,A_38) ) ),
    inference(resolution,[status(thm)],[c_82,c_2])).

tff(c_2340,plain,(
    ! [C_37] : ~ r1_tarski(C_37,'#skF_4'('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_2336,c_86])).

tff(c_2342,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2340,c_761])).

tff(c_2343,plain,(
    v1_xboole_0('#skF_4'('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_775])).

tff(c_2345,plain,(
    ~ v1_xboole_0('#skF_4'('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_772])).

tff(c_2347,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2343,c_2345])).

tff(c_2348,plain,(
    v1_xboole_0(k1_zfmisc_1('#skF_4'('#skF_5','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_772])).

tff(c_2380,plain,(
    ! [C_37] : ~ r1_tarski(C_37,'#skF_4'('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_2348,c_86])).

tff(c_2382,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2380,c_761])).

tff(c_2383,plain,(
    ~ v1_zfmisc_1('#skF_6') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_2384,plain,(
    v3_tex_2('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_2555,plain,(
    ! [B_285,A_286] :
      ( v2_tex_2(B_285,A_286)
      | ~ v3_tex_2(B_285,A_286)
      | ~ m1_subset_1(B_285,k1_zfmisc_1(u1_struct_0(A_286)))
      | ~ l1_pre_topc(A_286) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2570,plain,
    ( v2_tex_2('#skF_6','#skF_5')
    | ~ v3_tex_2('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_2555])).

tff(c_2576,plain,(
    v2_tex_2('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_2384,c_2570])).

tff(c_2947,plain,(
    ! [B_335,A_336] :
      ( v1_zfmisc_1(B_335)
      | ~ v2_tex_2(B_335,A_336)
      | ~ m1_subset_1(B_335,k1_zfmisc_1(u1_struct_0(A_336)))
      | v1_xboole_0(B_335)
      | ~ l1_pre_topc(A_336)
      | ~ v2_tdlat_3(A_336)
      | ~ v2_pre_topc(A_336)
      | v2_struct_0(A_336) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_2973,plain,
    ( v1_zfmisc_1('#skF_6')
    | ~ v2_tex_2('#skF_6','#skF_5')
    | v1_xboole_0('#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_tdlat_3('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_2947])).

tff(c_2982,plain,
    ( v1_zfmisc_1('#skF_6')
    | v1_xboole_0('#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_2576,c_2973])).

tff(c_2984,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_50,c_2383,c_2982])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:44:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.86/2.08  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.86/2.09  
% 5.86/2.09  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.86/2.09  %$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 5.86/2.09  
% 5.86/2.09  %Foreground sorts:
% 5.86/2.09  
% 5.86/2.09  
% 5.86/2.09  %Background operators:
% 5.86/2.09  
% 5.86/2.09  
% 5.86/2.09  %Foreground operators:
% 5.86/2.09  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.86/2.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.86/2.09  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.86/2.09  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.86/2.09  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.86/2.09  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.86/2.09  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.86/2.09  tff('#skF_5', type, '#skF_5': $i).
% 5.86/2.09  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 5.86/2.09  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 5.86/2.09  tff('#skF_6', type, '#skF_6': $i).
% 5.86/2.09  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.86/2.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.86/2.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.86/2.09  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.86/2.09  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 5.86/2.09  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.86/2.09  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.86/2.09  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.86/2.09  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 5.86/2.09  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 5.86/2.09  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.86/2.09  
% 5.86/2.11  tff(f_134, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v3_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_tex_2)).
% 5.86/2.11  tff(f_82, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 5.86/2.11  tff(f_114, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tex_2)).
% 5.86/2.11  tff(f_38, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 5.86/2.11  tff(f_51, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 5.86/2.11  tff(f_58, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 5.86/2.11  tff(f_95, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 5.86/2.11  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.86/2.11  tff(c_58, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_134])).
% 5.86/2.11  tff(c_50, plain, (~v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_134])).
% 5.86/2.11  tff(c_60, plain, (~v1_zfmisc_1('#skF_6') | ~v3_tex_2('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_134])).
% 5.86/2.11  tff(c_67, plain, (~v3_tex_2('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_60])).
% 5.86/2.11  tff(c_52, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_134])).
% 5.86/2.11  tff(c_48, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_134])).
% 5.86/2.11  tff(c_283, plain, (![A_78, B_79]: ('#skF_4'(A_78, B_79)!=B_79 | v3_tex_2(B_79, A_78) | ~v2_tex_2(B_79, A_78) | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0(A_78))) | ~l1_pre_topc(A_78))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.86/2.11  tff(c_298, plain, ('#skF_4'('#skF_5', '#skF_6')!='#skF_6' | v3_tex_2('#skF_6', '#skF_5') | ~v2_tex_2('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_48, c_283])).
% 5.86/2.11  tff(c_304, plain, ('#skF_4'('#skF_5', '#skF_6')!='#skF_6' | v3_tex_2('#skF_6', '#skF_5') | ~v2_tex_2('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_298])).
% 5.86/2.11  tff(c_305, plain, ('#skF_4'('#skF_5', '#skF_6')!='#skF_6' | ~v2_tex_2('#skF_6', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_67, c_304])).
% 5.86/2.11  tff(c_306, plain, (~v2_tex_2('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_305])).
% 5.86/2.11  tff(c_56, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_134])).
% 5.86/2.11  tff(c_54, plain, (v2_tdlat_3('#skF_5')), inference(cnfTransformation, [status(thm)], [f_134])).
% 5.86/2.11  tff(c_66, plain, (v3_tex_2('#skF_6', '#skF_5') | v1_zfmisc_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_134])).
% 5.86/2.11  tff(c_69, plain, (v1_zfmisc_1('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_67, c_66])).
% 5.86/2.11  tff(c_608, plain, (![B_115, A_116]: (v2_tex_2(B_115, A_116) | ~v1_zfmisc_1(B_115) | ~m1_subset_1(B_115, k1_zfmisc_1(u1_struct_0(A_116))) | v1_xboole_0(B_115) | ~l1_pre_topc(A_116) | ~v2_tdlat_3(A_116) | ~v2_pre_topc(A_116) | v2_struct_0(A_116))), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.86/2.11  tff(c_634, plain, (v2_tex_2('#skF_6', '#skF_5') | ~v1_zfmisc_1('#skF_6') | v1_xboole_0('#skF_6') | ~l1_pre_topc('#skF_5') | ~v2_tdlat_3('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_48, c_608])).
% 5.86/2.11  tff(c_643, plain, (v2_tex_2('#skF_6', '#skF_5') | v1_xboole_0('#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_69, c_634])).
% 5.86/2.11  tff(c_645, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_50, c_306, c_643])).
% 5.86/2.11  tff(c_647, plain, (v2_tex_2('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_305])).
% 5.86/2.11  tff(c_739, plain, (![B_130, A_131]: (r1_tarski(B_130, '#skF_4'(A_131, B_130)) | v3_tex_2(B_130, A_131) | ~v2_tex_2(B_130, A_131) | ~m1_subset_1(B_130, k1_zfmisc_1(u1_struct_0(A_131))) | ~l1_pre_topc(A_131))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.86/2.11  tff(c_753, plain, (r1_tarski('#skF_6', '#skF_4'('#skF_5', '#skF_6')) | v3_tex_2('#skF_6', '#skF_5') | ~v2_tex_2('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_48, c_739])).
% 5.86/2.11  tff(c_760, plain, (r1_tarski('#skF_6', '#skF_4'('#skF_5', '#skF_6')) | v3_tex_2('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_647, c_753])).
% 5.86/2.11  tff(c_761, plain, (r1_tarski('#skF_6', '#skF_4'('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_67, c_760])).
% 5.86/2.11  tff(c_8, plain, (![C_9, A_5]: (r2_hidden(C_9, k1_zfmisc_1(A_5)) | ~r1_tarski(C_9, A_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.86/2.11  tff(c_122, plain, (![B_49, A_50]: (m1_subset_1(B_49, A_50) | ~r2_hidden(B_49, A_50) | v1_xboole_0(A_50))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.86/2.11  tff(c_162, plain, (![C_58, A_59]: (m1_subset_1(C_58, k1_zfmisc_1(A_59)) | v1_xboole_0(k1_zfmisc_1(A_59)) | ~r1_tarski(C_58, A_59))), inference(resolution, [status(thm)], [c_8, c_122])).
% 5.86/2.11  tff(c_26, plain, (![B_14, A_12]: (v1_xboole_0(B_14) | ~m1_subset_1(B_14, k1_zfmisc_1(A_12)) | ~v1_xboole_0(A_12))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.86/2.11  tff(c_169, plain, (![C_58, A_59]: (v1_xboole_0(C_58) | ~v1_xboole_0(A_59) | v1_xboole_0(k1_zfmisc_1(A_59)) | ~r1_tarski(C_58, A_59))), inference(resolution, [status(thm)], [c_162, c_26])).
% 5.86/2.11  tff(c_765, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0('#skF_4'('#skF_5', '#skF_6')) | v1_xboole_0(k1_zfmisc_1('#skF_4'('#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_761, c_169])).
% 5.86/2.11  tff(c_772, plain, (~v1_xboole_0('#skF_4'('#skF_5', '#skF_6')) | v1_xboole_0(k1_zfmisc_1('#skF_4'('#skF_5', '#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_50, c_765])).
% 5.86/2.11  tff(c_777, plain, (~v1_xboole_0('#skF_4'('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_772])).
% 5.86/2.11  tff(c_646, plain, ('#skF_4'('#skF_5', '#skF_6')!='#skF_6'), inference(splitRight, [status(thm)], [c_305])).
% 5.86/2.11  tff(c_42, plain, (![B_28, A_26]: (B_28=A_26 | ~r1_tarski(A_26, B_28) | ~v1_zfmisc_1(B_28) | v1_xboole_0(B_28) | v1_xboole_0(A_26))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.86/2.11  tff(c_768, plain, ('#skF_4'('#skF_5', '#skF_6')='#skF_6' | ~v1_zfmisc_1('#skF_4'('#skF_5', '#skF_6')) | v1_xboole_0('#skF_4'('#skF_5', '#skF_6')) | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_761, c_42])).
% 5.86/2.11  tff(c_775, plain, (~v1_zfmisc_1('#skF_4'('#skF_5', '#skF_6')) | v1_xboole_0('#skF_4'('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_50, c_646, c_768])).
% 5.86/2.11  tff(c_776, plain, (~v1_zfmisc_1('#skF_4'('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_775])).
% 5.86/2.11  tff(c_670, plain, (![A_124, B_125]: (v2_tex_2('#skF_4'(A_124, B_125), A_124) | v3_tex_2(B_125, A_124) | ~v2_tex_2(B_125, A_124) | ~m1_subset_1(B_125, k1_zfmisc_1(u1_struct_0(A_124))) | ~l1_pre_topc(A_124))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.86/2.11  tff(c_681, plain, (v2_tex_2('#skF_4'('#skF_5', '#skF_6'), '#skF_5') | v3_tex_2('#skF_6', '#skF_5') | ~v2_tex_2('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_48, c_670])).
% 5.86/2.11  tff(c_687, plain, (v2_tex_2('#skF_4'('#skF_5', '#skF_6'), '#skF_5') | v3_tex_2('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_647, c_681])).
% 5.86/2.11  tff(c_688, plain, (v2_tex_2('#skF_4'('#skF_5', '#skF_6'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_67, c_687])).
% 5.86/2.11  tff(c_36, plain, (![A_16, B_22]: (m1_subset_1('#skF_4'(A_16, B_22), k1_zfmisc_1(u1_struct_0(A_16))) | v3_tex_2(B_22, A_16) | ~v2_tex_2(B_22, A_16) | ~m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0(A_16))) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.86/2.11  tff(c_961, plain, (![B_150, A_151]: (v1_zfmisc_1(B_150) | ~v2_tex_2(B_150, A_151) | ~m1_subset_1(B_150, k1_zfmisc_1(u1_struct_0(A_151))) | v1_xboole_0(B_150) | ~l1_pre_topc(A_151) | ~v2_tdlat_3(A_151) | ~v2_pre_topc(A_151) | v2_struct_0(A_151))), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.86/2.11  tff(c_2316, plain, (![A_244, B_245]: (v1_zfmisc_1('#skF_4'(A_244, B_245)) | ~v2_tex_2('#skF_4'(A_244, B_245), A_244) | v1_xboole_0('#skF_4'(A_244, B_245)) | ~v2_tdlat_3(A_244) | ~v2_pre_topc(A_244) | v2_struct_0(A_244) | v3_tex_2(B_245, A_244) | ~v2_tex_2(B_245, A_244) | ~m1_subset_1(B_245, k1_zfmisc_1(u1_struct_0(A_244))) | ~l1_pre_topc(A_244))), inference(resolution, [status(thm)], [c_36, c_961])).
% 5.86/2.11  tff(c_2324, plain, (v1_zfmisc_1('#skF_4'('#skF_5', '#skF_6')) | v1_xboole_0('#skF_4'('#skF_5', '#skF_6')) | ~v2_tdlat_3('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | v3_tex_2('#skF_6', '#skF_5') | ~v2_tex_2('#skF_6', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_688, c_2316])).
% 5.86/2.11  tff(c_2333, plain, (v1_zfmisc_1('#skF_4'('#skF_5', '#skF_6')) | v1_xboole_0('#skF_4'('#skF_5', '#skF_6')) | v2_struct_0('#skF_5') | v3_tex_2('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_647, c_56, c_54, c_2324])).
% 5.86/2.11  tff(c_2335, plain, $false, inference(negUnitSimplification, [status(thm)], [c_67, c_58, c_777, c_776, c_2333])).
% 5.86/2.11  tff(c_2336, plain, (v1_xboole_0(k1_zfmisc_1('#skF_4'('#skF_5', '#skF_6')))), inference(splitRight, [status(thm)], [c_772])).
% 5.86/2.11  tff(c_82, plain, (![C_37, A_38]: (r2_hidden(C_37, k1_zfmisc_1(A_38)) | ~r1_tarski(C_37, A_38))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.86/2.11  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.86/2.11  tff(c_86, plain, (![A_38, C_37]: (~v1_xboole_0(k1_zfmisc_1(A_38)) | ~r1_tarski(C_37, A_38))), inference(resolution, [status(thm)], [c_82, c_2])).
% 5.86/2.11  tff(c_2340, plain, (![C_37]: (~r1_tarski(C_37, '#skF_4'('#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_2336, c_86])).
% 5.86/2.11  tff(c_2342, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2340, c_761])).
% 5.86/2.11  tff(c_2343, plain, (v1_xboole_0('#skF_4'('#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_775])).
% 5.86/2.11  tff(c_2345, plain, (~v1_xboole_0('#skF_4'('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_772])).
% 5.86/2.11  tff(c_2347, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2343, c_2345])).
% 5.86/2.11  tff(c_2348, plain, (v1_xboole_0(k1_zfmisc_1('#skF_4'('#skF_5', '#skF_6')))), inference(splitRight, [status(thm)], [c_772])).
% 5.86/2.11  tff(c_2380, plain, (![C_37]: (~r1_tarski(C_37, '#skF_4'('#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_2348, c_86])).
% 5.86/2.11  tff(c_2382, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2380, c_761])).
% 5.86/2.11  tff(c_2383, plain, (~v1_zfmisc_1('#skF_6')), inference(splitRight, [status(thm)], [c_60])).
% 5.86/2.11  tff(c_2384, plain, (v3_tex_2('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_60])).
% 5.86/2.11  tff(c_2555, plain, (![B_285, A_286]: (v2_tex_2(B_285, A_286) | ~v3_tex_2(B_285, A_286) | ~m1_subset_1(B_285, k1_zfmisc_1(u1_struct_0(A_286))) | ~l1_pre_topc(A_286))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.86/2.11  tff(c_2570, plain, (v2_tex_2('#skF_6', '#skF_5') | ~v3_tex_2('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_48, c_2555])).
% 5.86/2.11  tff(c_2576, plain, (v2_tex_2('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_2384, c_2570])).
% 5.86/2.11  tff(c_2947, plain, (![B_335, A_336]: (v1_zfmisc_1(B_335) | ~v2_tex_2(B_335, A_336) | ~m1_subset_1(B_335, k1_zfmisc_1(u1_struct_0(A_336))) | v1_xboole_0(B_335) | ~l1_pre_topc(A_336) | ~v2_tdlat_3(A_336) | ~v2_pre_topc(A_336) | v2_struct_0(A_336))), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.86/2.11  tff(c_2973, plain, (v1_zfmisc_1('#skF_6') | ~v2_tex_2('#skF_6', '#skF_5') | v1_xboole_0('#skF_6') | ~l1_pre_topc('#skF_5') | ~v2_tdlat_3('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_48, c_2947])).
% 5.86/2.11  tff(c_2982, plain, (v1_zfmisc_1('#skF_6') | v1_xboole_0('#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_2576, c_2973])).
% 5.86/2.11  tff(c_2984, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_50, c_2383, c_2982])).
% 5.86/2.11  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.86/2.11  
% 5.86/2.11  Inference rules
% 5.86/2.11  ----------------------
% 5.86/2.11  #Ref     : 1
% 5.86/2.11  #Sup     : 666
% 5.86/2.11  #Fact    : 1
% 5.86/2.11  #Define  : 0
% 5.86/2.11  #Split   : 9
% 5.86/2.11  #Chain   : 0
% 5.86/2.11  #Close   : 0
% 5.86/2.11  
% 5.86/2.11  Ordering : KBO
% 5.86/2.11  
% 5.86/2.11  Simplification rules
% 5.86/2.11  ----------------------
% 5.86/2.11  #Subsume      : 131
% 5.86/2.11  #Demod        : 94
% 5.86/2.11  #Tautology    : 63
% 5.86/2.11  #SimpNegUnit  : 41
% 5.86/2.11  #BackRed      : 2
% 5.86/2.11  
% 5.86/2.11  #Partial instantiations: 0
% 5.86/2.11  #Strategies tried      : 1
% 5.86/2.11  
% 5.86/2.11  Timing (in seconds)
% 5.86/2.11  ----------------------
% 5.86/2.11  Preprocessing        : 0.33
% 5.86/2.11  Parsing              : 0.18
% 5.86/2.11  CNF conversion       : 0.03
% 5.86/2.11  Main loop            : 1.03
% 5.86/2.11  Inferencing          : 0.35
% 5.86/2.11  Reduction            : 0.24
% 5.86/2.11  Demodulation         : 0.15
% 5.86/2.11  BG Simplification    : 0.05
% 5.86/2.11  Subsumption          : 0.30
% 5.86/2.11  Abstraction          : 0.06
% 5.86/2.11  MUC search           : 0.00
% 5.86/2.11  Cooper               : 0.00
% 5.86/2.11  Total                : 1.40
% 5.86/2.11  Index Insertion      : 0.00
% 5.86/2.11  Index Deletion       : 0.00
% 5.86/2.11  Index Matching       : 0.00
% 5.86/2.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
