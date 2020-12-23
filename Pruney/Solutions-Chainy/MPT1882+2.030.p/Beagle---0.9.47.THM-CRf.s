%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:16 EST 2020

% Result     : Theorem 2.49s
% Output     : CNFRefutation 2.78s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 299 expanded)
%              Number of leaves         :   28 ( 115 expanded)
%              Depth                    :   11
%              Number of atoms          :  205 (1126 expanded)
%              Number of equality atoms :    9 (  45 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(v2_tdlat_3,type,(
    v2_tdlat_3: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_136,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_tex_2)).

tff(f_84,axiom,(
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

tff(f_116,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tex_2)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_97,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_36,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_52,plain,
    ( v3_tex_2('#skF_4','#skF_3')
    | v1_zfmisc_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_54,plain,(
    v1_zfmisc_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_46,plain,
    ( ~ v1_zfmisc_1('#skF_4')
    | ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_57,plain,(
    ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_46])).

tff(c_38,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_102,plain,(
    ! [A_52,B_53] :
      ( '#skF_2'(A_52,B_53) != B_53
      | v3_tex_2(B_53,A_52)
      | ~ v2_tex_2(B_53,A_52)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(u1_struct_0(A_52)))
      | ~ l1_pre_topc(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_105,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_102])).

tff(c_108,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_105])).

tff(c_109,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_108])).

tff(c_110,plain,(
    ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_109])).

tff(c_42,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_40,plain,(
    v2_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_125,plain,(
    ! [B_58,A_59] :
      ( v2_tex_2(B_58,A_59)
      | ~ v1_zfmisc_1(B_58)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(u1_struct_0(A_59)))
      | v1_xboole_0(B_58)
      | ~ l1_pre_topc(A_59)
      | ~ v2_tdlat_3(A_59)
      | ~ v2_pre_topc(A_59)
      | v2_struct_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_128,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | ~ v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_125])).

tff(c_131,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_54,c_128])).

tff(c_133,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_36,c_110,c_131])).

tff(c_135,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_109])).

tff(c_143,plain,(
    ! [B_62,A_63] :
      ( r1_tarski(B_62,'#skF_2'(A_63,B_62))
      | v3_tex_2(B_62,A_63)
      | ~ v2_tex_2(B_62,A_63)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ l1_pre_topc(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_145,plain,
    ( r1_tarski('#skF_4','#skF_2'('#skF_3','#skF_4'))
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_143])).

tff(c_148,plain,
    ( r1_tarski('#skF_4','#skF_2'('#skF_3','#skF_4'))
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_135,c_145])).

tff(c_149,plain,(
    r1_tarski('#skF_4','#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_148])).

tff(c_65,plain,(
    ! [A_33,B_34] :
      ( r2_hidden('#skF_1'(A_33,B_34),B_34)
      | r1_xboole_0(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( ~ v1_xboole_0(B_9)
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_69,plain,(
    ! [B_34,A_33] :
      ( ~ v1_xboole_0(B_34)
      | r1_xboole_0(A_33,B_34) ) ),
    inference(resolution,[status(thm)],[c_65,c_10])).

tff(c_71,plain,(
    ! [B_37,A_38] :
      ( ~ r1_xboole_0(B_37,A_38)
      | ~ r1_tarski(B_37,A_38)
      | v1_xboole_0(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_75,plain,(
    ! [A_33,B_34] :
      ( ~ r1_tarski(A_33,B_34)
      | v1_xboole_0(A_33)
      | ~ v1_xboole_0(B_34) ) ),
    inference(resolution,[status(thm)],[c_69,c_71])).

tff(c_155,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_149,c_75])).

tff(c_161,plain,(
    ~ v1_xboole_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_155])).

tff(c_134,plain,(
    '#skF_2'('#skF_3','#skF_4') != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_109])).

tff(c_28,plain,(
    ! [B_24,A_22] :
      ( B_24 = A_22
      | ~ r1_tarski(A_22,B_24)
      | ~ v1_zfmisc_1(B_24)
      | v1_xboole_0(B_24)
      | v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_152,plain,
    ( '#skF_2'('#skF_3','#skF_4') = '#skF_4'
    | ~ v1_zfmisc_1('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_149,c_28])).

tff(c_158,plain,
    ( ~ v1_zfmisc_1('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_134,c_152])).

tff(c_162,plain,(
    ~ v1_zfmisc_1('#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_161,c_158])).

tff(c_136,plain,(
    ! [A_60,B_61] :
      ( v2_tex_2('#skF_2'(A_60,B_61),A_60)
      | v3_tex_2(B_61,A_60)
      | ~ v2_tex_2(B_61,A_60)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ l1_pre_topc(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_138,plain,
    ( v2_tex_2('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_136])).

tff(c_141,plain,
    ( v2_tex_2('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_135,c_138])).

tff(c_142,plain,(
    v2_tex_2('#skF_2'('#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_141])).

tff(c_175,plain,(
    ! [A_66,B_67] :
      ( m1_subset_1('#skF_2'(A_66,B_67),k1_zfmisc_1(u1_struct_0(A_66)))
      | v3_tex_2(B_67,A_66)
      | ~ v2_tex_2(B_67,A_66)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ l1_pre_topc(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_32,plain,(
    ! [B_27,A_25] :
      ( v1_zfmisc_1(B_27)
      | ~ v2_tex_2(B_27,A_25)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(u1_struct_0(A_25)))
      | v1_xboole_0(B_27)
      | ~ l1_pre_topc(A_25)
      | ~ v2_tdlat_3(A_25)
      | ~ v2_pre_topc(A_25)
      | v2_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_233,plain,(
    ! [A_78,B_79] :
      ( v1_zfmisc_1('#skF_2'(A_78,B_79))
      | ~ v2_tex_2('#skF_2'(A_78,B_79),A_78)
      | v1_xboole_0('#skF_2'(A_78,B_79))
      | ~ v2_tdlat_3(A_78)
      | ~ v2_pre_topc(A_78)
      | v2_struct_0(A_78)
      | v3_tex_2(B_79,A_78)
      | ~ v2_tex_2(B_79,A_78)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ l1_pre_topc(A_78) ) ),
    inference(resolution,[status(thm)],[c_175,c_32])).

tff(c_237,plain,
    ( v1_zfmisc_1('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_2'('#skF_3','#skF_4'))
    | ~ v2_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_142,c_233])).

tff(c_241,plain,
    ( v1_zfmisc_1('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_2'('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3')
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_135,c_42,c_40,c_237])).

tff(c_243,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_44,c_161,c_162,c_241])).

tff(c_245,plain,(
    ~ v1_zfmisc_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_244,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_290,plain,(
    ! [B_100,A_101] :
      ( v2_tex_2(B_100,A_101)
      | ~ v3_tex_2(B_100,A_101)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ l1_pre_topc(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_293,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | ~ v3_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_290])).

tff(c_296,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_244,c_293])).

tff(c_316,plain,(
    ! [B_108,A_109] :
      ( v1_zfmisc_1(B_108)
      | ~ v2_tex_2(B_108,A_109)
      | ~ m1_subset_1(B_108,k1_zfmisc_1(u1_struct_0(A_109)))
      | v1_xboole_0(B_108)
      | ~ l1_pre_topc(A_109)
      | ~ v2_tdlat_3(A_109)
      | ~ v2_pre_topc(A_109)
      | v2_struct_0(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_319,plain,
    ( v1_zfmisc_1('#skF_4')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_316])).

tff(c_322,plain,
    ( v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_296,c_319])).

tff(c_324,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_36,c_245,c_322])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.10  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.10/0.30  % Computer   : n020.cluster.edu
% 0.10/0.30  % Model      : x86_64 x86_64
% 0.10/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.30  % Memory     : 8042.1875MB
% 0.10/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.30  % CPULimit   : 60
% 0.10/0.30  % DateTime   : Tue Dec  1 16:23:22 EST 2020
% 0.10/0.30  % CPUTime    : 
% 0.16/0.31  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.49/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.49/1.39  
% 2.49/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.49/1.39  %$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.49/1.39  
% 2.49/1.39  %Foreground sorts:
% 2.49/1.39  
% 2.49/1.39  
% 2.49/1.39  %Background operators:
% 2.49/1.39  
% 2.49/1.39  
% 2.49/1.39  %Foreground operators:
% 2.49/1.39  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.49/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.49/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.49/1.39  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.49/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.49/1.39  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 2.49/1.39  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.49/1.39  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.49/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.49/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.49/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.49/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.49/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.49/1.39  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.49/1.39  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.49/1.39  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.49/1.39  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.49/1.39  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.49/1.39  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.49/1.39  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 2.49/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.49/1.39  
% 2.78/1.41  tff(f_136, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v3_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_tex_2)).
% 2.78/1.41  tff(f_84, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_tex_2)).
% 2.78/1.41  tff(f_116, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tex_2)).
% 2.78/1.41  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.78/1.41  tff(f_56, axiom, (![A, B]: ~(r2_hidden(A, B) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_boole)).
% 2.78/1.41  tff(f_51, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 2.78/1.41  tff(f_97, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 2.78/1.41  tff(c_44, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.78/1.41  tff(c_36, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.78/1.41  tff(c_52, plain, (v3_tex_2('#skF_4', '#skF_3') | v1_zfmisc_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.78/1.41  tff(c_54, plain, (v1_zfmisc_1('#skF_4')), inference(splitLeft, [status(thm)], [c_52])).
% 2.78/1.41  tff(c_46, plain, (~v1_zfmisc_1('#skF_4') | ~v3_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.78/1.41  tff(c_57, plain, (~v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_46])).
% 2.78/1.41  tff(c_38, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.78/1.41  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.78/1.41  tff(c_102, plain, (![A_52, B_53]: ('#skF_2'(A_52, B_53)!=B_53 | v3_tex_2(B_53, A_52) | ~v2_tex_2(B_53, A_52) | ~m1_subset_1(B_53, k1_zfmisc_1(u1_struct_0(A_52))) | ~l1_pre_topc(A_52))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.78/1.41  tff(c_105, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_34, c_102])).
% 2.78/1.41  tff(c_108, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_105])).
% 2.78/1.41  tff(c_109, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | ~v2_tex_2('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_57, c_108])).
% 2.78/1.41  tff(c_110, plain, (~v2_tex_2('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_109])).
% 2.78/1.41  tff(c_42, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.78/1.41  tff(c_40, plain, (v2_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.78/1.41  tff(c_125, plain, (![B_58, A_59]: (v2_tex_2(B_58, A_59) | ~v1_zfmisc_1(B_58) | ~m1_subset_1(B_58, k1_zfmisc_1(u1_struct_0(A_59))) | v1_xboole_0(B_58) | ~l1_pre_topc(A_59) | ~v2_tdlat_3(A_59) | ~v2_pre_topc(A_59) | v2_struct_0(A_59))), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.78/1.41  tff(c_128, plain, (v2_tex_2('#skF_4', '#skF_3') | ~v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_34, c_125])).
% 2.78/1.41  tff(c_131, plain, (v2_tex_2('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_54, c_128])).
% 2.78/1.41  tff(c_133, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_36, c_110, c_131])).
% 2.78/1.41  tff(c_135, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_109])).
% 2.78/1.41  tff(c_143, plain, (![B_62, A_63]: (r1_tarski(B_62, '#skF_2'(A_63, B_62)) | v3_tex_2(B_62, A_63) | ~v2_tex_2(B_62, A_63) | ~m1_subset_1(B_62, k1_zfmisc_1(u1_struct_0(A_63))) | ~l1_pre_topc(A_63))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.78/1.41  tff(c_145, plain, (r1_tarski('#skF_4', '#skF_2'('#skF_3', '#skF_4')) | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_34, c_143])).
% 2.78/1.41  tff(c_148, plain, (r1_tarski('#skF_4', '#skF_2'('#skF_3', '#skF_4')) | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_135, c_145])).
% 2.78/1.41  tff(c_149, plain, (r1_tarski('#skF_4', '#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_57, c_148])).
% 2.78/1.41  tff(c_65, plain, (![A_33, B_34]: (r2_hidden('#skF_1'(A_33, B_34), B_34) | r1_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.78/1.41  tff(c_10, plain, (![B_9, A_8]: (~v1_xboole_0(B_9) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.78/1.41  tff(c_69, plain, (![B_34, A_33]: (~v1_xboole_0(B_34) | r1_xboole_0(A_33, B_34))), inference(resolution, [status(thm)], [c_65, c_10])).
% 2.78/1.41  tff(c_71, plain, (![B_37, A_38]: (~r1_xboole_0(B_37, A_38) | ~r1_tarski(B_37, A_38) | v1_xboole_0(B_37))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.78/1.41  tff(c_75, plain, (![A_33, B_34]: (~r1_tarski(A_33, B_34) | v1_xboole_0(A_33) | ~v1_xboole_0(B_34))), inference(resolution, [status(thm)], [c_69, c_71])).
% 2.78/1.41  tff(c_155, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_2'('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_149, c_75])).
% 2.78/1.41  tff(c_161, plain, (~v1_xboole_0('#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_36, c_155])).
% 2.78/1.41  tff(c_134, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4'), inference(splitRight, [status(thm)], [c_109])).
% 2.78/1.41  tff(c_28, plain, (![B_24, A_22]: (B_24=A_22 | ~r1_tarski(A_22, B_24) | ~v1_zfmisc_1(B_24) | v1_xboole_0(B_24) | v1_xboole_0(A_22))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.78/1.41  tff(c_152, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4' | ~v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_149, c_28])).
% 2.78/1.41  tff(c_158, plain, (~v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_36, c_134, c_152])).
% 2.78/1.41  tff(c_162, plain, (~v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_161, c_158])).
% 2.78/1.41  tff(c_136, plain, (![A_60, B_61]: (v2_tex_2('#skF_2'(A_60, B_61), A_60) | v3_tex_2(B_61, A_60) | ~v2_tex_2(B_61, A_60) | ~m1_subset_1(B_61, k1_zfmisc_1(u1_struct_0(A_60))) | ~l1_pre_topc(A_60))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.78/1.41  tff(c_138, plain, (v2_tex_2('#skF_2'('#skF_3', '#skF_4'), '#skF_3') | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_34, c_136])).
% 2.78/1.41  tff(c_141, plain, (v2_tex_2('#skF_2'('#skF_3', '#skF_4'), '#skF_3') | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_135, c_138])).
% 2.78/1.41  tff(c_142, plain, (v2_tex_2('#skF_2'('#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_57, c_141])).
% 2.78/1.41  tff(c_175, plain, (![A_66, B_67]: (m1_subset_1('#skF_2'(A_66, B_67), k1_zfmisc_1(u1_struct_0(A_66))) | v3_tex_2(B_67, A_66) | ~v2_tex_2(B_67, A_66) | ~m1_subset_1(B_67, k1_zfmisc_1(u1_struct_0(A_66))) | ~l1_pre_topc(A_66))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.78/1.41  tff(c_32, plain, (![B_27, A_25]: (v1_zfmisc_1(B_27) | ~v2_tex_2(B_27, A_25) | ~m1_subset_1(B_27, k1_zfmisc_1(u1_struct_0(A_25))) | v1_xboole_0(B_27) | ~l1_pre_topc(A_25) | ~v2_tdlat_3(A_25) | ~v2_pre_topc(A_25) | v2_struct_0(A_25))), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.78/1.41  tff(c_233, plain, (![A_78, B_79]: (v1_zfmisc_1('#skF_2'(A_78, B_79)) | ~v2_tex_2('#skF_2'(A_78, B_79), A_78) | v1_xboole_0('#skF_2'(A_78, B_79)) | ~v2_tdlat_3(A_78) | ~v2_pre_topc(A_78) | v2_struct_0(A_78) | v3_tex_2(B_79, A_78) | ~v2_tex_2(B_79, A_78) | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0(A_78))) | ~l1_pre_topc(A_78))), inference(resolution, [status(thm)], [c_175, c_32])).
% 2.78/1.41  tff(c_237, plain, (v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_2'('#skF_3', '#skF_4')) | ~v2_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_142, c_233])).
% 2.78/1.41  tff(c_241, plain, (v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_2'('#skF_3', '#skF_4')) | v2_struct_0('#skF_3') | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_135, c_42, c_40, c_237])).
% 2.78/1.41  tff(c_243, plain, $false, inference(negUnitSimplification, [status(thm)], [c_57, c_44, c_161, c_162, c_241])).
% 2.78/1.41  tff(c_245, plain, (~v1_zfmisc_1('#skF_4')), inference(splitRight, [status(thm)], [c_52])).
% 2.78/1.41  tff(c_244, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_52])).
% 2.78/1.41  tff(c_290, plain, (![B_100, A_101]: (v2_tex_2(B_100, A_101) | ~v3_tex_2(B_100, A_101) | ~m1_subset_1(B_100, k1_zfmisc_1(u1_struct_0(A_101))) | ~l1_pre_topc(A_101))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.78/1.41  tff(c_293, plain, (v2_tex_2('#skF_4', '#skF_3') | ~v3_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_34, c_290])).
% 2.78/1.41  tff(c_296, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_244, c_293])).
% 2.78/1.41  tff(c_316, plain, (![B_108, A_109]: (v1_zfmisc_1(B_108) | ~v2_tex_2(B_108, A_109) | ~m1_subset_1(B_108, k1_zfmisc_1(u1_struct_0(A_109))) | v1_xboole_0(B_108) | ~l1_pre_topc(A_109) | ~v2_tdlat_3(A_109) | ~v2_pre_topc(A_109) | v2_struct_0(A_109))), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.78/1.41  tff(c_319, plain, (v1_zfmisc_1('#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_34, c_316])).
% 2.78/1.41  tff(c_322, plain, (v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_296, c_319])).
% 2.78/1.41  tff(c_324, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_36, c_245, c_322])).
% 2.78/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.41  
% 2.78/1.41  Inference rules
% 2.78/1.41  ----------------------
% 2.78/1.41  #Ref     : 0
% 2.78/1.41  #Sup     : 44
% 2.78/1.41  #Fact    : 0
% 2.78/1.41  #Define  : 0
% 2.78/1.41  #Split   : 3
% 2.78/1.41  #Chain   : 0
% 2.78/1.41  #Close   : 0
% 2.78/1.41  
% 2.78/1.41  Ordering : KBO
% 2.78/1.41  
% 2.78/1.41  Simplification rules
% 2.78/1.41  ----------------------
% 2.78/1.41  #Subsume      : 13
% 2.78/1.41  #Demod        : 55
% 2.78/1.41  #Tautology    : 11
% 2.78/1.41  #SimpNegUnit  : 16
% 2.78/1.41  #BackRed      : 0
% 2.78/1.41  
% 2.78/1.41  #Partial instantiations: 0
% 2.78/1.41  #Strategies tried      : 1
% 2.78/1.41  
% 2.78/1.41  Timing (in seconds)
% 2.78/1.41  ----------------------
% 2.78/1.41  Preprocessing        : 0.33
% 2.78/1.41  Parsing              : 0.18
% 2.78/1.41  CNF conversion       : 0.03
% 2.78/1.41  Main loop            : 0.28
% 2.78/1.41  Inferencing          : 0.11
% 2.78/1.41  Reduction            : 0.07
% 2.78/1.41  Demodulation         : 0.05
% 2.78/1.41  BG Simplification    : 0.02
% 2.78/1.41  Subsumption          : 0.06
% 2.78/1.41  Abstraction          : 0.01
% 2.78/1.41  MUC search           : 0.00
% 2.78/1.41  Cooper               : 0.00
% 2.78/1.41  Total                : 0.65
% 2.78/1.41  Index Insertion      : 0.00
% 2.78/1.41  Index Deletion       : 0.00
% 2.78/1.41  Index Matching       : 0.00
% 2.78/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
