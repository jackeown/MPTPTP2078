%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:11 EST 2020

% Result     : Theorem 2.59s
% Output     : CNFRefutation 2.96s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 448 expanded)
%              Number of leaves         :   23 ( 159 expanded)
%              Depth                    :   14
%              Number of atoms          :  205 (1367 expanded)
%              Number of equality atoms :   21 ( 120 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > v1_subset_1 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_92,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v1_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_tex_2(B,A)
            <=> ~ v1_subset_1(B,u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_tex_2)).

tff(f_74,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( B = u1_struct_0(A)
           => ( v2_tex_2(B,A)
            <=> v1_tdlat_3(A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_tex_2)).

tff(f_60,axiom,(
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

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_408,plain,(
    ! [A_68,B_69] :
      ( m1_subset_1(A_68,k1_zfmisc_1(B_69))
      | ~ r1_tarski(A_68,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ! [B_6] :
      ( ~ v1_subset_1(B_6,B_6)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_412,plain,(
    ! [B_69] :
      ( ~ v1_subset_1(B_69,B_69)
      | ~ r1_tarski(B_69,B_69) ) ),
    inference(resolution,[status(thm)],[c_408,c_14])).

tff(c_418,plain,(
    ! [B_69] : ~ v1_subset_1(B_69,B_69) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_412])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_34,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_36,plain,(
    v1_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_486,plain,(
    ! [A_84] :
      ( v2_tex_2(u1_struct_0(A_84),A_84)
      | ~ v1_tdlat_3(A_84)
      | ~ m1_subset_1(u1_struct_0(A_84),k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ l1_pre_topc(A_84)
      | v2_struct_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_489,plain,(
    ! [A_84] :
      ( v2_tex_2(u1_struct_0(A_84),A_84)
      | ~ v1_tdlat_3(A_84)
      | ~ l1_pre_topc(A_84)
      | v2_struct_0(A_84)
      | ~ r1_tarski(u1_struct_0(A_84),u1_struct_0(A_84)) ) ),
    inference(resolution,[status(thm)],[c_10,c_486])).

tff(c_492,plain,(
    ! [A_84] :
      ( v2_tex_2(u1_struct_0(A_84),A_84)
      | ~ v1_tdlat_3(A_84)
      | ~ l1_pre_topc(A_84)
      | v2_struct_0(A_84) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_489])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_42,plain,
    ( v1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ v3_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_57,plain,(
    ~ v3_tex_2('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_48,plain,
    ( v3_tex_2('#skF_3','#skF_2')
    | ~ v1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_58,plain,(
    ~ v1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_48])).

tff(c_82,plain,(
    ! [B_30,A_31] :
      ( v1_subset_1(B_30,A_31)
      | B_30 = A_31
      | ~ m1_subset_1(B_30,k1_zfmisc_1(A_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_88,plain,
    ( v1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | u1_struct_0('#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_32,c_82])).

tff(c_92,plain,(
    u1_struct_0('#skF_2') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_88])).

tff(c_95,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_32])).

tff(c_189,plain,(
    ! [A_43] :
      ( v2_tex_2(u1_struct_0(A_43),A_43)
      | ~ v1_tdlat_3(A_43)
      | ~ m1_subset_1(u1_struct_0(A_43),k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ l1_pre_topc(A_43)
      | v2_struct_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_192,plain,
    ( v2_tex_2(u1_struct_0('#skF_2'),'#skF_2')
    | ~ v1_tdlat_3('#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_189])).

tff(c_200,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_95,c_92,c_36,c_92,c_192])).

tff(c_201,plain,(
    v2_tex_2('#skF_3','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_200])).

tff(c_344,plain,(
    ! [A_64,B_65] :
      ( m1_subset_1('#skF_1'(A_64,B_65),k1_zfmisc_1(u1_struct_0(A_64)))
      | v3_tex_2(B_65,A_64)
      | ~ v2_tex_2(B_65,A_64)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ l1_pre_topc(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_363,plain,(
    ! [B_65] :
      ( m1_subset_1('#skF_1'('#skF_2',B_65),k1_zfmisc_1('#skF_3'))
      | v3_tex_2(B_65,'#skF_2')
      | ~ v2_tex_2(B_65,'#skF_2')
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_344])).

tff(c_378,plain,(
    ! [B_66] :
      ( m1_subset_1('#skF_1'('#skF_2',B_66),k1_zfmisc_1('#skF_3'))
      | v3_tex_2(B_66,'#skF_2')
      | ~ v2_tex_2(B_66,'#skF_2')
      | ~ m1_subset_1(B_66,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_92,c_363])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_395,plain,(
    ! [B_67] :
      ( r1_tarski('#skF_1'('#skF_2',B_67),'#skF_3')
      | v3_tex_2(B_67,'#skF_2')
      | ~ v2_tex_2(B_67,'#skF_2')
      | ~ m1_subset_1(B_67,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_378,c_8])).

tff(c_220,plain,(
    ! [A_45,B_46] :
      ( '#skF_1'(A_45,B_46) != B_46
      | v3_tex_2(B_46,A_45)
      | ~ v2_tex_2(B_46,A_45)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ l1_pre_topc(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_223,plain,(
    ! [B_46] :
      ( '#skF_1'('#skF_2',B_46) != B_46
      | v3_tex_2(B_46,'#skF_2')
      | ~ v2_tex_2(B_46,'#skF_2')
      | ~ m1_subset_1(B_46,k1_zfmisc_1('#skF_3'))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_220])).

tff(c_231,plain,(
    ! [B_47] :
      ( '#skF_1'('#skF_2',B_47) != B_47
      | v3_tex_2(B_47,'#skF_2')
      | ~ v2_tex_2(B_47,'#skF_2')
      | ~ m1_subset_1(B_47,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_223])).

tff(c_234,plain,
    ( '#skF_1'('#skF_2','#skF_3') != '#skF_3'
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_95,c_231])).

tff(c_241,plain,
    ( '#skF_1'('#skF_2','#skF_3') != '#skF_3'
    | v3_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_234])).

tff(c_242,plain,(
    '#skF_1'('#skF_2','#skF_3') != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_241])).

tff(c_301,plain,(
    ! [B_55,A_56] :
      ( r1_tarski(B_55,'#skF_1'(A_56,B_55))
      | v3_tex_2(B_55,A_56)
      | ~ v2_tex_2(B_55,A_56)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ l1_pre_topc(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_314,plain,(
    ! [A_58,A_59] :
      ( r1_tarski(A_58,'#skF_1'(A_59,A_58))
      | v3_tex_2(A_58,A_59)
      | ~ v2_tex_2(A_58,A_59)
      | ~ l1_pre_topc(A_59)
      | ~ r1_tarski(A_58,u1_struct_0(A_59)) ) ),
    inference(resolution,[status(thm)],[c_10,c_301])).

tff(c_328,plain,(
    ! [A_63] :
      ( r1_tarski(u1_struct_0(A_63),'#skF_1'(A_63,u1_struct_0(A_63)))
      | v3_tex_2(u1_struct_0(A_63),A_63)
      | ~ v2_tex_2(u1_struct_0(A_63),A_63)
      | ~ l1_pre_topc(A_63) ) ),
    inference(resolution,[status(thm)],[c_6,c_314])).

tff(c_333,plain,
    ( r1_tarski('#skF_3','#skF_1'('#skF_2',u1_struct_0('#skF_2')))
    | v3_tex_2(u1_struct_0('#skF_2'),'#skF_2')
    | ~ v2_tex_2(u1_struct_0('#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_328])).

tff(c_339,plain,
    ( r1_tarski('#skF_3','#skF_1'('#skF_2','#skF_3'))
    | v3_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_201,c_92,c_92,c_92,c_333])).

tff(c_340,plain,(
    r1_tarski('#skF_3','#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_339])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_373,plain,
    ( '#skF_1'('#skF_2','#skF_3') = '#skF_3'
    | ~ r1_tarski('#skF_1'('#skF_2','#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_340,c_2])).

tff(c_376,plain,(
    ~ r1_tarski('#skF_1'('#skF_2','#skF_3'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_242,c_373])).

tff(c_398,plain,
    ( v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_395,c_376])).

tff(c_403,plain,(
    v3_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_201,c_398])).

tff(c_405,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_403])).

tff(c_407,plain,(
    v3_tex_2('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_51,plain,(
    ! [A_22,B_23] :
      ( r1_tarski(A_22,B_23)
      | ~ m1_subset_1(A_22,k1_zfmisc_1(B_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_55,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_51])).

tff(c_600,plain,(
    ! [C_104,B_105,A_106] :
      ( C_104 = B_105
      | ~ r1_tarski(B_105,C_104)
      | ~ v2_tex_2(C_104,A_106)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ v3_tex_2(B_105,A_106)
      | ~ m1_subset_1(B_105,k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ l1_pre_topc(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_611,plain,(
    ! [A_106] :
      ( u1_struct_0('#skF_2') = '#skF_3'
      | ~ v2_tex_2(u1_struct_0('#skF_2'),A_106)
      | ~ m1_subset_1(u1_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ v3_tex_2('#skF_3',A_106)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ l1_pre_topc(A_106) ) ),
    inference(resolution,[status(thm)],[c_55,c_600])).

tff(c_615,plain,(
    ! [A_107] :
      ( ~ v2_tex_2(u1_struct_0('#skF_2'),A_107)
      | ~ m1_subset_1(u1_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ v3_tex_2('#skF_3',A_107)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ l1_pre_topc(A_107) ) ),
    inference(splitLeft,[status(thm)],[c_611])).

tff(c_620,plain,(
    ! [A_108] :
      ( ~ v2_tex_2(u1_struct_0('#skF_2'),A_108)
      | ~ v3_tex_2('#skF_3',A_108)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ l1_pre_topc(A_108)
      | ~ r1_tarski(u1_struct_0('#skF_2'),u1_struct_0(A_108)) ) ),
    inference(resolution,[status(thm)],[c_10,c_615])).

tff(c_624,plain,
    ( ~ v2_tex_2(u1_struct_0('#skF_2'),'#skF_2')
    | ~ v3_tex_2('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_620])).

tff(c_627,plain,(
    ~ v2_tex_2(u1_struct_0('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_407,c_624])).

tff(c_630,plain,
    ( ~ v1_tdlat_3('#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_492,c_627])).

tff(c_633,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_36,c_630])).

tff(c_635,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_633])).

tff(c_636,plain,(
    u1_struct_0('#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_611])).

tff(c_423,plain,(
    ! [B_71,A_72] :
      ( B_71 = A_72
      | ~ r1_tarski(B_71,A_72)
      | ~ r1_tarski(A_72,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_428,plain,
    ( u1_struct_0('#skF_2') = '#skF_3'
    | ~ r1_tarski(u1_struct_0('#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_55,c_423])).

tff(c_433,plain,(
    ~ r1_tarski(u1_struct_0('#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_428])).

tff(c_637,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_636,c_433])).

tff(c_643,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_637])).

tff(c_644,plain,(
    u1_struct_0('#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_428])).

tff(c_406,plain,(
    v1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_656,plain,(
    v1_subset_1('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_644,c_406])).

tff(c_660,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_418,c_656])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:19:04 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.59/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.84/1.43  
% 2.84/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.84/1.44  %$ v3_tex_2 > v2_tex_2 > v1_subset_1 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.84/1.44  
% 2.84/1.44  %Foreground sorts:
% 2.84/1.44  
% 2.84/1.44  
% 2.84/1.44  %Background operators:
% 2.84/1.44  
% 2.84/1.44  
% 2.84/1.44  %Foreground operators:
% 2.84/1.44  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.84/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.84/1.44  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.84/1.44  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.84/1.44  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 2.84/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.84/1.44  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 2.84/1.44  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.84/1.44  tff('#skF_2', type, '#skF_2': $i).
% 2.84/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.84/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.84/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.84/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.84/1.44  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.84/1.44  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.84/1.44  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.84/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.84/1.44  
% 2.96/1.46  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.96/1.46  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.96/1.46  tff(f_42, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 2.96/1.46  tff(f_92, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> ~v1_subset_1(B, u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_tex_2)).
% 2.96/1.46  tff(f_74, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((B = u1_struct_0(A)) => (v2_tex_2(B, A) <=> v1_tdlat_3(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_tex_2)).
% 2.96/1.46  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_tex_2)).
% 2.96/1.46  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.96/1.46  tff(c_408, plain, (![A_68, B_69]: (m1_subset_1(A_68, k1_zfmisc_1(B_69)) | ~r1_tarski(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.96/1.46  tff(c_14, plain, (![B_6]: (~v1_subset_1(B_6, B_6) | ~m1_subset_1(B_6, k1_zfmisc_1(B_6)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.96/1.46  tff(c_412, plain, (![B_69]: (~v1_subset_1(B_69, B_69) | ~r1_tarski(B_69, B_69))), inference(resolution, [status(thm)], [c_408, c_14])).
% 2.96/1.46  tff(c_418, plain, (![B_69]: (~v1_subset_1(B_69, B_69))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_412])).
% 2.96/1.46  tff(c_40, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.96/1.46  tff(c_34, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.96/1.46  tff(c_36, plain, (v1_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.96/1.46  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.96/1.46  tff(c_486, plain, (![A_84]: (v2_tex_2(u1_struct_0(A_84), A_84) | ~v1_tdlat_3(A_84) | ~m1_subset_1(u1_struct_0(A_84), k1_zfmisc_1(u1_struct_0(A_84))) | ~l1_pre_topc(A_84) | v2_struct_0(A_84))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.96/1.46  tff(c_489, plain, (![A_84]: (v2_tex_2(u1_struct_0(A_84), A_84) | ~v1_tdlat_3(A_84) | ~l1_pre_topc(A_84) | v2_struct_0(A_84) | ~r1_tarski(u1_struct_0(A_84), u1_struct_0(A_84)))), inference(resolution, [status(thm)], [c_10, c_486])).
% 2.96/1.46  tff(c_492, plain, (![A_84]: (v2_tex_2(u1_struct_0(A_84), A_84) | ~v1_tdlat_3(A_84) | ~l1_pre_topc(A_84) | v2_struct_0(A_84))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_489])).
% 2.96/1.46  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.96/1.46  tff(c_42, plain, (v1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~v3_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.96/1.46  tff(c_57, plain, (~v3_tex_2('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_42])).
% 2.96/1.46  tff(c_48, plain, (v3_tex_2('#skF_3', '#skF_2') | ~v1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.96/1.46  tff(c_58, plain, (~v1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_57, c_48])).
% 2.96/1.46  tff(c_82, plain, (![B_30, A_31]: (v1_subset_1(B_30, A_31) | B_30=A_31 | ~m1_subset_1(B_30, k1_zfmisc_1(A_31)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.96/1.46  tff(c_88, plain, (v1_subset_1('#skF_3', u1_struct_0('#skF_2')) | u1_struct_0('#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_32, c_82])).
% 2.96/1.46  tff(c_92, plain, (u1_struct_0('#skF_2')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_58, c_88])).
% 2.96/1.46  tff(c_95, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_32])).
% 2.96/1.46  tff(c_189, plain, (![A_43]: (v2_tex_2(u1_struct_0(A_43), A_43) | ~v1_tdlat_3(A_43) | ~m1_subset_1(u1_struct_0(A_43), k1_zfmisc_1(u1_struct_0(A_43))) | ~l1_pre_topc(A_43) | v2_struct_0(A_43))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.96/1.46  tff(c_192, plain, (v2_tex_2(u1_struct_0('#skF_2'), '#skF_2') | ~v1_tdlat_3('#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_92, c_189])).
% 2.96/1.46  tff(c_200, plain, (v2_tex_2('#skF_3', '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_95, c_92, c_36, c_92, c_192])).
% 2.96/1.46  tff(c_201, plain, (v2_tex_2('#skF_3', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_40, c_200])).
% 2.96/1.46  tff(c_344, plain, (![A_64, B_65]: (m1_subset_1('#skF_1'(A_64, B_65), k1_zfmisc_1(u1_struct_0(A_64))) | v3_tex_2(B_65, A_64) | ~v2_tex_2(B_65, A_64) | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0(A_64))) | ~l1_pre_topc(A_64))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.96/1.46  tff(c_363, plain, (![B_65]: (m1_subset_1('#skF_1'('#skF_2', B_65), k1_zfmisc_1('#skF_3')) | v3_tex_2(B_65, '#skF_2') | ~v2_tex_2(B_65, '#skF_2') | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_92, c_344])).
% 2.96/1.46  tff(c_378, plain, (![B_66]: (m1_subset_1('#skF_1'('#skF_2', B_66), k1_zfmisc_1('#skF_3')) | v3_tex_2(B_66, '#skF_2') | ~v2_tex_2(B_66, '#skF_2') | ~m1_subset_1(B_66, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_92, c_363])).
% 2.96/1.46  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.96/1.46  tff(c_395, plain, (![B_67]: (r1_tarski('#skF_1'('#skF_2', B_67), '#skF_3') | v3_tex_2(B_67, '#skF_2') | ~v2_tex_2(B_67, '#skF_2') | ~m1_subset_1(B_67, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_378, c_8])).
% 2.96/1.46  tff(c_220, plain, (![A_45, B_46]: ('#skF_1'(A_45, B_46)!=B_46 | v3_tex_2(B_46, A_45) | ~v2_tex_2(B_46, A_45) | ~m1_subset_1(B_46, k1_zfmisc_1(u1_struct_0(A_45))) | ~l1_pre_topc(A_45))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.96/1.46  tff(c_223, plain, (![B_46]: ('#skF_1'('#skF_2', B_46)!=B_46 | v3_tex_2(B_46, '#skF_2') | ~v2_tex_2(B_46, '#skF_2') | ~m1_subset_1(B_46, k1_zfmisc_1('#skF_3')) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_92, c_220])).
% 2.96/1.46  tff(c_231, plain, (![B_47]: ('#skF_1'('#skF_2', B_47)!=B_47 | v3_tex_2(B_47, '#skF_2') | ~v2_tex_2(B_47, '#skF_2') | ~m1_subset_1(B_47, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_223])).
% 2.96/1.46  tff(c_234, plain, ('#skF_1'('#skF_2', '#skF_3')!='#skF_3' | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_95, c_231])).
% 2.96/1.46  tff(c_241, plain, ('#skF_1'('#skF_2', '#skF_3')!='#skF_3' | v3_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_201, c_234])).
% 2.96/1.46  tff(c_242, plain, ('#skF_1'('#skF_2', '#skF_3')!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_57, c_241])).
% 2.96/1.46  tff(c_301, plain, (![B_55, A_56]: (r1_tarski(B_55, '#skF_1'(A_56, B_55)) | v3_tex_2(B_55, A_56) | ~v2_tex_2(B_55, A_56) | ~m1_subset_1(B_55, k1_zfmisc_1(u1_struct_0(A_56))) | ~l1_pre_topc(A_56))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.96/1.46  tff(c_314, plain, (![A_58, A_59]: (r1_tarski(A_58, '#skF_1'(A_59, A_58)) | v3_tex_2(A_58, A_59) | ~v2_tex_2(A_58, A_59) | ~l1_pre_topc(A_59) | ~r1_tarski(A_58, u1_struct_0(A_59)))), inference(resolution, [status(thm)], [c_10, c_301])).
% 2.96/1.46  tff(c_328, plain, (![A_63]: (r1_tarski(u1_struct_0(A_63), '#skF_1'(A_63, u1_struct_0(A_63))) | v3_tex_2(u1_struct_0(A_63), A_63) | ~v2_tex_2(u1_struct_0(A_63), A_63) | ~l1_pre_topc(A_63))), inference(resolution, [status(thm)], [c_6, c_314])).
% 2.96/1.46  tff(c_333, plain, (r1_tarski('#skF_3', '#skF_1'('#skF_2', u1_struct_0('#skF_2'))) | v3_tex_2(u1_struct_0('#skF_2'), '#skF_2') | ~v2_tex_2(u1_struct_0('#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_92, c_328])).
% 2.96/1.46  tff(c_339, plain, (r1_tarski('#skF_3', '#skF_1'('#skF_2', '#skF_3')) | v3_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_201, c_92, c_92, c_92, c_333])).
% 2.96/1.46  tff(c_340, plain, (r1_tarski('#skF_3', '#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_57, c_339])).
% 2.96/1.46  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.96/1.46  tff(c_373, plain, ('#skF_1'('#skF_2', '#skF_3')='#skF_3' | ~r1_tarski('#skF_1'('#skF_2', '#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_340, c_2])).
% 2.96/1.46  tff(c_376, plain, (~r1_tarski('#skF_1'('#skF_2', '#skF_3'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_242, c_373])).
% 2.96/1.46  tff(c_398, plain, (v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_395, c_376])).
% 2.96/1.46  tff(c_403, plain, (v3_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_95, c_201, c_398])).
% 2.96/1.46  tff(c_405, plain, $false, inference(negUnitSimplification, [status(thm)], [c_57, c_403])).
% 2.96/1.46  tff(c_407, plain, (v3_tex_2('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_42])).
% 2.96/1.46  tff(c_51, plain, (![A_22, B_23]: (r1_tarski(A_22, B_23) | ~m1_subset_1(A_22, k1_zfmisc_1(B_23)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.96/1.46  tff(c_55, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_32, c_51])).
% 2.96/1.46  tff(c_600, plain, (![C_104, B_105, A_106]: (C_104=B_105 | ~r1_tarski(B_105, C_104) | ~v2_tex_2(C_104, A_106) | ~m1_subset_1(C_104, k1_zfmisc_1(u1_struct_0(A_106))) | ~v3_tex_2(B_105, A_106) | ~m1_subset_1(B_105, k1_zfmisc_1(u1_struct_0(A_106))) | ~l1_pre_topc(A_106))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.96/1.46  tff(c_611, plain, (![A_106]: (u1_struct_0('#skF_2')='#skF_3' | ~v2_tex_2(u1_struct_0('#skF_2'), A_106) | ~m1_subset_1(u1_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_106))) | ~v3_tex_2('#skF_3', A_106) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_106))) | ~l1_pre_topc(A_106))), inference(resolution, [status(thm)], [c_55, c_600])).
% 2.96/1.46  tff(c_615, plain, (![A_107]: (~v2_tex_2(u1_struct_0('#skF_2'), A_107) | ~m1_subset_1(u1_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_107))) | ~v3_tex_2('#skF_3', A_107) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_107))) | ~l1_pre_topc(A_107))), inference(splitLeft, [status(thm)], [c_611])).
% 2.96/1.46  tff(c_620, plain, (![A_108]: (~v2_tex_2(u1_struct_0('#skF_2'), A_108) | ~v3_tex_2('#skF_3', A_108) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_108))) | ~l1_pre_topc(A_108) | ~r1_tarski(u1_struct_0('#skF_2'), u1_struct_0(A_108)))), inference(resolution, [status(thm)], [c_10, c_615])).
% 2.96/1.46  tff(c_624, plain, (~v2_tex_2(u1_struct_0('#skF_2'), '#skF_2') | ~v3_tex_2('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_6, c_620])).
% 2.96/1.46  tff(c_627, plain, (~v2_tex_2(u1_struct_0('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_407, c_624])).
% 2.96/1.46  tff(c_630, plain, (~v1_tdlat_3('#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_492, c_627])).
% 2.96/1.46  tff(c_633, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_36, c_630])).
% 2.96/1.46  tff(c_635, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_633])).
% 2.96/1.46  tff(c_636, plain, (u1_struct_0('#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_611])).
% 2.96/1.46  tff(c_423, plain, (![B_71, A_72]: (B_71=A_72 | ~r1_tarski(B_71, A_72) | ~r1_tarski(A_72, B_71))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.96/1.46  tff(c_428, plain, (u1_struct_0('#skF_2')='#skF_3' | ~r1_tarski(u1_struct_0('#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_55, c_423])).
% 2.96/1.46  tff(c_433, plain, (~r1_tarski(u1_struct_0('#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_428])).
% 2.96/1.46  tff(c_637, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_636, c_433])).
% 2.96/1.46  tff(c_643, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_637])).
% 2.96/1.46  tff(c_644, plain, (u1_struct_0('#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_428])).
% 2.96/1.46  tff(c_406, plain, (v1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_42])).
% 2.96/1.46  tff(c_656, plain, (v1_subset_1('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_644, c_406])).
% 2.96/1.46  tff(c_660, plain, $false, inference(negUnitSimplification, [status(thm)], [c_418, c_656])).
% 2.96/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.96/1.46  
% 2.96/1.46  Inference rules
% 2.96/1.46  ----------------------
% 2.96/1.46  #Ref     : 0
% 2.96/1.46  #Sup     : 110
% 2.96/1.46  #Fact    : 0
% 2.96/1.46  #Define  : 0
% 2.96/1.46  #Split   : 3
% 2.96/1.46  #Chain   : 0
% 2.96/1.46  #Close   : 0
% 2.96/1.46  
% 2.96/1.46  Ordering : KBO
% 2.96/1.46  
% 2.96/1.46  Simplification rules
% 2.96/1.46  ----------------------
% 2.96/1.46  #Subsume      : 19
% 2.96/1.46  #Demod        : 132
% 2.96/1.46  #Tautology    : 36
% 2.96/1.46  #SimpNegUnit  : 17
% 2.96/1.46  #BackRed      : 10
% 2.96/1.46  
% 2.96/1.46  #Partial instantiations: 0
% 2.96/1.46  #Strategies tried      : 1
% 2.96/1.46  
% 2.96/1.46  Timing (in seconds)
% 2.96/1.46  ----------------------
% 2.96/1.46  Preprocessing        : 0.30
% 2.96/1.46  Parsing              : 0.16
% 2.96/1.46  CNF conversion       : 0.02
% 2.96/1.46  Main loop            : 0.34
% 2.96/1.46  Inferencing          : 0.13
% 2.96/1.46  Reduction            : 0.10
% 2.96/1.46  Demodulation         : 0.07
% 2.96/1.46  BG Simplification    : 0.02
% 2.96/1.46  Subsumption          : 0.07
% 2.96/1.46  Abstraction          : 0.02
% 2.96/1.46  MUC search           : 0.00
% 2.96/1.46  Cooper               : 0.00
% 2.96/1.46  Total                : 0.69
% 2.96/1.46  Index Insertion      : 0.00
% 2.96/1.46  Index Deletion       : 0.00
% 2.96/1.46  Index Matching       : 0.00
% 2.96/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
