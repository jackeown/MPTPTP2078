%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:18 EST 2020

% Result     : Theorem 2.82s
% Output     : CNFRefutation 2.82s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 268 expanded)
%              Number of leaves         :   27 ( 103 expanded)
%              Depth                    :   10
%              Number of atoms          :  206 (1009 expanded)
%              Number of equality atoms :   10 (  46 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(v2_tdlat_3,type,(
    v2_tdlat_3: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_112,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).

tff(f_92,axiom,(
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

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_73,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_32,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_42,plain,
    ( ~ v1_zfmisc_1('#skF_4')
    | ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_49,plain,(
    ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_34,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_30,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_113,plain,(
    ! [A_48,B_49] :
      ( '#skF_2'(A_48,B_49) != B_49
      | v3_tex_2(B_49,A_48)
      | ~ v2_tex_2(B_49,A_48)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ l1_pre_topc(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_120,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_113])).

tff(c_124,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_120])).

tff(c_125,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_49,c_124])).

tff(c_137,plain,(
    ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_125])).

tff(c_38,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_36,plain,(
    v2_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_48,plain,
    ( v3_tex_2('#skF_4','#skF_3')
    | v1_zfmisc_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_50,plain,(
    v1_zfmisc_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_49,c_48])).

tff(c_236,plain,(
    ! [B_68,A_69] :
      ( v2_tex_2(B_68,A_69)
      | ~ v1_zfmisc_1(B_68)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(u1_struct_0(A_69)))
      | v1_xboole_0(B_68)
      | ~ l1_pre_topc(A_69)
      | ~ v2_tdlat_3(A_69)
      | ~ v2_pre_topc(A_69)
      | v2_struct_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_246,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | ~ v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_236])).

tff(c_251,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_50,c_246])).

tff(c_253,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_32,c_137,c_251])).

tff(c_255,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_125])).

tff(c_126,plain,(
    ! [B_50,A_51] :
      ( r1_tarski(B_50,'#skF_2'(A_51,B_50))
      | v3_tex_2(B_50,A_51)
      | ~ v2_tex_2(B_50,A_51)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ l1_pre_topc(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_131,plain,
    ( r1_tarski('#skF_4','#skF_2'('#skF_3','#skF_4'))
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_126])).

tff(c_135,plain,
    ( r1_tarski('#skF_4','#skF_2'('#skF_3','#skF_4'))
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_131])).

tff(c_136,plain,
    ( r1_tarski('#skF_4','#skF_2'('#skF_3','#skF_4'))
    | ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_49,c_135])).

tff(c_257,plain,(
    r1_tarski('#skF_4','#skF_2'('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_255,c_136])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_67,plain,(
    ! [C_34,B_35,A_36] :
      ( ~ v1_xboole_0(C_34)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(C_34))
      | ~ r2_hidden(A_36,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_82,plain,(
    ! [B_39,A_40,A_41] :
      ( ~ v1_xboole_0(B_39)
      | ~ r2_hidden(A_40,A_41)
      | ~ r1_tarski(A_41,B_39) ) ),
    inference(resolution,[status(thm)],[c_8,c_67])).

tff(c_85,plain,(
    ! [B_39,A_1] :
      ( ~ v1_xboole_0(B_39)
      | ~ r1_tarski(A_1,B_39)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_82])).

tff(c_260,plain,
    ( ~ v1_xboole_0('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_257,c_85])).

tff(c_266,plain,(
    ~ v1_xboole_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_260])).

tff(c_254,plain,(
    '#skF_2'('#skF_3','#skF_4') != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_125])).

tff(c_24,plain,(
    ! [B_22,A_20] :
      ( B_22 = A_20
      | ~ r1_tarski(A_20,B_22)
      | ~ v1_zfmisc_1(B_22)
      | v1_xboole_0(B_22)
      | v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_263,plain,
    ( '#skF_2'('#skF_3','#skF_4') = '#skF_4'
    | ~ v1_zfmisc_1('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_257,c_24])).

tff(c_269,plain,
    ( '#skF_2'('#skF_3','#skF_4') = '#skF_4'
    | ~ v1_zfmisc_1('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_263])).

tff(c_270,plain,(
    ~ v1_zfmisc_1('#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_266,c_254,c_269])).

tff(c_286,plain,(
    ! [A_74,B_75] :
      ( v2_tex_2('#skF_2'(A_74,B_75),A_74)
      | v3_tex_2(B_75,A_74)
      | ~ v2_tex_2(B_75,A_74)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ l1_pre_topc(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_291,plain,
    ( v2_tex_2('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_286])).

tff(c_295,plain,
    ( v2_tex_2('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_255,c_291])).

tff(c_296,plain,(
    v2_tex_2('#skF_2'('#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_49,c_295])).

tff(c_18,plain,(
    ! [A_10,B_16] :
      ( m1_subset_1('#skF_2'(A_10,B_16),k1_zfmisc_1(u1_struct_0(A_10)))
      | v3_tex_2(B_16,A_10)
      | ~ v2_tex_2(B_16,A_10)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(u1_struct_0(A_10)))
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_369,plain,(
    ! [B_86,A_87] :
      ( v1_zfmisc_1(B_86)
      | ~ v2_tex_2(B_86,A_87)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0(A_87)))
      | v1_xboole_0(B_86)
      | ~ l1_pre_topc(A_87)
      | ~ v2_tdlat_3(A_87)
      | ~ v2_pre_topc(A_87)
      | v2_struct_0(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_531,plain,(
    ! [A_116,B_117] :
      ( v1_zfmisc_1('#skF_2'(A_116,B_117))
      | ~ v2_tex_2('#skF_2'(A_116,B_117),A_116)
      | v1_xboole_0('#skF_2'(A_116,B_117))
      | ~ v2_tdlat_3(A_116)
      | ~ v2_pre_topc(A_116)
      | v2_struct_0(A_116)
      | v3_tex_2(B_117,A_116)
      | ~ v2_tex_2(B_117,A_116)
      | ~ m1_subset_1(B_117,k1_zfmisc_1(u1_struct_0(A_116)))
      | ~ l1_pre_topc(A_116) ) ),
    inference(resolution,[status(thm)],[c_18,c_369])).

tff(c_537,plain,
    ( v1_zfmisc_1('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_2'('#skF_3','#skF_4'))
    | ~ v2_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_296,c_531])).

tff(c_542,plain,
    ( v1_zfmisc_1('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_2'('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3')
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_255,c_38,c_36,c_537])).

tff(c_544,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_49,c_40,c_266,c_270,c_542])).

tff(c_545,plain,(
    ~ v1_zfmisc_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_546,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_585,plain,(
    ! [B_133,A_134] :
      ( v2_tex_2(B_133,A_134)
      | ~ v3_tex_2(B_133,A_134)
      | ~ m1_subset_1(B_133,k1_zfmisc_1(u1_struct_0(A_134)))
      | ~ l1_pre_topc(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_592,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | ~ v3_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_585])).

tff(c_596,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_546,c_592])).

tff(c_656,plain,(
    ! [B_151,A_152] :
      ( v1_zfmisc_1(B_151)
      | ~ v2_tex_2(B_151,A_152)
      | ~ m1_subset_1(B_151,k1_zfmisc_1(u1_struct_0(A_152)))
      | v1_xboole_0(B_151)
      | ~ l1_pre_topc(A_152)
      | ~ v2_tdlat_3(A_152)
      | ~ v2_pre_topc(A_152)
      | v2_struct_0(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_663,plain,
    ( v1_zfmisc_1('#skF_4')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_656])).

tff(c_667,plain,
    ( v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_596,c_663])).

tff(c_669,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_32,c_545,c_667])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:32:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.82/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.82/1.39  
% 2.82/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.82/1.39  %$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.82/1.39  
% 2.82/1.39  %Foreground sorts:
% 2.82/1.39  
% 2.82/1.39  
% 2.82/1.39  %Background operators:
% 2.82/1.39  
% 2.82/1.39  
% 2.82/1.39  %Foreground operators:
% 2.82/1.39  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.82/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.82/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.82/1.39  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.82/1.39  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.82/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.82/1.39  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 2.82/1.39  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.82/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.82/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.82/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.82/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.82/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.82/1.39  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.82/1.39  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.82/1.39  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.82/1.39  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.82/1.39  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.82/1.39  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 2.82/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.82/1.39  
% 2.82/1.41  tff(f_112, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v3_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_tex_2)).
% 2.82/1.41  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 2.82/1.41  tff(f_92, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tex_2)).
% 2.82/1.41  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.82/1.41  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.82/1.41  tff(f_42, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.82/1.41  tff(f_73, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 2.82/1.41  tff(c_40, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.82/1.41  tff(c_32, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.82/1.41  tff(c_42, plain, (~v1_zfmisc_1('#skF_4') | ~v3_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.82/1.41  tff(c_49, plain, (~v3_tex_2('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_42])).
% 2.82/1.41  tff(c_34, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.82/1.41  tff(c_30, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.82/1.41  tff(c_113, plain, (![A_48, B_49]: ('#skF_2'(A_48, B_49)!=B_49 | v3_tex_2(B_49, A_48) | ~v2_tex_2(B_49, A_48) | ~m1_subset_1(B_49, k1_zfmisc_1(u1_struct_0(A_48))) | ~l1_pre_topc(A_48))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.82/1.41  tff(c_120, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_30, c_113])).
% 2.82/1.41  tff(c_124, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_120])).
% 2.82/1.41  tff(c_125, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | ~v2_tex_2('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_49, c_124])).
% 2.82/1.41  tff(c_137, plain, (~v2_tex_2('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_125])).
% 2.82/1.41  tff(c_38, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.82/1.41  tff(c_36, plain, (v2_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.82/1.41  tff(c_48, plain, (v3_tex_2('#skF_4', '#skF_3') | v1_zfmisc_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.82/1.41  tff(c_50, plain, (v1_zfmisc_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_49, c_48])).
% 2.82/1.41  tff(c_236, plain, (![B_68, A_69]: (v2_tex_2(B_68, A_69) | ~v1_zfmisc_1(B_68) | ~m1_subset_1(B_68, k1_zfmisc_1(u1_struct_0(A_69))) | v1_xboole_0(B_68) | ~l1_pre_topc(A_69) | ~v2_tdlat_3(A_69) | ~v2_pre_topc(A_69) | v2_struct_0(A_69))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.82/1.41  tff(c_246, plain, (v2_tex_2('#skF_4', '#skF_3') | ~v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_30, c_236])).
% 2.82/1.41  tff(c_251, plain, (v2_tex_2('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_50, c_246])).
% 2.82/1.41  tff(c_253, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_32, c_137, c_251])).
% 2.82/1.41  tff(c_255, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_125])).
% 2.82/1.41  tff(c_126, plain, (![B_50, A_51]: (r1_tarski(B_50, '#skF_2'(A_51, B_50)) | v3_tex_2(B_50, A_51) | ~v2_tex_2(B_50, A_51) | ~m1_subset_1(B_50, k1_zfmisc_1(u1_struct_0(A_51))) | ~l1_pre_topc(A_51))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.82/1.41  tff(c_131, plain, (r1_tarski('#skF_4', '#skF_2'('#skF_3', '#skF_4')) | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_30, c_126])).
% 2.82/1.41  tff(c_135, plain, (r1_tarski('#skF_4', '#skF_2'('#skF_3', '#skF_4')) | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_131])).
% 2.82/1.41  tff(c_136, plain, (r1_tarski('#skF_4', '#skF_2'('#skF_3', '#skF_4')) | ~v2_tex_2('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_49, c_135])).
% 2.82/1.41  tff(c_257, plain, (r1_tarski('#skF_4', '#skF_2'('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_255, c_136])).
% 2.82/1.41  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.82/1.41  tff(c_8, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.82/1.41  tff(c_67, plain, (![C_34, B_35, A_36]: (~v1_xboole_0(C_34) | ~m1_subset_1(B_35, k1_zfmisc_1(C_34)) | ~r2_hidden(A_36, B_35))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.82/1.41  tff(c_82, plain, (![B_39, A_40, A_41]: (~v1_xboole_0(B_39) | ~r2_hidden(A_40, A_41) | ~r1_tarski(A_41, B_39))), inference(resolution, [status(thm)], [c_8, c_67])).
% 2.82/1.41  tff(c_85, plain, (![B_39, A_1]: (~v1_xboole_0(B_39) | ~r1_tarski(A_1, B_39) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_82])).
% 2.82/1.41  tff(c_260, plain, (~v1_xboole_0('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_257, c_85])).
% 2.82/1.41  tff(c_266, plain, (~v1_xboole_0('#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_32, c_260])).
% 2.82/1.41  tff(c_254, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4'), inference(splitRight, [status(thm)], [c_125])).
% 2.82/1.41  tff(c_24, plain, (![B_22, A_20]: (B_22=A_20 | ~r1_tarski(A_20, B_22) | ~v1_zfmisc_1(B_22) | v1_xboole_0(B_22) | v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.82/1.41  tff(c_263, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4' | ~v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_257, c_24])).
% 2.82/1.41  tff(c_269, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4' | ~v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_32, c_263])).
% 2.82/1.41  tff(c_270, plain, (~v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_266, c_254, c_269])).
% 2.82/1.41  tff(c_286, plain, (![A_74, B_75]: (v2_tex_2('#skF_2'(A_74, B_75), A_74) | v3_tex_2(B_75, A_74) | ~v2_tex_2(B_75, A_74) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0(A_74))) | ~l1_pre_topc(A_74))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.82/1.41  tff(c_291, plain, (v2_tex_2('#skF_2'('#skF_3', '#skF_4'), '#skF_3') | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_30, c_286])).
% 2.82/1.41  tff(c_295, plain, (v2_tex_2('#skF_2'('#skF_3', '#skF_4'), '#skF_3') | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_255, c_291])).
% 2.82/1.41  tff(c_296, plain, (v2_tex_2('#skF_2'('#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_49, c_295])).
% 2.82/1.41  tff(c_18, plain, (![A_10, B_16]: (m1_subset_1('#skF_2'(A_10, B_16), k1_zfmisc_1(u1_struct_0(A_10))) | v3_tex_2(B_16, A_10) | ~v2_tex_2(B_16, A_10) | ~m1_subset_1(B_16, k1_zfmisc_1(u1_struct_0(A_10))) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.82/1.41  tff(c_369, plain, (![B_86, A_87]: (v1_zfmisc_1(B_86) | ~v2_tex_2(B_86, A_87) | ~m1_subset_1(B_86, k1_zfmisc_1(u1_struct_0(A_87))) | v1_xboole_0(B_86) | ~l1_pre_topc(A_87) | ~v2_tdlat_3(A_87) | ~v2_pre_topc(A_87) | v2_struct_0(A_87))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.82/1.41  tff(c_531, plain, (![A_116, B_117]: (v1_zfmisc_1('#skF_2'(A_116, B_117)) | ~v2_tex_2('#skF_2'(A_116, B_117), A_116) | v1_xboole_0('#skF_2'(A_116, B_117)) | ~v2_tdlat_3(A_116) | ~v2_pre_topc(A_116) | v2_struct_0(A_116) | v3_tex_2(B_117, A_116) | ~v2_tex_2(B_117, A_116) | ~m1_subset_1(B_117, k1_zfmisc_1(u1_struct_0(A_116))) | ~l1_pre_topc(A_116))), inference(resolution, [status(thm)], [c_18, c_369])).
% 2.82/1.41  tff(c_537, plain, (v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_2'('#skF_3', '#skF_4')) | ~v2_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_296, c_531])).
% 2.82/1.41  tff(c_542, plain, (v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_2'('#skF_3', '#skF_4')) | v2_struct_0('#skF_3') | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_255, c_38, c_36, c_537])).
% 2.82/1.41  tff(c_544, plain, $false, inference(negUnitSimplification, [status(thm)], [c_49, c_40, c_266, c_270, c_542])).
% 2.82/1.41  tff(c_545, plain, (~v1_zfmisc_1('#skF_4')), inference(splitRight, [status(thm)], [c_42])).
% 2.82/1.41  tff(c_546, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_42])).
% 2.82/1.41  tff(c_585, plain, (![B_133, A_134]: (v2_tex_2(B_133, A_134) | ~v3_tex_2(B_133, A_134) | ~m1_subset_1(B_133, k1_zfmisc_1(u1_struct_0(A_134))) | ~l1_pre_topc(A_134))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.82/1.41  tff(c_592, plain, (v2_tex_2('#skF_4', '#skF_3') | ~v3_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_30, c_585])).
% 2.82/1.41  tff(c_596, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_546, c_592])).
% 2.82/1.41  tff(c_656, plain, (![B_151, A_152]: (v1_zfmisc_1(B_151) | ~v2_tex_2(B_151, A_152) | ~m1_subset_1(B_151, k1_zfmisc_1(u1_struct_0(A_152))) | v1_xboole_0(B_151) | ~l1_pre_topc(A_152) | ~v2_tdlat_3(A_152) | ~v2_pre_topc(A_152) | v2_struct_0(A_152))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.82/1.41  tff(c_663, plain, (v1_zfmisc_1('#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_30, c_656])).
% 2.82/1.41  tff(c_667, plain, (v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_596, c_663])).
% 2.82/1.41  tff(c_669, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_32, c_545, c_667])).
% 2.82/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.82/1.41  
% 2.82/1.41  Inference rules
% 2.82/1.41  ----------------------
% 2.82/1.41  #Ref     : 0
% 2.82/1.41  #Sup     : 113
% 2.82/1.41  #Fact    : 0
% 2.82/1.41  #Define  : 0
% 2.82/1.41  #Split   : 8
% 2.82/1.41  #Chain   : 0
% 2.82/1.41  #Close   : 0
% 2.82/1.41  
% 2.82/1.41  Ordering : KBO
% 2.82/1.41  
% 2.82/1.41  Simplification rules
% 2.82/1.41  ----------------------
% 2.82/1.41  #Subsume      : 26
% 2.82/1.41  #Demod        : 96
% 2.82/1.41  #Tautology    : 18
% 2.82/1.41  #SimpNegUnit  : 35
% 2.82/1.41  #BackRed      : 0
% 2.82/1.41  
% 2.82/1.41  #Partial instantiations: 0
% 2.82/1.41  #Strategies tried      : 1
% 2.82/1.41  
% 2.82/1.41  Timing (in seconds)
% 2.82/1.41  ----------------------
% 2.82/1.41  Preprocessing        : 0.28
% 2.82/1.41  Parsing              : 0.16
% 2.82/1.41  CNF conversion       : 0.02
% 2.82/1.41  Main loop            : 0.36
% 2.82/1.41  Inferencing          : 0.14
% 2.82/1.41  Reduction            : 0.09
% 2.82/1.41  Demodulation         : 0.05
% 2.82/1.41  BG Simplification    : 0.02
% 2.82/1.41  Subsumption          : 0.08
% 2.82/1.41  Abstraction          : 0.02
% 2.82/1.41  MUC search           : 0.00
% 2.82/1.41  Cooper               : 0.00
% 2.82/1.41  Total                : 0.67
% 2.82/1.41  Index Insertion      : 0.00
% 2.82/1.41  Index Deletion       : 0.00
% 2.82/1.41  Index Matching       : 0.00
% 2.82/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
