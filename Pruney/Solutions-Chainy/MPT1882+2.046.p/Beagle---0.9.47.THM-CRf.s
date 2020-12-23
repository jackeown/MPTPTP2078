%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:19 EST 2020

% Result     : Theorem 2.37s
% Output     : CNFRefutation 2.66s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 308 expanded)
%              Number of leaves         :   25 ( 114 expanded)
%              Depth                    :   11
%              Number of atoms          :  199 (1169 expanded)
%              Number of equality atoms :   12 (  66 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r1_tarski > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_pre_topc > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

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

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

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

tff(f_119,negated_conjecture,(
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

tff(f_53,axiom,(
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

tff(f_99,axiom,(
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

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(A)
     => ~ v1_xboole_0(k2_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_xboole_0)).

tff(f_66,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_28,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_38,plain,
    ( ~ v1_zfmisc_1('#skF_3')
    | ~ v3_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_45,plain,(
    ~ v3_tex_2('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_30,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_26,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_65,plain,(
    ! [A_35,B_36] :
      ( '#skF_1'(A_35,B_36) != B_36
      | v3_tex_2(B_36,A_35)
      | ~ v2_tex_2(B_36,A_35)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ l1_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_68,plain,
    ( '#skF_1'('#skF_2','#skF_3') != '#skF_3'
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_65])).

tff(c_71,plain,
    ( '#skF_1'('#skF_2','#skF_3') != '#skF_3'
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_68])).

tff(c_72,plain,
    ( '#skF_1'('#skF_2','#skF_3') != '#skF_3'
    | ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_71])).

tff(c_80,plain,(
    ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_34,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_32,plain,(
    v2_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_44,plain,
    ( v3_tex_2('#skF_3','#skF_2')
    | v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_46,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_44])).

tff(c_119,plain,(
    ! [B_45,A_46] :
      ( v2_tex_2(B_45,A_46)
      | ~ v1_zfmisc_1(B_45)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(u1_struct_0(A_46)))
      | v1_xboole_0(B_45)
      | ~ l1_pre_topc(A_46)
      | ~ v2_tdlat_3(A_46)
      | ~ v2_pre_topc(A_46)
      | v2_struct_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_125,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_119])).

tff(c_129,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_46,c_125])).

tff(c_131,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_28,c_80,c_129])).

tff(c_133,plain,(
    v2_tex_2('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_73,plain,(
    ! [B_37,A_38] :
      ( r1_tarski(B_37,'#skF_1'(A_38,B_37))
      | v3_tex_2(B_37,A_38)
      | ~ v2_tex_2(B_37,A_38)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ l1_pre_topc(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_75,plain,
    ( r1_tarski('#skF_3','#skF_1'('#skF_2','#skF_3'))
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_73])).

tff(c_78,plain,
    ( r1_tarski('#skF_3','#skF_1'('#skF_2','#skF_3'))
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_75])).

tff(c_79,plain,
    ( r1_tarski('#skF_3','#skF_1'('#skF_2','#skF_3'))
    | ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_78])).

tff(c_142,plain,(
    r1_tarski('#skF_3','#skF_1'('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_79])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k2_xboole_0(A_3,B_4) = B_4
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_152,plain,(
    k2_xboole_0('#skF_3','#skF_1'('#skF_2','#skF_3')) = '#skF_1'('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_142,c_4])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( ~ v1_xboole_0(k2_xboole_0(A_1,B_2))
      | v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_157,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_2])).

tff(c_160,plain,(
    ~ v1_xboole_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_157])).

tff(c_132,plain,(
    '#skF_1'('#skF_2','#skF_3') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_18,plain,(
    ! [B_17,A_15] :
      ( B_17 = A_15
      | ~ r1_tarski(A_15,B_17)
      | ~ v1_zfmisc_1(B_17)
      | v1_xboole_0(B_17)
      | v1_xboole_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_145,plain,
    ( '#skF_1'('#skF_2','#skF_3') = '#skF_3'
    | ~ v1_zfmisc_1('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_142,c_18])).

tff(c_151,plain,
    ( ~ v1_zfmisc_1('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_132,c_145])).

tff(c_153,plain,(
    ~ v1_zfmisc_1('#skF_1'('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_151])).

tff(c_134,plain,(
    ! [A_47,B_48] :
      ( v2_tex_2('#skF_1'(A_47,B_48),A_47)
      | v3_tex_2(B_48,A_47)
      | ~ v2_tex_2(B_48,A_47)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ l1_pre_topc(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_136,plain,
    ( v2_tex_2('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_134])).

tff(c_139,plain,
    ( v2_tex_2('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v3_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_133,c_136])).

tff(c_140,plain,(
    v2_tex_2('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_139])).

tff(c_12,plain,(
    ! [A_5,B_11] :
      ( m1_subset_1('#skF_1'(A_5,B_11),k1_zfmisc_1(u1_struct_0(A_5)))
      | v3_tex_2(B_11,A_5)
      | ~ v2_tex_2(B_11,A_5)
      | ~ m1_subset_1(B_11,k1_zfmisc_1(u1_struct_0(A_5)))
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_193,plain,(
    ! [B_53,A_54] :
      ( v1_zfmisc_1(B_53)
      | ~ v2_tex_2(B_53,A_54)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(u1_struct_0(A_54)))
      | v1_xboole_0(B_53)
      | ~ l1_pre_topc(A_54)
      | ~ v2_tdlat_3(A_54)
      | ~ v2_pre_topc(A_54)
      | v2_struct_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_244,plain,(
    ! [A_65,B_66] :
      ( v1_zfmisc_1('#skF_1'(A_65,B_66))
      | ~ v2_tex_2('#skF_1'(A_65,B_66),A_65)
      | v1_xboole_0('#skF_1'(A_65,B_66))
      | ~ v2_tdlat_3(A_65)
      | ~ v2_pre_topc(A_65)
      | v2_struct_0(A_65)
      | v3_tex_2(B_66,A_65)
      | ~ v2_tex_2(B_66,A_65)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ l1_pre_topc(A_65) ) ),
    inference(resolution,[status(thm)],[c_12,c_193])).

tff(c_248,plain,
    ( v1_zfmisc_1('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_1'('#skF_2','#skF_3'))
    | ~ v2_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_140,c_244])).

tff(c_252,plain,
    ( v1_zfmisc_1('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_1'('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2')
    | v3_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26,c_133,c_34,c_32,c_248])).

tff(c_254,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_36,c_160,c_153,c_252])).

tff(c_255,plain,(
    v1_xboole_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_151])).

tff(c_279,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_2])).

tff(c_283,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_255,c_279])).

tff(c_285,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_283])).

tff(c_286,plain,(
    ~ v1_zfmisc_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_287,plain,(
    v3_tex_2('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_293,plain,(
    ! [B_75,A_76] :
      ( v2_tex_2(B_75,A_76)
      | ~ v3_tex_2(B_75,A_76)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ l1_pre_topc(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_296,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | ~ v3_tex_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_293])).

tff(c_299,plain,(
    v2_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_287,c_296])).

tff(c_346,plain,(
    ! [B_87,A_88] :
      ( v1_zfmisc_1(B_87)
      | ~ v2_tex_2(B_87,A_88)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(u1_struct_0(A_88)))
      | v1_xboole_0(B_87)
      | ~ l1_pre_topc(A_88)
      | ~ v2_tdlat_3(A_88)
      | ~ v2_pre_topc(A_88)
      | v2_struct_0(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_352,plain,
    ( v1_zfmisc_1('#skF_3')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_346])).

tff(c_356,plain,
    ( v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_299,c_352])).

tff(c_358,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_28,c_286,c_356])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:30:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.37/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.37/1.32  
% 2.37/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.37/1.32  %$ v3_tex_2 > v2_tex_2 > r1_tarski > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_pre_topc > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.37/1.32  
% 2.37/1.32  %Foreground sorts:
% 2.37/1.32  
% 2.37/1.32  
% 2.37/1.32  %Background operators:
% 2.37/1.32  
% 2.37/1.32  
% 2.37/1.32  %Foreground operators:
% 2.37/1.32  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.37/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.37/1.32  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.37/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.37/1.32  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 2.37/1.32  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.37/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.37/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.37/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.37/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.37/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.37/1.32  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.37/1.32  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.37/1.32  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.37/1.32  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.37/1.32  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.37/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.37/1.32  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 2.37/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.37/1.32  
% 2.66/1.34  tff(f_119, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v3_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_tex_2)).
% 2.66/1.34  tff(f_53, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_tex_2)).
% 2.66/1.34  tff(f_99, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tex_2)).
% 2.66/1.34  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.66/1.34  tff(f_31, axiom, (![A, B]: (~v1_xboole_0(A) => ~v1_xboole_0(k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_xboole_0)).
% 2.66/1.34  tff(f_66, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 2.66/1.34  tff(c_36, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.66/1.34  tff(c_28, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.66/1.34  tff(c_38, plain, (~v1_zfmisc_1('#skF_3') | ~v3_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.66/1.34  tff(c_45, plain, (~v3_tex_2('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_38])).
% 2.66/1.34  tff(c_30, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.66/1.34  tff(c_26, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.66/1.34  tff(c_65, plain, (![A_35, B_36]: ('#skF_1'(A_35, B_36)!=B_36 | v3_tex_2(B_36, A_35) | ~v2_tex_2(B_36, A_35) | ~m1_subset_1(B_36, k1_zfmisc_1(u1_struct_0(A_35))) | ~l1_pre_topc(A_35))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.66/1.34  tff(c_68, plain, ('#skF_1'('#skF_2', '#skF_3')!='#skF_3' | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_26, c_65])).
% 2.66/1.34  tff(c_71, plain, ('#skF_1'('#skF_2', '#skF_3')!='#skF_3' | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_68])).
% 2.66/1.34  tff(c_72, plain, ('#skF_1'('#skF_2', '#skF_3')!='#skF_3' | ~v2_tex_2('#skF_3', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_45, c_71])).
% 2.66/1.34  tff(c_80, plain, (~v2_tex_2('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_72])).
% 2.66/1.34  tff(c_34, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.66/1.34  tff(c_32, plain, (v2_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.66/1.34  tff(c_44, plain, (v3_tex_2('#skF_3', '#skF_2') | v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.66/1.34  tff(c_46, plain, (v1_zfmisc_1('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_45, c_44])).
% 2.66/1.34  tff(c_119, plain, (![B_45, A_46]: (v2_tex_2(B_45, A_46) | ~v1_zfmisc_1(B_45) | ~m1_subset_1(B_45, k1_zfmisc_1(u1_struct_0(A_46))) | v1_xboole_0(B_45) | ~l1_pre_topc(A_46) | ~v2_tdlat_3(A_46) | ~v2_pre_topc(A_46) | v2_struct_0(A_46))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.66/1.34  tff(c_125, plain, (v2_tex_2('#skF_3', '#skF_2') | ~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_26, c_119])).
% 2.66/1.34  tff(c_129, plain, (v2_tex_2('#skF_3', '#skF_2') | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_46, c_125])).
% 2.66/1.34  tff(c_131, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_28, c_80, c_129])).
% 2.66/1.34  tff(c_133, plain, (v2_tex_2('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_72])).
% 2.66/1.34  tff(c_73, plain, (![B_37, A_38]: (r1_tarski(B_37, '#skF_1'(A_38, B_37)) | v3_tex_2(B_37, A_38) | ~v2_tex_2(B_37, A_38) | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0(A_38))) | ~l1_pre_topc(A_38))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.66/1.34  tff(c_75, plain, (r1_tarski('#skF_3', '#skF_1'('#skF_2', '#skF_3')) | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_26, c_73])).
% 2.66/1.34  tff(c_78, plain, (r1_tarski('#skF_3', '#skF_1'('#skF_2', '#skF_3')) | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_75])).
% 2.66/1.34  tff(c_79, plain, (r1_tarski('#skF_3', '#skF_1'('#skF_2', '#skF_3')) | ~v2_tex_2('#skF_3', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_45, c_78])).
% 2.66/1.34  tff(c_142, plain, (r1_tarski('#skF_3', '#skF_1'('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_79])).
% 2.66/1.34  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, B_4)=B_4 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.66/1.34  tff(c_152, plain, (k2_xboole_0('#skF_3', '#skF_1'('#skF_2', '#skF_3'))='#skF_1'('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_142, c_4])).
% 2.66/1.34  tff(c_2, plain, (![A_1, B_2]: (~v1_xboole_0(k2_xboole_0(A_1, B_2)) | v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.66/1.34  tff(c_157, plain, (~v1_xboole_0('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_152, c_2])).
% 2.66/1.34  tff(c_160, plain, (~v1_xboole_0('#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_28, c_157])).
% 2.66/1.34  tff(c_132, plain, ('#skF_1'('#skF_2', '#skF_3')!='#skF_3'), inference(splitRight, [status(thm)], [c_72])).
% 2.66/1.34  tff(c_18, plain, (![B_17, A_15]: (B_17=A_15 | ~r1_tarski(A_15, B_17) | ~v1_zfmisc_1(B_17) | v1_xboole_0(B_17) | v1_xboole_0(A_15))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.66/1.34  tff(c_145, plain, ('#skF_1'('#skF_2', '#skF_3')='#skF_3' | ~v1_zfmisc_1('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_142, c_18])).
% 2.66/1.34  tff(c_151, plain, (~v1_zfmisc_1('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_28, c_132, c_145])).
% 2.66/1.34  tff(c_153, plain, (~v1_zfmisc_1('#skF_1'('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_151])).
% 2.66/1.34  tff(c_134, plain, (![A_47, B_48]: (v2_tex_2('#skF_1'(A_47, B_48), A_47) | v3_tex_2(B_48, A_47) | ~v2_tex_2(B_48, A_47) | ~m1_subset_1(B_48, k1_zfmisc_1(u1_struct_0(A_47))) | ~l1_pre_topc(A_47))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.66/1.34  tff(c_136, plain, (v2_tex_2('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_26, c_134])).
% 2.66/1.34  tff(c_139, plain, (v2_tex_2('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v3_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_133, c_136])).
% 2.66/1.34  tff(c_140, plain, (v2_tex_2('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_45, c_139])).
% 2.66/1.34  tff(c_12, plain, (![A_5, B_11]: (m1_subset_1('#skF_1'(A_5, B_11), k1_zfmisc_1(u1_struct_0(A_5))) | v3_tex_2(B_11, A_5) | ~v2_tex_2(B_11, A_5) | ~m1_subset_1(B_11, k1_zfmisc_1(u1_struct_0(A_5))) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.66/1.34  tff(c_193, plain, (![B_53, A_54]: (v1_zfmisc_1(B_53) | ~v2_tex_2(B_53, A_54) | ~m1_subset_1(B_53, k1_zfmisc_1(u1_struct_0(A_54))) | v1_xboole_0(B_53) | ~l1_pre_topc(A_54) | ~v2_tdlat_3(A_54) | ~v2_pre_topc(A_54) | v2_struct_0(A_54))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.66/1.34  tff(c_244, plain, (![A_65, B_66]: (v1_zfmisc_1('#skF_1'(A_65, B_66)) | ~v2_tex_2('#skF_1'(A_65, B_66), A_65) | v1_xboole_0('#skF_1'(A_65, B_66)) | ~v2_tdlat_3(A_65) | ~v2_pre_topc(A_65) | v2_struct_0(A_65) | v3_tex_2(B_66, A_65) | ~v2_tex_2(B_66, A_65) | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0(A_65))) | ~l1_pre_topc(A_65))), inference(resolution, [status(thm)], [c_12, c_193])).
% 2.66/1.34  tff(c_248, plain, (v1_zfmisc_1('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_1'('#skF_2', '#skF_3')) | ~v2_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_140, c_244])).
% 2.66/1.34  tff(c_252, plain, (v1_zfmisc_1('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_1'('#skF_2', '#skF_3')) | v2_struct_0('#skF_2') | v3_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_26, c_133, c_34, c_32, c_248])).
% 2.66/1.34  tff(c_254, plain, $false, inference(negUnitSimplification, [status(thm)], [c_45, c_36, c_160, c_153, c_252])).
% 2.66/1.34  tff(c_255, plain, (v1_xboole_0('#skF_1'('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_151])).
% 2.66/1.34  tff(c_279, plain, (~v1_xboole_0('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_152, c_2])).
% 2.66/1.34  tff(c_283, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_255, c_279])).
% 2.66/1.34  tff(c_285, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_283])).
% 2.66/1.34  tff(c_286, plain, (~v1_zfmisc_1('#skF_3')), inference(splitRight, [status(thm)], [c_38])).
% 2.66/1.34  tff(c_287, plain, (v3_tex_2('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_38])).
% 2.66/1.34  tff(c_293, plain, (![B_75, A_76]: (v2_tex_2(B_75, A_76) | ~v3_tex_2(B_75, A_76) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0(A_76))) | ~l1_pre_topc(A_76))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.66/1.34  tff(c_296, plain, (v2_tex_2('#skF_3', '#skF_2') | ~v3_tex_2('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_26, c_293])).
% 2.66/1.34  tff(c_299, plain, (v2_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_287, c_296])).
% 2.66/1.34  tff(c_346, plain, (![B_87, A_88]: (v1_zfmisc_1(B_87) | ~v2_tex_2(B_87, A_88) | ~m1_subset_1(B_87, k1_zfmisc_1(u1_struct_0(A_88))) | v1_xboole_0(B_87) | ~l1_pre_topc(A_88) | ~v2_tdlat_3(A_88) | ~v2_pre_topc(A_88) | v2_struct_0(A_88))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.66/1.34  tff(c_352, plain, (v1_zfmisc_1('#skF_3') | ~v2_tex_2('#skF_3', '#skF_2') | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_26, c_346])).
% 2.66/1.34  tff(c_356, plain, (v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_299, c_352])).
% 2.66/1.34  tff(c_358, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_28, c_286, c_356])).
% 2.66/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.66/1.34  
% 2.66/1.34  Inference rules
% 2.66/1.34  ----------------------
% 2.66/1.34  #Ref     : 0
% 2.66/1.34  #Sup     : 58
% 2.66/1.34  #Fact    : 0
% 2.66/1.34  #Define  : 0
% 2.66/1.34  #Split   : 4
% 2.66/1.34  #Chain   : 0
% 2.66/1.34  #Close   : 0
% 2.66/1.34  
% 2.66/1.34  Ordering : KBO
% 2.66/1.34  
% 2.66/1.34  Simplification rules
% 2.66/1.34  ----------------------
% 2.66/1.34  #Subsume      : 17
% 2.66/1.34  #Demod        : 58
% 2.66/1.34  #Tautology    : 11
% 2.66/1.34  #SimpNegUnit  : 20
% 2.66/1.34  #BackRed      : 0
% 2.66/1.34  
% 2.66/1.34  #Partial instantiations: 0
% 2.66/1.34  #Strategies tried      : 1
% 2.66/1.34  
% 2.66/1.34  Timing (in seconds)
% 2.66/1.34  ----------------------
% 2.66/1.34  Preprocessing        : 0.29
% 2.66/1.34  Parsing              : 0.16
% 2.66/1.34  CNF conversion       : 0.02
% 2.66/1.34  Main loop            : 0.28
% 2.66/1.34  Inferencing          : 0.11
% 2.66/1.34  Reduction            : 0.08
% 2.66/1.34  Demodulation         : 0.05
% 2.66/1.34  BG Simplification    : 0.02
% 2.66/1.34  Subsumption          : 0.06
% 2.66/1.34  Abstraction          : 0.01
% 2.66/1.34  MUC search           : 0.00
% 2.66/1.34  Cooper               : 0.00
% 2.66/1.34  Total                : 0.61
% 2.66/1.34  Index Insertion      : 0.00
% 2.66/1.34  Index Deletion       : 0.00
% 2.66/1.34  Index Matching       : 0.00
% 2.66/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
