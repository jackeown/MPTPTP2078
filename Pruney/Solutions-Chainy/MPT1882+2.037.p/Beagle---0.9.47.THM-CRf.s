%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:17 EST 2020

% Result     : Theorem 2.24s
% Output     : CNFRefutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 261 expanded)
%              Number of leaves         :   25 ( 100 expanded)
%              Depth                    :   11
%              Number of atoms          :  194 ( 986 expanded)
%              Number of equality atoms :   12 (  51 expanded)
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

tff(f_111,negated_conjecture,(
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

tff(f_59,axiom,(
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

tff(f_91,axiom,(
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

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(A)
     => ~ v1_xboole_0(k2_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_xboole_0)).

tff(f_72,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_28,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_38,plain,
    ( ~ v1_zfmisc_1('#skF_3')
    | ~ v3_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_45,plain,(
    ~ v3_tex_2('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_30,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_26,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_64,plain,(
    ! [A_32,B_33] :
      ( '#skF_1'(A_32,B_33) != B_33
      | v3_tex_2(B_33,A_32)
      | ~ v2_tex_2(B_33,A_32)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ l1_pre_topc(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_67,plain,
    ( '#skF_1'('#skF_2','#skF_3') != '#skF_3'
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_64])).

tff(c_70,plain,
    ( '#skF_1'('#skF_2','#skF_3') != '#skF_3'
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_67])).

tff(c_71,plain,
    ( '#skF_1'('#skF_2','#skF_3') != '#skF_3'
    | ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_70])).

tff(c_79,plain,(
    ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_71])).

tff(c_34,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_32,plain,(
    v2_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_44,plain,
    ( v3_tex_2('#skF_3','#skF_2')
    | v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_46,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_44])).

tff(c_95,plain,(
    ! [B_40,A_41] :
      ( v2_tex_2(B_40,A_41)
      | ~ v1_zfmisc_1(B_40)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(u1_struct_0(A_41)))
      | v1_xboole_0(B_40)
      | ~ l1_pre_topc(A_41)
      | ~ v2_tdlat_3(A_41)
      | ~ v2_pre_topc(A_41)
      | v2_struct_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_98,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_95])).

tff(c_101,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_46,c_98])).

tff(c_103,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_28,c_79,c_101])).

tff(c_105,plain,(
    v2_tex_2('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_71])).

tff(c_72,plain,(
    ! [B_34,A_35] :
      ( r1_tarski(B_34,'#skF_1'(A_35,B_34))
      | v3_tex_2(B_34,A_35)
      | ~ v2_tex_2(B_34,A_35)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ l1_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_74,plain,
    ( r1_tarski('#skF_3','#skF_1'('#skF_2','#skF_3'))
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_72])).

tff(c_77,plain,
    ( r1_tarski('#skF_3','#skF_1'('#skF_2','#skF_3'))
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_74])).

tff(c_78,plain,
    ( r1_tarski('#skF_3','#skF_1'('#skF_2','#skF_3'))
    | ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_77])).

tff(c_107,plain,(
    r1_tarski('#skF_3','#skF_1'('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_78])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k2_xboole_0(A_3,B_4) = B_4
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_117,plain,(
    k2_xboole_0('#skF_3','#skF_1'('#skF_2','#skF_3')) = '#skF_1'('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_107,c_4])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( ~ v1_xboole_0(k2_xboole_0(A_1,B_2))
      | v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_128,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_2])).

tff(c_131,plain,(
    ~ v1_xboole_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_128])).

tff(c_104,plain,(
    '#skF_1'('#skF_2','#skF_3') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_71])).

tff(c_20,plain,(
    ! [B_18,A_16] :
      ( B_18 = A_16
      | ~ r1_tarski(A_16,B_18)
      | ~ v1_zfmisc_1(B_18)
      | v1_xboole_0(B_18)
      | v1_xboole_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_110,plain,
    ( '#skF_1'('#skF_2','#skF_3') = '#skF_3'
    | ~ v1_zfmisc_1('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_107,c_20])).

tff(c_116,plain,
    ( ~ v1_zfmisc_1('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_104,c_110])).

tff(c_133,plain,(
    ~ v1_zfmisc_1('#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_116])).

tff(c_118,plain,(
    ! [A_42,B_43] :
      ( v2_tex_2('#skF_1'(A_42,B_43),A_42)
      | v3_tex_2(B_43,A_42)
      | ~ v2_tex_2(B_43,A_42)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(u1_struct_0(A_42)))
      | ~ l1_pre_topc(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_120,plain,
    ( v2_tex_2('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_118])).

tff(c_123,plain,
    ( v2_tex_2('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v3_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_105,c_120])).

tff(c_124,plain,(
    v2_tex_2('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_123])).

tff(c_14,plain,(
    ! [A_6,B_12] :
      ( m1_subset_1('#skF_1'(A_6,B_12),k1_zfmisc_1(u1_struct_0(A_6)))
      | v3_tex_2(B_12,A_6)
      | ~ v2_tex_2(B_12,A_6)
      | ~ m1_subset_1(B_12,k1_zfmisc_1(u1_struct_0(A_6)))
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_161,plain,(
    ! [B_48,A_49] :
      ( v1_zfmisc_1(B_48)
      | ~ v2_tex_2(B_48,A_49)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(u1_struct_0(A_49)))
      | v1_xboole_0(B_48)
      | ~ l1_pre_topc(A_49)
      | ~ v2_tdlat_3(A_49)
      | ~ v2_pre_topc(A_49)
      | v2_struct_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_200,plain,(
    ! [A_58,B_59] :
      ( v1_zfmisc_1('#skF_1'(A_58,B_59))
      | ~ v2_tex_2('#skF_1'(A_58,B_59),A_58)
      | v1_xboole_0('#skF_1'(A_58,B_59))
      | ~ v2_tdlat_3(A_58)
      | ~ v2_pre_topc(A_58)
      | v2_struct_0(A_58)
      | v3_tex_2(B_59,A_58)
      | ~ v2_tex_2(B_59,A_58)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ l1_pre_topc(A_58) ) ),
    inference(resolution,[status(thm)],[c_14,c_161])).

tff(c_204,plain,
    ( v1_zfmisc_1('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_1'('#skF_2','#skF_3'))
    | ~ v2_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_124,c_200])).

tff(c_208,plain,
    ( v1_zfmisc_1('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_1'('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2')
    | v3_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26,c_105,c_34,c_32,c_204])).

tff(c_210,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_36,c_131,c_133,c_208])).

tff(c_211,plain,(
    ~ v1_zfmisc_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_212,plain,(
    v3_tex_2('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_225,plain,(
    ! [B_67,A_68] :
      ( v2_tex_2(B_67,A_68)
      | ~ v3_tex_2(B_67,A_68)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ l1_pre_topc(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_228,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | ~ v3_tex_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_225])).

tff(c_231,plain,(
    v2_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_212,c_228])).

tff(c_278,plain,(
    ! [B_79,A_80] :
      ( v1_zfmisc_1(B_79)
      | ~ v2_tex_2(B_79,A_80)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0(A_80)))
      | v1_xboole_0(B_79)
      | ~ l1_pre_topc(A_80)
      | ~ v2_tdlat_3(A_80)
      | ~ v2_pre_topc(A_80)
      | v2_struct_0(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_284,plain,
    ( v1_zfmisc_1('#skF_3')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_278])).

tff(c_288,plain,
    ( v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_231,c_284])).

tff(c_290,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_28,c_211,c_288])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n017.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 14:04:46 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.24/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.25  
% 2.24/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.25  %$ v3_tex_2 > v2_tex_2 > r1_tarski > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_pre_topc > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.24/1.25  
% 2.24/1.25  %Foreground sorts:
% 2.24/1.25  
% 2.24/1.25  
% 2.24/1.25  %Background operators:
% 2.24/1.25  
% 2.24/1.25  
% 2.24/1.25  %Foreground operators:
% 2.24/1.25  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.24/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.24/1.25  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.24/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.24/1.25  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 2.24/1.25  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.24/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.24/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.24/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.24/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.24/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.24/1.25  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.24/1.25  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.24/1.25  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.24/1.25  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.24/1.25  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.24/1.25  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.24/1.25  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 2.24/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.24/1.25  
% 2.24/1.27  tff(f_111, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v3_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_tex_2)).
% 2.24/1.27  tff(f_59, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 2.24/1.27  tff(f_91, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tex_2)).
% 2.24/1.27  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.24/1.27  tff(f_31, axiom, (![A, B]: (~v1_xboole_0(A) => ~v1_xboole_0(k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_xboole_0)).
% 2.24/1.27  tff(f_72, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 2.24/1.27  tff(c_36, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.24/1.27  tff(c_28, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.24/1.27  tff(c_38, plain, (~v1_zfmisc_1('#skF_3') | ~v3_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.24/1.27  tff(c_45, plain, (~v3_tex_2('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_38])).
% 2.24/1.27  tff(c_30, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.24/1.27  tff(c_26, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.24/1.27  tff(c_64, plain, (![A_32, B_33]: ('#skF_1'(A_32, B_33)!=B_33 | v3_tex_2(B_33, A_32) | ~v2_tex_2(B_33, A_32) | ~m1_subset_1(B_33, k1_zfmisc_1(u1_struct_0(A_32))) | ~l1_pre_topc(A_32))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.24/1.27  tff(c_67, plain, ('#skF_1'('#skF_2', '#skF_3')!='#skF_3' | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_26, c_64])).
% 2.24/1.27  tff(c_70, plain, ('#skF_1'('#skF_2', '#skF_3')!='#skF_3' | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_67])).
% 2.24/1.27  tff(c_71, plain, ('#skF_1'('#skF_2', '#skF_3')!='#skF_3' | ~v2_tex_2('#skF_3', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_45, c_70])).
% 2.24/1.27  tff(c_79, plain, (~v2_tex_2('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_71])).
% 2.24/1.27  tff(c_34, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.24/1.27  tff(c_32, plain, (v2_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.24/1.27  tff(c_44, plain, (v3_tex_2('#skF_3', '#skF_2') | v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.24/1.27  tff(c_46, plain, (v1_zfmisc_1('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_45, c_44])).
% 2.24/1.27  tff(c_95, plain, (![B_40, A_41]: (v2_tex_2(B_40, A_41) | ~v1_zfmisc_1(B_40) | ~m1_subset_1(B_40, k1_zfmisc_1(u1_struct_0(A_41))) | v1_xboole_0(B_40) | ~l1_pre_topc(A_41) | ~v2_tdlat_3(A_41) | ~v2_pre_topc(A_41) | v2_struct_0(A_41))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.24/1.27  tff(c_98, plain, (v2_tex_2('#skF_3', '#skF_2') | ~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_26, c_95])).
% 2.24/1.27  tff(c_101, plain, (v2_tex_2('#skF_3', '#skF_2') | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_46, c_98])).
% 2.24/1.27  tff(c_103, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_28, c_79, c_101])).
% 2.24/1.27  tff(c_105, plain, (v2_tex_2('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_71])).
% 2.24/1.27  tff(c_72, plain, (![B_34, A_35]: (r1_tarski(B_34, '#skF_1'(A_35, B_34)) | v3_tex_2(B_34, A_35) | ~v2_tex_2(B_34, A_35) | ~m1_subset_1(B_34, k1_zfmisc_1(u1_struct_0(A_35))) | ~l1_pre_topc(A_35))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.24/1.27  tff(c_74, plain, (r1_tarski('#skF_3', '#skF_1'('#skF_2', '#skF_3')) | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_26, c_72])).
% 2.24/1.27  tff(c_77, plain, (r1_tarski('#skF_3', '#skF_1'('#skF_2', '#skF_3')) | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_74])).
% 2.24/1.27  tff(c_78, plain, (r1_tarski('#skF_3', '#skF_1'('#skF_2', '#skF_3')) | ~v2_tex_2('#skF_3', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_45, c_77])).
% 2.24/1.27  tff(c_107, plain, (r1_tarski('#skF_3', '#skF_1'('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_78])).
% 2.24/1.27  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, B_4)=B_4 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.24/1.27  tff(c_117, plain, (k2_xboole_0('#skF_3', '#skF_1'('#skF_2', '#skF_3'))='#skF_1'('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_107, c_4])).
% 2.24/1.27  tff(c_2, plain, (![A_1, B_2]: (~v1_xboole_0(k2_xboole_0(A_1, B_2)) | v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.24/1.27  tff(c_128, plain, (~v1_xboole_0('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_117, c_2])).
% 2.24/1.27  tff(c_131, plain, (~v1_xboole_0('#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_28, c_128])).
% 2.24/1.27  tff(c_104, plain, ('#skF_1'('#skF_2', '#skF_3')!='#skF_3'), inference(splitRight, [status(thm)], [c_71])).
% 2.24/1.27  tff(c_20, plain, (![B_18, A_16]: (B_18=A_16 | ~r1_tarski(A_16, B_18) | ~v1_zfmisc_1(B_18) | v1_xboole_0(B_18) | v1_xboole_0(A_16))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.24/1.27  tff(c_110, plain, ('#skF_1'('#skF_2', '#skF_3')='#skF_3' | ~v1_zfmisc_1('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_107, c_20])).
% 2.24/1.27  tff(c_116, plain, (~v1_zfmisc_1('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_28, c_104, c_110])).
% 2.24/1.27  tff(c_133, plain, (~v1_zfmisc_1('#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_131, c_116])).
% 2.24/1.27  tff(c_118, plain, (![A_42, B_43]: (v2_tex_2('#skF_1'(A_42, B_43), A_42) | v3_tex_2(B_43, A_42) | ~v2_tex_2(B_43, A_42) | ~m1_subset_1(B_43, k1_zfmisc_1(u1_struct_0(A_42))) | ~l1_pre_topc(A_42))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.24/1.27  tff(c_120, plain, (v2_tex_2('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_26, c_118])).
% 2.24/1.27  tff(c_123, plain, (v2_tex_2('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v3_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_105, c_120])).
% 2.24/1.27  tff(c_124, plain, (v2_tex_2('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_45, c_123])).
% 2.24/1.27  tff(c_14, plain, (![A_6, B_12]: (m1_subset_1('#skF_1'(A_6, B_12), k1_zfmisc_1(u1_struct_0(A_6))) | v3_tex_2(B_12, A_6) | ~v2_tex_2(B_12, A_6) | ~m1_subset_1(B_12, k1_zfmisc_1(u1_struct_0(A_6))) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.24/1.27  tff(c_161, plain, (![B_48, A_49]: (v1_zfmisc_1(B_48) | ~v2_tex_2(B_48, A_49) | ~m1_subset_1(B_48, k1_zfmisc_1(u1_struct_0(A_49))) | v1_xboole_0(B_48) | ~l1_pre_topc(A_49) | ~v2_tdlat_3(A_49) | ~v2_pre_topc(A_49) | v2_struct_0(A_49))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.24/1.27  tff(c_200, plain, (![A_58, B_59]: (v1_zfmisc_1('#skF_1'(A_58, B_59)) | ~v2_tex_2('#skF_1'(A_58, B_59), A_58) | v1_xboole_0('#skF_1'(A_58, B_59)) | ~v2_tdlat_3(A_58) | ~v2_pre_topc(A_58) | v2_struct_0(A_58) | v3_tex_2(B_59, A_58) | ~v2_tex_2(B_59, A_58) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(A_58))) | ~l1_pre_topc(A_58))), inference(resolution, [status(thm)], [c_14, c_161])).
% 2.24/1.27  tff(c_204, plain, (v1_zfmisc_1('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_1'('#skF_2', '#skF_3')) | ~v2_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_124, c_200])).
% 2.24/1.27  tff(c_208, plain, (v1_zfmisc_1('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_1'('#skF_2', '#skF_3')) | v2_struct_0('#skF_2') | v3_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_26, c_105, c_34, c_32, c_204])).
% 2.24/1.27  tff(c_210, plain, $false, inference(negUnitSimplification, [status(thm)], [c_45, c_36, c_131, c_133, c_208])).
% 2.24/1.27  tff(c_211, plain, (~v1_zfmisc_1('#skF_3')), inference(splitRight, [status(thm)], [c_38])).
% 2.24/1.27  tff(c_212, plain, (v3_tex_2('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_38])).
% 2.24/1.27  tff(c_225, plain, (![B_67, A_68]: (v2_tex_2(B_67, A_68) | ~v3_tex_2(B_67, A_68) | ~m1_subset_1(B_67, k1_zfmisc_1(u1_struct_0(A_68))) | ~l1_pre_topc(A_68))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.24/1.27  tff(c_228, plain, (v2_tex_2('#skF_3', '#skF_2') | ~v3_tex_2('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_26, c_225])).
% 2.24/1.27  tff(c_231, plain, (v2_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_212, c_228])).
% 2.24/1.27  tff(c_278, plain, (![B_79, A_80]: (v1_zfmisc_1(B_79) | ~v2_tex_2(B_79, A_80) | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0(A_80))) | v1_xboole_0(B_79) | ~l1_pre_topc(A_80) | ~v2_tdlat_3(A_80) | ~v2_pre_topc(A_80) | v2_struct_0(A_80))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.24/1.27  tff(c_284, plain, (v1_zfmisc_1('#skF_3') | ~v2_tex_2('#skF_3', '#skF_2') | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_26, c_278])).
% 2.24/1.27  tff(c_288, plain, (v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_231, c_284])).
% 2.24/1.27  tff(c_290, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_28, c_211, c_288])).
% 2.24/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.27  
% 2.24/1.27  Inference rules
% 2.24/1.27  ----------------------
% 2.24/1.27  #Ref     : 0
% 2.24/1.27  #Sup     : 40
% 2.24/1.27  #Fact    : 0
% 2.24/1.27  #Define  : 0
% 2.24/1.27  #Split   : 3
% 2.24/1.27  #Chain   : 0
% 2.24/1.27  #Close   : 0
% 2.24/1.27  
% 2.24/1.27  Ordering : KBO
% 2.24/1.27  
% 2.24/1.27  Simplification rules
% 2.24/1.27  ----------------------
% 2.24/1.27  #Subsume      : 10
% 2.24/1.27  #Demod        : 61
% 2.24/1.27  #Tautology    : 12
% 2.24/1.27  #SimpNegUnit  : 19
% 2.24/1.27  #BackRed      : 0
% 2.24/1.27  
% 2.24/1.27  #Partial instantiations: 0
% 2.24/1.27  #Strategies tried      : 1
% 2.24/1.27  
% 2.24/1.27  Timing (in seconds)
% 2.24/1.27  ----------------------
% 2.24/1.28  Preprocessing        : 0.29
% 2.24/1.28  Parsing              : 0.16
% 2.24/1.28  CNF conversion       : 0.02
% 2.24/1.28  Main loop            : 0.23
% 2.24/1.28  Inferencing          : 0.09
% 2.24/1.28  Reduction            : 0.06
% 2.24/1.28  Demodulation         : 0.04
% 2.24/1.28  BG Simplification    : 0.01
% 2.24/1.28  Subsumption          : 0.05
% 2.24/1.28  Abstraction          : 0.01
% 2.24/1.28  MUC search           : 0.00
% 2.24/1.28  Cooper               : 0.00
% 2.24/1.28  Total                : 0.56
% 2.24/1.28  Index Insertion      : 0.00
% 2.24/1.28  Index Deletion       : 0.00
% 2.24/1.28  Index Matching       : 0.00
% 2.24/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
