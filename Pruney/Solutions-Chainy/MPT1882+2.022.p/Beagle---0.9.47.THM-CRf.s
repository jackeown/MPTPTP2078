%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:15 EST 2020

% Result     : Theorem 2.41s
% Output     : CNFRefutation 2.77s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 387 expanded)
%              Number of leaves         :   32 ( 143 expanded)
%              Depth                    :   12
%              Number of atoms          :  215 (1455 expanded)
%              Number of equality atoms :   20 (  86 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_pre_topc > k6_subset_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

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

tff(f_137,negated_conjecture,(
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

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_zfmisc_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_zfmisc_1)).

tff(f_77,axiom,(
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

tff(f_117,axiom,(
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

tff(f_98,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_53,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ( ( r2_hidden(C,D)
                    & r2_hidden(D,B) )
                 => r1_xboole_0(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_mcart_1)).

tff(f_31,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_85,axiom,(
    ! [A,B] :
      ~ ( r1_tarski(A,B)
        & A != B
        & k6_subset_1(B,A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l48_tex_2)).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_36,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_52,plain,
    ( v3_tex_2('#skF_4','#skF_3')
    | v1_zfmisc_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_54,plain,(
    v1_zfmisc_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_46,plain,
    ( ~ v1_zfmisc_1('#skF_4')
    | ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_56,plain,(
    ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_46])).

tff(c_2,plain,(
    ! [A_1] :
      ( v1_zfmisc_1(A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_38,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_108,plain,(
    ! [A_64,B_65] :
      ( '#skF_2'(A_64,B_65) != B_65
      | v3_tex_2(B_65,A_64)
      | ~ v2_tex_2(B_65,A_64)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ l1_pre_topc(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_115,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_108])).

tff(c_119,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_115])).

tff(c_120,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_119])).

tff(c_121,plain,(
    ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_120])).

tff(c_42,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_40,plain,(
    v2_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_162,plain,(
    ! [B_72,A_73] :
      ( v2_tex_2(B_72,A_73)
      | ~ v1_zfmisc_1(B_72)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0(A_73)))
      | v1_xboole_0(B_72)
      | ~ l1_pre_topc(A_73)
      | ~ v2_tdlat_3(A_73)
      | ~ v2_pre_topc(A_73)
      | v2_struct_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_172,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | ~ v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_162])).

tff(c_177,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_54,c_172])).

tff(c_179,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_36,c_121,c_177])).

tff(c_180,plain,(
    '#skF_2'('#skF_3','#skF_4') != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_120])).

tff(c_181,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_120])).

tff(c_182,plain,(
    ! [B_74,A_75] :
      ( r1_tarski(B_74,'#skF_2'(A_75,B_74))
      | v3_tex_2(B_74,A_75)
      | ~ v2_tex_2(B_74,A_75)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ l1_pre_topc(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_187,plain,
    ( r1_tarski('#skF_4','#skF_2'('#skF_3','#skF_4'))
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_182])).

tff(c_191,plain,
    ( r1_tarski('#skF_4','#skF_2'('#skF_3','#skF_4'))
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_181,c_187])).

tff(c_192,plain,(
    r1_tarski('#skF_4','#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_191])).

tff(c_28,plain,(
    ! [B_32,A_30] :
      ( B_32 = A_30
      | ~ r1_tarski(A_30,B_32)
      | ~ v1_zfmisc_1(B_32)
      | v1_xboole_0(B_32)
      | v1_xboole_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_206,plain,
    ( '#skF_2'('#skF_3','#skF_4') = '#skF_4'
    | ~ v1_zfmisc_1('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_192,c_28])).

tff(c_212,plain,
    ( ~ v1_zfmisc_1('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_180,c_206])).

tff(c_216,plain,(
    ~ v1_zfmisc_1('#skF_2'('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_212])).

tff(c_220,plain,(
    ~ v1_xboole_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_2,c_216])).

tff(c_193,plain,(
    ! [A_76,B_77] :
      ( v2_tex_2('#skF_2'(A_76,B_77),A_76)
      | v3_tex_2(B_77,A_76)
      | ~ v2_tex_2(B_77,A_76)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ l1_pre_topc(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_198,plain,
    ( v2_tex_2('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_193])).

tff(c_202,plain,
    ( v2_tex_2('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_181,c_198])).

tff(c_203,plain,(
    v2_tex_2('#skF_2'('#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_202])).

tff(c_20,plain,(
    ! [A_18,B_24] :
      ( m1_subset_1('#skF_2'(A_18,B_24),k1_zfmisc_1(u1_struct_0(A_18)))
      | v3_tex_2(B_24,A_18)
      | ~ v2_tex_2(B_24,A_18)
      | ~ m1_subset_1(B_24,k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_256,plain,(
    ! [B_82,A_83] :
      ( v1_zfmisc_1(B_82)
      | ~ v2_tex_2(B_82,A_83)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(u1_struct_0(A_83)))
      | v1_xboole_0(B_82)
      | ~ l1_pre_topc(A_83)
      | ~ v2_tdlat_3(A_83)
      | ~ v2_pre_topc(A_83)
      | v2_struct_0(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_367,plain,(
    ! [A_111,B_112] :
      ( v1_zfmisc_1('#skF_2'(A_111,B_112))
      | ~ v2_tex_2('#skF_2'(A_111,B_112),A_111)
      | v1_xboole_0('#skF_2'(A_111,B_112))
      | ~ v2_tdlat_3(A_111)
      | ~ v2_pre_topc(A_111)
      | v2_struct_0(A_111)
      | v3_tex_2(B_112,A_111)
      | ~ v2_tex_2(B_112,A_111)
      | ~ m1_subset_1(B_112,k1_zfmisc_1(u1_struct_0(A_111)))
      | ~ l1_pre_topc(A_111) ) ),
    inference(resolution,[status(thm)],[c_20,c_256])).

tff(c_373,plain,
    ( v1_zfmisc_1('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_2'('#skF_3','#skF_4'))
    | ~ v2_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_203,c_367])).

tff(c_380,plain,
    ( v1_zfmisc_1('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_2'('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3')
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_181,c_42,c_40,c_373])).

tff(c_382,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_44,c_220,c_216,c_380])).

tff(c_383,plain,(
    v1_xboole_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_212])).

tff(c_10,plain,(
    ! [A_7] :
      ( r2_hidden('#skF_1'(A_7),A_7)
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_4,plain,(
    ! [A_2,B_3] : m1_subset_1(k6_subset_1(A_2,B_3),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_66,plain,(
    ! [C_42,B_43,A_44] :
      ( ~ v1_xboole_0(C_42)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(C_42))
      | ~ r2_hidden(A_44,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_75,plain,(
    ! [A_47,A_48,B_49] :
      ( ~ v1_xboole_0(A_47)
      | ~ r2_hidden(A_48,k6_subset_1(A_47,B_49)) ) ),
    inference(resolution,[status(thm)],[c_4,c_66])).

tff(c_80,plain,(
    ! [A_47,B_49] :
      ( ~ v1_xboole_0(A_47)
      | k6_subset_1(A_47,B_49) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_75])).

tff(c_387,plain,(
    ! [B_49] : k6_subset_1('#skF_2'('#skF_3','#skF_4'),B_49) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_383,c_80])).

tff(c_26,plain,(
    ! [B_29,A_28] :
      ( k6_subset_1(B_29,A_28) != k1_xboole_0
      | B_29 = A_28
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_209,plain,
    ( k6_subset_1('#skF_2'('#skF_3','#skF_4'),'#skF_4') != k1_xboole_0
    | '#skF_2'('#skF_3','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_192,c_26])).

tff(c_215,plain,(
    k6_subset_1('#skF_2'('#skF_3','#skF_4'),'#skF_4') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_180,c_209])).

tff(c_390,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_387,c_215])).

tff(c_392,plain,(
    ~ v1_zfmisc_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_391,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_430,plain,(
    ! [B_132,A_133] :
      ( v2_tex_2(B_132,A_133)
      | ~ v3_tex_2(B_132,A_133)
      | ~ m1_subset_1(B_132,k1_zfmisc_1(u1_struct_0(A_133)))
      | ~ l1_pre_topc(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_437,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | ~ v3_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_430])).

tff(c_441,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_391,c_437])).

tff(c_495,plain,(
    ! [B_147,A_148] :
      ( v1_zfmisc_1(B_147)
      | ~ v2_tex_2(B_147,A_148)
      | ~ m1_subset_1(B_147,k1_zfmisc_1(u1_struct_0(A_148)))
      | v1_xboole_0(B_147)
      | ~ l1_pre_topc(A_148)
      | ~ v2_tdlat_3(A_148)
      | ~ v2_pre_topc(A_148)
      | v2_struct_0(A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_502,plain,
    ( v1_zfmisc_1('#skF_4')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_495])).

tff(c_506,plain,
    ( v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_441,c_502])).

tff(c_508,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_36,c_392,c_506])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:57:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.41/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/1.43  
% 2.77/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/1.44  %$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_pre_topc > k6_subset_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.77/1.44  
% 2.77/1.44  %Foreground sorts:
% 2.77/1.44  
% 2.77/1.44  
% 2.77/1.44  %Background operators:
% 2.77/1.44  
% 2.77/1.44  
% 2.77/1.44  %Foreground operators:
% 2.77/1.44  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.77/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.77/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.77/1.44  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.77/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.77/1.44  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.77/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.77/1.44  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 2.77/1.44  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.77/1.44  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.77/1.44  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.77/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.77/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.77/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.77/1.44  tff('#skF_4', type, '#skF_4': $i).
% 2.77/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.77/1.44  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.77/1.44  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.77/1.44  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.77/1.44  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.77/1.44  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.77/1.44  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 2.77/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.77/1.44  
% 2.77/1.45  tff(f_137, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v3_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_tex_2)).
% 2.77/1.45  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => v1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_zfmisc_1)).
% 2.77/1.45  tff(f_77, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 2.77/1.45  tff(f_117, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tex_2)).
% 2.77/1.45  tff(f_98, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 2.77/1.45  tff(f_53, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ((r2_hidden(C, D) & r2_hidden(D, B)) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_mcart_1)).
% 2.77/1.45  tff(f_31, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 2.77/1.45  tff(f_38, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.77/1.45  tff(f_85, axiom, (![A, B]: ~((r1_tarski(A, B) & ~(A = B)) & (k6_subset_1(B, A) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l48_tex_2)).
% 2.77/1.45  tff(c_44, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.77/1.45  tff(c_36, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.77/1.45  tff(c_52, plain, (v3_tex_2('#skF_4', '#skF_3') | v1_zfmisc_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.77/1.45  tff(c_54, plain, (v1_zfmisc_1('#skF_4')), inference(splitLeft, [status(thm)], [c_52])).
% 2.77/1.45  tff(c_46, plain, (~v1_zfmisc_1('#skF_4') | ~v3_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.77/1.45  tff(c_56, plain, (~v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_46])).
% 2.77/1.45  tff(c_2, plain, (![A_1]: (v1_zfmisc_1(A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.77/1.45  tff(c_38, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.77/1.45  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.77/1.45  tff(c_108, plain, (![A_64, B_65]: ('#skF_2'(A_64, B_65)!=B_65 | v3_tex_2(B_65, A_64) | ~v2_tex_2(B_65, A_64) | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0(A_64))) | ~l1_pre_topc(A_64))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.77/1.45  tff(c_115, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_34, c_108])).
% 2.77/1.45  tff(c_119, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_115])).
% 2.77/1.45  tff(c_120, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | ~v2_tex_2('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_56, c_119])).
% 2.77/1.45  tff(c_121, plain, (~v2_tex_2('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_120])).
% 2.77/1.45  tff(c_42, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.77/1.45  tff(c_40, plain, (v2_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.77/1.45  tff(c_162, plain, (![B_72, A_73]: (v2_tex_2(B_72, A_73) | ~v1_zfmisc_1(B_72) | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0(A_73))) | v1_xboole_0(B_72) | ~l1_pre_topc(A_73) | ~v2_tdlat_3(A_73) | ~v2_pre_topc(A_73) | v2_struct_0(A_73))), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.77/1.45  tff(c_172, plain, (v2_tex_2('#skF_4', '#skF_3') | ~v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_34, c_162])).
% 2.77/1.45  tff(c_177, plain, (v2_tex_2('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_54, c_172])).
% 2.77/1.45  tff(c_179, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_36, c_121, c_177])).
% 2.77/1.45  tff(c_180, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4'), inference(splitRight, [status(thm)], [c_120])).
% 2.77/1.45  tff(c_181, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_120])).
% 2.77/1.45  tff(c_182, plain, (![B_74, A_75]: (r1_tarski(B_74, '#skF_2'(A_75, B_74)) | v3_tex_2(B_74, A_75) | ~v2_tex_2(B_74, A_75) | ~m1_subset_1(B_74, k1_zfmisc_1(u1_struct_0(A_75))) | ~l1_pre_topc(A_75))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.77/1.45  tff(c_187, plain, (r1_tarski('#skF_4', '#skF_2'('#skF_3', '#skF_4')) | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_34, c_182])).
% 2.77/1.45  tff(c_191, plain, (r1_tarski('#skF_4', '#skF_2'('#skF_3', '#skF_4')) | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_181, c_187])).
% 2.77/1.45  tff(c_192, plain, (r1_tarski('#skF_4', '#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_56, c_191])).
% 2.77/1.45  tff(c_28, plain, (![B_32, A_30]: (B_32=A_30 | ~r1_tarski(A_30, B_32) | ~v1_zfmisc_1(B_32) | v1_xboole_0(B_32) | v1_xboole_0(A_30))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.77/1.45  tff(c_206, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4' | ~v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_192, c_28])).
% 2.77/1.45  tff(c_212, plain, (~v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_36, c_180, c_206])).
% 2.77/1.45  tff(c_216, plain, (~v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_212])).
% 2.77/1.45  tff(c_220, plain, (~v1_xboole_0('#skF_2'('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_2, c_216])).
% 2.77/1.45  tff(c_193, plain, (![A_76, B_77]: (v2_tex_2('#skF_2'(A_76, B_77), A_76) | v3_tex_2(B_77, A_76) | ~v2_tex_2(B_77, A_76) | ~m1_subset_1(B_77, k1_zfmisc_1(u1_struct_0(A_76))) | ~l1_pre_topc(A_76))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.77/1.45  tff(c_198, plain, (v2_tex_2('#skF_2'('#skF_3', '#skF_4'), '#skF_3') | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_34, c_193])).
% 2.77/1.45  tff(c_202, plain, (v2_tex_2('#skF_2'('#skF_3', '#skF_4'), '#skF_3') | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_181, c_198])).
% 2.77/1.45  tff(c_203, plain, (v2_tex_2('#skF_2'('#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_56, c_202])).
% 2.77/1.45  tff(c_20, plain, (![A_18, B_24]: (m1_subset_1('#skF_2'(A_18, B_24), k1_zfmisc_1(u1_struct_0(A_18))) | v3_tex_2(B_24, A_18) | ~v2_tex_2(B_24, A_18) | ~m1_subset_1(B_24, k1_zfmisc_1(u1_struct_0(A_18))) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.77/1.45  tff(c_256, plain, (![B_82, A_83]: (v1_zfmisc_1(B_82) | ~v2_tex_2(B_82, A_83) | ~m1_subset_1(B_82, k1_zfmisc_1(u1_struct_0(A_83))) | v1_xboole_0(B_82) | ~l1_pre_topc(A_83) | ~v2_tdlat_3(A_83) | ~v2_pre_topc(A_83) | v2_struct_0(A_83))), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.77/1.45  tff(c_367, plain, (![A_111, B_112]: (v1_zfmisc_1('#skF_2'(A_111, B_112)) | ~v2_tex_2('#skF_2'(A_111, B_112), A_111) | v1_xboole_0('#skF_2'(A_111, B_112)) | ~v2_tdlat_3(A_111) | ~v2_pre_topc(A_111) | v2_struct_0(A_111) | v3_tex_2(B_112, A_111) | ~v2_tex_2(B_112, A_111) | ~m1_subset_1(B_112, k1_zfmisc_1(u1_struct_0(A_111))) | ~l1_pre_topc(A_111))), inference(resolution, [status(thm)], [c_20, c_256])).
% 2.77/1.45  tff(c_373, plain, (v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_2'('#skF_3', '#skF_4')) | ~v2_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_203, c_367])).
% 2.77/1.45  tff(c_380, plain, (v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_2'('#skF_3', '#skF_4')) | v2_struct_0('#skF_3') | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_181, c_42, c_40, c_373])).
% 2.77/1.45  tff(c_382, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_44, c_220, c_216, c_380])).
% 2.77/1.45  tff(c_383, plain, (v1_xboole_0('#skF_2'('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_212])).
% 2.77/1.45  tff(c_10, plain, (![A_7]: (r2_hidden('#skF_1'(A_7), A_7) | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.77/1.45  tff(c_4, plain, (![A_2, B_3]: (m1_subset_1(k6_subset_1(A_2, B_3), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.77/1.45  tff(c_66, plain, (![C_42, B_43, A_44]: (~v1_xboole_0(C_42) | ~m1_subset_1(B_43, k1_zfmisc_1(C_42)) | ~r2_hidden(A_44, B_43))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.77/1.45  tff(c_75, plain, (![A_47, A_48, B_49]: (~v1_xboole_0(A_47) | ~r2_hidden(A_48, k6_subset_1(A_47, B_49)))), inference(resolution, [status(thm)], [c_4, c_66])).
% 2.77/1.45  tff(c_80, plain, (![A_47, B_49]: (~v1_xboole_0(A_47) | k6_subset_1(A_47, B_49)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_75])).
% 2.77/1.45  tff(c_387, plain, (![B_49]: (k6_subset_1('#skF_2'('#skF_3', '#skF_4'), B_49)=k1_xboole_0)), inference(resolution, [status(thm)], [c_383, c_80])).
% 2.77/1.45  tff(c_26, plain, (![B_29, A_28]: (k6_subset_1(B_29, A_28)!=k1_xboole_0 | B_29=A_28 | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.77/1.45  tff(c_209, plain, (k6_subset_1('#skF_2'('#skF_3', '#skF_4'), '#skF_4')!=k1_xboole_0 | '#skF_2'('#skF_3', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_192, c_26])).
% 2.77/1.45  tff(c_215, plain, (k6_subset_1('#skF_2'('#skF_3', '#skF_4'), '#skF_4')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_180, c_209])).
% 2.77/1.45  tff(c_390, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_387, c_215])).
% 2.77/1.45  tff(c_392, plain, (~v1_zfmisc_1('#skF_4')), inference(splitRight, [status(thm)], [c_52])).
% 2.77/1.45  tff(c_391, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_52])).
% 2.77/1.45  tff(c_430, plain, (![B_132, A_133]: (v2_tex_2(B_132, A_133) | ~v3_tex_2(B_132, A_133) | ~m1_subset_1(B_132, k1_zfmisc_1(u1_struct_0(A_133))) | ~l1_pre_topc(A_133))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.77/1.45  tff(c_437, plain, (v2_tex_2('#skF_4', '#skF_3') | ~v3_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_34, c_430])).
% 2.77/1.45  tff(c_441, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_391, c_437])).
% 2.77/1.45  tff(c_495, plain, (![B_147, A_148]: (v1_zfmisc_1(B_147) | ~v2_tex_2(B_147, A_148) | ~m1_subset_1(B_147, k1_zfmisc_1(u1_struct_0(A_148))) | v1_xboole_0(B_147) | ~l1_pre_topc(A_148) | ~v2_tdlat_3(A_148) | ~v2_pre_topc(A_148) | v2_struct_0(A_148))), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.77/1.45  tff(c_502, plain, (v1_zfmisc_1('#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_34, c_495])).
% 2.77/1.45  tff(c_506, plain, (v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_441, c_502])).
% 2.77/1.45  tff(c_508, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_36, c_392, c_506])).
% 2.77/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/1.45  
% 2.77/1.45  Inference rules
% 2.77/1.45  ----------------------
% 2.77/1.45  #Ref     : 0
% 2.77/1.45  #Sup     : 81
% 2.77/1.45  #Fact    : 0
% 2.77/1.45  #Define  : 0
% 2.77/1.45  #Split   : 6
% 2.77/1.45  #Chain   : 0
% 2.77/1.45  #Close   : 0
% 2.77/1.45  
% 2.77/1.45  Ordering : KBO
% 2.77/1.45  
% 2.77/1.45  Simplification rules
% 2.77/1.45  ----------------------
% 2.77/1.45  #Subsume      : 12
% 2.77/1.45  #Demod        : 63
% 2.77/1.45  #Tautology    : 12
% 2.77/1.45  #SimpNegUnit  : 17
% 2.77/1.45  #BackRed      : 1
% 2.77/1.45  
% 2.77/1.45  #Partial instantiations: 0
% 2.77/1.45  #Strategies tried      : 1
% 2.77/1.45  
% 2.77/1.45  Timing (in seconds)
% 2.77/1.45  ----------------------
% 2.77/1.46  Preprocessing        : 0.31
% 2.77/1.46  Parsing              : 0.17
% 2.77/1.46  CNF conversion       : 0.02
% 2.77/1.46  Main loop            : 0.32
% 2.77/1.46  Inferencing          : 0.12
% 2.77/1.46  Reduction            : 0.08
% 2.77/1.46  Demodulation         : 0.06
% 2.77/1.46  BG Simplification    : 0.02
% 2.77/1.46  Subsumption          : 0.07
% 2.77/1.46  Abstraction          : 0.01
% 2.77/1.46  MUC search           : 0.00
% 2.77/1.46  Cooper               : 0.00
% 2.77/1.46  Total                : 0.66
% 2.77/1.46  Index Insertion      : 0.00
% 2.77/1.46  Index Deletion       : 0.00
% 2.77/1.46  Index Matching       : 0.00
% 2.77/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
