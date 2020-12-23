%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:17 EST 2020

% Result     : Theorem 3.73s
% Output     : CNFRefutation 3.73s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 300 expanded)
%              Number of leaves         :   30 ( 114 expanded)
%              Depth                    :   11
%              Number of atoms          :  211 (1103 expanded)
%              Number of equality atoms :   15 (  69 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(v2_tdlat_3,type,(
    v2_tdlat_3: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_125,negated_conjecture,(
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

tff(f_73,axiom,(
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

tff(f_105,axiom,(
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

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_40,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_42,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_86,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_42,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_52,plain,
    ( ~ v1_zfmisc_1('#skF_4')
    | ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_72,plain,(
    ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_44,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_171,plain,(
    ! [A_66,B_67] :
      ( '#skF_2'(A_66,B_67) != B_67
      | v3_tex_2(B_67,A_66)
      | ~ v2_tex_2(B_67,A_66)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ l1_pre_topc(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_174,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_171])).

tff(c_181,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_174])).

tff(c_182,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_181])).

tff(c_184,plain,(
    ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_182])).

tff(c_48,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_46,plain,(
    v2_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_58,plain,
    ( v3_tex_2('#skF_4','#skF_3')
    | v1_zfmisc_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_73,plain,(
    v1_zfmisc_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_58])).

tff(c_239,plain,(
    ! [B_81,A_82] :
      ( v2_tex_2(B_81,A_82)
      | ~ v1_zfmisc_1(B_81)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(u1_struct_0(A_82)))
      | v1_xboole_0(B_81)
      | ~ l1_pre_topc(A_82)
      | ~ v2_tdlat_3(A_82)
      | ~ v2_pre_topc(A_82)
      | v2_struct_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_242,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | ~ v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_239])).

tff(c_249,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_73,c_242])).

tff(c_251,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_42,c_184,c_249])).

tff(c_252,plain,(
    '#skF_2'('#skF_3','#skF_4') != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_182])).

tff(c_253,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_182])).

tff(c_266,plain,(
    ! [B_88,A_89] :
      ( r1_tarski(B_88,'#skF_2'(A_89,B_88))
      | v3_tex_2(B_88,A_89)
      | ~ v2_tex_2(B_88,A_89)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0(A_89)))
      | ~ l1_pre_topc(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_268,plain,
    ( r1_tarski('#skF_4','#skF_2'('#skF_3','#skF_4'))
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_266])).

tff(c_274,plain,
    ( r1_tarski('#skF_4','#skF_2'('#skF_3','#skF_4'))
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_253,c_268])).

tff(c_275,plain,(
    r1_tarski('#skF_4','#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_274])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_14,plain,(
    ! [A_8] : k2_subset_1(A_8) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_16,plain,(
    ! [A_9] : m1_subset_1(k2_subset_1(A_9),k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_59,plain,(
    ! [A_9] : m1_subset_1(A_9,k1_zfmisc_1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_16])).

tff(c_100,plain,(
    ! [C_44,B_45,A_46] :
      ( ~ v1_xboole_0(C_44)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(C_44))
      | ~ r2_hidden(A_46,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_107,plain,(
    ! [A_47,A_48] :
      ( ~ v1_xboole_0(A_47)
      | ~ r2_hidden(A_48,A_47) ) ),
    inference(resolution,[status(thm)],[c_59,c_100])).

tff(c_113,plain,(
    ! [A_49,B_50] :
      ( ~ v1_xboole_0(A_49)
      | r1_tarski(A_49,B_50) ) ),
    inference(resolution,[status(thm)],[c_6,c_107])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_116,plain,(
    ! [B_50,A_49] :
      ( B_50 = A_49
      | ~ r1_tarski(B_50,A_49)
      | ~ v1_xboole_0(A_49) ) ),
    inference(resolution,[status(thm)],[c_113,c_8])).

tff(c_297,plain,
    ( '#skF_2'('#skF_3','#skF_4') = '#skF_4'
    | ~ v1_xboole_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_275,c_116])).

tff(c_307,plain,(
    ~ v1_xboole_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_252,c_297])).

tff(c_34,plain,(
    ! [B_26,A_24] :
      ( B_26 = A_24
      | ~ r1_tarski(A_24,B_26)
      | ~ v1_zfmisc_1(B_26)
      | v1_xboole_0(B_26)
      | v1_xboole_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_294,plain,
    ( '#skF_2'('#skF_3','#skF_4') = '#skF_4'
    | ~ v1_zfmisc_1('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_275,c_34])).

tff(c_304,plain,
    ( ~ v1_zfmisc_1('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_252,c_294])).

tff(c_311,plain,(
    ~ v1_zfmisc_1('#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_307,c_304])).

tff(c_277,plain,(
    ! [A_90,B_91] :
      ( v2_tex_2('#skF_2'(A_90,B_91),A_90)
      | v3_tex_2(B_91,A_90)
      | ~ v2_tex_2(B_91,A_90)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(u1_struct_0(A_90)))
      | ~ l1_pre_topc(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_279,plain,
    ( v2_tex_2('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_277])).

tff(c_285,plain,
    ( v2_tex_2('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_253,c_279])).

tff(c_286,plain,(
    v2_tex_2('#skF_2'('#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_285])).

tff(c_491,plain,(
    ! [A_119,B_120] :
      ( m1_subset_1('#skF_2'(A_119,B_120),k1_zfmisc_1(u1_struct_0(A_119)))
      | v3_tex_2(B_120,A_119)
      | ~ v2_tex_2(B_120,A_119)
      | ~ m1_subset_1(B_120,k1_zfmisc_1(u1_struct_0(A_119)))
      | ~ l1_pre_topc(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_38,plain,(
    ! [B_29,A_27] :
      ( v1_zfmisc_1(B_29)
      | ~ v2_tex_2(B_29,A_27)
      | ~ m1_subset_1(B_29,k1_zfmisc_1(u1_struct_0(A_27)))
      | v1_xboole_0(B_29)
      | ~ l1_pre_topc(A_27)
      | ~ v2_tdlat_3(A_27)
      | ~ v2_pre_topc(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_999,plain,(
    ! [A_185,B_186] :
      ( v1_zfmisc_1('#skF_2'(A_185,B_186))
      | ~ v2_tex_2('#skF_2'(A_185,B_186),A_185)
      | v1_xboole_0('#skF_2'(A_185,B_186))
      | ~ v2_tdlat_3(A_185)
      | ~ v2_pre_topc(A_185)
      | v2_struct_0(A_185)
      | v3_tex_2(B_186,A_185)
      | ~ v2_tex_2(B_186,A_185)
      | ~ m1_subset_1(B_186,k1_zfmisc_1(u1_struct_0(A_185)))
      | ~ l1_pre_topc(A_185) ) ),
    inference(resolution,[status(thm)],[c_491,c_38])).

tff(c_1005,plain,
    ( v1_zfmisc_1('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_2'('#skF_3','#skF_4'))
    | ~ v2_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_286,c_999])).

tff(c_1012,plain,
    ( v1_zfmisc_1('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_2'('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3')
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_253,c_48,c_46,c_1005])).

tff(c_1014,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_50,c_307,c_311,c_1012])).

tff(c_1015,plain,(
    ~ v1_zfmisc_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_1016,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_1103,plain,(
    ! [B_216,A_217] :
      ( v2_tex_2(B_216,A_217)
      | ~ v3_tex_2(B_216,A_217)
      | ~ m1_subset_1(B_216,k1_zfmisc_1(u1_struct_0(A_217)))
      | ~ l1_pre_topc(A_217) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1106,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | ~ v3_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_1103])).

tff(c_1113,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1016,c_1106])).

tff(c_1216,plain,(
    ! [B_239,A_240] :
      ( v1_zfmisc_1(B_239)
      | ~ v2_tex_2(B_239,A_240)
      | ~ m1_subset_1(B_239,k1_zfmisc_1(u1_struct_0(A_240)))
      | v1_xboole_0(B_239)
      | ~ l1_pre_topc(A_240)
      | ~ v2_tdlat_3(A_240)
      | ~ v2_pre_topc(A_240)
      | v2_struct_0(A_240) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1222,plain,
    ( v1_zfmisc_1('#skF_4')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_1216])).

tff(c_1230,plain,
    ( v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_1113,c_1222])).

tff(c_1232,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_42,c_1015,c_1230])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:53:17 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.73/1.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.73/1.63  
% 3.73/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.73/1.63  %$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.73/1.63  
% 3.73/1.63  %Foreground sorts:
% 3.73/1.63  
% 3.73/1.63  
% 3.73/1.63  %Background operators:
% 3.73/1.63  
% 3.73/1.63  
% 3.73/1.63  %Foreground operators:
% 3.73/1.63  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.73/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.73/1.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.73/1.63  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.73/1.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.73/1.63  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 3.73/1.63  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.73/1.63  tff('#skF_3', type, '#skF_3': $i).
% 3.73/1.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.73/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.73/1.63  tff('#skF_4', type, '#skF_4': $i).
% 3.73/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.73/1.63  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.73/1.63  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 3.73/1.63  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.73/1.63  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.73/1.63  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.73/1.63  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.73/1.63  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.73/1.63  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 3.73/1.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.73/1.63  
% 3.73/1.65  tff(f_125, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v3_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_tex_2)).
% 3.73/1.65  tff(f_73, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 3.73/1.65  tff(f_105, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tex_2)).
% 3.73/1.65  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.73/1.65  tff(f_40, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 3.73/1.65  tff(f_42, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.73/1.65  tff(f_49, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 3.73/1.65  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.73/1.65  tff(f_86, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 3.73/1.65  tff(c_50, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.73/1.65  tff(c_42, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.73/1.65  tff(c_52, plain, (~v1_zfmisc_1('#skF_4') | ~v3_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.73/1.65  tff(c_72, plain, (~v3_tex_2('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_52])).
% 3.73/1.65  tff(c_44, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.73/1.65  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.73/1.65  tff(c_171, plain, (![A_66, B_67]: ('#skF_2'(A_66, B_67)!=B_67 | v3_tex_2(B_67, A_66) | ~v2_tex_2(B_67, A_66) | ~m1_subset_1(B_67, k1_zfmisc_1(u1_struct_0(A_66))) | ~l1_pre_topc(A_66))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.73/1.65  tff(c_174, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_40, c_171])).
% 3.73/1.65  tff(c_181, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_174])).
% 3.73/1.65  tff(c_182, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | ~v2_tex_2('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_72, c_181])).
% 3.73/1.65  tff(c_184, plain, (~v2_tex_2('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_182])).
% 3.73/1.65  tff(c_48, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.73/1.65  tff(c_46, plain, (v2_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.73/1.65  tff(c_58, plain, (v3_tex_2('#skF_4', '#skF_3') | v1_zfmisc_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.73/1.65  tff(c_73, plain, (v1_zfmisc_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_72, c_58])).
% 3.73/1.65  tff(c_239, plain, (![B_81, A_82]: (v2_tex_2(B_81, A_82) | ~v1_zfmisc_1(B_81) | ~m1_subset_1(B_81, k1_zfmisc_1(u1_struct_0(A_82))) | v1_xboole_0(B_81) | ~l1_pre_topc(A_82) | ~v2_tdlat_3(A_82) | ~v2_pre_topc(A_82) | v2_struct_0(A_82))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.73/1.65  tff(c_242, plain, (v2_tex_2('#skF_4', '#skF_3') | ~v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_40, c_239])).
% 3.73/1.65  tff(c_249, plain, (v2_tex_2('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_73, c_242])).
% 3.73/1.65  tff(c_251, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_42, c_184, c_249])).
% 3.73/1.65  tff(c_252, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4'), inference(splitRight, [status(thm)], [c_182])).
% 3.73/1.65  tff(c_253, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_182])).
% 3.73/1.65  tff(c_266, plain, (![B_88, A_89]: (r1_tarski(B_88, '#skF_2'(A_89, B_88)) | v3_tex_2(B_88, A_89) | ~v2_tex_2(B_88, A_89) | ~m1_subset_1(B_88, k1_zfmisc_1(u1_struct_0(A_89))) | ~l1_pre_topc(A_89))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.73/1.65  tff(c_268, plain, (r1_tarski('#skF_4', '#skF_2'('#skF_3', '#skF_4')) | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_40, c_266])).
% 3.73/1.65  tff(c_274, plain, (r1_tarski('#skF_4', '#skF_2'('#skF_3', '#skF_4')) | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_253, c_268])).
% 3.73/1.65  tff(c_275, plain, (r1_tarski('#skF_4', '#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_72, c_274])).
% 3.73/1.65  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.73/1.65  tff(c_14, plain, (![A_8]: (k2_subset_1(A_8)=A_8)), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.73/1.65  tff(c_16, plain, (![A_9]: (m1_subset_1(k2_subset_1(A_9), k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.73/1.65  tff(c_59, plain, (![A_9]: (m1_subset_1(A_9, k1_zfmisc_1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_16])).
% 3.73/1.65  tff(c_100, plain, (![C_44, B_45, A_46]: (~v1_xboole_0(C_44) | ~m1_subset_1(B_45, k1_zfmisc_1(C_44)) | ~r2_hidden(A_46, B_45))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.73/1.65  tff(c_107, plain, (![A_47, A_48]: (~v1_xboole_0(A_47) | ~r2_hidden(A_48, A_47))), inference(resolution, [status(thm)], [c_59, c_100])).
% 3.73/1.65  tff(c_113, plain, (![A_49, B_50]: (~v1_xboole_0(A_49) | r1_tarski(A_49, B_50))), inference(resolution, [status(thm)], [c_6, c_107])).
% 3.73/1.65  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.73/1.65  tff(c_116, plain, (![B_50, A_49]: (B_50=A_49 | ~r1_tarski(B_50, A_49) | ~v1_xboole_0(A_49))), inference(resolution, [status(thm)], [c_113, c_8])).
% 3.73/1.65  tff(c_297, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4' | ~v1_xboole_0('#skF_2'('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_275, c_116])).
% 3.73/1.65  tff(c_307, plain, (~v1_xboole_0('#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_252, c_297])).
% 3.73/1.65  tff(c_34, plain, (![B_26, A_24]: (B_26=A_24 | ~r1_tarski(A_24, B_26) | ~v1_zfmisc_1(B_26) | v1_xboole_0(B_26) | v1_xboole_0(A_24))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.73/1.65  tff(c_294, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4' | ~v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_275, c_34])).
% 3.73/1.65  tff(c_304, plain, (~v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_42, c_252, c_294])).
% 3.73/1.65  tff(c_311, plain, (~v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_307, c_304])).
% 3.73/1.65  tff(c_277, plain, (![A_90, B_91]: (v2_tex_2('#skF_2'(A_90, B_91), A_90) | v3_tex_2(B_91, A_90) | ~v2_tex_2(B_91, A_90) | ~m1_subset_1(B_91, k1_zfmisc_1(u1_struct_0(A_90))) | ~l1_pre_topc(A_90))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.73/1.65  tff(c_279, plain, (v2_tex_2('#skF_2'('#skF_3', '#skF_4'), '#skF_3') | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_40, c_277])).
% 3.73/1.65  tff(c_285, plain, (v2_tex_2('#skF_2'('#skF_3', '#skF_4'), '#skF_3') | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_253, c_279])).
% 3.73/1.65  tff(c_286, plain, (v2_tex_2('#skF_2'('#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_72, c_285])).
% 3.73/1.65  tff(c_491, plain, (![A_119, B_120]: (m1_subset_1('#skF_2'(A_119, B_120), k1_zfmisc_1(u1_struct_0(A_119))) | v3_tex_2(B_120, A_119) | ~v2_tex_2(B_120, A_119) | ~m1_subset_1(B_120, k1_zfmisc_1(u1_struct_0(A_119))) | ~l1_pre_topc(A_119))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.73/1.65  tff(c_38, plain, (![B_29, A_27]: (v1_zfmisc_1(B_29) | ~v2_tex_2(B_29, A_27) | ~m1_subset_1(B_29, k1_zfmisc_1(u1_struct_0(A_27))) | v1_xboole_0(B_29) | ~l1_pre_topc(A_27) | ~v2_tdlat_3(A_27) | ~v2_pre_topc(A_27) | v2_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.73/1.65  tff(c_999, plain, (![A_185, B_186]: (v1_zfmisc_1('#skF_2'(A_185, B_186)) | ~v2_tex_2('#skF_2'(A_185, B_186), A_185) | v1_xboole_0('#skF_2'(A_185, B_186)) | ~v2_tdlat_3(A_185) | ~v2_pre_topc(A_185) | v2_struct_0(A_185) | v3_tex_2(B_186, A_185) | ~v2_tex_2(B_186, A_185) | ~m1_subset_1(B_186, k1_zfmisc_1(u1_struct_0(A_185))) | ~l1_pre_topc(A_185))), inference(resolution, [status(thm)], [c_491, c_38])).
% 3.73/1.65  tff(c_1005, plain, (v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_2'('#skF_3', '#skF_4')) | ~v2_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_286, c_999])).
% 3.73/1.65  tff(c_1012, plain, (v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_2'('#skF_3', '#skF_4')) | v2_struct_0('#skF_3') | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_253, c_48, c_46, c_1005])).
% 3.73/1.65  tff(c_1014, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_50, c_307, c_311, c_1012])).
% 3.73/1.65  tff(c_1015, plain, (~v1_zfmisc_1('#skF_4')), inference(splitRight, [status(thm)], [c_52])).
% 3.73/1.65  tff(c_1016, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_52])).
% 3.73/1.65  tff(c_1103, plain, (![B_216, A_217]: (v2_tex_2(B_216, A_217) | ~v3_tex_2(B_216, A_217) | ~m1_subset_1(B_216, k1_zfmisc_1(u1_struct_0(A_217))) | ~l1_pre_topc(A_217))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.73/1.65  tff(c_1106, plain, (v2_tex_2('#skF_4', '#skF_3') | ~v3_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_40, c_1103])).
% 3.73/1.65  tff(c_1113, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_1016, c_1106])).
% 3.73/1.65  tff(c_1216, plain, (![B_239, A_240]: (v1_zfmisc_1(B_239) | ~v2_tex_2(B_239, A_240) | ~m1_subset_1(B_239, k1_zfmisc_1(u1_struct_0(A_240))) | v1_xboole_0(B_239) | ~l1_pre_topc(A_240) | ~v2_tdlat_3(A_240) | ~v2_pre_topc(A_240) | v2_struct_0(A_240))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.73/1.65  tff(c_1222, plain, (v1_zfmisc_1('#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_40, c_1216])).
% 3.73/1.65  tff(c_1230, plain, (v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_1113, c_1222])).
% 3.73/1.65  tff(c_1232, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_42, c_1015, c_1230])).
% 3.73/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.73/1.65  
% 3.73/1.65  Inference rules
% 3.73/1.65  ----------------------
% 3.73/1.65  #Ref     : 0
% 3.73/1.65  #Sup     : 247
% 3.73/1.65  #Fact    : 0
% 3.73/1.65  #Define  : 0
% 3.73/1.65  #Split   : 11
% 3.73/1.65  #Chain   : 0
% 3.73/1.65  #Close   : 0
% 3.73/1.65  
% 3.73/1.65  Ordering : KBO
% 3.73/1.65  
% 3.73/1.65  Simplification rules
% 3.73/1.65  ----------------------
% 3.73/1.65  #Subsume      : 76
% 3.73/1.65  #Demod        : 99
% 3.73/1.65  #Tautology    : 33
% 3.73/1.65  #SimpNegUnit  : 32
% 3.73/1.65  #BackRed      : 0
% 3.73/1.65  
% 3.73/1.65  #Partial instantiations: 0
% 3.73/1.65  #Strategies tried      : 1
% 3.73/1.65  
% 3.73/1.65  Timing (in seconds)
% 3.73/1.65  ----------------------
% 3.73/1.65  Preprocessing        : 0.31
% 3.73/1.65  Parsing              : 0.18
% 3.73/1.65  CNF conversion       : 0.02
% 3.73/1.65  Main loop            : 0.54
% 3.73/1.65  Inferencing          : 0.19
% 3.73/1.65  Reduction            : 0.14
% 3.73/1.65  Demodulation         : 0.09
% 3.73/1.65  BG Simplification    : 0.02
% 3.73/1.65  Subsumption          : 0.15
% 3.73/1.65  Abstraction          : 0.02
% 3.73/1.65  MUC search           : 0.00
% 3.73/1.65  Cooper               : 0.00
% 3.73/1.65  Total                : 0.88
% 3.73/1.65  Index Insertion      : 0.00
% 3.73/1.65  Index Deletion       : 0.00
% 3.73/1.65  Index Matching       : 0.00
% 3.73/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
