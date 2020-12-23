%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:16 EST 2020

% Result     : Theorem 3.00s
% Output     : CNFRefutation 3.18s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 387 expanded)
%              Number of leaves         :   32 ( 143 expanded)
%              Depth                    :   12
%              Number of atoms          :  215 (1455 expanded)
%              Number of equality atoms :   21 (  87 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_pre_topc > k6_subset_1 > k4_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

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

tff(f_138,negated_conjecture,(
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

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_zfmisc_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_zfmisc_1)).

tff(f_78,axiom,(
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

tff(f_118,axiom,(
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

tff(f_99,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_54,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_31,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_86,axiom,(
    ! [A,B] :
      ~ ( r1_tarski(A,B)
        & A != B
        & k6_subset_1(B,A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l48_tex_2)).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_38,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_54,plain,
    ( v3_tex_2('#skF_4','#skF_3')
    | v1_zfmisc_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_56,plain,(
    v1_zfmisc_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_48,plain,
    ( ~ v1_zfmisc_1('#skF_4')
    | ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_58,plain,(
    ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_48])).

tff(c_2,plain,(
    ! [A_1] :
      ( v1_zfmisc_1(A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_40,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_107,plain,(
    ! [A_66,B_67] :
      ( '#skF_2'(A_66,B_67) != B_67
      | v3_tex_2(B_67,A_66)
      | ~ v2_tex_2(B_67,A_66)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ l1_pre_topc(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_114,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_107])).

tff(c_118,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_114])).

tff(c_119,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_118])).

tff(c_120,plain,(
    ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_119])).

tff(c_44,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_42,plain,(
    v2_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_157,plain,(
    ! [B_76,A_77] :
      ( v2_tex_2(B_76,A_77)
      | ~ v1_zfmisc_1(B_76)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(u1_struct_0(A_77)))
      | v1_xboole_0(B_76)
      | ~ l1_pre_topc(A_77)
      | ~ v2_tdlat_3(A_77)
      | ~ v2_pre_topc(A_77)
      | v2_struct_0(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_164,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | ~ v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_157])).

tff(c_168,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_56,c_164])).

tff(c_170,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_38,c_120,c_168])).

tff(c_171,plain,(
    '#skF_2'('#skF_3','#skF_4') != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_119])).

tff(c_172,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_119])).

tff(c_173,plain,(
    ! [B_78,A_79] :
      ( r1_tarski(B_78,'#skF_2'(A_79,B_78))
      | v3_tex_2(B_78,A_79)
      | ~ v2_tex_2(B_78,A_79)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ l1_pre_topc(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_178,plain,
    ( r1_tarski('#skF_4','#skF_2'('#skF_3','#skF_4'))
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_173])).

tff(c_182,plain,
    ( r1_tarski('#skF_4','#skF_2'('#skF_3','#skF_4'))
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_172,c_178])).

tff(c_183,plain,(
    r1_tarski('#skF_4','#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_182])).

tff(c_30,plain,(
    ! [B_32,A_30] :
      ( B_32 = A_30
      | ~ r1_tarski(A_30,B_32)
      | ~ v1_zfmisc_1(B_32)
      | v1_xboole_0(B_32)
      | v1_xboole_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_186,plain,
    ( '#skF_2'('#skF_3','#skF_4') = '#skF_4'
    | ~ v1_zfmisc_1('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_183,c_30])).

tff(c_192,plain,
    ( ~ v1_zfmisc_1('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_171,c_186])).

tff(c_196,plain,(
    ~ v1_zfmisc_1('#skF_2'('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_192])).

tff(c_200,plain,(
    ~ v1_xboole_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_2,c_196])).

tff(c_202,plain,(
    ! [A_82,B_83] :
      ( v2_tex_2('#skF_2'(A_82,B_83),A_82)
      | v3_tex_2(B_83,A_82)
      | ~ v2_tex_2(B_83,A_82)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ l1_pre_topc(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_207,plain,
    ( v2_tex_2('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_202])).

tff(c_211,plain,
    ( v2_tex_2('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_172,c_207])).

tff(c_212,plain,(
    v2_tex_2('#skF_2'('#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_211])).

tff(c_239,plain,(
    ! [A_88,B_89] :
      ( m1_subset_1('#skF_2'(A_88,B_89),k1_zfmisc_1(u1_struct_0(A_88)))
      | v3_tex_2(B_89,A_88)
      | ~ v2_tex_2(B_89,A_88)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ l1_pre_topc(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_34,plain,(
    ! [B_35,A_33] :
      ( v1_zfmisc_1(B_35)
      | ~ v2_tex_2(B_35,A_33)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(u1_struct_0(A_33)))
      | v1_xboole_0(B_35)
      | ~ l1_pre_topc(A_33)
      | ~ v2_tdlat_3(A_33)
      | ~ v2_pre_topc(A_33)
      | v2_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_359,plain,(
    ! [A_117,B_118] :
      ( v1_zfmisc_1('#skF_2'(A_117,B_118))
      | ~ v2_tex_2('#skF_2'(A_117,B_118),A_117)
      | v1_xboole_0('#skF_2'(A_117,B_118))
      | ~ v2_tdlat_3(A_117)
      | ~ v2_pre_topc(A_117)
      | v2_struct_0(A_117)
      | v3_tex_2(B_118,A_117)
      | ~ v2_tex_2(B_118,A_117)
      | ~ m1_subset_1(B_118,k1_zfmisc_1(u1_struct_0(A_117)))
      | ~ l1_pre_topc(A_117) ) ),
    inference(resolution,[status(thm)],[c_239,c_34])).

tff(c_365,plain,
    ( v1_zfmisc_1('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_2'('#skF_3','#skF_4'))
    | ~ v2_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_212,c_359])).

tff(c_372,plain,
    ( v1_zfmisc_1('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_2'('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3')
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_172,c_44,c_42,c_365])).

tff(c_374,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_46,c_200,c_196,c_372])).

tff(c_375,plain,(
    v1_xboole_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_192])).

tff(c_8,plain,(
    ! [A_7] :
      ( r2_hidden('#skF_1'(A_7),A_7)
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_4,plain,(
    ! [A_2,B_3] : m1_subset_1(k6_subset_1(A_2,B_3),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_69,plain,(
    ! [C_44,B_45,A_46] :
      ( ~ v1_xboole_0(C_44)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(C_44))
      | ~ r2_hidden(A_46,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_81,plain,(
    ! [A_50,A_51,B_52] :
      ( ~ v1_xboole_0(A_50)
      | ~ r2_hidden(A_51,k6_subset_1(A_50,B_52)) ) ),
    inference(resolution,[status(thm)],[c_4,c_69])).

tff(c_86,plain,(
    ! [A_50,B_52] :
      ( ~ v1_xboole_0(A_50)
      | k6_subset_1(A_50,B_52) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_81])).

tff(c_379,plain,(
    ! [B_52] : k6_subset_1('#skF_2'('#skF_3','#skF_4'),B_52) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_375,c_86])).

tff(c_28,plain,(
    ! [B_29,A_28] :
      ( k6_subset_1(B_29,A_28) != k1_xboole_0
      | B_29 = A_28
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_189,plain,
    ( k6_subset_1('#skF_2'('#skF_3','#skF_4'),'#skF_4') != k1_xboole_0
    | '#skF_2'('#skF_3','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_183,c_28])).

tff(c_195,plain,(
    k6_subset_1('#skF_2'('#skF_3','#skF_4'),'#skF_4') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_171,c_189])).

tff(c_393,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_379,c_195])).

tff(c_395,plain,(
    ~ v1_zfmisc_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_394,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_436,plain,(
    ! [B_147,A_148] :
      ( v2_tex_2(B_147,A_148)
      | ~ v3_tex_2(B_147,A_148)
      | ~ m1_subset_1(B_147,k1_zfmisc_1(u1_struct_0(A_148)))
      | ~ l1_pre_topc(A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_443,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | ~ v3_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_436])).

tff(c_447,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_394,c_443])).

tff(c_499,plain,(
    ! [B_159,A_160] :
      ( v1_zfmisc_1(B_159)
      | ~ v2_tex_2(B_159,A_160)
      | ~ m1_subset_1(B_159,k1_zfmisc_1(u1_struct_0(A_160)))
      | v1_xboole_0(B_159)
      | ~ l1_pre_topc(A_160)
      | ~ v2_tdlat_3(A_160)
      | ~ v2_pre_topc(A_160)
      | v2_struct_0(A_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_509,plain,
    ( v1_zfmisc_1('#skF_4')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_499])).

tff(c_514,plain,
    ( v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_447,c_509])).

tff(c_516,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_38,c_395,c_514])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:02:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.00/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.00/1.51  
% 3.00/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.00/1.51  %$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_pre_topc > k6_subset_1 > k4_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 3.00/1.51  
% 3.00/1.51  %Foreground sorts:
% 3.00/1.51  
% 3.00/1.51  
% 3.00/1.51  %Background operators:
% 3.00/1.51  
% 3.00/1.51  
% 3.00/1.51  %Foreground operators:
% 3.00/1.51  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.00/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.00/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.00/1.51  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.00/1.51  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.00/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.00/1.51  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.00/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.00/1.51  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 3.00/1.51  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.00/1.51  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 3.00/1.51  tff('#skF_3', type, '#skF_3': $i).
% 3.00/1.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.00/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.00/1.51  tff('#skF_4', type, '#skF_4': $i).
% 3.00/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.00/1.51  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.00/1.51  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 3.00/1.51  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.00/1.51  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.00/1.51  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.00/1.51  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 3.00/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.00/1.51  
% 3.18/1.53  tff(f_138, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v3_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_tex_2)).
% 3.18/1.53  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => v1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_zfmisc_1)).
% 3.18/1.53  tff(f_78, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_tex_2)).
% 3.18/1.53  tff(f_118, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tex_2)).
% 3.18/1.53  tff(f_99, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 3.18/1.53  tff(f_54, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_mcart_1)).
% 3.18/1.53  tff(f_31, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 3.18/1.53  tff(f_38, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 3.18/1.53  tff(f_86, axiom, (![A, B]: ~((r1_tarski(A, B) & ~(A = B)) & (k6_subset_1(B, A) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l48_tex_2)).
% 3.18/1.53  tff(c_46, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.18/1.53  tff(c_38, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.18/1.53  tff(c_54, plain, (v3_tex_2('#skF_4', '#skF_3') | v1_zfmisc_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.18/1.53  tff(c_56, plain, (v1_zfmisc_1('#skF_4')), inference(splitLeft, [status(thm)], [c_54])).
% 3.18/1.53  tff(c_48, plain, (~v1_zfmisc_1('#skF_4') | ~v3_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.18/1.53  tff(c_58, plain, (~v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_48])).
% 3.18/1.53  tff(c_2, plain, (![A_1]: (v1_zfmisc_1(A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.18/1.53  tff(c_40, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.18/1.53  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.18/1.53  tff(c_107, plain, (![A_66, B_67]: ('#skF_2'(A_66, B_67)!=B_67 | v3_tex_2(B_67, A_66) | ~v2_tex_2(B_67, A_66) | ~m1_subset_1(B_67, k1_zfmisc_1(u1_struct_0(A_66))) | ~l1_pre_topc(A_66))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.18/1.53  tff(c_114, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_36, c_107])).
% 3.18/1.53  tff(c_118, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_114])).
% 3.18/1.53  tff(c_119, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | ~v2_tex_2('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_58, c_118])).
% 3.18/1.53  tff(c_120, plain, (~v2_tex_2('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_119])).
% 3.18/1.53  tff(c_44, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.18/1.53  tff(c_42, plain, (v2_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.18/1.53  tff(c_157, plain, (![B_76, A_77]: (v2_tex_2(B_76, A_77) | ~v1_zfmisc_1(B_76) | ~m1_subset_1(B_76, k1_zfmisc_1(u1_struct_0(A_77))) | v1_xboole_0(B_76) | ~l1_pre_topc(A_77) | ~v2_tdlat_3(A_77) | ~v2_pre_topc(A_77) | v2_struct_0(A_77))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.18/1.53  tff(c_164, plain, (v2_tex_2('#skF_4', '#skF_3') | ~v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_36, c_157])).
% 3.18/1.53  tff(c_168, plain, (v2_tex_2('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_56, c_164])).
% 3.18/1.53  tff(c_170, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_38, c_120, c_168])).
% 3.18/1.53  tff(c_171, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4'), inference(splitRight, [status(thm)], [c_119])).
% 3.18/1.53  tff(c_172, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_119])).
% 3.18/1.53  tff(c_173, plain, (![B_78, A_79]: (r1_tarski(B_78, '#skF_2'(A_79, B_78)) | v3_tex_2(B_78, A_79) | ~v2_tex_2(B_78, A_79) | ~m1_subset_1(B_78, k1_zfmisc_1(u1_struct_0(A_79))) | ~l1_pre_topc(A_79))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.18/1.53  tff(c_178, plain, (r1_tarski('#skF_4', '#skF_2'('#skF_3', '#skF_4')) | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_36, c_173])).
% 3.18/1.53  tff(c_182, plain, (r1_tarski('#skF_4', '#skF_2'('#skF_3', '#skF_4')) | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_172, c_178])).
% 3.18/1.53  tff(c_183, plain, (r1_tarski('#skF_4', '#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_58, c_182])).
% 3.18/1.53  tff(c_30, plain, (![B_32, A_30]: (B_32=A_30 | ~r1_tarski(A_30, B_32) | ~v1_zfmisc_1(B_32) | v1_xboole_0(B_32) | v1_xboole_0(A_30))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.18/1.53  tff(c_186, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4' | ~v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_183, c_30])).
% 3.18/1.53  tff(c_192, plain, (~v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_38, c_171, c_186])).
% 3.18/1.53  tff(c_196, plain, (~v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_192])).
% 3.18/1.53  tff(c_200, plain, (~v1_xboole_0('#skF_2'('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_2, c_196])).
% 3.18/1.53  tff(c_202, plain, (![A_82, B_83]: (v2_tex_2('#skF_2'(A_82, B_83), A_82) | v3_tex_2(B_83, A_82) | ~v2_tex_2(B_83, A_82) | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0(A_82))) | ~l1_pre_topc(A_82))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.18/1.53  tff(c_207, plain, (v2_tex_2('#skF_2'('#skF_3', '#skF_4'), '#skF_3') | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_36, c_202])).
% 3.18/1.53  tff(c_211, plain, (v2_tex_2('#skF_2'('#skF_3', '#skF_4'), '#skF_3') | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_172, c_207])).
% 3.18/1.53  tff(c_212, plain, (v2_tex_2('#skF_2'('#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_58, c_211])).
% 3.18/1.53  tff(c_239, plain, (![A_88, B_89]: (m1_subset_1('#skF_2'(A_88, B_89), k1_zfmisc_1(u1_struct_0(A_88))) | v3_tex_2(B_89, A_88) | ~v2_tex_2(B_89, A_88) | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0(A_88))) | ~l1_pre_topc(A_88))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.18/1.53  tff(c_34, plain, (![B_35, A_33]: (v1_zfmisc_1(B_35) | ~v2_tex_2(B_35, A_33) | ~m1_subset_1(B_35, k1_zfmisc_1(u1_struct_0(A_33))) | v1_xboole_0(B_35) | ~l1_pre_topc(A_33) | ~v2_tdlat_3(A_33) | ~v2_pre_topc(A_33) | v2_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.18/1.53  tff(c_359, plain, (![A_117, B_118]: (v1_zfmisc_1('#skF_2'(A_117, B_118)) | ~v2_tex_2('#skF_2'(A_117, B_118), A_117) | v1_xboole_0('#skF_2'(A_117, B_118)) | ~v2_tdlat_3(A_117) | ~v2_pre_topc(A_117) | v2_struct_0(A_117) | v3_tex_2(B_118, A_117) | ~v2_tex_2(B_118, A_117) | ~m1_subset_1(B_118, k1_zfmisc_1(u1_struct_0(A_117))) | ~l1_pre_topc(A_117))), inference(resolution, [status(thm)], [c_239, c_34])).
% 3.18/1.53  tff(c_365, plain, (v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_2'('#skF_3', '#skF_4')) | ~v2_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_212, c_359])).
% 3.18/1.53  tff(c_372, plain, (v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_2'('#skF_3', '#skF_4')) | v2_struct_0('#skF_3') | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_172, c_44, c_42, c_365])).
% 3.18/1.53  tff(c_374, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_46, c_200, c_196, c_372])).
% 3.18/1.53  tff(c_375, plain, (v1_xboole_0('#skF_2'('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_192])).
% 3.18/1.53  tff(c_8, plain, (![A_7]: (r2_hidden('#skF_1'(A_7), A_7) | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.18/1.53  tff(c_4, plain, (![A_2, B_3]: (m1_subset_1(k6_subset_1(A_2, B_3), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.18/1.53  tff(c_69, plain, (![C_44, B_45, A_46]: (~v1_xboole_0(C_44) | ~m1_subset_1(B_45, k1_zfmisc_1(C_44)) | ~r2_hidden(A_46, B_45))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.18/1.53  tff(c_81, plain, (![A_50, A_51, B_52]: (~v1_xboole_0(A_50) | ~r2_hidden(A_51, k6_subset_1(A_50, B_52)))), inference(resolution, [status(thm)], [c_4, c_69])).
% 3.18/1.53  tff(c_86, plain, (![A_50, B_52]: (~v1_xboole_0(A_50) | k6_subset_1(A_50, B_52)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_81])).
% 3.18/1.53  tff(c_379, plain, (![B_52]: (k6_subset_1('#skF_2'('#skF_3', '#skF_4'), B_52)=k1_xboole_0)), inference(resolution, [status(thm)], [c_375, c_86])).
% 3.18/1.53  tff(c_28, plain, (![B_29, A_28]: (k6_subset_1(B_29, A_28)!=k1_xboole_0 | B_29=A_28 | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.18/1.53  tff(c_189, plain, (k6_subset_1('#skF_2'('#skF_3', '#skF_4'), '#skF_4')!=k1_xboole_0 | '#skF_2'('#skF_3', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_183, c_28])).
% 3.18/1.53  tff(c_195, plain, (k6_subset_1('#skF_2'('#skF_3', '#skF_4'), '#skF_4')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_171, c_189])).
% 3.18/1.53  tff(c_393, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_379, c_195])).
% 3.18/1.53  tff(c_395, plain, (~v1_zfmisc_1('#skF_4')), inference(splitRight, [status(thm)], [c_54])).
% 3.18/1.53  tff(c_394, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_54])).
% 3.18/1.53  tff(c_436, plain, (![B_147, A_148]: (v2_tex_2(B_147, A_148) | ~v3_tex_2(B_147, A_148) | ~m1_subset_1(B_147, k1_zfmisc_1(u1_struct_0(A_148))) | ~l1_pre_topc(A_148))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.18/1.53  tff(c_443, plain, (v2_tex_2('#skF_4', '#skF_3') | ~v3_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_36, c_436])).
% 3.18/1.53  tff(c_447, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_394, c_443])).
% 3.18/1.53  tff(c_499, plain, (![B_159, A_160]: (v1_zfmisc_1(B_159) | ~v2_tex_2(B_159, A_160) | ~m1_subset_1(B_159, k1_zfmisc_1(u1_struct_0(A_160))) | v1_xboole_0(B_159) | ~l1_pre_topc(A_160) | ~v2_tdlat_3(A_160) | ~v2_pre_topc(A_160) | v2_struct_0(A_160))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.18/1.53  tff(c_509, plain, (v1_zfmisc_1('#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_36, c_499])).
% 3.18/1.53  tff(c_514, plain, (v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_447, c_509])).
% 3.18/1.53  tff(c_516, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_38, c_395, c_514])).
% 3.18/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.18/1.53  
% 3.18/1.53  Inference rules
% 3.18/1.53  ----------------------
% 3.18/1.53  #Ref     : 0
% 3.18/1.53  #Sup     : 83
% 3.18/1.53  #Fact    : 0
% 3.18/1.53  #Define  : 0
% 3.18/1.53  #Split   : 6
% 3.18/1.54  #Chain   : 0
% 3.18/1.54  #Close   : 0
% 3.18/1.54  
% 3.18/1.54  Ordering : KBO
% 3.18/1.54  
% 3.18/1.54  Simplification rules
% 3.18/1.54  ----------------------
% 3.18/1.54  #Subsume      : 11
% 3.18/1.54  #Demod        : 64
% 3.18/1.54  #Tautology    : 12
% 3.18/1.54  #SimpNegUnit  : 18
% 3.18/1.54  #BackRed      : 1
% 3.18/1.54  
% 3.18/1.54  #Partial instantiations: 0
% 3.18/1.54  #Strategies tried      : 1
% 3.18/1.54  
% 3.18/1.54  Timing (in seconds)
% 3.18/1.54  ----------------------
% 3.18/1.54  Preprocessing        : 0.33
% 3.18/1.54  Parsing              : 0.19
% 3.18/1.54  CNF conversion       : 0.02
% 3.18/1.54  Main loop            : 0.40
% 3.18/1.54  Inferencing          : 0.16
% 3.18/1.54  Reduction            : 0.11
% 3.18/1.54  Demodulation         : 0.07
% 3.18/1.54  BG Simplification    : 0.02
% 3.18/1.54  Subsumption          : 0.08
% 3.18/1.54  Abstraction          : 0.02
% 3.18/1.54  MUC search           : 0.00
% 3.18/1.54  Cooper               : 0.00
% 3.18/1.54  Total                : 0.77
% 3.18/1.54  Index Insertion      : 0.00
% 3.18/1.54  Index Deletion       : 0.00
% 3.18/1.54  Index Matching       : 0.00
% 3.18/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
