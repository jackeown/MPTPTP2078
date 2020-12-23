%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:17 EST 2020

% Result     : Theorem 5.57s
% Output     : CNFRefutation 5.57s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 338 expanded)
%              Number of leaves         :   28 ( 126 expanded)
%              Depth                    :   11
%              Number of atoms          :  215 (1260 expanded)
%              Number of equality atoms :   13 (  67 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_tex_2)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tex_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_86,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_42,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_58,plain,
    ( v3_tex_2('#skF_4','#skF_3')
    | v1_zfmisc_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_61,plain,(
    v1_zfmisc_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_52,plain,
    ( ~ v1_zfmisc_1('#skF_4')
    | ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_63,plain,(
    ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_52])).

tff(c_44,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_217,plain,(
    ! [A_74,B_75] :
      ( '#skF_2'(A_74,B_75) != B_75
      | v3_tex_2(B_75,A_74)
      | ~ v2_tex_2(B_75,A_74)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ l1_pre_topc(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_224,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_217])).

tff(c_228,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_224])).

tff(c_229,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_228])).

tff(c_230,plain,(
    ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_229])).

tff(c_48,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_46,plain,(
    v2_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_776,plain,(
    ! [B_135,A_136] :
      ( v2_tex_2(B_135,A_136)
      | ~ v1_zfmisc_1(B_135)
      | ~ m1_subset_1(B_135,k1_zfmisc_1(u1_struct_0(A_136)))
      | v1_xboole_0(B_135)
      | ~ l1_pre_topc(A_136)
      | ~ v2_tdlat_3(A_136)
      | ~ v2_pre_topc(A_136)
      | v2_struct_0(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_786,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | ~ v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_776])).

tff(c_791,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_61,c_786])).

tff(c_793,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_42,c_230,c_791])).

tff(c_794,plain,(
    '#skF_2'('#skF_3','#skF_4') != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_229])).

tff(c_795,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_229])).

tff(c_797,plain,(
    ! [B_138,A_139] :
      ( r1_tarski(B_138,'#skF_2'(A_139,B_138))
      | v3_tex_2(B_138,A_139)
      | ~ v2_tex_2(B_138,A_139)
      | ~ m1_subset_1(B_138,k1_zfmisc_1(u1_struct_0(A_139)))
      | ~ l1_pre_topc(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_802,plain,
    ( r1_tarski('#skF_4','#skF_2'('#skF_3','#skF_4'))
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_797])).

tff(c_806,plain,
    ( r1_tarski('#skF_4','#skF_2'('#skF_3','#skF_4'))
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_795,c_802])).

tff(c_807,plain,(
    r1_tarski('#skF_4','#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_806])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_100,plain,(
    ! [C_43,B_44,A_45] :
      ( ~ v1_xboole_0(C_43)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(C_43))
      | ~ r2_hidden(A_45,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_108,plain,(
    ! [B_46,A_47,A_48] :
      ( ~ v1_xboole_0(B_46)
      | ~ r2_hidden(A_47,A_48)
      | ~ r1_tarski(A_48,B_46) ) ),
    inference(resolution,[status(thm)],[c_16,c_100])).

tff(c_112,plain,(
    ! [B_49,A_50,B_51] :
      ( ~ v1_xboole_0(B_49)
      | ~ r1_tarski(A_50,B_49)
      | r1_tarski(A_50,B_51) ) ),
    inference(resolution,[status(thm)],[c_6,c_108])).

tff(c_119,plain,(
    ! [B_52,B_53] :
      ( ~ v1_xboole_0(B_52)
      | r1_tarski(B_52,B_53) ) ),
    inference(resolution,[status(thm)],[c_12,c_112])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_129,plain,(
    ! [B_53,B_52] :
      ( B_53 = B_52
      | ~ r1_tarski(B_53,B_52)
      | ~ v1_xboole_0(B_52) ) ),
    inference(resolution,[status(thm)],[c_119,c_8])).

tff(c_815,plain,
    ( '#skF_2'('#skF_3','#skF_4') = '#skF_4'
    | ~ v1_xboole_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_807,c_129])).

tff(c_826,plain,(
    ~ v1_xboole_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_794,c_815])).

tff(c_34,plain,(
    ! [B_26,A_24] :
      ( B_26 = A_24
      | ~ r1_tarski(A_24,B_26)
      | ~ v1_zfmisc_1(B_26)
      | v1_xboole_0(B_26)
      | v1_xboole_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_812,plain,
    ( '#skF_2'('#skF_3','#skF_4') = '#skF_4'
    | ~ v1_zfmisc_1('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_807,c_34])).

tff(c_823,plain,
    ( ~ v1_zfmisc_1('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_794,c_812])).

tff(c_835,plain,(
    ~ v1_zfmisc_1('#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_826,c_823])).

tff(c_836,plain,(
    ! [A_140,B_141] :
      ( v2_tex_2('#skF_2'(A_140,B_141),A_140)
      | v3_tex_2(B_141,A_140)
      | ~ v2_tex_2(B_141,A_140)
      | ~ m1_subset_1(B_141,k1_zfmisc_1(u1_struct_0(A_140)))
      | ~ l1_pre_topc(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_841,plain,
    ( v2_tex_2('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_836])).

tff(c_845,plain,
    ( v2_tex_2('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_795,c_841])).

tff(c_846,plain,(
    v2_tex_2('#skF_2'('#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_845])).

tff(c_931,plain,(
    ! [A_155,B_156] :
      ( m1_subset_1('#skF_2'(A_155,B_156),k1_zfmisc_1(u1_struct_0(A_155)))
      | v3_tex_2(B_156,A_155)
      | ~ v2_tex_2(B_156,A_155)
      | ~ m1_subset_1(B_156,k1_zfmisc_1(u1_struct_0(A_155)))
      | ~ l1_pre_topc(A_155) ) ),
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

tff(c_2456,plain,(
    ! [A_283,B_284] :
      ( v1_zfmisc_1('#skF_2'(A_283,B_284))
      | ~ v2_tex_2('#skF_2'(A_283,B_284),A_283)
      | v1_xboole_0('#skF_2'(A_283,B_284))
      | ~ v2_tdlat_3(A_283)
      | ~ v2_pre_topc(A_283)
      | v2_struct_0(A_283)
      | v3_tex_2(B_284,A_283)
      | ~ v2_tex_2(B_284,A_283)
      | ~ m1_subset_1(B_284,k1_zfmisc_1(u1_struct_0(A_283)))
      | ~ l1_pre_topc(A_283) ) ),
    inference(resolution,[status(thm)],[c_931,c_38])).

tff(c_2465,plain,
    ( v1_zfmisc_1('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_2'('#skF_3','#skF_4'))
    | ~ v2_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_846,c_2456])).

tff(c_2474,plain,
    ( v1_zfmisc_1('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_2'('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3')
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_795,c_48,c_46,c_2465])).

tff(c_2476,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_50,c_826,c_835,c_2474])).

tff(c_2478,plain,(
    ~ v1_zfmisc_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_2477,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_2605,plain,(
    ! [B_323,A_324] :
      ( v2_tex_2(B_323,A_324)
      | ~ v3_tex_2(B_323,A_324)
      | ~ m1_subset_1(B_323,k1_zfmisc_1(u1_struct_0(A_324)))
      | ~ l1_pre_topc(A_324) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2612,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | ~ v3_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_2605])).

tff(c_2616,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_2477,c_2612])).

tff(c_3193,plain,(
    ! [B_389,A_390] :
      ( v1_zfmisc_1(B_389)
      | ~ v2_tex_2(B_389,A_390)
      | ~ m1_subset_1(B_389,k1_zfmisc_1(u1_struct_0(A_390)))
      | v1_xboole_0(B_389)
      | ~ l1_pre_topc(A_390)
      | ~ v2_tdlat_3(A_390)
      | ~ v2_pre_topc(A_390)
      | v2_struct_0(A_390) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_3203,plain,
    ( v1_zfmisc_1('#skF_4')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_3193])).

tff(c_3208,plain,
    ( v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_2616,c_3203])).

tff(c_3210,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_42,c_2478,c_3208])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:16:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.57/2.08  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.57/2.08  
% 5.57/2.08  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.57/2.09  %$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 5.57/2.09  
% 5.57/2.09  %Foreground sorts:
% 5.57/2.09  
% 5.57/2.09  
% 5.57/2.09  %Background operators:
% 5.57/2.09  
% 5.57/2.09  
% 5.57/2.09  %Foreground operators:
% 5.57/2.09  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.57/2.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.57/2.09  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.57/2.09  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.57/2.09  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.57/2.09  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 5.57/2.09  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 5.57/2.09  tff('#skF_3', type, '#skF_3': $i).
% 5.57/2.09  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.57/2.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.57/2.09  tff('#skF_4', type, '#skF_4': $i).
% 5.57/2.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.57/2.09  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.57/2.09  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 5.57/2.09  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.57/2.09  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.57/2.09  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.57/2.09  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.57/2.09  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 5.57/2.09  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.57/2.09  
% 5.57/2.10  tff(f_125, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v3_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_tex_2)).
% 5.57/2.10  tff(f_73, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_tex_2)).
% 5.57/2.10  tff(f_105, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tex_2)).
% 5.57/2.10  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.57/2.10  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.57/2.10  tff(f_42, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.57/2.10  tff(f_49, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 5.57/2.10  tff(f_86, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 5.57/2.10  tff(c_50, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.57/2.10  tff(c_42, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.57/2.10  tff(c_58, plain, (v3_tex_2('#skF_4', '#skF_3') | v1_zfmisc_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.57/2.10  tff(c_61, plain, (v1_zfmisc_1('#skF_4')), inference(splitLeft, [status(thm)], [c_58])).
% 5.57/2.10  tff(c_52, plain, (~v1_zfmisc_1('#skF_4') | ~v3_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.57/2.10  tff(c_63, plain, (~v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_61, c_52])).
% 5.57/2.10  tff(c_44, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.57/2.10  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.57/2.10  tff(c_217, plain, (![A_74, B_75]: ('#skF_2'(A_74, B_75)!=B_75 | v3_tex_2(B_75, A_74) | ~v2_tex_2(B_75, A_74) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0(A_74))) | ~l1_pre_topc(A_74))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.57/2.10  tff(c_224, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_40, c_217])).
% 5.57/2.10  tff(c_228, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_224])).
% 5.57/2.10  tff(c_229, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | ~v2_tex_2('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_63, c_228])).
% 5.57/2.10  tff(c_230, plain, (~v2_tex_2('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_229])).
% 5.57/2.10  tff(c_48, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.57/2.10  tff(c_46, plain, (v2_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.57/2.10  tff(c_776, plain, (![B_135, A_136]: (v2_tex_2(B_135, A_136) | ~v1_zfmisc_1(B_135) | ~m1_subset_1(B_135, k1_zfmisc_1(u1_struct_0(A_136))) | v1_xboole_0(B_135) | ~l1_pre_topc(A_136) | ~v2_tdlat_3(A_136) | ~v2_pre_topc(A_136) | v2_struct_0(A_136))), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.57/2.10  tff(c_786, plain, (v2_tex_2('#skF_4', '#skF_3') | ~v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_40, c_776])).
% 5.57/2.10  tff(c_791, plain, (v2_tex_2('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_61, c_786])).
% 5.57/2.10  tff(c_793, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_42, c_230, c_791])).
% 5.57/2.10  tff(c_794, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4'), inference(splitRight, [status(thm)], [c_229])).
% 5.57/2.10  tff(c_795, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_229])).
% 5.57/2.10  tff(c_797, plain, (![B_138, A_139]: (r1_tarski(B_138, '#skF_2'(A_139, B_138)) | v3_tex_2(B_138, A_139) | ~v2_tex_2(B_138, A_139) | ~m1_subset_1(B_138, k1_zfmisc_1(u1_struct_0(A_139))) | ~l1_pre_topc(A_139))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.57/2.10  tff(c_802, plain, (r1_tarski('#skF_4', '#skF_2'('#skF_3', '#skF_4')) | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_40, c_797])).
% 5.57/2.10  tff(c_806, plain, (r1_tarski('#skF_4', '#skF_2'('#skF_3', '#skF_4')) | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_795, c_802])).
% 5.57/2.10  tff(c_807, plain, (r1_tarski('#skF_4', '#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_63, c_806])).
% 5.57/2.10  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.57/2.10  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.57/2.10  tff(c_16, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.57/2.10  tff(c_100, plain, (![C_43, B_44, A_45]: (~v1_xboole_0(C_43) | ~m1_subset_1(B_44, k1_zfmisc_1(C_43)) | ~r2_hidden(A_45, B_44))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.57/2.10  tff(c_108, plain, (![B_46, A_47, A_48]: (~v1_xboole_0(B_46) | ~r2_hidden(A_47, A_48) | ~r1_tarski(A_48, B_46))), inference(resolution, [status(thm)], [c_16, c_100])).
% 5.57/2.10  tff(c_112, plain, (![B_49, A_50, B_51]: (~v1_xboole_0(B_49) | ~r1_tarski(A_50, B_49) | r1_tarski(A_50, B_51))), inference(resolution, [status(thm)], [c_6, c_108])).
% 5.57/2.10  tff(c_119, plain, (![B_52, B_53]: (~v1_xboole_0(B_52) | r1_tarski(B_52, B_53))), inference(resolution, [status(thm)], [c_12, c_112])).
% 5.57/2.10  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.57/2.10  tff(c_129, plain, (![B_53, B_52]: (B_53=B_52 | ~r1_tarski(B_53, B_52) | ~v1_xboole_0(B_52))), inference(resolution, [status(thm)], [c_119, c_8])).
% 5.57/2.10  tff(c_815, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4' | ~v1_xboole_0('#skF_2'('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_807, c_129])).
% 5.57/2.10  tff(c_826, plain, (~v1_xboole_0('#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_794, c_815])).
% 5.57/2.10  tff(c_34, plain, (![B_26, A_24]: (B_26=A_24 | ~r1_tarski(A_24, B_26) | ~v1_zfmisc_1(B_26) | v1_xboole_0(B_26) | v1_xboole_0(A_24))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.57/2.10  tff(c_812, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4' | ~v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_807, c_34])).
% 5.57/2.10  tff(c_823, plain, (~v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_42, c_794, c_812])).
% 5.57/2.10  tff(c_835, plain, (~v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_826, c_823])).
% 5.57/2.10  tff(c_836, plain, (![A_140, B_141]: (v2_tex_2('#skF_2'(A_140, B_141), A_140) | v3_tex_2(B_141, A_140) | ~v2_tex_2(B_141, A_140) | ~m1_subset_1(B_141, k1_zfmisc_1(u1_struct_0(A_140))) | ~l1_pre_topc(A_140))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.57/2.10  tff(c_841, plain, (v2_tex_2('#skF_2'('#skF_3', '#skF_4'), '#skF_3') | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_40, c_836])).
% 5.57/2.10  tff(c_845, plain, (v2_tex_2('#skF_2'('#skF_3', '#skF_4'), '#skF_3') | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_795, c_841])).
% 5.57/2.10  tff(c_846, plain, (v2_tex_2('#skF_2'('#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_63, c_845])).
% 5.57/2.10  tff(c_931, plain, (![A_155, B_156]: (m1_subset_1('#skF_2'(A_155, B_156), k1_zfmisc_1(u1_struct_0(A_155))) | v3_tex_2(B_156, A_155) | ~v2_tex_2(B_156, A_155) | ~m1_subset_1(B_156, k1_zfmisc_1(u1_struct_0(A_155))) | ~l1_pre_topc(A_155))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.57/2.10  tff(c_38, plain, (![B_29, A_27]: (v1_zfmisc_1(B_29) | ~v2_tex_2(B_29, A_27) | ~m1_subset_1(B_29, k1_zfmisc_1(u1_struct_0(A_27))) | v1_xboole_0(B_29) | ~l1_pre_topc(A_27) | ~v2_tdlat_3(A_27) | ~v2_pre_topc(A_27) | v2_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.57/2.10  tff(c_2456, plain, (![A_283, B_284]: (v1_zfmisc_1('#skF_2'(A_283, B_284)) | ~v2_tex_2('#skF_2'(A_283, B_284), A_283) | v1_xboole_0('#skF_2'(A_283, B_284)) | ~v2_tdlat_3(A_283) | ~v2_pre_topc(A_283) | v2_struct_0(A_283) | v3_tex_2(B_284, A_283) | ~v2_tex_2(B_284, A_283) | ~m1_subset_1(B_284, k1_zfmisc_1(u1_struct_0(A_283))) | ~l1_pre_topc(A_283))), inference(resolution, [status(thm)], [c_931, c_38])).
% 5.57/2.10  tff(c_2465, plain, (v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_2'('#skF_3', '#skF_4')) | ~v2_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_846, c_2456])).
% 5.57/2.10  tff(c_2474, plain, (v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_2'('#skF_3', '#skF_4')) | v2_struct_0('#skF_3') | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_795, c_48, c_46, c_2465])).
% 5.57/2.10  tff(c_2476, plain, $false, inference(negUnitSimplification, [status(thm)], [c_63, c_50, c_826, c_835, c_2474])).
% 5.57/2.10  tff(c_2478, plain, (~v1_zfmisc_1('#skF_4')), inference(splitRight, [status(thm)], [c_58])).
% 5.57/2.10  tff(c_2477, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_58])).
% 5.57/2.10  tff(c_2605, plain, (![B_323, A_324]: (v2_tex_2(B_323, A_324) | ~v3_tex_2(B_323, A_324) | ~m1_subset_1(B_323, k1_zfmisc_1(u1_struct_0(A_324))) | ~l1_pre_topc(A_324))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.57/2.10  tff(c_2612, plain, (v2_tex_2('#skF_4', '#skF_3') | ~v3_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_40, c_2605])).
% 5.57/2.10  tff(c_2616, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_2477, c_2612])).
% 5.57/2.10  tff(c_3193, plain, (![B_389, A_390]: (v1_zfmisc_1(B_389) | ~v2_tex_2(B_389, A_390) | ~m1_subset_1(B_389, k1_zfmisc_1(u1_struct_0(A_390))) | v1_xboole_0(B_389) | ~l1_pre_topc(A_390) | ~v2_tdlat_3(A_390) | ~v2_pre_topc(A_390) | v2_struct_0(A_390))), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.57/2.10  tff(c_3203, plain, (v1_zfmisc_1('#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_40, c_3193])).
% 5.57/2.10  tff(c_3208, plain, (v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_2616, c_3203])).
% 5.57/2.10  tff(c_3210, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_42, c_2478, c_3208])).
% 5.57/2.10  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.57/2.10  
% 5.57/2.10  Inference rules
% 5.57/2.10  ----------------------
% 5.57/2.10  #Ref     : 0
% 5.57/2.10  #Sup     : 669
% 5.57/2.10  #Fact    : 0
% 5.57/2.10  #Define  : 0
% 5.57/2.10  #Split   : 24
% 5.57/2.10  #Chain   : 0
% 5.57/2.10  #Close   : 0
% 5.57/2.10  
% 5.57/2.10  Ordering : KBO
% 5.57/2.10  
% 5.57/2.10  Simplification rules
% 5.57/2.10  ----------------------
% 5.57/2.10  #Subsume      : 291
% 5.57/2.10  #Demod        : 285
% 5.57/2.10  #Tautology    : 66
% 5.57/2.10  #SimpNegUnit  : 70
% 5.57/2.10  #BackRed      : 0
% 5.57/2.10  
% 5.57/2.10  #Partial instantiations: 0
% 5.57/2.10  #Strategies tried      : 1
% 5.57/2.10  
% 5.57/2.10  Timing (in seconds)
% 5.57/2.10  ----------------------
% 5.57/2.10  Preprocessing        : 0.32
% 5.57/2.10  Parsing              : 0.18
% 5.57/2.10  CNF conversion       : 0.02
% 5.57/2.10  Main loop            : 0.98
% 5.57/2.11  Inferencing          : 0.33
% 5.57/2.11  Reduction            : 0.27
% 5.57/2.11  Demodulation         : 0.17
% 5.57/2.11  BG Simplification    : 0.03
% 5.57/2.11  Subsumption          : 0.29
% 5.57/2.11  Abstraction          : 0.04
% 5.57/2.11  MUC search           : 0.00
% 5.57/2.11  Cooper               : 0.00
% 5.57/2.11  Total                : 1.33
% 5.57/2.11  Index Insertion      : 0.00
% 5.57/2.11  Index Deletion       : 0.00
% 5.57/2.11  Index Matching       : 0.00
% 5.57/2.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
